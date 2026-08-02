import Std.Async.System

/-!
A small data-parallel array executor with no dependencies beyond Lean's
standard library.

Lean's task pool is a good fit for coarse tasks, but representing every
element of a large array as its own `Task` pays queue and scheduler traffic
per element. Linen instead starts a bounded set of workers that claim chunks
from an atomic cursor, with every region drawing its workers from one
process-wide slot budget so nested regions cannot oversubscribe the machine.
This balances uneven work without creating a task per element.

The worker count follows `LINEN_WORKERS`, then `LEAN_NUM_THREADS`, then the
machine's logical core count. The per-call `chunkSize` argument controls claim
granularity and defaults to one.
-/

namespace Linen

/-- Runtime settings for the executor. -/
structure Config where
  workers : Nat
deriving Repr, DecidableEq, Inhabited

private def positiveEnvNat (name : String) : BaseIO (Option Nat) := do
  let some value ← IO.getEnv name | return none
  let some n := value.toNat? | return none
  return if n == 0 then none else some n

/-- Read Linen's executor settings. Invalid and zero-valued overrides are
ignored. A failed core-count query falls back to one worker. -/
def Config.fromEnv : IO Config := do
  let override ← positiveEnvNat "LINEN_WORKERS"
  let runtime ← positiveEnvNat "LEAN_NUM_THREADS"
  let workers ← match override.orElse fun _ => runtime with
    | some n => pure n
    | none =>
      try
        let cores ← Std.Async.System.getCPUInfo
        pure (cores.size.max 1)
      catch _ =>
        pure 1
  return { workers }

/-- Process-wide executor settings, read once at startup. -/
initialize config : Config ← Config.fromEnv

/-- Atomically claim the next chunk. Returns its start index, or `size` when
exhausted; the caller computes the end. Returning only the start avoids
allocating chunk metadata. -/
private def claim (cursor : IO.Ref Nat) (size chunkSize : Nat) : BaseIO Nat := do
  cursor.modifyGet fun next =>
    if next < size then
      (next, (next + chunkSize).min size)
    else
      (next, next)

/-- Initial value-buffer capacity for one worker is `⌈size/count⌉`. A worker
that claims more than the average grows its buffer. -/
private def valuesCapacity (size count : Nat) : Nat :=
  (size + count - 1) / count

/-- Capacity estimate for one worker's chunk-start buffer under even
claiming. -/
private def startsCapacity (size count chunkSize : Nat) : Nat :=
  (size + chunkSize - 1) / chunkSize / count + 1

/-- Outcome of one team-growth attempt under the occupancy policy (see the
occupancy section below). `teamFull` is permanent for a region; `budgetFull`
is transient and worth retrying. -/
private inductive GrowResult where
  | spawned
  | budgetFull
  | teamFull
deriving Inhabited

/-- Whether a growth result permits further attempts. -/
private def GrowResult.retryable : GrowResult → Bool
  | .teamFull => false
  | _ => true

/-- Monadic `mapM` worker. It appends values in claim order and records
each chunk's start; the merge derives chunk lengths from those starts. One
team-growth attempt runs per successful claim; `growing` caches the verdict,
so a full team costs nothing per claim. -/
private partial def workerMapMLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (xs : Array α) (f : α → BaseIO β)
    (chunkSize : Nat) (growing : Bool) (values : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (values, starts)
  let stop := (start + chunkSize).min xs.size
  let growing ← if growing then (·.retryable) <$> growth else pure false
  let values ← xs.foldlM (fun values x => return values.push (← f x))
    values start stop
  workerMapMLoop growth cursor xs f chunkSize growing values
    (starts.push start)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapM (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (f : α → BaseIO β) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapMLoop growth cursor xs f chunkSize true
    (Array.mkEmpty valuesCap) (Array.mkEmpty startsCap)

/-- Monadic `mapReduceM` worker. Each chunk is folded left-to-right into
one partial, seeded by its first element, with per-claim team growth. -/
private partial def workerMapReduceMLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (xs : Array α) (f : α → BaseIO β)
    (op : β → β → β) (chunkSize : Nat) (growing : Bool) (partials : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (partials, starts)
  let stop := (start + chunkSize).min xs.size
  let growing ← if growing then (·.retryable) <$> growth else pure false
  let some x ← pure xs[start]?
    | return (partials, starts)
  let seed ← f x
  let acc ← xs.foldlM (fun acc x => return op acc (← f x))
    seed (start + 1) stop
  workerMapReduceMLoop growth cursor xs f op chunkSize growing
    (partials.push acc) (starts.push start)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapReduceM (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (f : α → BaseIO β) (op : β → β → β)
    (chunkSize startsCap : Nat) : BaseIO (Array β × Array Nat) :=
  workerMapReduceMLoop growth cursor xs f op chunkSize true
    (Array.mkEmpty startsCap) (Array.mkEmpty startsCap)

/-- Run one fallible chunk and return its first failing index and error.
Explicit recursion keeps early-exit bookkeeping out of the success loop. -/
private partial def runChunk (xs : Array α) (f : α → BaseIO (Except ε β))
    (stop : Nat) (i : Nat) (values : Array β) :
    BaseIO (Array β × Option (Nat × ε)) := do
  if i < stop then
    match xs[i]? with
    | none => return (values, none)
    | some x =>
      match ← f x with
      | .ok value => runChunk xs f stop (i + 1) (values.push value)
      | .error e => return (values, some (i, e))
  else
    return (values, none)

/-- Fallible `mapIO` worker. On failure it sets the cursor to `size`,
preventing new claims while current chunks run to completion, and retains
the lowest-index failure; because chunks are claimed in order, all earlier
elements have run when the workers join. Failed chunks are omitted; results
are merged only when every worker succeeds. Grown siblings exit at their
next claim after the cursor is poisoned. -/
private partial def workerMapIOLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (failure : IO.Ref (Option (Nat × ε)))
    (xs : Array α) (f : α → BaseIO (Except ε β)) (chunkSize : Nat)
    (growing : Bool) (values : Array β) (starts : Array Nat) :
    BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (values, starts)
  let stop := (start + chunkSize).min xs.size
  let growing ← if growing then (·.retryable) <$> growth else pure false
  match ← runChunk xs f stop start values with
  | (values, none) =>
    workerMapIOLoop growth cursor failure xs f chunkSize growing values
      (starts.push start)
  | (values, some (i, e)) =>
    cursor.set xs.size
    failure.modify fun current =>
      match current with
      | some (j, _) => if i < j then some (i, e) else current
      | none => some (i, e)
    return (values, starts)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapIO (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (failure : IO.Ref (Option (Nat × ε))) (xs : Array α)
    (f : α → BaseIO (Except ε β)) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapIOLoop growth cursor failure xs f chunkSize true
    (Array.mkEmpty valuesCap) (Array.mkEmpty startsCap)

private def workerCount (size chunkSize : Nat) : Nat :=
  let chunks := (size + chunkSize - 1) / chunkSize
  config.workers.min chunks

/-! ## Occupancy-based team sizing

Sizing a team from the chunk count alone would let concurrently running
regions oversubscribe the machine: each nested region would start its own
full team. Instead the process holds a single worker-slot budget of
`config.workers`. A region spawns a worker task only while it can reserve a
slot, and always runs one worker inline on its caller (holding a slot when
one is free, proceeding without one otherwise), so at most `config.workers`
Linen worker tasks are live or queued at any time and nested work without a
slot runs on its caller. The budget covers Linen-created workers only, not other tasks
in the process. Workers retry reservation on each claim, so a team that
started small grows as other regions retire and release slots. -/

/-- Live count of reserved worker slots. Kept scalar in a ref of its own so
the per-claim growth gate reads it without touching a shared boxed object; a
boxed value would pay contended reference-count updates on every read. -/
private initialize activeRef : IO.Ref Nat ← IO.mkRef 0

/-- Reservation traffic under the occupancy policy, updated only on
reservation events, never on the per-claim gate path. `spawnedTasks` counts
every spawned worker; `grownTasks` is the subset spawned from a worker's
per-claim growth attempt rather than from entry seeding. At quiescence the
granted reservations `attempts - deniedBudget` equal `releases`,
`underflows` is zero, and `peak` never exceeds `config.workers`. -/
structure BudgetStats where
  peak : Nat := 0
  attempts : Nat := 0
  deniedBudget : Nat := 0
  deniedRegion : Nat := 0
  spawnedTasks : Nat := 0
  grownTasks : Nat := 0
  releases : Nat := 0
  underflows : Nat := 0
deriving Nonempty

private initialize statsRef : IO.Ref BudgetStats ← IO.mkRef {}

/-- Reserve one worker slot if the budget allows, recording the attempt. -/
private def tryReserveSlot : BaseIO Bool := do
  let newActive ← activeRef.modifyGet fun a =>
    if a < config.workers then (some (a + 1), a + 1) else (none, a)
  match newActive with
  | some a =>
    statsRef.modify fun st =>
      { st with attempts := st.attempts + 1, peak := st.peak.max a }
    return true
  | none =>
    statsRef.modify fun st =>
      { st with attempts := st.attempts + 1,
                deniedBudget := st.deniedBudget + 1 }
    return false

/-- Return a worker's slot to the budget. The release is guarded: a release
without a matching reservation is recorded as an underflow instead of
saturating silently, so a double release cannot quietly widen the budget. -/
private def releaseSlot : BaseIO Unit := do
  let ok ← activeRef.modifyGet fun a =>
    if a == 0 then (false, 0) else (true, a - 1)
  statsRef.modify fun st =>
    if ok then { st with releases := st.releases + 1 }
    else { st with underflows := st.underflows + 1 }

/-- Return a slot lost in a race for a region's last team position. -/
private def releaseSlotRegionFull : BaseIO Unit := do
  releaseSlot
  statsRef.modify fun st => { st with deniedRegion := st.deniedRegion + 1 }

/-- Run one worker and release its slot when it finishes. Every reserved
worker runs through this wrapper. `BaseIO` cannot throw, and the fail-fast
loops return normally after poisoning their cursor, so the release always
runs. -/
private def slottedWorker (work : BaseIO (Array β × Array Nat)) :
    BaseIO (Array β × Array Nat) := do
  let out ← work
  releaseSlot
  return out

/-- Per-region team state under the occupancy policy. `spawned` counts team
positions handed out, capped at `slots`; `registry` collects spawned worker
tasks for the region's join. -/
private structure Region (β : Type) where
  slots : Nat
  spawned : IO.Ref Nat
  registry : IO.Ref (Array (Task (Array β × Array Nat)))

/-- One team-growth attempt: reserve a global slot, then a team position, and
spawn a sibling worker holding both. The slot is released again if another
worker took the region's last position first; the atomic position counter is
what bounds the team, since concurrent workers could all pass a plain read of
it. Two plain reads of scalar counters gate the reservation, so a saturated
pool costs no read-modify-write per claim (budget denials under the read
gate therefore go unrecorded; `deniedBudget` counts lost races only). The
team-position gate comes first: a full team is permanent for the region --
`spawned` never decreases -- so `teamFull` lets callers stop attempting for
the rest of the region, while `budgetFull` is transient and worth retrying.
A spawned child is registered before its spawner can finish, which
`joinRegion` relies on. `fromWorker` distinguishes per-claim growth from
entry seeding in the statistics. -/
private partial def growTeam (region : Region β) (fromWorker : Bool)
    (mkWork : BaseIO GrowResult → BaseIO (Array β × Array Nat)) :
    BaseIO GrowResult := do
  if (← region.spawned.get) ≥ region.slots then return .teamFull
  if (← activeRef.get) ≥ config.workers then return .budgetFull
  if ← tryReserveSlot then
    if ← region.spawned.modifyGet fun s =>
        if s < region.slots then (true, s + 1) else (false, s) then
      let task ← BaseIO.asTask
        (slottedWorker (mkWork (growTeam region true mkWork)))
      region.registry.modify (·.push task)
      statsRef.modify fun st =>
        { st with spawnedTasks := st.spawnedTasks + 1,
                  grownTasks := st.grownTasks + (if fromWorker then 1 else 0) }
      return .spawned
    else
      releaseSlotRegionFull
      return .teamFull
  else
    return .budgetFull

/-- Wait for every spawned worker. Each round atomically empties the registry
and joins that batch; a worker registers any child before finishing, so an
empty registry observed after a fully joined batch means no producer remains.
Reading the registry without the swap would race with a late spawn. -/
private def joinRegion (region : Region β)
    (outs : Array (Array β × Array Nat)) :
    BaseIO (Array (Array β × Array Nat)) := do
  let mut outs := outs
  repeat
    let batch ← region.registry.modifyGet fun tasks => (tasks, (#[] : Array _))
    if batch.isEmpty then break
    for task in batch do
      outs := outs.push (← IO.wait task)
  return outs

/-- Run one region under the occupancy policy: seed the team from the free
budget, run one worker inline on the caller (the region's progress guarantee;
it proceeds with or without a slot), and join. Per-claim growth attempts let
the team approach `slots` as the budget frees up, so a region that started
small is not stuck small. The inline worker holds a slot when one is free: a
fully used budget is then visible to the growth read gates, which would
otherwise chase a permanently free slot with a reservation per claim. A
caller that is itself a slotted worker thereby reserves a second slot for
its inline role, conservatively under-provisioning some nested teams by one;
tracking execution context to avoid this is deliberately out of scope.
Seeding stops at the first denial, so on a saturated pool a nested region
costs a few counter reads rather than `slots` growth attempts. -/
private def runGrowingRegion (slots : Nat)
    (mkWork : BaseIO GrowResult → BaseIO (Array β × Array Nat)) :
    BaseIO (Array (Array β × Array Nat)) := do
  let region : Region β := ⟨slots, ← IO.mkRef 0, ← IO.mkRef #[]⟩
  let inlineSlot ← if (← activeRef.get) < config.workers then tryReserveSlot
    else pure false
  let mut seeding := true
  for _ in [0:slots] do
    if seeding then
      seeding := (← growTeam region false mkWork) matches .spawned
  let mine ← mkWork (growTeam region true mkWork)
  if inlineSlot then releaseSlot
  joinRegion region #[mine]

/-! Workers for the pure runtimes (`mapImpl` and `mapReduceImpl`). Their inner
loops call `f` and `op` without `BaseIO`. Bounds derived from `claim` justify
the array reads; the proofs are erased at compile time. Task setup, claiming,
bookkeeping, and ordered merging remain outside the inner loops. -/

private def mapChunkPure (xs : Array α) (f : α → β) (stop : Nat)
    (i : Nat) (values : Array β) : Array β :=
  xs.foldl (fun values x => values.push (f x)) values i stop

/-- Pure `map` worker with one team-growth attempt per successful claim.
`growing` caches `growth`'s verdict: once the team is full the loop stops
attempting, leaving no per-claim cost. -/
private partial def workerMapPureLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (xs : Array α) (f : α → β) (chunkSize : Nat)
    (growing : Bool) (values : Array β) (starts : Array Nat) :
    BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (values, starts)
  let stop := (start + chunkSize).min xs.size
  let growing ← if growing then (·.retryable) <$> growth else pure false
  workerMapPureLoop growth cursor xs f chunkSize growing
    (mapChunkPure xs f stop start values)
    (starts.push start)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapPure (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (f : α → β) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapPureLoop growth cursor xs f chunkSize true
    (Array.mkEmpty valuesCap) (Array.mkEmpty startsCap)

private def reduceChunkPure (xs : Array α) (f : α → β) (op : β → β → β)
    (stop : Nat) (i : Nat) (acc : β) : β :=
  xs.foldl (fun acc x => op acc (f x)) acc i stop

/-- Pure reducing worker: each chunk folds to one partial seeded by its
first element, with per-claim team growth. -/
private partial def workerReducePureLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (xs : Array α) (f : α → β) (op : β → β → β)
    (chunkSize : Nat) (growing : Bool) (partials : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if hstart : start < xs.size then
    let stop := (start + chunkSize).min xs.size
    let growing ← if growing then (·.retryable) <$> growth else pure false
    let seed := f (xs[start]'hstart)
    let acc := reduceChunkPure xs f op stop (start + 1) seed
    workerReducePureLoop growth cursor xs f op chunkSize growing
      (partials.push acc) (starts.push start)
  else
    return (partials, starts)

/-- Allocate worker-local buffers inside the task. -/
private def workerReducePure (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (f : α → β) (op : β → β → β) (chunkSize startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerReducePureLoop growth cursor xs f op chunkSize true
    (Array.mkEmpty startsCap) (Array.mkEmpty startsCap)

/-- Fold state while placing one worker's runs: the running buffer offset
and the two placement tables. -/
private structure PlaceRun where
  offset : Nat
  slotWorker : Array Nat
  slotOffset : Array Nat

/-- One run placed: record the owner and the run's buffer offset at the
run's ordinal, and advance the offset. -/
private def placeRun (chunkSize : Nat) (lenOf : Nat → Nat) (worker : Nat)
    (st : PlaceRun) (start : Nat) : PlaceRun :=
  { offset := st.offset + lenOf start,
    slotWorker := st.slotWorker.set! (start / chunkSize) (worker + 1),
    slotOffset := st.slotOffset.set! (start / chunkSize) st.offset }

/-- Fold state across workers: the next worker index and the tables. -/
private structure PlaceAll where
  worker : Nat
  slotWorker : Array Nat
  slotOffset : Array Nat

/-- One worker placed: fold its runs through `placeRun` and advance the
worker index. -/
private def placeWorker (chunkSize : Nat) (lenOf : Nat → Nat)
    (st : PlaceAll) (out : Array β × Array Nat) : PlaceAll :=
  let run := out.2.foldl (placeRun chunkSize lenOf st.worker)
    { offset := 0, slotWorker := st.slotWorker,
      slotOffset := st.slotOffset }
  { worker := st.worker + 1, slotWorker := run.slotWorker,
    slotOffset := run.slotOffset }

/-- Build lookup tables from chunk ordinal to worker and buffer offset.
`slotWorker` stores the worker index plus one, reserving zero for unclaimed
chunks. `slotOffset` stores the run's offset in that worker's buffer; `lenOf`
advances the offset between runs. -/
private def placeChunks (outs : Array (Array β × Array Nat))
    (chunkCount chunkSize : Nat) (lenOf : Nat → Nat) :
    Array Nat × Array Nat :=
  let st := outs.foldl (placeWorker chunkSize lenOf)
    { worker := 0, slotWorker := Array.replicate chunkCount 0,
      slotOffset := Array.replicate chunkCount 0 }
  (st.slotWorker, st.slotOffset)

/-- Append `values[j:stop)` onto `r`: a bounded fold, which compiles to a
tight loop with the bound computed once. -/
private def pushRange (values : Array β) (stop j : Nat) (r : Array β) :
    Array β :=
  values.foldl (fun r value => r.push value) r j stop

/-- One ordinal's contribution to the merge: append the owning worker's
buffer segment, or nothing for an unclaimed ordinal. A pure function so
`merge`'s loop body is a single state update, which the correspondence
proofs convert to a fold directly. -/
private def mergeStep (outs : Array (Array β × Array Nat))
    (slotWorker slotOffset : Array Nat) (size chunkSize ordinal : Nat)
    (result : Array β) : Array β :=
  let w := slotWorker[ordinal]!
  if w == 0 then result
  else
    match outs[w - 1]? with
    | some (values, _) =>
      let offset := slotOffset[ordinal]!
      let stop := offset + chunkSize.min (size - ordinal * chunkSize)
      pushRange values stop offset result
    | none => result

/-- Pure range loop over chunk ordinals: an index loop with no underlying
collection, so a small recursion rather than a collection fold. -/
private def mergeLoop (outs : Array (Array β × Array Nat))
    (slotWorker slotOffset : Array Nat) (size chunkSize cc ordinal : Nat)
    (result : Array β) : Array β :=
  if ordinal < cc then
    mergeLoop outs slotWorker slotOffset size chunkSize cc (ordinal + 1)
      (mergeStep outs slotWorker slotOffset size chunkSize ordinal result)
  else result
termination_by cc - ordinal

/-- Restore per-worker buffers to input order: place every chunk run by
ordinal without sorting, then append each ordinal's segment. -/
private def merge (outs : Array (Array β × Array Nat))
    (size chunkSize : Nat) : Array β :=
  let chunkCount := (size + chunkSize - 1) / chunkSize
  let tables :=
    placeChunks outs chunkCount chunkSize fun start => chunkSize.min (size - start)
  mergeLoop outs tables.1 tables.2 size chunkSize chunkCount 0
    (Array.mkEmpty size)

/-- Collect per-chunk partials into chunk-ordinal order. -/
private def orderedPartials (outs : Array (Array β × Array Nat))
    (size chunkSize : Nat) : Array β := Id.run do
  let chunkCount := (size + chunkSize - 1) / chunkSize
  let (slotWorker, slotOffset) := placeChunks outs chunkCount chunkSize fun _ => 1
  let mut ps : Array β := Array.mkEmpty chunkCount
  for ordinal in [0:chunkCount] do
    let w := slotWorker[ordinal]!
    if w > 0 then
      if let some (partials, _) := outs[w - 1]? then
        if let some p := partials[slotOffset[ordinal]!]? then
          ps := ps.push p
  return ps

/-- Combine chunk partials in input order. When partials outnumber workers,
first fold contiguous groups in parallel, leaving at most one partial per
worker for the final serial fold. Associativity preserves the sequential
left-fold result. If there are already at most as many partials as workers,
the parallel level would apply no `op`, so it is skipped. -/
private def mergeReduce (outs : Array (Array β × Array Nat))
    (size chunkSize : Nat) (op : β → β → β) (init : β) : BaseIO β := do
  let ps := orderedPartials outs size chunkSize
  if ps.size ≤ config.workers then
    return ps.foldl op init
  else
    let levelChunk := (ps.size + config.workers - 1) / config.workers
    let count := workerCount ps.size levelChunk
    let cursor ← IO.mkRef 0
    let levelOuts ← runGrowingRegion (count - 1) fun growth =>
      workerReducePure growth cursor ps id op levelChunk
        (startsCapacity ps.size count levelChunk)
    return (orderedPartials levelOuts ps.size levelChunk).foldl op init

/-- Parallel map using at most one task per configured worker. Workers claim
chunks dynamically, and the results are restored to input order. `chunkSize`
is clamped to at least one. -/
def mapM (xs : Array α) (f : α → BaseIO β) (chunkSize : Nat := 1) :
    BaseIO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.mapM f
  else
    let count := workerCount xs.size chunkSize
    let cursor ← IO.mkRef 0
    let outs ← runGrowingRegion (count - 1) fun growth =>
      workerMapM growth cursor xs f chunkSize
        (valuesCapacity xs.size count)
        (startsCapacity xs.size count chunkSize)
    return merge outs xs.size chunkSize

/-- Monadic map-reduce using dynamically claimed chunks. Each chunk produces
one partial; `mergeReduce` combines them in input order. `op` must be
associative but need not be commutative. -/
def mapReduceM (xs : Array α) (f : α → BaseIO β) (op : β → β → β)
    (init : β) (chunkSize : Nat := 1) [Std.Associative op] : BaseIO β := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.foldlM (fun acc x => return op acc (← f x)) init
  else
    let count := workerCount xs.size chunkSize
    let cursor ← IO.mkRef 0
    let outs ← runGrowingRegion (count - 1) fun growth =>
      workerMapReduceM growth cursor xs f op chunkSize
        (startsCapacity xs.size count chunkSize)
    mergeReduce outs xs.size chunkSize op init

/-- Parallel engine for the pure `map` runtime; preconditions (more than one
worker, `size > chunkSize`) are checked by `mapImpl`. -/
private def mapCoreIO (xs : Array α) (f : α → β) (chunkSize : Nat) :
    BaseIO (Array β) := do
  let base := workerCount xs.size chunkSize
  let cursor ← IO.mkRef 0
  -- The caller runs one worker inline, so the spawn cap is `base - 1`.
  let outs ← runGrowingRegion (base - 1) fun growth =>
    workerMapPure growth cursor xs f chunkSize
      (valuesCapacity xs.size base)
      (startsCapacity xs.size base chunkSize)
  return merge outs xs.size chunkSize

/-- Parallel engine for the pure `mapReduce` runtime; preconditions as for
`mapCoreIO`. -/
private def reduceCoreIO (xs : Array α) (f : α → β) (op : β → β → β)
    (init : β) (chunkSize : Nat) : BaseIO β := do
  let count := workerCount xs.size chunkSize
  let cursor ← IO.mkRef 0
  let outs ← runGrowingRegion (count - 1) fun growth =>
    workerReducePure growth cursor xs f op chunkSize
      (startsCapacity xs.size count chunkSize)
  mergeReduce outs xs.size chunkSize op init

/-- Runtime implementation of `map`. Its public specification is `xs.map f`,
so tasks and scheduling are absent from proofs. -/
private unsafe def mapImpl.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (chunkSize : Nat := 1) : Array β :=
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    -- Serial fast path through the bounded chunk fold: the bound is
    -- clamped once and the inner reads are unchecked, and with
    -- `stop = xs.size` the fold is exactly `xs.map f`.
    mapChunkPure xs f xs.size 0 (Array.mkEmpty xs.size)
  else
    -- `unsafeBaseIO` is justified because `f` is pure and the result does not
    -- depend on scheduling. The `NonScalar` casts bridge `BaseIO`'s `Type 0`
    -- boundary using the boxed erasure pattern from `Array.mapMUnsafe`.
    unsafeCast (unsafeBaseIO (mapCoreIO (unsafeCast xs : Array NonScalar)
      (unsafeCast f : NonScalar → NonScalar) chunkSize))

/-- Parallel `Array.map`, preserving input order. Its specification is
`xs.map f` for every `chunkSize`; chunk size affects runtime scheduling, not
the result. -/
@[implemented_by mapImpl]
def map.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (chunkSize : Nat := 1) : Array β :=
  xs.map f

/-- Parallel `Array.filterMap`, preserving input order. -/
def filterMap (xs : Array α) (f : α → Option β) (chunkSize : Nat := 1) :
    Array β :=
  (map xs f chunkSize).filterMap id

/-- Parallel flat-map, preserving input and per-element output order. -/
def flatMap (xs : Array α) (f : α → Array β) (chunkSize : Nat := 1) :
    Array β :=
  (map xs f chunkSize).flatten

private unsafe def mapReduceImpl.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (op : β → β → β) (init : β)
    (chunkSize : Nat := 1) [Std.Associative op] : β :=
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    -- Serial fast path through the bounded chunk fold: no task setup, no
    -- intermediate partials, the bound clamped once with unchecked inner
    -- reads, and with `stop = xs.size` the fold is exactly the fused left
    -- fold of the specification.
    reduceChunkPure xs f op xs.size 0 init
  else
    -- The same trust boundary as `mapImpl`; `op` and `init` are also cast
    -- through `NonScalar`.
    unsafeCast (unsafeBaseIO (reduceCoreIO (unsafeCast xs : Array NonScalar)
      (unsafeCast f : NonScalar → NonScalar)
      (unsafeCast op) (unsafeCast init) chunkSize))

/-- Parallel map-reduce with sequential specification
`(xs.map f).foldl op init`. Partials are combined in input order, so
associativity is sufficient: `op` need not be commutative, and `init` need not
be an identity. On the parallel path, contiguous groups of partials are also
combined in parallel when needed; the final serial fold applies `op` at most
`config.workers` times. -/
@[implemented_by mapReduceImpl]
def mapReduce.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (op : β → β → β) (init : β)
    (chunkSize : Nat := 1) [Std.Associative op] : β :=
  (xs.map f).foldl op init

/-- Parallel `IO` map. A failure stops new claims; after current chunks finish,
the failure with the lowest input index is rethrown deterministically (see
`workerMapIOLoop`). `chunkSize` is clamped to at least one. -/
def mapIO (xs : Array α) (f : α → IO β) (chunkSize : Nat := 1) :
    IO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.mapM f
  else
    let count := workerCount xs.size chunkSize
    let cursor ← IO.mkRef 0
    let failure ← IO.mkRef (none : Option (Nat × IO.Error))
    let outs ← runGrowingRegion (count - 1) fun growth =>
      workerMapIO growth cursor failure xs (fun x => (f x).toBaseIO) chunkSize
        (valuesCapacity xs.size count)
        (startsCapacity xs.size count chunkSize)
    match ← failure.get with
    | some (_, e) => throw e
    | none => return merge outs xs.size chunkSize

/-- Parallel `IO` traversal, fail-fast with the same deterministic
smallest-index error reporting as `mapIO`. -/
def forEach (xs : Array α) (f : α → IO Unit) (chunkSize : Nat := 1) :
    IO Unit :=
  discard <| mapIO xs f chunkSize

/-! ## Verified properties

The runtime implementations' trust boundary sits at `unsafeBaseIO`: Lean
cannot directly state kernel theorems about this unsafe task execution, so the
correspondence between the parallel engine and the serial specifications is
split into pure lemmas about the engine's pieces. Below, the serial chunk loops
equal their specification slices, which verifies the serial fast paths
outright; the associative regrouping core and `map`'s ordered-merge
reconstruction are also proved. The reduce-side instantiation -- including
the optional second reduction level -- and the bridge asserting that the
concurrent runtime always yields well-formed worker output remain open (see
LINEN.md). -/

/-- The pure map chunk loop computes exactly the mapped slice, appended to
the accumulator. -/
private theorem mapChunkPure_eq (xs : Array α) (f : α → β) (stop : Nat)
    (i : Nat) (values : Array β) :
    mapChunkPure xs f stop i values
      = values ++ (xs.extract i stop).map f := by
  unfold mapChunkPure
  rw [Array.foldl_eq_foldl_extract]
  grind

/-- The pure reduce chunk loop is the left fold of the mapped slice. -/
private theorem reduceChunkPure_eq (xs : Array α) (f : α → β)
    (op : β → β → β) (stop : Nat) (i : Nat) (acc : β) :
    reduceChunkPure xs f op stop i acc
      = ((xs.extract i stop).map f).foldl op acc := by
  unfold reduceChunkPure
  rw [Array.foldl_eq_foldl_extract]
  grind [Array.foldl_map]

/-- The serial fast path of `mapImpl` is the specification. -/
private theorem mapChunkPure_full (xs : Array α) (f : α → β) :
    mapChunkPure xs f xs.size 0 (Array.mkEmpty xs.size)
      = xs.map f := by
  simp [mapChunkPure_eq]

/-- The serial fast path of `mapReduceImpl` is the specification's fused
left fold. -/
private theorem reduceChunkPure_full (xs : Array α) (f : α → β)
    (op : β → β → β) (init : β) :
    reduceChunkPure xs f op xs.size 0 init
      = (xs.map f).foldl op init := by
  simp [reduceChunkPure_eq]

/-- Regrouping lemma for `mapReduce`: folding seeded chunk partials in input
order equals folding all elements, given associativity. Each chunk is
represented as its seed and remaining elements, matching how
`workerReducePureLoop` folds a claimed chunk from its first element. -/
private theorem foldl_seeded_partials (op : β → β → β) [Std.Associative op]
    (chunks : List (β × List β)) (init : β) :
    (chunks.map fun c => c.2.foldl op c.1).foldl op init
      = (chunks.map fun c => c.1 :: c.2).flatten.foldl op init := by
  induction chunks generalizing init with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons, List.flatten_cons,
      List.foldl_append]
    rw [← List.foldl_assoc (op := op) (l := c.2) (a₁ := init) (a₂ := c.1)]
    exact ih _

/-! Rungs 3-4 of the correspondence ladder: well-formed worker output, and
the pure assembly lemmas showing ordered chunk slices reconstruct the
specification. -/

/-- The mapped slice of the chunk starting at `s`. -/
private def chunkSlice (xs : Array α) (f : α → β) (chunkSize s : Nat) :
    Array β :=
  (xs.extract s (min (s + chunkSize) xs.size)).map f

/-- Well-formed output of one worker, parameterised by the `piece` each
recorded start contributes: starts are chunk-aligned and below `bound`, and
the value buffer is exactly the concatenated pieces of the recorded runs,
in claim order. `map` instantiates `piece` with the mapped chunk slice; a
reducing worker instantiates it with the singleton chunk partial, sharing
this placement and extraction theory. -/
private structure WFWorkerOut (piece : Nat → Array β)
    (chunkSize bound : Nat) (out : Array β × Array Nat) : Prop where
  aligned : ∀ start ∈ out.2.toList, start % chunkSize = 0 ∧ start < bound
  values : out.1 = out.2.foldl (fun acc start => acc ++ piece start) #[]

/-- A worker/run position whose recorded start is `start`. The output and
both successful lookups travel with the indices, so consumers do not repeat
Array/List lookup conversions. -/
private structure RunAt (outs : List (Array β × Array Nat)) (start : Nat) where
  worker : Nat
  runIdx : Nat
  out : Array β × Array Nat
  worker_eq : outs[worker]? = some out
  run_eq : out.2[runIdx]? = some start

/-- An aligned run at ordinal `o` gives a `RunAt` witness for `o * c`. -/
private theorem RunAt.exists_ofOrdinal (outs : List (Array β × Array Nat))
    (c o s w k : Nat) (out : Array β × Array Nat)
    (halign : ∀ out ∈ outs, ∀ start ∈ out.2.toList, start % c = 0)
    (hworker : outs[w]? = some out) (hrun : out.2[k]? = some s)
    (hso : s / c = o) :
    ∃ run : RunAt outs (o * c), run.worker = w ∧ run.runIdx = k := by
  have hmem : s ∈ out.2.toList := by
    simpa using Array.mem_of_getElem? hrun
  have hdiv := Nat.div_mul_cancel
    (Nat.dvd_of_mod_eq_zero
      (halign out (List.mem_of_getElem? hworker) s hmem))
  have heq : s = o * c := by
    rw [← hso]
    exact hdiv.symm
  exact ⟨⟨w, k, out, hworker, by simpa [heq] using hrun⟩, rfl, rfl⟩

/-- Well-formed collective worker output, parameterised like
`WFWorkerOut`: each worker is well formed and every chunk ordinal below the
chunk count of `bound` is recorded exactly once across all workers. Worker
count and claim order are otherwise unconstrained. The map correspondence
instantiates `piece` with `chunkSlice xs f chunkSize` and `bound` with
`xs.size`. -/
private structure WFOuts (piece : Nat → Array β) (chunkSize bound : Nat)
    (outs : Array (Array β × Array Nat)) : Prop where
  chunkPos : 0 < chunkSize
  workers : ∀ out ∈ outs.toList, WFWorkerOut piece chunkSize bound out
  once : ∀ o < (bound + chunkSize - 1) / chunkSize,
    ∃ run : RunAt outs.toList (o * chunkSize),
      ∀ other : RunAt outs.toList (o * chunkSize),
        other.worker = run.worker ∧ other.runIdx = run.runIdx

/-- Concatenating the chunk slices of all ordinals in order reconstructs the
mapped array. -/
private theorem foldl_chunkSlice_range (xs : Array α) (f : α → β)
    (chunkSize : Nat) (hchunk : 0 < chunkSize) :
    (List.range ((xs.size + chunkSize - 1) / chunkSize)).foldl
      (fun acc o => acc ++ chunkSlice xs f chunkSize (o * chunkSize)) #[]
        = xs.map f := by
  have aux : ∀ k : Nat,
      (List.range k).foldl
        (fun acc o => acc ++ chunkSlice xs f chunkSize (o * chunkSize)) #[]
          = (xs.extract 0 (min (k * chunkSize) xs.size)).map f := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih]
      unfold chunkSlice
      rw [← Array.map_append]
      congr 1
      grind
  rw [aux]
  have hcover : xs.size ≤ (xs.size + chunkSize - 1) / chunkSize * chunkSize := by
    have hdm := Nat.div_add_mod (xs.size + chunkSize - 1) chunkSize
    have hlt := Nat.mod_lt (xs.size + chunkSize - 1) hchunk
    grind
  grind

/-- Shifting a sum-fold's initial value out front. -/
private theorem foldl_add_shift (g : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun n s => n + g s) a = a + l.foldl (fun n s => n + g s) 0 := by
  rw [← List.foldl_map (f := g) (g := (· + ·)),
    ← List.foldl_map (f := g) (g := (· + ·)),
    ← Nat.add_zero a, List.foldl_assoc, Nat.add_zero]

/-- Appending more blocks to a buffer does not disturb an extraction that
lies within the existing prefix. -/
private theorem extract_foldl_append_of_le (g : Nat → Array β)
    (l : List Nat) (b : Array β) (i j : Nat) (hj : j ≤ b.size) :
    (l.foldl (fun acc s => acc ++ g s) b).extract i j = b.extract i j := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih =>
    have hj' : j ≤ (b ++ g x).size := by grind
    rw [List.foldl_cons, ih (b ++ g x) hj']
    grind

/-- `pushRange` appends exactly the extracted segment. -/
private theorem pushRange_eq (values : Array β) (stop j : Nat)
    (r : Array β) :
    pushRange values stop j r = r ++ values.extract j stop := by
  unfold pushRange
  rw [Array.foldl_eq_foldl_extract]
  simpa using (Array.foldl_push_eq_append
    (as := values.extract j stop) (bs := r) (f := id) rfl)

/-- Extracting a run's block from a well-formed buffer at its prefix-sum
offset yields exactly that run's piece: the pure content of `merge`'s
per-ordinal copy, given `WFWorkerOut.values`. Stated for an arbitrary
per-start `piece`, so the map and reduce instantiations share it. -/
private theorem extract_foldl_pieces (piece : Nat → Array β)
    (starts : List Nat) (k : Nat) (hk : k < starts.length)
    (acc : Array β) :
    ((starts.foldl (fun b s => b ++ piece s) acc).extract
        (acc.size
          + (starts.take k).foldl (fun n s => n + (piece s).size) 0)
        (acc.size
          + (starts.take k).foldl (fun n s => n + (piece s).size) 0
          + (piece starts[k]).size))
      = piece starts[k] := by
  induction starts generalizing k acc with
  | nil => exact absurd hk (by simp)
  | cons s rest ih =>
    match k with
    | 0 =>
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil,
        Nat.add_zero, List.getElem_cons_zero]
      rw [extract_foldl_append_of_le _ rest (acc ++ piece s) acc.size
        (acc.size + (piece s).size) (by grind)]
      grind
    | k + 1 =>
      simp only [List.foldl_cons, List.take_succ_cons,
        List.getElem_cons_succ]
      rw [foldl_add_shift _ (List.take k rest)]
      simpa [Array.size_append, Nat.add_assoc]
        using ih k (Nat.lt_of_succ_lt_succ hk) (acc ++ piece s)

/-- The ordinal loop is the fold of `mergeStep` over the remaining
ordinals. -/
private theorem mergeLoop_eq (outs : Array (Array β × Array Nat))
    (slotWorker slotOffset : Array Nat) (size chunkSize cc ordinal : Nat)
    (result : Array β) :
    mergeLoop outs slotWorker slotOffset size chunkSize cc ordinal result
      = (List.range' ordinal (cc - ordinal)).foldl
          (fun r o => mergeStep outs slotWorker slotOffset size chunkSize o r)
          result := by
  unfold mergeLoop
  split
  next h =>
    rw [mergeLoop_eq outs slotWorker slotOffset size chunkSize cc
      (ordinal + 1)]
    rw [show cc - ordinal = (cc - (ordinal + 1)) + 1 from by omega]
    simp [List.range'_succ]
  next h =>
    rw [show cc - ordinal = 0 from by omega]
    rfl
termination_by cc - ordinal

/-- `merge` as a pure fold over chunk ordinals. -/
private theorem merge_eq_foldl (outs : Array (Array β × Array Nat))
    (size chunkSize : Nat) :
    merge outs size chunkSize
      = (List.range ((size + chunkSize - 1) / chunkSize)).foldl
          (fun r o =>
            mergeStep outs
              (placeChunks outs ((size + chunkSize - 1) / chunkSize) chunkSize
                fun start => chunkSize.min (size - start)).1
              (placeChunks outs ((size + chunkSize - 1) / chunkSize) chunkSize
                fun start => chunkSize.min (size - start)).2
              size chunkSize o r)
          (Array.mkEmpty size) := by
  rw [merge, mergeLoop_eq]
  simp [List.range_eq_range']

/-- Prefix sum of piece lengths over the first `k` recorded runs: the
buffer offset `placeChunks` records for run `k`. -/
private def prefixLen (lenOf : Nat → Nat) (starts : List Nat) (k : Nat) :
    Nat :=
  (starts.take k).foldl (fun n s => n + lenOf s) 0

/-- One logical write performed by `placeChunks`. -/
private structure RunPlacement where
  worker : Nat
  start : Nat
  offset : Nat

/-- Logical writes for one worker, with offsets supplied by a prefix scan. -/
private noncomputable def workerPlacementTrace (lenOf : Nat → Nat)
    (worker : Nat) (starts : List Nat) (offset : Nat) : List RunPlacement :=
  (starts.zip (starts.scanl (fun n s => n + lenOf s) offset)).map fun p =>
    { worker, start := p.1, offset := p.2 }

/-- The nested worker/run output flattened into its logical table writes. -/
private noncomputable def placementTrace (lenOf : Nat → Nat)
    (firstWorker : Nat)
    (outs : List (Array β × Array Nat)) : List RunPlacement :=
  (outs.zipIdx firstWorker).flatMap fun p =>
    workerPlacementTrace lenOf p.2 p.1.2.toList 0

/-- Apply one logical table write. -/
private noncomputable def applyRunPlacement (c : Nat)
    (tables : Array Nat × Array Nat)
    (run : RunPlacement) : Array Nat × Array Nat :=
  (tables.1.set! (run.start / c) (run.worker + 1),
    tables.2.set! (run.start / c) run.offset)

/-- Folding `placeRun` performs exactly the corresponding logical writes. -/
private theorem placeRun_foldl_eq_trace (c : Nat) (lenOf : Nat → Nat)
    (worker : Nat) (starts : List Nat) (st : PlaceRun) :
    let final := starts.foldl (placeRun c lenOf worker) st
    (final.slotWorker, final.slotOffset) =
      (workerPlacementTrace lenOf worker starts st.offset).foldl
        (applyRunPlacement c) (st.slotWorker, st.slotOffset) := by
  induction starts generalizing st with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.foldl_cons]
    rw [ih (st := placeRun c lenOf worker st s)]
    simp [workerPlacementTrace, applyRunPlacement, placeRun, List.scanl_cons]

/-- The nested implementation fold equals one fold over logical writes. -/
private theorem placeWorker_foldl_eq_trace (c : Nat) (lenOf : Nat → Nat)
    (outs : List (Array β × Array Nat)) (st : PlaceAll) :
    let final := outs.foldl (placeWorker c lenOf) st
    (final.slotWorker, final.slotOffset) =
      (placementTrace lenOf st.worker outs).foldl (applyRunPlacement c)
        (st.slotWorker, st.slotOffset) := by
  induction outs generalizing st with
  | nil => rfl
  | cons out rest ih =>
    have hin := placeRun_foldl_eq_trace c lenOf st.worker out.2.toList
      { offset := 0, slotWorker := st.slotWorker,
        slotOffset := st.slotOffset }
    have hrec := ih (placeWorker c lenOf st out)
    have hin' :
        ((placeWorker c lenOf st out).slotWorker,
          (placeWorker c lenOf st out).slotOffset) =
          (workerPlacementTrace lenOf st.worker out.2.toList 0).foldl
            (applyRunPlacement c) (st.slotWorker, st.slotOffset) := by
      simpa [placeWorker, Array.foldl_toList] using hin
    have hrec' :
        let final := rest.foldl (placeWorker c lenOf) (placeWorker c lenOf st out)
        (final.slotWorker, final.slotOffset) =
          (placementTrace lenOf (st.worker + 1) rest).foldl
            (applyRunPlacement c)
            ((placeWorker c lenOf st out).slotWorker,
              (placeWorker c lenOf st out).slotOffset) := by
      simpa [placeWorker] using hrec
    simp only [List.foldl_cons]
    rw [hrec']
    rw [show placementTrace lenOf st.worker (out :: rest) =
        workerPlacementTrace lenOf st.worker out.2.toList 0 ++
          placementTrace lenOf (st.worker + 1) rest from rfl,
      List.foldl_append, ← hin']

/-- A fold of writes away from `o` preserves the entry at `o`. -/
private theorem foldl_set_untouched (items : List σ) (index : σ → Nat)
    (value : σ → Nat) (a : Array Nat) (o : Nat)
    (h : ∀ x ∈ items, index x ≠ o) :
    (items.foldl (fun a x => a.set! (index x) (value x)) a)[o]? = a[o]? := by
  induction items generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, index y ≠ o :=
      fun y hy => h y (by simp [hy])
    rw [List.foldl_cons, ih (a := a.set! (index x) (value x)) hxs]
    grind

/-- If every write to `o` stores `v` and at least one such write occurs,
the final entry is `v`. -/
private theorem foldl_set_constant (items : List σ) (index : σ → Nat)
    (value : σ → Nat) (a : Array Nat) (o v : Nat) (ho : o < a.size)
    (hsame : ∀ x ∈ items, index x = o → value x = v)
    (hexists : ∃ x ∈ items, index x = o) :
    (items.foldl (fun a x => a.set! (index x) (value x)) a)[o]? = some v := by
  induction items generalizing a with
  | nil => grind
  | cons x xs ih =>
    have htail : ∀ y ∈ xs, index y = o → value y = v :=
      fun y hy => hsame y (by simp [hy])
    by_cases hx : index x = o
    · have hv := hsame x (by simp) hx
      by_cases hmore : ∃ y ∈ xs, index y = o
      · exact ih (a := a.set! (index x) (value x)) (by grind)
          htail hmore
      · rw [List.foldl_cons, foldl_set_untouched xs index value
          (a.set! (index x) (value x)) o (by grind)]
        grind
    · exact ih (a := a.set! (index x) (value x)) (by grind) htail
        (by grind)

/-- Folding paired logical writes is the pair of the component folds. -/
private theorem foldl_applyRunPlacement (c : Nat)
    (runs : List RunPlacement)
    (tables : Array Nat × Array Nat) :
    runs.foldl (applyRunPlacement c) tables =
      (runs.foldl
          (fun a run => a.set! (run.start / c) (run.worker + 1)) tables.1,
        runs.foldl
          (fun a run => a.set! (run.start / c) run.offset) tables.2) := by
  induction runs generalizing tables with
  | nil => rfl
  | cons run rest ih =>
    simpa [List.foldl_cons, applyRunPlacement] using
      ih (applyRunPlacement c tables run)

/-- A concrete `RunAt` occurs in the flattened logical writes. -/
private theorem RunAt.mem_placementTrace (lenOf : Nat → Nat)
    (firstWorker : Nat)
    {outs : List (Array β × Array Nat)} {start : Nat}
    (target : RunAt outs start) :
    (⟨firstWorker + target.worker, start,
      prefixLen lenOf target.out.2.toList target.runIdx⟩ : RunPlacement) ∈
        placementTrace lenOf firstWorker outs := by
  refine List.mem_flatMap_of_mem
    (List.mk_add_mem_zipIdx_iff_getElem?.2 target.worker_eq) ?_
  refine List.mem_map.mpr ⟨(start,
    prefixLen lenOf target.out.2.toList target.runIdx), ?_, rfl⟩
  apply List.mem_of_getElem? (i := target.runIdx)
  apply List.getElem?_zip_eq_some.mpr
  constructor <;> grind [prefixLen, RunAt]

/-- Every logical write comes from a concrete worker/run position. -/
private theorem RunPlacement.of_mem_placementTrace (lenOf : Nat → Nat)
    (firstWorker : Nat) {outs : List (Array β × Array Nat)}
    (run : RunPlacement) (hmem : run ∈ placementTrace lenOf firstWorker outs) :
    ∃ target : RunAt outs run.start,
      run.worker = firstWorker + target.worker ∧
      run.offset = prefixLen lenOf target.out.2.toList target.runIdx := by
  obtain ⟨p, hp, hrun⟩ := List.mem_flatMap.mp hmem
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrun
  obtain ⟨k, hk, hqval⟩ := List.mem_iff_getElem.mp hq
  refine ⟨⟨p.2 - firstWorker, k, p.1, ?_, ?_⟩, ?_⟩
  · grind
  · grind
  · grind [prefixLen]

/-- Table correctness derived from the flattened logical writes. -/
private theorem placeWorker_foldl_spec (c : Nat) (lenOf : Nat → Nat)
    (outs : List (Array β × Array Nat)) (st : PlaceAll) (o : Nat)
    (target : RunAt outs (o * c)) (hc : 0 < c)
    (hbw : o < st.slotWorker.size) (hbo : o < st.slotOffset.size)
    (halign : ∀ out ∈ outs, ∀ s ∈ out.2.toList, s % c = 0)
    (huniq : ∀ other : RunAt outs (o * c),
      other.worker = target.worker ∧ other.runIdx = target.runIdx) :
    ((outs.foldl (placeWorker c lenOf) st).slotWorker[o]? =
        some (st.worker + target.worker + 1)) ∧
      ((outs.foldl (placeWorker c lenOf) st).slotOffset[o]? =
        some (prefixLen lenOf target.out.2.toList target.runIdx)) := by
  let runs := placementTrace lenOf st.worker outs
  let wanted : RunPlacement :=
    ⟨st.worker + target.worker, o * c,
      prefixLen lenOf target.out.2.toList target.runIdx⟩
  have hwanted : wanted ∈ runs := by
    simpa [wanted, runs] using target.mem_placementTrace lenOf st.worker
  have hsame : ∀ run ∈ runs, run.start / c = o →
      run.worker + 1 = st.worker + target.worker + 1 ∧
      run.offset = prefixLen lenOf target.out.2.toList target.runIdx := by
    intro run hrun hro
    obtain ⟨other, hw, hoffset⟩ :=
      RunPlacement.of_mem_placementTrace lenOf st.worker run hrun
    obtain ⟨normal, hnW, hnK⟩ := RunAt.exists_ofOrdinal outs c o run.start
      other.worker other.runIdx other.out halign other.worker_eq other.run_eq hro
    have hunique := huniq normal
    have hworker : other.worker = target.worker := by omega
    have hrunIdx : other.runIdx = target.runIdx := by omega
    have htargetOut : outs[other.worker]? = some target.out := by
      simpa [hworker] using target.worker_eq
    have houtEq : other.out = target.out :=
      Option.some.inj (other.worker_eq.symm.trans htargetOut)
    constructor
    · omega
    · simpa [houtEq, hrunIdx] using hoffset
  have hordinal : wanted.start / c = o := by
    simp [wanted, Nat.mul_div_cancel o hc]
  have hexists : ∃ run ∈ runs, run.start / c = o :=
    ⟨wanted, hwanted, hordinal⟩
  have hworker := foldl_set_constant runs (fun run => run.start / c)
    (fun run => run.worker + 1) st.slotWorker o
    (st.worker + target.worker + 1) hbw
    (fun run hrun hro => (hsame run hrun hro).1) hexists
  have hoffset := foldl_set_constant runs (fun run => run.start / c)
    (fun run => run.offset) st.slotOffset o
    (prefixLen lenOf target.out.2.toList target.runIdx) hbo
    (fun run hrun hro => (hsame run hrun hro).2) hexists
  have hflat := (placeWorker_foldl_eq_trace c lenOf outs st).trans
    (foldl_applyRunPlacement c runs (st.slotWorker, st.slotOffset))
  exact ⟨by simpa [runs] using
      congrArg (fun tables => tables.1[o]?) hflat |>.trans hworker,
    by simpa [runs] using
      congrArg (fun tables => tables.2[o]?) hflat |>.trans hoffset⟩

/-- `placeChunks` computes the owner and prefix-sum tables from any
uniquely-claimed, aligned worker output: the array-level table
correctness. -/
private theorem placeChunks_spec (outs : Array (Array β × Array Nat))
    (cc c : Nat) (lenOf : Nat → Nat) (o : Nat)
    (target : RunAt outs.toList (o * c))
    (hc : 0 < c) (hocc : o < cc)
    (halign : ∀ out ∈ outs.toList, ∀ s ∈ out.2.toList, s % c = 0)
    (huniq : ∀ other : RunAt outs.toList (o * c),
      other.worker = target.worker ∧ other.runIdx = target.runIdx) :
    ((placeChunks outs cc c lenOf).1[o]? = some (target.worker + 1))
      ∧ ((placeChunks outs cc c lenOf).2[o]?
        = some (prefixLen lenOf target.out.2.toList target.runIdx)) := by
  have hspec := placeWorker_foldl_spec c lenOf outs.toList
    { worker := 0, slotWorker := Array.replicate cc 0,
      slotOffset := Array.replicate cc 0 } o target hc
    (by simpa using hocc) (by simpa using hocc) (by simpa using halign) huniq
  unfold placeChunks
  rw [← Array.foldl_toList]
  exact ⟨by simpa using hspec.1, hspec.2⟩

/-- Pointwise-equal step functions fold equally. -/
private theorem foldl_congr_mem {σ δ : Type _} (l : List σ)
    (f g : δ → σ → δ)
    (h : ∀ x ∈ l, ∀ r, f r x = g r x) (init : δ) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, h x (by simp),
      ih (fun x' hx' r => h x' (by simp [hx']) r)]

/-- Sums of piece sizes agree with any length function that matches on the
summed runs. -/
private theorem prefixLen_congr (g₁ g₂ : Nat → Nat) (starts : List Nat)
    (K : Nat) (h : ∀ s ∈ starts, g₁ s = g₂ s) :
    prefixLen g₁ starts K = prefixLen g₂ starts K :=
  foldl_congr_mem _ _ _
    (fun s hs n => by rw [h s (List.mem_of_mem_take hs)]) 0

/-- A successful `getElem?` lookup determines the panicking access. -/
private theorem getElem!_of_getElem? [Inhabited δ] {xs : Array δ}
    {i : Nat} {v : δ} (h : xs[i]? = some v) : xs[i]! = v := by
  obtain ⟨hlt, hval⟩ := Array.getElem?_eq_some_iff.mp h
  rw [getElem!_pos _ i hlt]
  exact hval

/-- The size of a chunk slice, for offset bookkeeping. -/
private theorem chunkSlice_size (xs : Array α) (f : α → β)
    (chunkSize s : Nat) :
    (chunkSlice xs f chunkSize s).size = min (s + chunkSize) xs.size - s := by
  unfold chunkSlice
  simp

/-- The chunk slice's size equals `merge`'s length function on in-range
starts. -/
private theorem chunkSlice_size_eq (xs : Array α) (f : α → β)
    (chunkSize s : Nat) (hs : s < xs.size) :
    (chunkSlice xs f chunkSize s).size = chunkSize.min (xs.size - s) := by
  rw [chunkSlice_size]
  simp only [Nat.min_def]
  split <;> split <;> omega

/-- At an ordinal carried by `target`, `merge`'s step appends exactly that
run's chunk slice. -/
private theorem mergeStep_owned (xs : Array α) (f : α → β) (c : Nat)
    (outs : Array (Array β × Array Nat)) (o : Nat)
    (target : RunAt outs.toList (o * c))
    (h : WFOuts (chunkSlice xs f c) c xs.size outs)
    (hocc : o < (xs.size + c - 1) / c)
    (huniq : ∀ other : RunAt outs.toList (o * c),
      other.worker = target.worker ∧ other.runIdx = target.runIdx)
    (r : Array β) :
    mergeStep outs
      (placeChunks outs ((xs.size + c - 1) / c) c
        fun start => c.min (xs.size - start)).1
      (placeChunks outs ((xs.size + c - 1) / c) c
        fun start => c.min (xs.size - start)).2
      xs.size c o r
      = r ++ chunkSlice xs f c (o * c) := by
  have hmem : target.out ∈ outs.toList :=
    List.mem_of_getElem? target.worker_eq
  have hownA : outs[target.worker]? = some target.out := by
    simpa using target.worker_eq
  have hwf := h.workers target.out hmem
  have halign : ∀ out ∈ outs.toList, ∀ s ∈ out.2.toList, s % c = 0 :=
    fun out hout s hs => ((h.workers out hout).aligned s hs).1
  have hspec := placeChunks_spec outs ((xs.size + c - 1) / c) c
    (fun start => c.min (xs.size - start)) o target h.chunkPos hocc
    halign huniq
  obtain ⟨hKlt, hKeq⟩ := Array.getElem?_eq_some_iff.mp target.run_eq
  have hKl : target.runIdx < target.out.2.toList.length := by simpa using hKlt
  have hstart_mem : (o * c) ∈ target.out.2.toList := by
    simpa using Array.mem_of_getElem? target.run_eq
  have hstart_lt : o * c < xs.size := (hwf.aligned _ hstart_mem).2
  have hlen : ∀ s ∈ target.out.2.toList,
      (fun start => c.min (xs.size - start)) s
        = ((chunkSlice xs f c ·) s).size := by
    intro s hs
    exact (chunkSlice_size_eq xs f c s (hwf.aligned s hs).2).symm
  have h1 := getElem!_of_getElem? hspec.1
  have h2 := (getElem!_of_getElem? hspec.2).trans
    (prefixLen_congr _ _ target.out.2.toList target.runIdx hlen)
  have hKtl : target.out.2.toList[target.runIdx] = o * c := by
    simpa using hKeq
  unfold mergeStep
  rw [h1, h2]
  simp only [Nat.add_sub_cancel, hownA,
    show (target.worker + 1 == 0) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [pushRange_eq, hwf.values, ← Array.foldl_toList]
  congr 1
  have hpieces := extract_foldl_pieces (chunkSlice xs f c ·)
    target.out.2.toList target.runIdx hKl #[]
  simpa only [prefixLen, Array.size_empty, Nat.zero_add, hKtl,
    ← chunkSlice_size_eq xs f c (o * c) hstart_lt] using hpieces

/-- Rung 4 closed for `map`: from any well-formed worker output, `merge`
reconstructs the specification, so worker count and claim order cannot
affect the result. -/
private theorem merge_wf (xs : Array α) (f : α → β) (chunkSize : Nat)
    (outs : Array (Array β × Array Nat))
    (h : WFOuts (chunkSlice xs f chunkSize) chunkSize xs.size outs) :
    merge outs xs.size chunkSize = xs.map f := by
  rw [merge_eq_foldl, Array.mkEmpty_eq,
    ← foldl_chunkSlice_range xs f chunkSize h.chunkPos]
  refine foldl_congr_mem _ _ _ ?_ #[]
  intro o ho r
  have hocc : o < (xs.size + chunkSize - 1) / chunkSize :=
    List.mem_range.mp ho
  obtain ⟨target, huniq⟩ := h.once o hocc
  exact mergeStep_owned xs f chunkSize outs o target h hocc huniq r

/-- Number of currently reserved worker slots, including inline callers'
slots; zero whenever no combinator is running. For tests and diagnostics. -/
def activeSlots : BaseIO Nat :=
  activeRef.get

/-- Snapshot of the reservation statistics. For tests and diagnostics. -/
def budgetStats : BaseIO BudgetStats :=
  statsRef.get

end Linen
