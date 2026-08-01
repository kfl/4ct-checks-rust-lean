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
  let mut values := values
  for x in xs[start:stop] do
    values := values.push (← f x)
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
  let mut acc ← f x
  for x in xs[start + 1:stop] do
    acc := op acc (← f x)
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
    (hstop : stop ≤ xs.size) (i : Nat) (values : Array β) : Array β :=
  if hi : i < stop then
    mapChunkPure xs f stop hstop (i + 1)
      (values.push (f (xs[i]'(Nat.lt_of_lt_of_le hi hstop))))
  else values
termination_by stop - i

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
    (mapChunkPure xs f stop (Nat.min_le_right _ _) start values)
    (starts.push start)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapPure (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (f : α → β) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapPureLoop growth cursor xs f chunkSize true
    (Array.mkEmpty valuesCap) (Array.mkEmpty startsCap)

private def reduceChunkPure (xs : Array α) (f : α → β) (op : β → β → β)
    (stop : Nat) (hstop : stop ≤ xs.size) (i : Nat) (acc : β) : β :=
  if hi : i < stop then
    reduceChunkPure xs f op stop hstop (i + 1)
      (op acc (f (xs[i]'(Nat.lt_of_lt_of_le hi hstop))))
  else acc
termination_by stop - i

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
    let acc := reduceChunkPure xs f op stop (Nat.min_le_right _ _) (start + 1) seed
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

/-- Build lookup tables from chunk ordinal to worker and buffer offset.
`slotWorker` stores the worker index plus one, reserving zero for unclaimed
chunks. `slotOffset` stores the run's offset in that worker's buffer; `lenOf`
advances the offset between runs. -/
private def placeChunks (outs : Array (Array β × Array Nat))
    (chunkCount chunkSize : Nat) (lenOf : Nat → Nat) :
    Array Nat × Array Nat := Id.run do
  let mut slotWorker : Array Nat := Array.replicate chunkCount 0
  let mut slotOffset : Array Nat := Array.replicate chunkCount 0
  for w in [0:outs.size] do
    if let some (_, starts) := outs[w]? then
      let mut offset := 0
      for start in starts do
        let ordinal := start / chunkSize
        slotWorker := slotWorker.set! ordinal (w + 1)
        slotOffset := slotOffset.set! ordinal offset
        offset := offset + lenOf start
  return (slotWorker, slotOffset)

/-- Restore per-worker buffers to input order: place every chunk run by
ordinal without sorting, then walk each run as a subarray. -/
private def merge (outs : Array (Array β × Array Nat))
    (size chunkSize : Nat) : Array β := Id.run do
  let chunkCount := (size + chunkSize - 1) / chunkSize
  let (slotWorker, slotOffset) :=
    placeChunks outs chunkCount chunkSize fun start => chunkSize.min (size - start)
  let mut result : Array β := Array.mkEmpty size
  for ordinal in [0:chunkCount] do
    let w := slotWorker[ordinal]!
    if w > 0 then
      if let some (values, _) := outs[w - 1]? then
        let offset := slotOffset[ordinal]!
        let len := chunkSize.min (size - ordinal * chunkSize)
        for value in values[offset : offset + len] do
          result := result.push value
  return result

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
    -- Serial fast path through the unchecked chunk loop: the erased bound
    -- proof removes per-element bounds checks, and with `stop = xs.size`
    -- the loop is exactly `xs.map f`.
    mapChunkPure xs f xs.size (Nat.le_refl _) 0 (Array.mkEmpty xs.size)
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
    -- Serial fast path through the unchecked chunk loop: no task setup, no
    -- intermediate partials, no per-element bounds checks, and with
    -- `stop = xs.size` the loop is exactly the fused left fold of the
    -- specification.
    reduceChunkPure xs f op xs.size (Nat.le_refl _) 0 init
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
outright, and the associative regrouping core is proved. The ordered-merge
reconstruction, the connection from `orderedPartials` through the optional
second reduction level to that regrouping lemma, and the bridge asserting that
the concurrent runtime always yields well-formed worker output remain open
(see LINEN.md). -/

/-- The pure map chunk loop computes exactly the mapped slice, appended to
the accumulator. -/
private theorem mapChunkPure_eq (xs : Array α) (f : α → β) (stop : Nat)
    (hstop : stop ≤ xs.size) (i : Nat) (values : Array β) :
    mapChunkPure xs f stop hstop i values
      = values ++ (xs.extract i stop).map f := by
  unfold mapChunkPure
  split
  next hi =>
    rw [mapChunkPure_eq xs f stop hstop (i + 1)]
    grind
  next hi =>
    grind
termination_by stop - i

/-- The pure reduce chunk loop is the left fold of the mapped slice. -/
private theorem reduceChunkPure_eq (xs : Array α) (f : α → β)
    (op : β → β → β) (stop : Nat) (hstop : stop ≤ xs.size) (i : Nat)
    (acc : β) :
    reduceChunkPure xs f op stop hstop i acc
      = ((xs.extract i stop).map f).foldl op acc := by
  unfold reduceChunkPure
  split
  next hi =>
    rw [reduceChunkPure_eq xs f op stop hstop (i + 1),
      show xs.extract i stop = #[xs[i]] ++ xs.extract (i + 1) stop from by grind]
    simp
  next hi =>
    rw [show xs.extract i stop = #[] from by grind]
    simp
termination_by stop - i

/-- The serial fast path of `mapImpl` is the specification. -/
private theorem mapChunkPure_full (xs : Array α) (f : α → β) :
    mapChunkPure xs f xs.size (Nat.le_refl _) 0 (Array.mkEmpty xs.size)
      = xs.map f := by
  rw [mapChunkPure_eq]
  simp

/-- The serial fast path of `mapReduceImpl` is the specification's fused
left fold. -/
private theorem reduceChunkPure_full (xs : Array α) (f : α → β)
    (op : β → β → β) (init : β) :
    reduceChunkPure xs f op xs.size (Nat.le_refl _) 0 init
      = (xs.map f).foldl op init := by
  rw [reduceChunkPure_eq]
  simp

/-- Folding from a shifted accumulator commutes with an associative
operation: the algebraic core of combining chunk partials in input order. -/
private theorem foldl_assoc_shift (op : β → β → β) [Std.Associative op]
    (l : List β) (a b : β) :
    l.foldl op (op a b) = op a (l.foldl op b) := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih =>
    calc (x :: xs).foldl op (op a b)
        = xs.foldl op (op (op a b) x) := rfl
      _ = xs.foldl op (op a (op b x)) := by
            rw [Std.Associative.assoc (op := op)]
      _ = op a ((x :: xs).foldl op b) := ih (op b x)

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
    rw [← foldl_assoc_shift op c.2 init c.1]
    exact ih _

/-- Number of currently reserved worker slots, including inline callers'
slots; zero whenever no combinator is running. For tests and diagnostics. -/
def activeSlots : BaseIO Nat :=
  activeRef.get

/-- Snapshot of the reservation statistics. For tests and diagnostics. -/
def budgetStats : BaseIO BudgetStats :=
  statsRef.get

end Linen
