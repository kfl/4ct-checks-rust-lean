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

/-- Chunking of `n` elements: the clamped, positive chunk size and its cached
chunk count. The equality proof keeps the cached count tied to its defining
ceiling division. -/
private structure Chunking (n : Nat) where
  chunkSize : Nat
  count : Nat
  pos : 0 < chunkSize
  count_eq : count = (n + chunkSize - 1) / chunkSize

/-- Clamp a requested chunk size and compute its chunk count once. -/
private def Chunking.clamp (n chunkSize : Nat) : Chunking n :=
  let c := chunkSize.max 1
  { chunkSize := c
    count := (n + c - 1) / c
    pos := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_right _ _)
    count_eq := rfl }

/-- An in-range chunk ordinal. -/
private abbrev Chunking.Ordinal {n : Nat} (ck : Chunking n) := Fin ck.count

/-- A chunk's start index. -/
private def Chunking.start {n : Nat} (ck : Chunking n) (o : ck.Ordinal) : Nat :=
  o.1 * ck.chunkSize

/-- A chunk's end index from its cached start. `hstart` prevents the cached
value from drifting from the ordinal while avoiding a second multiplication. -/
private def Chunking.stop {n : Nat} (ck : Chunking n) (o : ck.Ordinal)
    (start : Nat) (_hstart : start = ck.start o) : Nat :=
  (start + ck.chunkSize).min n

/-- Chunks end within bounds; the chunk loops take this bound. -/
private theorem Chunking.stop_le {n : Nat} (ck : Chunking n)
    (o : ck.Ordinal) (start : Nat) (hstart : start = ck.start o) :
    ck.stop o start hstart ≤ n :=
  Nat.min_le_right _ _

/-- In-range ordinals start below `n`; the reduce workers read their seed
element through this bound. -/
private theorem Chunking.start_lt {n : Nat} (ck : Chunking n)
    (o : ck.Ordinal) : ck.start o < n := by
  have hord : (o.1 + 1) * ck.chunkSize ≤ ck.count * ck.chunkSize :=
    Nat.mul_le_mul_right _ o.2
  have hbound : ck.count * ck.chunkSize ≤ n + ck.chunkSize - 1 :=
    ck.count_eq ▸ Nat.div_mul_le_self _ _
  grind [Chunking.start, Chunking]

/-- One worker's output: appended values and the claimed chunk ordinals in
claim order. The ordinal type carries the range invariant, so recorded
claims are aligned and in range by construction. -/
private structure WorkerOut {n : Nat} (ck : Chunking n) (β : Type) where
  values : Array β
  ordinals : Array ck.Ordinal
deriving Inhabited

/-- Placement tables sized by the chunk count: chunk ordinal to owning
worker (index plus one; zero means unclaimed) and to the run's offset in
that worker's buffer. -/
private structure Placement {n : Nat} (ck : Chunking n) where
  slotWorker : Vector Nat ck.count
  slotOffset : Vector Nat ck.count

/-- Atomically claim the next chunk ordinal; `chunkCount` means exhausted.
Counting ordinals rather than start indices keeps recorded claims in
`Fin chunkCount`. -/
private def claim (cursor : IO.Ref Nat) (chunkCount : Nat) : BaseIO Nat := do
  cursor.modifyGet fun next =>
    if next < chunkCount then (next, next + 1) else (next, next)

/-- Initial value-buffer capacity for one worker is `⌈size/count⌉`. A worker
that claims more than the average grows its buffer. -/
private def valuesCapacity (size count : Nat) : Nat :=
  (size + count - 1) / count

/-- Capacity estimate for one worker's ordinal buffer under even
claiming. -/
private def ordinalsCapacity (chunkCount count : Nat) : Nat :=
  chunkCount / count + 1

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

/-- Monadic chunk loop for `tabulateM`: append `(← g i)` for every index in
`[i, stop)`, with effects in index order within the chunk. The bound
`stop ≤ n` supplies each index's `Fin` proof, erased at compile time. -/
@[specialize] private def tabulateChunkM {m : Type → Type} [Monad m]
    (n : Nat) (g : Fin n → m β) (stop : Nat)
    (hstop : stop ≤ n) (i : Nat) (values : Array β) :
    m (Array β) := do
  if h : i < stop then
    tabulateChunkM n g stop hstop (i + 1)
      (values.push (← g ⟨i, Nat.lt_of_lt_of_le h hstop⟩))
  else
    return values
termination_by stop - i

/-- Monadic tabulation worker. It appends values in claim order and records
each chunk's ordinal; the merge derives chunk lengths from those ordinals.
One team-growth attempt runs per successful claim; `growing` caches the
verdict, so a full team costs nothing per claim. -/
@[specialize] private partial def workerTabulateMLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (n : Nat) (ck : Chunking n)
    (g : Fin n → BaseIO β) (growing : Bool) (values : Array β)
    (ordinals : Array ck.Ordinal) : BaseIO (WorkerOut ck β) := do
  let raw ← claim cursor ck.count
  if h : raw < ck.count then
    let o : ck.Ordinal := ⟨raw, h⟩
    let start := ck.start o
    let stop := ck.stop o start rfl
    let growing ← if growing then (·.retryable) <$> growth else pure false
    let values ← tabulateChunkM n g stop (ck.stop_le o start rfl) start values
    workerTabulateMLoop growth cursor n ck g growing values
      (ordinals.push o)
  else
    return ⟨values, ordinals⟩

/-- Allocate worker-local buffers and construct the callback inside the
worker. -/
@[specialize] private def workerTabulateM (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (n : Nat) (ck : Chunking n) (makeWorkerFn : Unit → Fin n → BaseIO β)
    (valuesCap ordinalsCap : Nat) : BaseIO (WorkerOut ck β) :=
  workerTabulateMLoop growth cursor n ck (makeWorkerFn ()) true
    (Array.mkEmpty valuesCap) (Array.mkEmpty ordinalsCap)

/-- Monadic `mapReduceM` worker. Each chunk is folded left-to-right into
one partial, seeded by its first element; the ordinal bound proves the
seed read in bounds. -/
private partial def workerMapReduceMLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (xs : Array α) (ck : Chunking xs.size)
    (f : α → BaseIO β) (op : β → β → β) (growing : Bool)
    (partials : Array β) (ordinals : Array ck.Ordinal) :
    BaseIO (WorkerOut ck β) := do
  let raw ← claim cursor ck.count
  if h : raw < ck.count then
    let o : ck.Ordinal := ⟨raw, h⟩
    let growing ← if growing then (·.retryable) <$> growth else pure false
    let start := ck.start o
    let stop := ck.stop o start rfl
    let seed ← f (xs[start]'(ck.start_lt o))
    let acc ← xs.foldlM (fun acc x => return op acc (← f x))
      seed (start + 1) stop
    workerMapReduceMLoop growth cursor xs ck f op growing
      (partials.push acc) (ordinals.push o)
  else
    return ⟨partials, ordinals⟩

/-- Allocate worker-local buffers inside the task. -/
private def workerMapReduceM (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (ck : Chunking xs.size) (f : α → BaseIO β)
    (op : β → β → β) (ordinalsCap : Nat) :
    BaseIO (WorkerOut ck β) :=
  workerMapReduceMLoop growth cursor xs ck f op true
    (Array.mkEmpty ordinalsCap) (Array.mkEmpty ordinalsCap)

/-- Run one fallible chunk and return its first failing index and error.
Explicit recursion keeps early-exit bookkeeping out of the success loop;
the index bound makes each call total, so there is no missing-element
case. -/
@[specialize] private def runChunk {m : Type → Type} [Monad m]
    (n : Nat) (g : Fin n → m (Except ε β))
    (stop : Nat) (hstop : stop ≤ n) (i : Nat) (values : Array β) :
    m (Array β × Option (Fin n × ε)) := do
  if h : i < stop then
    match ← g ⟨i, Nat.lt_of_lt_of_le h hstop⟩ with
    | .ok value => runChunk n g stop hstop (i + 1) (values.push value)
    | .error e => return (values, some (⟨i, Nat.lt_of_lt_of_le h hstop⟩, e))
  else
    return (values, none)
termination_by stop - i

/-- Merge one reported failure into the register, keeping the lower input
index. Shared with the specification proofs, so the runtime's selection
is the proved selection. -/
private def keepLower {n : Nat} (current : Option (Fin n × ε))
    (incoming : Fin n × ε) : Option (Fin n × ε) :=
  match current with
  | some (j, e) => if incoming.1 < j then some incoming else some (j, e)
  | none => some incoming

/-- Fallible `tabulateIO` worker. On failure it poisons the cursor,
preventing new claims while current chunks run to completion, and retains
the lowest-index failure; because chunks are claimed in order, all earlier
indices have run when the workers join. Failed chunks are omitted; results
are merged only when every worker succeeds. Grown siblings exit at their
next claim after the cursor is poisoned. -/
@[specialize] private partial def workerTabulateIOLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (n : Nat)
    (failure : IO.Ref (Option (Fin n × ε))) (ck : Chunking n)
    (g : Fin n → BaseIO (Except ε β))
    (growing : Bool) (values : Array β)
    (ordinals : Array ck.Ordinal) : BaseIO (WorkerOut ck β) := do
  let raw ← claim cursor ck.count
  if h : raw < ck.count then
    let o : ck.Ordinal := ⟨raw, h⟩
    let start := ck.start o
    let stop := ck.stop o start rfl
    let growing ← if growing then (·.retryable) <$> growth else pure false
    match ← runChunk n g stop (ck.stop_le o start rfl) start values with
    | (values, none) =>
      workerTabulateIOLoop growth cursor n failure ck g growing values
        (ordinals.push o)
    | (values, some failed) =>
      cursor.set ck.count
      failure.modify (keepLower · failed)
      return ⟨values, ordinals⟩
  else
    return ⟨values, ordinals⟩

/-- Allocate worker-local buffers and construct the callback inside the
worker. -/
@[specialize] private def workerTabulateIO (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (n : Nat) (failure : IO.Ref (Option (Fin n × ε))) (ck : Chunking n)
    (makeWorkerFn : Unit → Fin n → BaseIO (Except ε β))
    (valuesCap ordinalsCap : Nat) : BaseIO (WorkerOut ck β) :=
  workerTabulateIOLoop growth cursor n failure ck (makeWorkerFn ()) true
    (Array.mkEmpty valuesCap) (Array.mkEmpty ordinalsCap)

private def workerCount {n : Nat} (ck : Chunking n) : Nat :=
  config.workers.min ck.count

/-! ## Occupancy-based team sizing

All regions share `config.workers` slots. A region spawns only after reserving
a slot and always runs one worker inline, with or without a slot, so nested
work cannot lose progress when the budget is full. At most `config.workers`
Linen-created worker tasks are live or queued; the budget does not cover other
tasks in the process. Workers retry reservations after claims, letting a team
grow as other regions release slots. -/

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
private def slottedWorker {ρ : Type} (work : BaseIO ρ) : BaseIO ρ := do
  let out ← work
  releaseSlot
  return out

/-- Per-region team state under the occupancy policy. `spawned` counts team
positions handed out, capped at `slots`; `registry` collects spawned worker
tasks for the region's join. Generic in the worker result type: the
scheduler needs no view of chunking or ordinals. -/
private structure Region (ρ : Type) where
  slots : Nat
  spawned : IO.Ref Nat
  registry : IO.Ref (Array (Task ρ))

/-- Reserve a global slot and a region team position, then spawn a sibling.
Plain reads gate the atomic reservations, avoiding read-modify-write traffic
while the pool or team is full. The team counter resolves races for the last
position; a loser releases its slot. `teamFull` is permanent because
`spawned` never decreases, while `budgetFull` is worth retrying. The child is
registered before its spawner can finish, as required by `joinRegion`.
`fromWorker` distinguishes growth from entry seeding in the statistics. -/
private partial def growTeam {ρ : Type} (region : Region ρ)
    (fromWorker : Bool)
    (mkWork : BaseIO GrowResult → BaseIO ρ) : BaseIO GrowResult := do
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
private def joinRegion {ρ : Type} (region : Region ρ) (outs : Array ρ) :
    BaseIO (Array ρ) := do
  let mut outs := outs
  repeat
    let batch ← region.registry.modifyGet fun tasks => (tasks, (#[] : Array _))
    if batch.isEmpty then break
    for task in batch do
      outs := outs.push (← IO.wait task)
  return outs

/-- Seed a region from the free budget, run one worker inline, then join all
spawned workers. The inline worker reserves a slot when possible so the growth
gates see the occupied capacity; a nested caller may therefore hold one slot
for its outer role and another for its inline inner role. Growth after each
claim lets a region expand when slots become free. Seeding stops at the first
denial. -/
private def runGrowingRegion {ρ : Type} (slots : Nat)
    (mkWork : BaseIO GrowResult → BaseIO ρ) : BaseIO (Array ρ) := do
  let region : Region ρ := ⟨slots, ← IO.mkRef 0, ← IO.mkRef #[]⟩
  let inlineSlot ← if (← activeRef.get) < config.workers then tryReserveSlot
    else pure false
  let mut seeding := true
  for _ in [0:slots] do
    if seeding then
      seeding := (← growTeam region false mkWork) matches .spawned
  let mine ← mkWork (growTeam region true mkWork)
  if inlineSlot then releaseSlot
  joinRegion region #[mine]

/-! Workers for the pure runtimes (`tabulateWithWorkerFnImpl` and
`mapReduceImpl`).
Their inner loops call `g`, `f`, and `op` without `BaseIO`. Bounds derived
from `claim` justify the indexed calls and array reads; the proofs are
erased at compile time. Task setup, claiming, bookkeeping, and ordered
merging remain outside the inner loops. -/

/-- Chunk loop for the pure tabulation runtime: append `g i` for every
index in `[i, stop)`. An index loop with no underlying collection (compare
`mergeLoop`); the bound `stop ≤ n` supplies each index's `Fin` proof,
erased at compile time. -/
@[specialize] private def tabulateChunk (n : Nat) (g : Fin n → β) (stop : Nat)
    (hstop : stop ≤ n) (i : Nat) (values : Array β) : Array β :=
  if h : i < stop then
    tabulateChunk n g stop hstop (i + 1)
      (values.push (g ⟨i, Nat.lt_of_lt_of_le h hstop⟩))
  else values
termination_by stop - i

/-- Pure tabulation worker with one team-growth attempt per successful
claim. `growing` caches `growth`'s verdict: once the team is full the loop
stops attempting, leaving no per-claim cost. -/
@[specialize] private partial def workerTabulatePureLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (n : Nat) (ck : Chunking n) (g : Fin n → β)
    (growing : Bool) (values : Array β)
    (ordinals : Array ck.Ordinal) : BaseIO (WorkerOut ck β) := do
  let raw ← claim cursor ck.count
  if h : raw < ck.count then
    let o : ck.Ordinal := ⟨raw, h⟩
    let start := ck.start o
    let stop := ck.stop o start rfl
    let growing ← if growing then (·.retryable) <$> growth else pure false
    workerTabulatePureLoop growth cursor n ck g growing
      (tabulateChunk n g stop (ck.stop_le o start rfl) start values)
      (ordinals.push o)
  else
    return ⟨values, ordinals⟩

/-- Allocate worker-local buffers and construct the callback inside the
worker. -/
@[specialize] private def workerTabulatePure (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (n : Nat) (ck : Chunking n)
    (makeWorkerFn : Unit → Fin n → β) (valuesCap ordinalsCap : Nat) :
    BaseIO (WorkerOut ck β) :=
  workerTabulatePureLoop growth cursor n ck (makeWorkerFn ()) true
    (Array.mkEmpty valuesCap) (Array.mkEmpty ordinalsCap)

private def reduceChunkPure (xs : Array α) (f : α → β) (op : β → β → β)
    (stop : Nat) (i : Nat) (acc : β) : β :=
  xs.foldl (fun acc x => op acc (f x)) acc i stop

/-- Pure reducing worker: each chunk folds to one partial seeded by its
first element; the ordinal bound proves the seed read in bounds. -/
private partial def workerReducePureLoop (growth : BaseIO GrowResult)
    (cursor : IO.Ref Nat) (xs : Array α) (ck : Chunking xs.size)
    (f : α → β) (op : β → β → β) (growing : Bool) (partials : Array β)
    (ordinals : Array ck.Ordinal) : BaseIO (WorkerOut ck β) := do
  let raw ← claim cursor ck.count
  if h : raw < ck.count then
    let o : ck.Ordinal := ⟨raw, h⟩
    let growing ← if growing then (·.retryable) <$> growth else pure false
    let start := ck.start o
    let stop := ck.stop o start rfl
    let seed := f (xs[start]'(ck.start_lt o))
    let acc := reduceChunkPure xs f op stop (start + 1) seed
    workerReducePureLoop growth cursor xs ck f op growing
      (partials.push acc) (ordinals.push o)
  else
    return ⟨partials, ordinals⟩

/-- Allocate worker-local buffers inside the task. -/
private def workerReducePure (growth : BaseIO GrowResult) (cursor : IO.Ref Nat)
    (xs : Array α) (ck : Chunking xs.size) (f : α → β) (op : β → β → β)
    (ordinalsCap : Nat) : BaseIO (WorkerOut ck β) :=
  workerReducePureLoop growth cursor xs ck f op true
    (Array.mkEmpty ordinalsCap) (Array.mkEmpty ordinalsCap)

/-- Fold state while placing one worker's runs: the running buffer offset
and the placement tables. -/
private structure PlaceRun {n : Nat} (ck : Chunking n) where
  offset : Nat
  tables : Placement ck

/-- One run placed: record the owner and the run's buffer offset at the
run's ordinal, and advance the offset. The ordinal's bound proves both
writes in range. -/
private def placeRun {n : Nat} {ck : Chunking n} (lenOf : ck.Ordinal → Nat)
    (worker : Nat) (st : PlaceRun ck) (o : ck.Ordinal) : PlaceRun ck :=
  { offset := st.offset + lenOf o,
    tables :=
      { slotWorker := st.tables.slotWorker.set o.1 (worker + 1) o.2,
        slotOffset := st.tables.slotOffset.set o.1 st.offset o.2 } }

/-- Fold state across workers: the next worker index and the tables. -/
private structure PlaceAll {n : Nat} (ck : Chunking n) where
  worker : Nat
  tables : Placement ck

/-- One worker placed: fold its runs through `placeRun` and advance the
worker index. -/
private def placeWorker {n : Nat} {ck : Chunking n} (lenOf : ck.Ordinal → Nat)
    (st : PlaceAll ck) (out : WorkerOut ck β) : PlaceAll ck :=
  let run := out.ordinals.foldl (placeRun lenOf st.worker)
    { offset := 0, tables := st.tables }
  { worker := st.worker + 1, tables := run.tables }

/-- Build lookup tables from chunk ordinal to worker and buffer offset.
`slotWorker` stores the worker index plus one, reserving zero for unclaimed
chunks. `slotOffset` stores the run's offset in that worker's buffer; `lenOf`
advances the offset between runs. -/
private def placeChunks {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (lenOf : ck.Ordinal → Nat) : Placement ck :=
  (outs.foldl (placeWorker lenOf)
    { worker := 0,
      tables := { slotWorker := Vector.replicate ck.count 0,
                  slotOffset := Vector.replicate ck.count 0 } }).tables

/-- Append `values[j:stop)` onto `r`: a bounded fold, which compiles to a
tight loop with the bound computed once. -/
private def pushRange (values : Array β) (stop j : Nat) (r : Array β) :
    Array β :=
  values.foldl (fun r value => r.push value) r j stop

/-- One ordinal's contribution to the merge: append the owning worker's
buffer segment, or nothing for an unclaimed ordinal. A pure function so
`merge`'s loop body is a single state update, which the correspondence
proofs convert to a fold directly; the ordinal bound proves the table
reads in range. -/
@[inline] private def mergeStep {n : Nat} (ck : Chunking n)
    (outs : Array (WorkerOut ck β)) (tables : Placement ck)
    (o : ck.Ordinal) (result : Array β) : Array β :=
  let w := tables.slotWorker[o.1]
  if w == 0 then result
  else
    match outs[w - 1]? with
    | some out =>
      let offset := tables.slotOffset[o.1]
      let stop := offset + ck.chunkSize.min (n - ck.start o)
      pushRange out.values stop offset result
    | none => result

/-- Pure range loop over chunk ordinals: an index loop with no underlying
collection, so a small recursion rather than a collection fold. -/
private def mergeLoop {n : Nat} (ck : Chunking n)
    (outs : Array (WorkerOut ck β)) (tables : Placement ck)
    (ordinal : Nat) (result : Array β) : Array β :=
  if h : ordinal < ck.count then
    mergeLoop ck outs tables (ordinal + 1)
      (mergeStep ck outs tables ⟨ordinal, h⟩ result)
  else result
termination_by ck.count - ordinal

/-- Restore per-worker buffers to input order: place every chunk run by
ordinal without sorting, then append each ordinal's segment. -/
private def merge {n : Nat} (ck : Chunking n)
    (outs : Array (WorkerOut ck β)) : Array β :=
  let tables := placeChunks outs fun o => ck.chunkSize.min (n - ck.start o)
  mergeLoop ck outs tables 0 (Array.mkEmpty n)

/-- One ordinal's contribution to the ordered partials: push the owning
worker's recorded partial, or nothing for an unclaimed ordinal. A pure
function so the loop body is a single state update, mirroring
`mergeStep`. -/
@[inline] private def orderedStep {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (tables : Placement ck)
    (o : ck.Ordinal) (ps : Array β) : Array β :=
  let w := tables.slotWorker[o.1]
  if w == 0 then ps
  else
    match outs[w - 1]? with
    | some out =>
      match out.values[tables.slotOffset[o.1]]? with
      | some p => ps.push p
      | none => ps
    | none => ps

/-- Range loop collecting per-chunk partials into chunk-ordinal order. -/
private def orderedPartialsLoop {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (tables : Placement ck)
    (ordinal : Nat) (ps : Array β) : Array β :=
  if h : ordinal < ck.count then
    orderedPartialsLoop outs tables (ordinal + 1)
      (orderedStep outs tables ⟨ordinal, h⟩ ps)
  else ps
termination_by ck.count - ordinal

/-- Collect per-chunk partials into chunk-ordinal order. -/
private def orderedPartials {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) : Array β :=
  orderedPartialsLoop outs (placeChunks outs fun _ => 1) 0
    (Array.mkEmpty ck.count)

/-- Combine chunk partials in input order. When partials outnumber workers,
first fold contiguous groups in parallel, leaving at most one partial per
worker for the final serial fold. Associativity preserves the sequential
left-fold result. If there are already at most as many partials as workers,
the parallel level would apply no `op`, so it is skipped. -/
private def mergeReduce {n : Nat} (ck : Chunking n)
    (outs : Array (WorkerOut ck β)) (op : β → β → β) (init : β) :
    BaseIO β := do
  let ps := orderedPartials outs
  if ps.size ≤ config.workers then
    return ps.foldl op init
  else
    let ckL := Chunking.clamp ps.size
      ((ps.size + config.workers - 1) / config.workers)
    let count := workerCount ckL
    let cursor ← IO.mkRef 0
    let levelOuts ← runGrowingRegion (count - 1) fun growth =>
      workerReducePure growth cursor ps ckL id op
        (ordinalsCapacity ckL.count count)
    return (orderedPartials levelOuts).foldl op init

/-- Parallel monadic-tabulation engine; callers ensure `config.workers > 1`
and `n > chunkSize`. -/
@[specialize] private def tabulateMCore (n : Nat) (ck : Chunking n)
    (makeWorkerFn : Unit → Fin n → BaseIO β) : BaseIO (Array β) := do
  let count := workerCount ck
  let cursor ← IO.mkRef 0
  let outs ← runGrowingRegion (count - 1) fun growth =>
    workerTabulateM growth cursor n ck makeWorkerFn
      (valuesCapacity n count) (ordinalsCapacity ck.count count)
  return merge ck outs

/-- Monadic tabulation behind the worker-callback factory boundary. -/
@[specialize] private def tabulateMWithWorkerFn (n : Nat)
    (makeWorkerFn : Unit → Fin n → BaseIO β) (chunkSize : Nat := 1) :
    BaseIO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || n ≤ chunkSize then
    tabulateChunkM n (makeWorkerFn ()) n (Nat.le_refl n) 0
      (Array.mkEmpty n)
  else
    tabulateMCore n (Chunking.clamp n chunkSize) makeWorkerFn

/-- Parallel monadic tabulation using at most one task per configured
worker: build the array whose entry at `i` is the result of `g i`. Workers
claim chunks dynamically, and the results are restored to index order.
Result positions are deterministic, but `g`'s externally observable
effects can reveal scheduling: effects within a chunk run in index order,
while cross-chunk effect order is unspecified and depends on `chunkSize`
and the worker count. `chunkSize` is clamped to at least one. -/
@[inline]
def tabulateM (n : Nat) (g : Fin n → BaseIO β) (chunkSize : Nat := 1) :
    BaseIO (Array β) :=
  tabulateMWithWorkerFn n (fun _ i => g i) chunkSize

/-- Parallel monadic map with the scheduling and effect-order behaviour of
`tabulateM`. The serial fast path traverses the array directly. -/
-- Inlining exposes the caller's mapper to the worker-callback factory.
@[inline]
def mapM (xs : Array α) (f : α → BaseIO β) (chunkSize : Nat := 1) :
    BaseIO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.mapM f
  else
    tabulateMCore xs.size (Chunking.clamp xs.size chunkSize)
      (fun _ => fun i => f xs[i])

/-- Monadic map-reduce using dynamically claimed chunks. Each chunk produces
one partial; `mergeReduce` combines them in input order. `op` must be
associative but need not be commutative. -/
def mapReduceM (xs : Array α) (f : α → BaseIO β) (op : β → β → β)
    (init : β) (chunkSize : Nat := 1) [Std.Associative op] : BaseIO β := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.foldlM (fun acc x => return op acc (← f x)) init
  else
    let ck := Chunking.clamp xs.size chunkSize
    let count := workerCount ck
    let cursor ← IO.mkRef 0
    let outs ← runGrowingRegion (count - 1) fun growth =>
      workerMapReduceM growth cursor xs ck f op
        (ordinalsCapacity ck.count count)
    mergeReduce ck outs op init

/-- Parallel pure-tabulation engine; its caller ensures `config.workers > 1`
and `n > chunkSize`. -/
@[specialize] private def tabulateCoreIO (n : Nat) (ck : Chunking n)
    (makeWorkerFn : Unit → Fin n → β) : BaseIO (Array β) := do
  let base := workerCount ck
  let cursor ← IO.mkRef 0
  -- The caller runs one worker inline, so the spawn cap is `base - 1`.
  let outs ← runGrowingRegion (base - 1) fun growth =>
    workerTabulatePure growth cursor n ck makeWorkerFn
      (valuesCapacity n base) (ordinalsCapacity ck.count base)
  return merge ck outs

/-- Parallel engine for the pure `mapReduce` runtime; preconditions as for
`tabulateCoreIO`. -/
private def reduceCoreIO (xs : Array α) (ck : Chunking xs.size)
    (f : α → β) (op : β → β → β) (init : β) : BaseIO β := do
  let count := workerCount ck
  let cursor ← IO.mkRef 0
  let outs ← runGrowingRegion (count - 1) fun growth =>
    workerReducePure growth cursor xs ck f op
      (ordinalsCapacity ck.count count)
  mergeReduce ck outs op init

/-- Runtime implementation of `tabulateWithWorkerFn`, specialised so a
literal factory reaches the worker loop intact. -/
@[specialize] private unsafe def tabulateWithWorkerFnImpl.{u} {α : Type u} (n : Nat)
    (makeWorkerFn : Unit → Fin n → α) (chunkSize : Nat := 1) : Array α :=
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || n ≤ chunkSize then
    -- Serial fast path through the chunk loop: no task setup, unchecked
    -- indexed calls, and with `stop = n` the loop is exactly the
    -- specification.
    tabulateChunk n (makeWorkerFn ()) n (Nat.le_refl n) 0 (Array.mkEmpty n)
  else
    -- `unsafeBaseIO` is justified because the callback is pure and the
    -- result does not depend on scheduling. The `NonScalar` cast bridges
    -- `BaseIO`'s `Type 0` boundary using the boxed erasure pattern from
    -- `Array.mapMUnsafe`.
    unsafeCast (unsafeBaseIO (tabulateCoreIO n (Chunking.clamp n chunkSize)
      (unsafeCast makeWorkerFn : Unit → Fin n → NonScalar)))

/-- Specification boundary for worker-local callback construction. The
runtime invokes the factory once per worker. Public `@[inline]` wrappers let
ordinary lambdas enter the factory before closure conversion. -/
@[implemented_by tabulateWithWorkerFnImpl]
private def tabulateWithWorkerFn.{u} {α : Type u} (n : Nat)
    (makeWorkerFn : Unit → Fin n → α) (chunkSize : Nat := 1) : Array α :=
  Array.ofFn (makeWorkerFn ())

/-- Parallel indexed tabulation, the primitive under `map`: build the array
whose entry at `i` is `g i`. Its specification is `Array.ofFn g` for every
`chunkSize`; chunk size affects runtime scheduling, not the result, and
`g` observes only its index, never workers, claims, or chunk boundaries. -/
@[inline]
def tabulate.{u} {α : Type u} (n : Nat) (g : Fin n → α)
    (chunkSize : Nat := 1) : Array α :=
  tabulateWithWorkerFn n (fun _ i => g i) chunkSize

/-- Runtime implementation of `map`: tabulation reading the input at each
index; `i.isLt` justifies the unchecked read. Its public specification is
`xs.map f`, so tasks and scheduling are absent from proofs. -/
private unsafe def mapImpl.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (chunkSize : Nat := 1) : Array β :=
  tabulateWithWorkerFnImpl xs.size (fun _ i => f xs[i]) chunkSize

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
    -- The same trust boundary as `tabulateWithWorkerFnImpl`; `op` and
    -- `init` are also cast through `NonScalar`.
    unsafeCast (unsafeBaseIO (reduceCoreIO
      (unsafeCast xs : Array NonScalar)
      (Chunking.clamp _ chunkSize)
      (unsafeCast f : NonScalar → NonScalar)
      (unsafeCast op) (unsafeCast init)))

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

/-- Parallel fallible-tabulation engine; callers ensure `config.workers > 1`
and `n > chunkSize`. -/
@[specialize] private def tabulateIOCore (n : Nat) (ck : Chunking n)
    (makeWorkerFn : Unit → Fin n → BaseIO (Except IO.Error β)) :
    IO (Array β) := do
  let count := workerCount ck
  let cursor ← IO.mkRef 0
  let failure ← IO.mkRef (none : Option (Fin n × IO.Error))
  let outs ← runGrowingRegion (count - 1) fun growth =>
    workerTabulateIO growth cursor n failure ck makeWorkerFn
      (valuesCapacity n count) (ordinalsCapacity ck.count count)
  match ← failure.get with
  | some (_, e) => throw e
  | none => return merge ck outs

/-- Fallible tabulation behind the worker-callback factory boundary. -/
@[specialize] private def tabulateIOWithWorkerFn (n : Nat)
    (makeWorkerFn : Unit → Fin n → BaseIO (Except IO.Error β))
    (chunkSize : Nat := 1) : IO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || n ≤ chunkSize then
    match ← (runChunk n (makeWorkerFn ()) n (Nat.le_refl n) 0
        (Array.mkEmpty n) : BaseIO _) with
    | (values, none) => return values
    | (_, some (_, e)) => throw e
  else
    tabulateIOCore n (Chunking.clamp n chunkSize) makeWorkerFn

/-- Parallel fallible tabulation: build the array whose entry at `i` is
the result of `g i`. A failure stops new claims; after current chunks
finish, the failure with the lowest index is rethrown deterministically
(see `workerTabulateIOLoop`). The selected error and all result positions
are deterministic, but `g`'s externally observable effects can reveal
scheduling: effects within a chunk run in index order, while cross-chunk
effect order is unspecified and depends on `chunkSize` and the worker
count. `chunkSize` is clamped to at least one. -/
@[inline]
def tabulateIO (n : Nat) (g : Fin n → IO β) (chunkSize : Nat := 1) :
    IO (Array β) :=
  tabulateIOWithWorkerFn n (fun _ i => (g i).toBaseIO) chunkSize

/-- Parallel `IO` map with the fail-fast, lowest-index error, and effect-order
behaviour of `tabulateIO`. The serial fast path traverses the array directly. -/
-- Inlining exposes the caller's mapper to the worker-callback factory.
@[inline]
def mapIO (xs : Array α) (f : α → IO β) (chunkSize : Nat := 1) :
    IO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.mapM f
  else
    tabulateIOCore xs.size (Chunking.clamp xs.size chunkSize)
      (fun _ => fun i => (f xs[i]).toBaseIO)

/-- Parallel `IO` traversal, fail-fast with the same deterministic
smallest-index error reporting as `mapIO`. -/
def forEach (xs : Array α) (f : α → IO Unit) (chunkSize : Nat := 1) :
    IO Unit :=
  discard <| mapIO xs f chunkSize

/-! ## Verified properties

The runtime crosses an `unsafeBaseIO` boundary, so the correspondence is split
into pure lemmas about its data path. The serial chunk loops, associative
regrouping, and ordered assembly are proved below. The concurrent bridge and
effectful specifications remain open; see LINEN.md. -/

/-- The tabulation chunk loop computes exactly the specification slice,
appended to the accumulator. -/
private theorem tabulateChunk_eq (n : Nat) (g : Fin n → β) (stop : Nat)
    (hstop : stop ≤ n) (i : Nat) (values : Array β) :
    tabulateChunk n g stop hstop i values
      = values ++ (Array.ofFn g).extract i stop := by
  fun_induction tabulateChunk <;>
    grind [Array.getElem_ofFn, Array.push_eq_append, Array.size_ofFn]

/-- The pure reduce chunk loop is the left fold of the mapped slice. -/
private theorem reduceChunkPure_eq (xs : Array α) (f : α → β)
    (op : β → β → β) (stop : Nat) (i : Nat) (acc : β) :
    reduceChunkPure xs f op stop i acc
      = ((xs.extract i stop).map f).foldl op acc := by
  unfold reduceChunkPure
  rw [Array.foldl_eq_foldl_extract]
  grind [Array.foldl_map]

/-- The serial fast path of `tabulateWithWorkerFnImpl` is the
specification. -/
private theorem tabulateChunk_full (n : Nat) (g : Fin n → β) :
    tabulateChunk n g n (Nat.le_refl n) 0 (Array.mkEmpty n)
      = Array.ofFn g := by
  simp [tabulateChunk_eq]

/-- Tabulating the indexed reads of `xs` through `f` is the map
specification: `map`'s instantiation of the tabulation engine is exact. -/
private theorem ofFn_read_eq_map (xs : Array α) (f : α → β) :
    (Array.ofFn fun i : Fin xs.size => f xs[i]) = xs.map f := by
  grind [Array.getElem_ofFn, Array.size_ofFn]

/-- The serial fast path of `mapImpl` is the specification. -/
private theorem tabulateChunk_map_full (xs : Array α) (f : α → β) :
    tabulateChunk xs.size (fun i => f xs[i]) xs.size (Nat.le_refl xs.size)
      0 (Array.mkEmpty xs.size) = xs.map f := by
  rw [tabulateChunk_full, ofFn_read_eq_map]

/-- The serial fast path of `mapReduceImpl` is the specification's fused
left fold. -/
private theorem reduceChunkPure_full (xs : Array α) (f : α → β)
    (op : β → β → β) (init : β) :
    reduceChunkPure xs f op xs.size 0 init
      = (xs.map f).foldl op init := by
  simp [reduceChunkPure_eq]

/-! ## Ordered assembly -/

/-- The mapped slice of the chunk starting at `s`. -/
private def chunkSlice (xs : Array α) (f : α → β) (chunkSize s : Nat) :
    Array β :=
  (xs.extract s (min (s + chunkSize) xs.size)).map f

/-- Well-formed output of one worker, parameterised by the `piece` each
recorded ordinal contributes: the value buffer is exactly the concatenated
pieces of the recorded ordinals, in claim order. Alignment and range need
no clauses; recorded ordinals carry them in their type. -/
private structure WFWorkerOut {n : Nat} {ck : Chunking n}
    (piece : ck.Ordinal → Array β) (out : WorkerOut ck β) : Prop where
  values : out.values
    = out.ordinals.foldl (fun acc o => acc ++ piece o) #[]

/-- A worker/run position whose recorded ordinal is `o`. The output and
both successful lookups travel with the indices, so consumers do not
repeat Array/List lookup conversions. -/
private structure RunAt {n : Nat} {ck : Chunking n}
    (outs : List (WorkerOut ck β)) (o : ck.Ordinal) where
  worker : Nat
  runIdx : Nat
  out : WorkerOut ck β
  worker_eq : outs[worker]? = some out
  run_eq : out.ordinals[runIdx]? = some o

/-- Well-formed collective worker output: each worker well formed and
every chunk ordinal recorded exactly once across all workers. Worker
count and claim order are otherwise unconstrained. -/
private structure WFOuts {n : Nat} {ck : Chunking n}
    (piece : ck.Ordinal → Array β) (outs : Array (WorkerOut ck β)) : Prop where
  workers : ∀ out ∈ outs.toList, WFWorkerOut piece out
  once : ∀ o : ck.Ordinal,
    ∃ run : RunAt outs.toList o,
      ∀ other : RunAt outs.toList o,
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
private theorem foldl_add_shift {σ : Type _} (g : σ → Nat) (l : List σ)
    (a : Nat) :
    l.foldl (fun n s => n + g s) a = a + l.foldl (fun n s => n + g s) 0 := by
  rw [← List.foldl_map (f := g) (g := (· + ·)),
    ← List.foldl_map (f := g) (g := (· + ·)),
    ← Nat.add_zero a, List.foldl_assoc, Nat.add_zero]

/-- Appending more blocks to a buffer does not disturb an extraction that
lies within the existing prefix. -/
private theorem extract_foldl_append_of_le {σ : Type _} (g : σ → Array β)
    (l : List σ) (b : Array β) (i j : Nat) (hj : j ≤ b.size) :
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
per-run `piece`, so the map and reduce instantiations share it. -/
private theorem extract_foldl_pieces {σ : Type _} (piece : σ → Array β)
    (runs : List σ) (k : Nat) (hk : k < runs.length)
    (acc : Array β) :
    ((runs.foldl (fun b s => b ++ piece s) acc).extract
        (acc.size
          + (runs.take k).foldl (fun n s => n + (piece s).size) 0)
        (acc.size
          + (runs.take k).foldl (fun n s => n + (piece s).size) 0
          + (piece runs[k]).size))
      = piece runs[k] := by
  induction runs generalizing k acc with
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
private theorem mergeLoop_eq {n : Nat} (ck : Chunking n)
    (outs : Array (WorkerOut ck β)) (tables : Placement ck)
    (ordinal : Nat) (result : Array β) :
    mergeLoop ck outs tables ordinal result
      = (List.range' ordinal (ck.count - ordinal)).foldl
          (fun r o =>
            if h : o < ck.count then mergeStep ck outs tables ⟨o, h⟩ r else r)
          result := by
  unfold mergeLoop
  split
  next h =>
    rw [mergeLoop_eq ck outs tables (ordinal + 1)]
    rw [show ck.count - ordinal = (ck.count - (ordinal + 1)) + 1 from by
      omega]
    simp [List.range'_succ, dif_pos h]
  next h =>
    rw [show ck.count - ordinal = 0 from by omega]
    rfl
termination_by ck.count - ordinal

/-- `merge` as a pure fold over chunk ordinals. -/
private theorem merge_eq_foldl {n : Nat} (ck : Chunking n)
    (outs : Array (WorkerOut ck β)) :
    merge ck outs
      = (List.range ck.count).foldl
          (fun r o =>
            if h : o < ck.count then
              mergeStep ck outs
                (placeChunks outs
                  fun o' => ck.chunkSize.min (n - ck.start o'))
                ⟨o, h⟩ r
            else r)
          (Array.mkEmpty n) := by
  rw [merge, mergeLoop_eq]
  simp [List.range_eq_range']

/-- Prefix sum of piece lengths over the first `k` recorded runs: the
buffer offset `placeChunks` records for run `k`. -/
private def prefixLen {σ : Type _} (lenOf : σ → Nat) (runs : List σ)
    (k : Nat) : Nat :=
  (runs.take k).foldl (fun n s => n + lenOf s) 0

/-- One logical write performed by `placeChunks`. -/
private structure RunPlacement {n : Nat} (ck : Chunking n) where
  worker : Nat
  ordinal : ck.Ordinal
  offset : Nat

/-- Logical writes for one worker, with offsets supplied by a prefix scan. -/
private noncomputable def workerPlacementTrace {n : Nat} {ck : Chunking n}
    (lenOf : ck.Ordinal → Nat) (worker : Nat) (ordinals : List ck.Ordinal)
    (offset : Nat) : List (RunPlacement ck) :=
  (ordinals.zip (ordinals.scanl (fun acc o => acc + lenOf o) offset)).map
    fun p => { worker, ordinal := p.1, offset := p.2 }

/-- The nested worker/run output flattened into its logical table writes. -/
private noncomputable def placementTrace {n : Nat} {ck : Chunking n}
    (lenOf : ck.Ordinal → Nat) (firstWorker : Nat)
    (outs : List (WorkerOut ck β)) : List (RunPlacement ck) :=
  (outs.zipIdx firstWorker).flatMap fun p =>
    workerPlacementTrace lenOf p.2 p.1.ordinals.toList 0

/-- Apply one logical table write; the ordinal's bound proves it in
range. -/
private noncomputable def applyRunPlacement {n : Nat} {ck : Chunking n}
    (tables : Placement ck) (run : RunPlacement ck) : Placement ck :=
  { slotWorker := tables.slotWorker.set run.ordinal.1 (run.worker + 1)
      run.ordinal.2,
    slotOffset := tables.slotOffset.set run.ordinal.1 run.offset
      run.ordinal.2 }

/-- Folding `placeRun` performs exactly the corresponding logical writes. -/
private theorem placeRun_foldl_eq_trace {n : Nat} {ck : Chunking n}
    (lenOf : ck.Ordinal → Nat) (worker : Nat) (ordinals : List ck.Ordinal)
    (st : PlaceRun ck) :
    (ordinals.foldl (placeRun lenOf worker) st).tables =
      (workerPlacementTrace lenOf worker ordinals st.offset).foldl
        applyRunPlacement st.tables := by
  induction ordinals generalizing st with
  | nil => rfl
  | cons o rest ih =>
    simp only [List.foldl_cons]
    rw [ih (st := placeRun lenOf worker st o)]
    simp [workerPlacementTrace, applyRunPlacement, placeRun,
      List.scanl_cons]

/-- The nested implementation fold equals one fold over logical writes. -/
private theorem placeWorker_foldl_eq_trace {n : Nat} {ck : Chunking n}
    (lenOf : ck.Ordinal → Nat) (outs : List (WorkerOut ck β))
    (st : PlaceAll ck) :
    (outs.foldl (placeWorker lenOf) st).tables =
      (placementTrace lenOf st.worker outs).foldl applyRunPlacement
        st.tables := by
  induction outs generalizing st with
  | nil => rfl
  | cons out rest ih =>
    have hin := placeRun_foldl_eq_trace lenOf st.worker out.ordinals.toList
      { offset := 0, tables := st.tables }
    have hrec := ih (placeWorker lenOf st out)
    have hin' : (placeWorker lenOf st out).tables =
        (workerPlacementTrace lenOf st.worker out.ordinals.toList 0).foldl
          applyRunPlacement st.tables := by
      simpa [placeWorker, Array.foldl_toList] using hin
    have hrec' : (rest.foldl (placeWorker lenOf)
          (placeWorker lenOf st out)).tables =
        (placementTrace lenOf (st.worker + 1) rest).foldl
          applyRunPlacement (placeWorker lenOf st out).tables := by
      simpa [placeWorker] using hrec
    simp only [List.foldl_cons]
    rw [hrec']
    rw [show placementTrace lenOf st.worker (out :: rest) =
        workerPlacementTrace lenOf st.worker out.ordinals.toList 0 ++
          placementTrace lenOf (st.worker + 1) rest from rfl,
      List.foldl_append, ← hin']

/-- A fold of writes away from `o` preserves the entry at `o`. -/
private theorem foldl_vset_untouched {σ : Type _} {cc : Nat}
    (items : List σ) (index : σ → Fin cc) (value : σ → Nat)
    (v : Vector Nat cc) (o : Fin cc)
    (h : ∀ x ∈ items, index x ≠ o) :
    (items.foldl
        (fun v x => v.set (index x).1 (value x) (index x).2) v)[o.1]
      = v[o.1] := by
  induction items generalizing v with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, index y ≠ o := fun y hy => h y (by simp [hy])
    rw [List.foldl_cons,
      ih (v := v.set (index x).1 (value x) (index x).2) hxs]
    grind [Fin.ext_iff]

/-- If every write to `o` stores `w` and at least one such write occurs,
the final entry is `w`. -/
private theorem foldl_vset_constant {σ : Type _} {cc : Nat}
    (items : List σ) (index : σ → Fin cc) (value : σ → Nat)
    (v : Vector Nat cc) (o : Fin cc) (w : Nat)
    (hsame : ∀ x ∈ items, index x = o → value x = w)
    (hexists : ∃ x ∈ items, index x = o) :
    (items.foldl
        (fun v x => v.set (index x).1 (value x) (index x).2) v)[o.1]
      = w := by
  induction items generalizing v with
  | nil => grind
  | cons x xs ih =>
    have htail : ∀ y ∈ xs, index y = o → value y = w :=
      fun y hy => hsame y (by simp [hy])
    by_cases hx : index x = o
    · have hv := hsame x (by simp) hx
      by_cases hmore : ∃ y ∈ xs, index y = o
      · exact ih (v := v.set (index x).1 (value x) (index x).2)
          htail hmore
      · rw [List.foldl_cons, foldl_vset_untouched xs index value
          (v.set (index x).1 (value x) (index x).2) o (by grind)]
        grind [Fin.ext_iff]
    · exact ih (v := v.set (index x).1 (value x) (index x).2) htail
        (by grind)

/-- Folding paired logical writes is the pair of the component folds. -/
private theorem foldl_applyRunPlacement {n : Nat} {ck : Chunking n}
    (runs : List (RunPlacement ck)) (tables : Placement ck) :
    runs.foldl applyRunPlacement tables =
      { slotWorker := runs.foldl
          (fun v run => v.set run.ordinal.1 (run.worker + 1) run.ordinal.2)
          tables.slotWorker,
        slotOffset := runs.foldl
          (fun v run => v.set run.ordinal.1 run.offset run.ordinal.2)
          tables.slotOffset } := by
  induction runs generalizing tables with
  | nil => rfl
  | cons run rest ih =>
    simpa [List.foldl_cons, applyRunPlacement] using
      ih (applyRunPlacement tables run)

/-- A concrete `RunAt` occurs in the flattened logical writes. -/
private theorem RunAt.mem_placementTrace {n : Nat} {ck : Chunking n}
    (lenOf : ck.Ordinal → Nat) (firstWorker : Nat)
    {outs : List (WorkerOut ck β)} {o : ck.Ordinal}
    (target : RunAt outs o) :
    (⟨firstWorker + target.worker, o,
      prefixLen lenOf target.out.ordinals.toList target.runIdx⟩ :
        RunPlacement ck) ∈
        placementTrace lenOf firstWorker outs := by
  refine List.mem_flatMap_of_mem
    (List.mk_add_mem_zipIdx_iff_getElem?.2 target.worker_eq) ?_
  refine List.mem_map.mpr ⟨(o,
    prefixLen lenOf target.out.ordinals.toList target.runIdx), ?_, rfl⟩
  apply List.mem_of_getElem? (i := target.runIdx)
  apply List.getElem?_zip_eq_some.mpr
  constructor <;> grind [prefixLen, RunAt]

/-- Every logical write comes from a concrete worker/run position. -/
private theorem RunPlacement.of_mem_placementTrace {n : Nat}
    {ck : Chunking n} (lenOf : ck.Ordinal → Nat) (firstWorker : Nat)
    {outs : List (WorkerOut ck β)} (run : RunPlacement ck)
    (hmem : run ∈ placementTrace lenOf firstWorker outs) :
    ∃ target : RunAt outs run.ordinal,
      run.worker = firstWorker + target.worker ∧
      run.offset = prefixLen lenOf target.out.ordinals.toList
        target.runIdx := by
  obtain ⟨p, hp, hrun⟩ := List.mem_flatMap.mp hmem
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrun
  obtain ⟨k, hk, hqval⟩ := List.mem_iff_getElem.mp hq
  refine ⟨⟨p.2 - firstWorker, k, p.1, ?_, ?_⟩, ?_⟩
  · grind
  · grind
  · grind [prefixLen]

/-- Table correctness derived from the flattened logical writes. -/
private theorem placeWorker_foldl_spec {n : Nat} {ck : Chunking n}
    (lenOf : ck.Ordinal → Nat) (outs : List (WorkerOut ck β))
    (st : PlaceAll ck) (o : ck.Ordinal)
    (target : RunAt outs o)
    (huniq : ∀ other : RunAt outs o,
      other.worker = target.worker ∧ other.runIdx = target.runIdx) :
    ((outs.foldl (placeWorker lenOf) st).tables.slotWorker[o.1] =
        st.worker + target.worker + 1) ∧
      ((outs.foldl (placeWorker lenOf) st).tables.slotOffset[o.1] =
        prefixLen lenOf target.out.ordinals.toList target.runIdx) := by
  let runs := placementTrace lenOf st.worker outs
  let wanted : RunPlacement ck :=
    ⟨st.worker + target.worker, o,
      prefixLen lenOf target.out.ordinals.toList target.runIdx⟩
  have hwanted : wanted ∈ runs := by
    simpa [wanted, runs] using target.mem_placementTrace lenOf st.worker
  have hsame : ∀ run ∈ runs, run.ordinal = o →
      run.worker + 1 = st.worker + target.worker + 1 ∧
      run.offset = prefixLen lenOf target.out.ordinals.toList
        target.runIdx := by
    intro run hrun hro
    obtain ⟨other, hw, hoffset⟩ :=
      RunPlacement.of_mem_placementTrace lenOf st.worker run hrun
    obtain ⟨w', k', out', hw', hk'⟩ := other
    have hk'' : out'.ordinals[k']? = some o := by rw [hk', hro]
    have hunique := huniq ⟨w', k', out', hw', hk''⟩
    have hworker : w' = target.worker := hunique.1
    have hrunIdx : k' = target.runIdx := hunique.2
    have houtEq : out' = target.out :=
      Option.some.inj (hw'.symm.trans
        (by simpa [hworker] using target.worker_eq))
    constructor
    · omega
    · simpa [houtEq, hrunIdx] using hoffset
  have hexists : ∃ run ∈ runs, run.ordinal = o := ⟨wanted, hwanted, rfl⟩
  have hworker := foldl_vset_constant runs (fun run => run.ordinal)
    (fun run => run.worker + 1) st.tables.slotWorker o
    (st.worker + target.worker + 1)
    (fun run hrun hro => (hsame run hrun hro).1) hexists
  have hoffset := foldl_vset_constant runs (fun run => run.ordinal)
    (fun run => run.offset) st.tables.slotOffset o
    (prefixLen lenOf target.out.ordinals.toList target.runIdx)
    (fun run hrun hro => (hsame run hrun hro).2) hexists
  have hflat := (placeWorker_foldl_eq_trace lenOf outs st).trans
    (foldl_applyRunPlacement runs st.tables)
  refine ⟨?_, ?_⟩ <;> rw [hflat]
  · exact hworker
  · exact hoffset

/-- `placeChunks` computes the owner and prefix-sum tables from any
uniquely-claimed worker output: the array-level table correctness. -/
private theorem placeChunks_spec {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (lenOf : ck.Ordinal → Nat)
    (o : ck.Ordinal) (target : RunAt outs.toList o)
    (huniq : ∀ other : RunAt outs.toList o,
      other.worker = target.worker ∧ other.runIdx = target.runIdx) :
    ((placeChunks outs lenOf).slotWorker[o.1] = target.worker + 1)
      ∧ ((placeChunks outs lenOf).slotOffset[o.1]
        = prefixLen lenOf target.out.ordinals.toList target.runIdx) := by
  have hspec := placeWorker_foldl_spec lenOf outs.toList
    ⟨0, ⟨Vector.replicate ck.count 0,
      Vector.replicate ck.count 0⟩⟩ o target huniq
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
private theorem prefixLen_congr {σ : Type _} (g₁ g₂ : σ → Nat)
    (runs : List σ) (K : Nat) (h : ∀ s ∈ runs, g₁ s = g₂ s) :
    prefixLen g₁ runs K = prefixLen g₂ runs K :=
  foldl_congr_mem _ _ _
    (fun s hs n => by rw [h s (List.mem_of_mem_take hs)]) 0

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
private theorem mergeStep_owned (xs : Array α) (f : α → β)
    (ck : Chunking xs.size) (outs : Array (WorkerOut ck β))
    (o : ck.Ordinal) (target : RunAt outs.toList o)
    (h : WFOuts (fun o' => chunkSlice xs f ck.chunkSize (ck.start o'))
      outs)
    (huniq : ∀ other : RunAt outs.toList o,
      other.worker = target.worker ∧ other.runIdx = target.runIdx)
    (r : Array β) :
    mergeStep ck outs
      (placeChunks outs fun o' => ck.chunkSize.min (xs.size - ck.start o'))
      o r
      = r ++ chunkSlice xs f ck.chunkSize (ck.start o) := by
  have hownA : outs[target.worker]? = some target.out := by
    simpa using target.worker_eq
  have hwf := h.workers target.out
    (List.mem_of_getElem? target.worker_eq)
  have hspec := placeChunks_spec outs
    (fun o' => ck.chunkSize.min (xs.size - ck.start o')) o target huniq
  obtain ⟨hKlt, hKeq⟩ := Array.getElem?_eq_some_iff.mp target.run_eq
  have hoff := (hspec.2).trans
    (prefixLen_congr _ _ target.out.ordinals.toList target.runIdx
      fun o' _ =>
        (chunkSlice_size_eq xs f ck.chunkSize (ck.start o')
          (ck.start_lt o')).symm)
  have hKtl : target.out.ordinals.toList[target.runIdx] = o := by
    simpa using hKeq
  unfold mergeStep
  rw [hspec.1, hoff]
  simp only [Nat.add_sub_cancel, hownA,
    show (target.worker + 1 == 0) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [pushRange_eq, hwf.values, ← Array.foldl_toList]
  congr 1
  have hpieces := extract_foldl_pieces
    (fun o'' : ck.Ordinal => chunkSlice xs f ck.chunkSize (ck.start o''))
    target.out.ordinals.toList target.runIdx (by simpa using hKlt) #[]
  simpa only [prefixLen, Array.size_empty, Nat.zero_add, hKtl,
    ← chunkSlice_size_eq xs f ck.chunkSize (ck.start o)
      (ck.start_lt o)] using hpieces

/-- Given well-formed worker output, `merge` reconstructs `xs.map f`
independently of worker count and claim order. -/
private theorem merge_wf (xs : Array α) (f : α → β)
    (ck : Chunking xs.size) (outs : Array (WorkerOut ck β))
    (h : WFOuts (fun o => chunkSlice xs f ck.chunkSize (ck.start o))
      outs) :
    merge ck outs = xs.map f := by
  rw [merge_eq_foldl, Array.mkEmpty_eq,
    ← foldl_chunkSlice_range xs f ck.chunkSize ck.pos,
    show (xs.size + ck.chunkSize - 1) / ck.chunkSize = ck.count from
      ck.count_eq.symm]
  refine foldl_congr_mem _ _ _ ?_ #[]
  intro o ho r
  have hocc : o < ck.count := List.mem_range.mp ho
  rw [dif_pos hocc]
  let ordinal : ck.Ordinal := ⟨o, hocc⟩
  obtain ⟨target, huniq⟩ := h.once ordinal
  exact mergeStep_owned xs f ck outs ordinal target h huniq r

/-- A tabulation chunk is the assembly piece at `start` in `Array.ofFn g`. -/
private theorem tabulateChunk_piece (n : Nat) (g : Fin n → β)
    (chunkSize start : Nat) (values : Array β) :
    tabulateChunk n g ((start + chunkSize).min n) (Nat.min_le_right _ _)
      start values
      = values ++ chunkSlice (Array.ofFn g) id chunkSize start := by
  simp [tabulateChunk_eq, chunkSlice]

/-- Slicing a mapped array equals mapping the corresponding input slice. -/
private theorem chunkSlice_map_id (xs : Array α) (f : α → β)
    (chunkSize s : Nat) :
    chunkSlice (xs.map f) id chunkSize s = chunkSlice xs f chunkSize s := by
  simp [chunkSlice, ← Array.map_extract]

/-- Given well-formed tabulation output, `merge` reconstructs `Array.ofFn g`.
This instantiates `merge_wf` with the identity mapper;
`tabulateChunk_piece` supplies the tabulation-specific chunk content. -/
private theorem merge_wf_ofFn (n : Nat) (g : Fin n → β)
    (ck : Chunking (Array.ofFn g).size)
    (outs : Array (WorkerOut ck β))
    (h : WFOuts (fun o => chunkSlice (Array.ofFn g) id ck.chunkSize
      (ck.start o)) outs) :
    merge ck outs = Array.ofFn g :=
  (merge_wf (Array.ofFn g) id ck outs h).trans (Array.map_id _)

/-! ## Reduce assembly -/

/-- A slice splits off its first element. -/
private theorem extract_cons (a : Array α) (i j : Nat) (hij : i < j)
    (hi : i < a.size) :
    a.extract i j = #[a[i]] ++ a.extract (i + 1) j := by
  rw [show (#[a[i]] : Array α) = a.extract i (i + 1) from by grind,
    Array.extract_append_extract]
  congr 1 <;> omega

/-- The partial for chunk `o`: the fold of its mapped slice, seeded by the
slice's first element, matching how `workerReducePureLoop` computes it. -/
private def reducePartial (xs : Array α) (f : α → β) (op : β → β → β)
    (ck : Chunking xs.size) (o : ck.Ordinal) : β :=
  ((xs.extract (ck.start o + 1) (ck.stop o (ck.start o) rfl)).map f).foldl
    op (f (xs[ck.start o]'(ck.start_lt o)))

/-- What the reduce worker records for the claim at `o` is exactly the
chunk's seeded fold. -/
private theorem reduceChunkPure_partial (xs : Array α) (f : α → β)
    (op : β → β → β) (ck : Chunking xs.size) (o : ck.Ordinal) :
    reduceChunkPure xs f op (ck.stop o (ck.start o) rfl) (ck.start o + 1)
      (f (xs[ck.start o]'(ck.start_lt o)))
      = reducePartial xs f op ck o := by
  rw [reduceChunkPure_eq, reducePartial]

/-- Under singleton pieces, a well-formed buffer is the map of its
ordinals. -/
private theorem WFWorkerOut.values_singleton {n : Nat} {ck : Chunking n}
    {out : WorkerOut ck β} {p : ck.Ordinal → β}
    (h : WFWorkerOut (fun o => #[p o]) out) :
    out.values = out.ordinals.map p := by
  rw [h.values]
  simp

/-- Under unit run lengths, run `k`'s prefix offset is `k` itself. -/
private theorem prefixLen_one {σ : Type _} (l : List σ) (k : Nat)
    (hk : k ≤ l.length) :
    prefixLen (fun _ => 1) l k = k := by
  simp [prefixLen]
  omega

/-- At an ordinal carried by `target`, the ordered-partials step pushes
exactly that run's recorded partial. -/
private theorem orderedStep_owned {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (p : ck.Ordinal → β)
    (o : ck.Ordinal) (target : RunAt outs.toList o)
    (h : WFOuts (fun o' => #[p o']) outs)
    (huniq : ∀ other : RunAt outs.toList o,
      other.worker = target.worker ∧ other.runIdx = target.runIdx)
    (ps : Array β) :
    orderedStep outs (placeChunks outs fun _ => 1) o ps
      = ps.push (p o) := by
  have hownA : outs[target.worker]? = some target.out := by
    simpa using target.worker_eq
  have hwf := h.workers target.out
    (List.mem_of_getElem? target.worker_eq)
  have hspec := placeChunks_spec outs (fun _ => 1) o target huniq
  obtain ⟨hKlt, hKeq⟩ := Array.getElem?_eq_some_iff.mp target.run_eq
  have hoff := (hspec.2).trans
    (prefixLen_one target.out.ordinals.toList target.runIdx
      (by simpa using Nat.le_of_lt hKlt))
  unfold orderedStep
  rw [hspec.1, hoff]
  simp only [Nat.add_sub_cancel, hownA,
    show (target.worker + 1 == 0) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [hwf.values_singleton]
  simp [Array.getElem?_map, target.run_eq]

/-- With well-formed singleton pieces, the ordinal loop appends the
corresponding suffix of `Array.ofFn p`. -/
private theorem orderedPartialsLoop_wf {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (p : ck.Ordinal → β)
    (h : WFOuts (fun o => #[p o]) outs) (ordinal : Nat) (ps : Array β) :
    orderedPartialsLoop outs (placeChunks outs fun _ => 1) ordinal ps
      = ps ++ (Array.ofFn p).extract ordinal ck.count := by
  unfold orderedPartialsLoop
  split
  next hocc =>
    obtain ⟨target, huniq⟩ := h.once ⟨ordinal, hocc⟩
    rw [orderedPartialsLoop_wf outs p h (ordinal + 1),
      orderedStep_owned outs p ⟨ordinal, hocc⟩ target h huniq,
      Array.push_eq_append,
      extract_cons (Array.ofFn p) ordinal ck.count hocc (by simpa)]
    simp [Array.getElem_ofFn]
  next hdone =>
    rw [Array.extract_empty_of_stop_le_start (Nat.le_of_not_gt hdone)]
    simp
termination_by ck.count - ordinal

/-- From well-formed reduce output with singleton pieces,
`orderedPartials` reconstructs every chunk's partial in ordinal order. -/
private theorem orderedPartials_wf {n : Nat} {ck : Chunking n}
    (outs : Array (WorkerOut ck β)) (p : ck.Ordinal → β)
    (h : WFOuts (fun o => #[p o]) outs) :
    orderedPartials outs = Array.ofFn p := by
  rw [orderedPartials, orderedPartialsLoop_wf outs p h]
  simp

/-- A seeded fold merges into a running fold, given associativity. -/
private theorem foldl_op_seeded (op : β → β → β) [Std.Associative op]
    (a : Array β) (x acc : β) :
    a.foldl op (op acc x) = op acc (a.foldl op x) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, List.foldl_assoc]

/-- Folding one seeded partial into an accumulator is folding its whole
mapped chunk into that accumulator. -/
private theorem reducePartial_foldl (xs : Array α) (f : α → β)
    (op : β → β → β) [Std.Associative op] (ck : Chunking xs.size)
    (o : ck.Ordinal) (acc : β) :
    op acc (reducePartial xs f op ck o)
      = (chunkSlice xs f ck.chunkSize (ck.start o)).foldl op acc := by
  unfold reducePartial chunkSlice Chunking.stop
  rw [extract_cons xs (ck.start o)
      ((ck.start o + ck.chunkSize).min xs.size)
      (by
        have hs := ck.start_lt o
        grind [Chunking])
      (ck.start_lt o),
    Array.map_append, Array.foldl_append]
  simp only [Array.map_singleton]
  rw [show (#[f (xs[ck.start o]'(ck.start_lt o))] : Array β).foldl op acc =
      op acc (f (xs[ck.start o]'(ck.start_lt o))) by simp]
  rw [foldl_op_seeded]

/-- Folding arrays one by one is folding their concatenation. -/
private theorem foldl_pieces {σ : Type _} (piece : σ → Array β)
    (items : List σ) (op : β → β → β) (out : Array β) (acc : β) :
    items.foldl (fun acc x => (piece x).foldl op acc) (out.foldl op acc)
      = (items.foldl (fun out x => out ++ piece x) out).foldl op acc := by
  induction items generalizing out acc with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ← Array.foldl_append, ih, List.foldl_cons]

/-- The `Fin` ordinals enumerate the same chunk slices as the natural-number
range used by ordered assembly. -/
private theorem foldl_chunkSlice_finRange (xs : Array α) (f : α → β)
    (ck : Chunking xs.size) :
    (List.finRange ck.count).foldl
        (fun acc o => acc ++ chunkSlice xs f ck.chunkSize (ck.start o)) #[]
      = xs.map f := by
  simp only [Chunking.start]
  rw [← List.foldl_map
    (f := fun o : ck.Ordinal => o.1)
    (g := fun acc o => acc ++
      chunkSlice xs f ck.chunkSize (o * ck.chunkSize))]
  rw [show (List.finRange ck.count).map (fun o => o.1) =
      List.range ck.count from by apply List.ext_getElem <;> simp]
  simpa [Chunking.start, ck.count_eq] using
    foldl_chunkSlice_range xs f ck.chunkSize ck.pos

/-- Folding the chunk partials in ordinal order is the serial fold:
associativity merges each seeded chunk fold into the running fold. -/
private theorem foldl_reducePartials (xs : Array α) (f : α → β)
    (op : β → β → β) [Std.Associative op] (ck : Chunking xs.size)
    (init : β) :
    (Array.ofFn (reducePartial xs f op ck)).foldl op init
      = (xs.map f).foldl op init := by
  rw [← Array.foldl_toList, Array.toList_ofFn,
    show List.ofFn (reducePartial xs f op ck) =
        (List.finRange ck.count).map (reducePartial xs f op ck) from by
      simp [List.finRange, Function.comp_def],
    List.foldl_map]
  calc
    _ = (List.finRange ck.count).foldl
        (fun acc o =>
          (chunkSlice xs f ck.chunkSize (ck.start o)).foldl op acc) init :=
      foldl_congr_mem _ _ _
        (fun o _ acc => reducePartial_foldl xs f op ck o acc) init
    _ = ((List.finRange ck.count).foldl
          (fun out o => out ++ chunkSlice xs f ck.chunkSize (ck.start o))
          #[]).foldl op init := by
      simpa using foldl_pieces
        (fun o : ck.Ordinal => chunkSlice xs f ck.chunkSize (ck.start o))
        (List.finRange ck.count) op #[] init
    _ = (xs.map f).foldl op init := by rw [foldl_chunkSlice_finRange]

/-- From well-formed reduce output with singleton pieces, the ordered
partials fold to the serial specification. -/
private theorem orderedPartials_foldl_wf (xs : Array α) (f : α → β)
    (op : β → β → β) [Std.Associative op] (ck : Chunking xs.size)
    (outs : Array (WorkerOut ck β)) (init : β)
    (h : WFOuts (fun o => #[reducePartial xs f op ck o]) outs) :
    (orderedPartials outs).foldl op init = (xs.map f).foldl op init := by
  rw [orderedPartials_wf outs _ h, foldl_reducePartials]

/-- The second reduction level is the same result at the identity mapper:
ordered partials of partials fold to the fold of the partials. -/
private theorem orderedPartials_foldl_wf_id (ps : Array β)
    (op : β → β → β) [Std.Associative op] (ck : Chunking ps.size)
    (outs : Array (WorkerOut ck β)) (init : β)
    (h : WFOuts (fun o => #[reducePartial ps id op ck o]) outs) :
    (orderedPartials outs).foldl op init = ps.foldl op init := by
  rw [orderedPartials_foldl_wf ps id op ck outs init h, Array.map_id]

/-! ## Schedule replay

Lean exposes no semantics for refs, tasks, or `unsafeBaseIO` against
which the workers' execution can be proved. Instead, a schedule -- the
ordered claim trace of every worker -- is modelled as pure data, and a
pure replay of any partitioned schedule is proved to produce well-formed
output. The assembly theorems then finish the job. What stays trusted is:

- successful claims collectively form a partition of all ordinals, made
  in ascending ordinal order;
- each worker processes and records its successful claims as the replay
  model specifies (per-claim content is the proved `tabulateChunk_piece`
  and `reduceChunkPure_partial`);
- `joinRegion` returns the inline output and every spawned worker's
  output; and
- the `unsafeCast`/`unsafeBaseIO` bridge preserves the pure callback and
  values.

The scheduler is trusted only to produce a partitioned trace and execute
it faithfully; all content, ordering, placement, and reduction reasoning
is kernel-checked. -/

/-- A schedule: each worker's successfully claimed ordinals, in claim
order. Order matters because buffer offsets depend on it; the carrier
matches the runtime workers' own recording. -/
private abbrev Schedule {n : Nat} (ck : Chunking n) :=
  Array (Array ck.Ordinal)

/-- A worker/position pair whose claimed ordinal is `o`, mirroring
`RunAt` on the schedule side. -/
private structure ClaimAt {n : Nat} {ck : Chunking n}
    (sched : Schedule ck) (o : ck.Ordinal) where
  worker : Nat
  position : Nat
  claims : Array ck.Ordinal
  worker_eq : sched[worker]? = some claims
  claim_eq : claims[position]? = some o

/-- A schedule partitions the ordinals: every ordinal is claimed at
exactly one worker and position. -/
private def Schedule.Partition {n : Nat} {ck : Chunking n}
    (sched : Schedule ck) : Prop :=
  ∀ o : ck.Ordinal,
    ∃ c : ClaimAt sched o, ∀ other : ClaimAt sched o,
      other.worker = c.worker ∧ other.position = c.position

/-- Pure replay of one worker: append each claim's piece and record its
ordinal, in claim order -- per claim, exactly what the runtime workers do. -/
@[reducible] private noncomputable def replayWorker {n : Nat} {ck : Chunking n}
    (piece : ck.Ordinal → Array β) (claims : Array ck.Ordinal) :
    WorkerOut ck β where
  values := claims.foldl (fun acc o => acc ++ piece o) #[]
  ordinals := claims

/-- A replayed worker is well formed, definitionally: its buffer is the
fold `WFWorkerOut` asks for. -/
private theorem replayWorker_wf {n : Nat} {ck : Chunking n}
    (piece : ck.Ordinal → Array β) (claims : Array ck.Ordinal) :
    WFWorkerOut piece (replayWorker piece claims) :=
  ⟨rfl⟩

/-- Pure replay of a whole schedule: one worker output per trace. -/
private noncomputable def replaySchedule {n : Nat} {ck : Chunking n}
    (piece : ck.Ordinal → Array β) (sched : Schedule ck) :
    Array (WorkerOut ck β) :=
  sched.map (replayWorker piece)

/-- A partitioned schedule replays to well-formed collective output: the
pure content of the concurrent bridge. -/
private theorem replaySchedule_wf {n : Nat} {ck : Chunking n}
    (piece : ck.Ordinal → Array β) (sched : Schedule ck)
    (h : sched.Partition) :
    WFOuts piece (replaySchedule piece sched) := by
  refine ⟨by grind only [replaySchedule, = Array.mem_toList_iff,
    = Array.mem_map, replayWorker_wf], ?_⟩
  intro o
  obtain ⟨c, huniq⟩ := h o
  refine ⟨⟨c.worker, c.position, replayWorker piece c.claims,
    by
      rw [Array.getElem?_toList, replaySchedule, Array.getElem?_map,
        c.worker_eq, Option.map_some],
    c.claim_eq⟩, ?_⟩
  intro other
  obtain ⟨w, k, out, hw, hk⟩ := other
  obtain ⟨claims, hclaims, rfl⟩ := Option.map_eq_some_iff.mp
    (by simpa [replaySchedule, Array.getElem?_toList,
      Array.getElem?_map] using hw)
  exact huniq ⟨w, k, claims, hclaims, hk⟩

/-- Any partitioned schedule replays to the serial map result. -/
private theorem replay_merge (xs : Array α) (f : α → β)
    (ck : Chunking xs.size) (sched : Schedule ck) (h : sched.Partition) :
    merge ck (replaySchedule
      (fun o => chunkSlice xs f ck.chunkSize (ck.start o)) sched)
      = xs.map f :=
  merge_wf xs f ck _ (replaySchedule_wf _ sched h)

/-- Any partitioned schedule replays to the tabulation result. -/
private theorem replay_merge_ofFn (n : Nat) (g : Fin n → β)
    (ck : Chunking (Array.ofFn g).size) (sched : Schedule ck)
    (h : sched.Partition) :
    merge ck (replaySchedule
      (fun o => chunkSlice (Array.ofFn g) id ck.chunkSize (ck.start o))
      sched)
      = Array.ofFn g :=
  merge_wf_ofFn n g ck _ (replaySchedule_wf _ sched h)

/-- Any partitioned schedule replays to the serial reduction. -/
private theorem replay_reduce (xs : Array α) (f : α → β)
    (op : β → β → β) [Std.Associative op] (ck : Chunking xs.size)
    (sched : Schedule ck) (h : sched.Partition) (init : β) :
    (orderedPartials (replaySchedule
        (fun o => #[reducePartial xs f op ck o]) sched)).foldl op init
      = (xs.map f).foldl op init :=
  orderedPartials_foldl_wf xs f op ck _ init (replaySchedule_wf _ sched h)

/-! ## Effectful specifications

The monadic combinators run real effects, so their contracts split into
proved pure content and an explicit assumption: outcomes are
schedule-independent -- the callback at `i` returns the value
`outcome i` (modelled as a pure callback below) regardless of worker
count, claim order, or chunk boundaries. Within a chunk, effects run in
index order; cross-chunk effect order is unspecified. Under that
assumption the monadic chunk loops compute the pure chunk loops, so a
monadic worker records the same `WorkerOut` the schedule replay models,
and the replay theorems give result order for `tabulateM` and `mapM`.
For the fallible path, a chunk yields the prefix before its least
failing index together with that failure, and the failure register
selects the least reported index whatever the arrival order; with claims
made in ascending ordinal order (part of the trusted schedule
statement), the rethrown error is therefore the one at the least failing
input index. -/

/-- With a pure callback in a lawful monad, the monadic tabulation chunk
is the pure chunk. -/
private theorem tabulateChunkM_pure {m : Type → Type} [Monad m]
    [LawfulMonad m] (n : Nat) (f : Fin n → β)
    (stop : Nat) (hstop : stop ≤ n) (i : Nat) (values : Array β) :
    tabulateChunkM (m := m) n (fun j => pure (f j)) stop hstop i values
      = pure (tabulateChunk n f stop hstop i values) := by
  fun_induction tabulateChunkM <;>
    (rw [tabulateChunk]; simp only [bind_pure_comp, map_pure, ↓reduceDIte, *])

/-- With a pure callback in a lawful monad, the monadic reduce chunk is
the pure chunk. -/
private theorem foldlM_reduceChunkPure {m : Type → Type} [Monad m]
    [LawfulMonad m] (xs : Array α) (f : α → β)
    (op : β → β → β) (stop i : Nat) (acc : β) :
    xs.foldlM (fun acc x => pure (op acc (f x))) acc i stop
      = (pure (reduceChunkPure xs f op stop i acc) : m β) :=
  Array.foldlM_pure

/-- Pure specification of one fallible chunk: the values of the
successes before the chunk's least failing index, and that failure if
any. -/
private noncomputable def runChunkSpec (n : Nat) (outcome : Fin n → Except ε β)
    (stop : Nat) (hstop : stop ≤ n) (i : Nat) (values : Array β) :
    Array β × Option (Fin n × ε) :=
  if h : i < stop then
    match outcome ⟨i, Nat.lt_of_lt_of_le h hstop⟩ with
    | .ok value => runChunkSpec n outcome stop hstop (i + 1)
        (values.push value)
    | .error e => (values, some (⟨i, Nat.lt_of_lt_of_le h hstop⟩, e))
  else (values, none)
termination_by stop - i

/-- With a pure callback in a lawful monad, the fallible chunk runner
computes its specification. -/
private theorem runChunk_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (n : Nat) (outcome : Fin n → Except ε β)
    (stop : Nat) (hstop : stop ≤ n) (i : Nat) (values : Array β) :
    runChunk (m := m) n (fun j => pure (outcome j)) stop hstop i values
      = pure (runChunkSpec n outcome stop hstop i values) := by
  fun_induction runChunkSpec <;>
    (rw [runChunk]; simp only [↓reduceDIte, pure_bind, *])

/-- A chunk with no failing index tabulates its successes. -/
private theorem runChunkSpec_ok (n : Nat) (outcome : Fin n → Except ε β)
    (f : Fin n → β) (stop : Nat) (hstop : stop ≤ n) (i : Nat)
    (values : Array β)
    (hok : ∀ j : Fin n, i ≤ j.1 → j.1 < stop → outcome j = .ok (f j)) :
    runChunkSpec n outcome stop hstop i values
      = (tabulateChunk n f stop hstop i values, none) := by
  fun_induction runChunkSpec <;> rw [tabulateChunk] <;>
    grind only

/-- A chunk whose least failing index is `j₀` yields the tabulated
prefix below `j₀` and that failure. -/
private theorem runChunkSpec_err (n : Nat) (outcome : Fin n → Except ε β)
    (f : Fin n → β) (stop : Nat) (hstop : stop ≤ n) (i : Nat)
    (values : Array β) (j₀ : Fin n) (e : ε)
    (hij : i ≤ j₀.1) (hjs : j₀.1 < stop)
    (hfail : outcome j₀ = .error e)
    (hbelow : ∀ j : Fin n, i ≤ j.1 → j.1 < j₀.1 → outcome j = .ok (f j)) :
    runChunkSpec n outcome stop hstop i values
      = (tabulateChunk n f j₀.1 (Nat.le_of_lt j₀.2) i values,
          some (j₀, e)) := by
  revert hij hbelow
  fun_induction runChunkSpec <;> rw [tabulateChunk] <;>
    grind only [= Lean.Grind.toInt_fin]

/-- On a nonempty register, `keepLower` is the standard first-minimum
operation on indices. -/
private theorem keepLower_some {n : Nat} (q p : Fin n × ε) :
    keepLower (some q) p = some (minOn Prod.fst q p) := by
  rcases q with ⟨j, e⟩
  by_cases h : p.1 < j
  · simp only [keepLower, h, ↓reduceIte, minOn, Fin.not_le.mpr h]
  · simp only [keepLower, h, ↓reduceIte, minOn, Fin.not_lt.mp h]

/-- Folding reported failures with `keepLower` is the standard
first-minimum fold on their indices. -/
private theorem foldl_keepLower_eq_minOn? {n : Nat}
    (l : List (Fin n × ε)) :
    l.foldl keepLower none = l.minOn? Prod.fst := by
  have fold_some : ∀ (l : List (Fin n × ε)) (q : Fin n × ε),
      l.foldl keepLower (some q) =
        some (l.foldl (minOn Prod.fst) q) := by
    intro l q
    induction l generalizing q <;>
      simp_all only [List.foldl_nil, Prod.forall, List.foldl_cons,
        keepLower_some]
  cases l <;>
    simp only [List.foldl_nil, List.foldl_cons, keepLower, fold_some,
      List.minOn?]

/-- Whatever order failures reach the register, it ends at the least
reported index; with each index reported at most once, at that index's
entry. -/
private theorem foldl_keepLower_min {n : Nat} (l : List (Fin n × ε))
    (j₀ : Fin n) (e₀ : ε)
    (hmem : (j₀, e₀) ∈ l)
    (hmin : ∀ p ∈ l, j₀ ≤ p.1)
    (huniq : ∀ p ∈ l, p.1 = j₀ → p = (j₀, e₀)) :
    l.foldl keepLower none = some (j₀, e₀) := by
  rw [foldl_keepLower_eq_minOn?, List.minOn?_eq_some_minOn
    (List.ne_nil_of_mem hmem)]
  congr 1
  exact huniq _ List.minOn_mem <| Fin.le_antisymm
    (List.apply_minOn_le_of_mem hmem) (hmin _ List.minOn_mem)

/-- Number of currently reserved worker slots, including inline callers'
slots; zero whenever no combinator is running. For tests and diagnostics. -/
def activeSlots : BaseIO Nat :=
  activeRef.get

/-- Snapshot of the reservation statistics. For tests and diagnostics. -/
def budgetStats : BaseIO BudgetStats :=
  statsRef.get

end Linen
