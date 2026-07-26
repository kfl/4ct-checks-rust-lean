import Std.Async.System

/-!
A small data-parallel array executor with no dependencies beyond Lean's
standard library.

Lean's task pool is a good fit for coarse tasks, but representing every
element of a large array as its own `Task` pays queue and scheduler traffic
per element. Linen instead starts a bounded set of workers that claim chunks
from an atomic cursor. This balances uneven work without creating a task per
element.

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

/-- Monadic `mapM` worker. It appends values in claim order and records each
chunk's start; the merge derives chunk lengths from those starts. -/
private partial def workerMapMLoop (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (chunkSize : Nat) (values : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (values, starts)
  let stop := (start + chunkSize).min xs.size
  let mut values := values
  for x in xs[start:stop] do
    values := values.push (← f x)
  workerMapMLoop cursor xs f chunkSize values (starts.push start)

/-- Allocate buffers when the task runs so workers do not share a captured
array. -/
private def workerMapM (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapMLoop cursor xs f chunkSize (Array.mkEmpty valuesCap)
    (Array.mkEmpty startsCap)

/-- Monadic `mapReduceM` worker. Each chunk is folded left-to-right into one
partial, seeded by its first element. -/
private partial def workerMapReduceMLoop (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (op : β → β → β) (chunkSize : Nat)
    (partials : Array β) (starts : Array Nat) :
    BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (partials, starts)
  let stop := (start + chunkSize).min xs.size
  let some x ← pure xs[start]?
    | return (partials, starts)
  let mut acc ← f x
  for x in xs[start + 1:stop] do
    acc := op acc (← f x)
  workerMapReduceMLoop cursor xs f op chunkSize (partials.push acc) (starts.push start)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapReduceM (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (op : β → β → β) (chunkSize startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapReduceMLoop cursor xs f op chunkSize (Array.mkEmpty startsCap)
    (Array.mkEmpty startsCap)

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
preventing new claims while the current chunks run to completion, and retains
the lowest-index failure. Because chunks are claimed in order, all earlier elements have run
when the tasks join. Failed chunks are omitted; results are merged only when
every worker succeeds. -/
private partial def workerMapIOLoop (cursor : IO.Ref Nat)
    (failure : IO.Ref (Option (Nat × ε))) (xs : Array α)
    (f : α → BaseIO (Except ε β)) (chunkSize : Nat) (values : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (values, starts)
  let stop := (start + chunkSize).min xs.size
  match ← runChunk xs f stop start values with
  | (values, none) =>
    workerMapIOLoop cursor failure xs f chunkSize values (starts.push start)
  | (values, some (i, e)) =>
    cursor.set xs.size
    failure.modify fun current =>
      match current with
      | some (j, _) => if i < j then some (i, e) else current
      | none => some (i, e)
    return (values, starts)

/-- Allocate worker-local buffers inside the task. -/
private def workerMapIO (cursor : IO.Ref Nat)
    (failure : IO.Ref (Option (Nat × ε))) (xs : Array α)
    (f : α → BaseIO (Except ε β)) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapIOLoop cursor failure xs f chunkSize (Array.mkEmpty valuesCap)
    (Array.mkEmpty startsCap)

private def spawnWorkers (count : Nat)
    (work : BaseIO (Array β × Array Nat)) :
    BaseIO (Array (Array β × Array Nat)) := do
  let mut tasks : Array (Task (Array β × Array Nat)) := Array.mkEmpty count
  for _ in [0:count] do
    tasks := tasks.push (← BaseIO.asTask work)
  tasks.mapM IO.wait

private def workerCount (size chunkSize : Nat) : Nat :=
  let chunks := (size + chunkSize - 1) / chunkSize
  config.workers.min chunks

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

private partial def workerMapPureLoop (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → β) (chunkSize : Nat) (values : Array β) (starts : Array Nat) :
    BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if start ≥ xs.size then return (values, starts)
  let stop := (start + chunkSize).min xs.size
  workerMapPureLoop cursor xs f chunkSize
    (mapChunkPure xs f stop (Nat.min_le_right _ _) start values)
    (starts.push start)

private def workerMapPure (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → β) (chunkSize valuesCap startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerMapPureLoop cursor xs f chunkSize (Array.mkEmpty valuesCap)
    (Array.mkEmpty startsCap)

private def reduceChunkPure (xs : Array α) (f : α → β) (op : β → β → β)
    (stop : Nat) (hstop : stop ≤ xs.size) (i : Nat) (acc : β) : β :=
  if hi : i < stop then
    reduceChunkPure xs f op stop hstop (i + 1)
      (op acc (f (xs[i]'(Nat.lt_of_lt_of_le hi hstop))))
  else acc
termination_by stop - i

private partial def workerReducePureLoop (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → β) (op : β → β → β) (chunkSize : Nat) (partials : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let start ← claim cursor xs.size chunkSize
  if hstart : start < xs.size then
    let stop := (start + chunkSize).min xs.size
    let seed := f (xs[start]'hstart)
    let acc := reduceChunkPure xs f op stop (Nat.min_le_right _ _) (start + 1) seed
    workerReducePureLoop cursor xs f op chunkSize (partials.push acc)
      (starts.push start)
  else
    return (partials, starts)

private def workerReducePure (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → β) (op : β → β → β) (chunkSize startsCap : Nat) :
    BaseIO (Array β × Array Nat) :=
  workerReducePureLoop cursor xs f op chunkSize (Array.mkEmpty startsCap)
    (Array.mkEmpty startsCap)

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
    let levelOuts ← spawnWorkers count
      (workerReducePure cursor ps id op levelChunk
        (startsCapacity ps.size count levelChunk))
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
    let outs ← spawnWorkers count
      (workerMapM cursor xs f chunkSize
        (valuesCapacity xs.size count)
        (startsCapacity xs.size count chunkSize))
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
    let outs ← spawnWorkers count
      (workerMapReduceM cursor xs f op chunkSize
        (startsCapacity xs.size count chunkSize))
    mergeReduce outs xs.size chunkSize op init

/-- Parallel engine for the pure `map` runtime; preconditions (more than one
worker, `size > chunkSize`) are checked by `mapImpl`. -/
private def mapCoreIO (xs : Array α) (f : α → β) (chunkSize : Nat) :
    BaseIO (Array β) := do
  let count := workerCount xs.size chunkSize
  let cursor ← IO.mkRef 0
  let outs ← spawnWorkers count
    (workerMapPure cursor xs f chunkSize
      (valuesCapacity xs.size count)
      (startsCapacity xs.size count chunkSize))
  return merge outs xs.size chunkSize

/-- Parallel engine for the pure `mapReduce` runtime; preconditions as for
`mapCoreIO`. -/
private def reduceCoreIO (xs : Array α) (f : α → β) (op : β → β → β)
    (init : β) (chunkSize : Nat) : BaseIO β := do
  let count := workerCount xs.size chunkSize
  let cursor ← IO.mkRef 0
  let outs ← spawnWorkers count
    (workerReducePure cursor xs f op chunkSize
      (startsCapacity xs.size count chunkSize))
  mergeReduce outs xs.size chunkSize op init

/-- Runtime implementation of `map`. Its public specification is `xs.map f`,
so tasks and scheduling are absent from proofs. -/
private unsafe def mapImpl.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (chunkSize : Nat := 1) : Array β :=
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.map f
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
    -- Serial fast path avoids task setup and intermediate partials.
    xs.foldl (fun acc x => op acc (f x)) init
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
    let outs ← spawnWorkers count
      (workerMapIO cursor failure xs (fun x => (f x).toBaseIO) chunkSize
        (valuesCapacity xs.size count)
        (startsCapacity xs.size count chunkSize))
    match ← failure.get with
    | some (_, e) => throw e
    | none => return merge outs xs.size chunkSize

/-- Parallel `IO` traversal, fail-fast with the same deterministic
smallest-index error reporting as `mapIO`. -/
def forEach (xs : Array α) (f : α → IO Unit) (chunkSize : Nat := 1) :
    IO Unit :=
  discard <| mapIO xs f chunkSize

end Linen
