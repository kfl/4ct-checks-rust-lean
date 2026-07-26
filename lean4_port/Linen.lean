import Std.Async.System

/-!
A small, dependency-free data-parallel executor.

Lean's task pool is a good fit for coarse tasks, but representing every
element of a large array as its own `Task` pays queue and scheduler traffic
per element. `Linen.mapM` instead starts a bounded team of workers. Workers
repeatedly claim a small chunk from an atomic cursor, so cheap and expensive
elements balance dynamically without becoming individual Lean `Task`s.

The worker count follows `LINEN_WORKERS`, then `LEAN_NUM_THREADS`, then the
machine's logical core count. The claim size is the per-call `chunkSize`
argument and defaults to one: granularity is a property of each call site's
workload, so it lives in the code rather than the environment.
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
ignored, leaving at least one worker; a failing core-count query degrades to
one worker. -/
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

/-- Claim the next half-open chunk.  This is the executor's scheduling point:
workers that finish cheap chunks return here and take work from the common
remainder instead of becoming idle. Fail-fast cancellation reuses the cursor
(a failing worker moves it to the end), so claiming stays a single shared
atomic operation. -/
private def claim (cursor : IO.Ref Nat) (size chunkSize : Nat) :
    BaseIO (Option (Nat × Nat)) := do
  cursor.modifyGet fun next =>
    if next < size then
      let stop := (next + chunkSize).min size
      (some (next, stop), stop)
    else
      (none, next)

/-- Infallible worker: values in claim order plus the start index of every
claimed chunk. Chunk lengths are derivable (`min chunkSize (size - start)`),
so the hot loop pushes bare values with no per-element bookkeeping. -/
private partial def workerPure (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (chunkSize : Nat) (values : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let some (start, stop) ← claim cursor xs.size chunkSize
    | return (values, starts)
  let mut values := values
  for x in xs[start:stop] do
    values := values.push (← f x)
  workerPure cursor xs f chunkSize values (starts.push start)

/-- Reducing worker: each claimed chunk is folded left-to-right into a single
partial, seeded by the chunk's first element, so the buffer holds one value
per chunk. -/
private partial def workerReduce (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (op : β → β → β) (chunkSize : Nat)
    (partials : Array β) (starts : Array Nat) :
    BaseIO (Array β × Array Nat) := do
  let some (start, stop) ← claim cursor xs.size chunkSize
    | return (partials, starts)
  let some x ← pure xs[start]?
    | return (partials, starts)
  let mut acc ← f x
  for x in xs[start + 1:stop] do
    acc := op acc (← f x)
  workerReduce cursor xs f op chunkSize (partials.push acc) (starts.push start)

/-- One chunk of fallible work, as explicit recursion so the failure exit does
not thread an early-exit step through the `forIn` lowering. Returns the input
index and error of the first failure, if any. -/
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

/-- Fallible worker. On failure it moves the cursor to the end -- so every
worker stops claiming within one chunk -- and records its failure if it is the
smallest-index one seen. The cursor is monotonic, so every element before the
smallest failing index has run and the reported failure is deterministic.
Failed chunks are not recorded in `starts`; results are only merged when no
worker failed. -/
private partial def workerIO (cursor : IO.Ref Nat)
    (failure : IO.Ref (Option (Nat × ε))) (xs : Array α)
    (f : α → BaseIO (Except ε β)) (chunkSize : Nat) (values : Array β)
    (starts : Array Nat) : BaseIO (Array β × Array Nat) := do
  let some (start, stop) ← claim cursor xs.size chunkSize
    | return (values, starts)
  match ← runChunk xs f stop start values with
  | (values, none) =>
    workerIO cursor failure xs f chunkSize values (starts.push start)
  | (values, some (i, e)) =>
    cursor.set xs.size
    failure.modify fun current =>
      match current with
      | some (j, _) => if i < j then some (i, e) else current
      | none => some (i, e)
    return (values, starts)

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

/-- Ordinal placement of per-worker chunk runs. Chunk starts are multiples of
`chunkSize`, so each chunk has the ordinal `start / chunkSize`; the tables
record, per ordinal, the worker that claimed the chunk (`+ 1`, with `0` for
unclaimed) and the offset of its run in that worker's buffer, where the chunk
starting at `start` contributes `lenOf start` buffer entries. -/
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

/-- Combine per-chunk partials into `((init ⋆ p₀) ⋆ p₁) ⋆ ⋯` for chunk-ordinal
order `p₀, p₁, …`; associativity of `⋆` makes the total equal the sequential
left fold. When the partials outnumber the workers, one bounded parallel level
folds contiguous runs of `⌈count/workers⌉` partials first -- order-preserving,
so associativity still suffices -- leaving at most one partial per worker for
the serial combine. At most as many partials as workers would give a level
with no `⋆` applications, so that case combines serially outright. -/
private def mergeReduce (outs : Array (Array β × Array Nat))
    (size chunkSize : Nat) (op : β → β → β) (init : β) : BaseIO β := do
  let ps := orderedPartials outs size chunkSize
  if ps.size ≤ config.workers then
    return ps.foldl op init
  else
    let levelChunk := (ps.size + config.workers - 1) / config.workers
    let cursor ← IO.mkRef 0
    let levelOuts ← spawnWorkers (workerCount ps.size levelChunk)
      (workerReduce cursor ps pure op levelChunk #[] #[])
    return (orderedPartials levelOuts ps.size levelChunk).foldl op init

/-- Bounded, dynamically balanced map engine.  At most one Lean task per
configured worker is created, regardless of `xs.size`; results are restored to
input order after all workers finish. `chunkSize` sets the claim granularity
for this call and is clamped to at least one. -/
def mapM (xs : Array α) (f : α → BaseIO β) (chunkSize : Nat := 1) :
    BaseIO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.mapM f
  else
    let cursor ← IO.mkRef 0
    let outs ← spawnWorkers (workerCount xs.size chunkSize)
      (workerPure cursor xs f chunkSize #[] #[])
    return merge outs xs.size chunkSize

/-- Bounded, dynamically balanced map-reduce engine: chunks are folded to one
partial each as they are claimed, and the partials are combined in input
order, so associativity of `op` (not commutativity) is what makes the result
equal the sequential left fold from `init` -- hence the `Std.Associative`
obligation. -/
def mapReduceM (xs : Array α) (f : α → BaseIO β) (op : β → β → β)
    (init : β) (chunkSize : Nat := 1) [Std.Associative op] : BaseIO β := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.foldlM (fun acc x => return op acc (← f x)) init
  else
    let cursor ← IO.mkRef 0
    let outs ← spawnWorkers (workerCount xs.size chunkSize)
      (workerReduce cursor xs f op chunkSize #[] #[])
    mergeReduce outs xs.size chunkSize op init

/-- Runtime implementation of `map`. The public definition remains the
sequential specification, so theorem proving never has to model tasks, atomic
references, or scheduling. -/
private unsafe def mapImpl.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (chunkSize : Nat := 1) : Array β :=
  -- `BaseIO`/`IO.Ref` store `Type 0`; the casts only erase universe
  -- bookkeeping. `NonScalar` is pointer-represented, so the compiler passes
  -- the runtime values through `f` and the result array unchanged (the same
  -- erasure pattern as `Array.mapMUnsafe`).
  unsafeCast <| unsafeBaseIO <|
    mapM (unsafeCast xs : Array NonScalar)
      (fun x => pure ((unsafeCast f : NonScalar → NonScalar) x)) chunkSize

/-- Parallel `Array.map`, order-preserving and definitionally equal to the
sequential operation for reasoning: for every `chunkSize` the specification is
`xs.map f` -- the claim granularity only affects scheduling. -/
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
  if config.workers == 1 || xs.size ≤ chunkSize.max 1 then
    -- Serial fast path on the pure operation. Routing this case through
    -- `mapReduceM` would pay the monadic fold's per-element bind machinery
    -- for no benefit.
    xs.foldl (fun acc x => op acc (f x)) init
  else
    -- The same universe erasure as `mapImpl`; `op` and `init` ride along as
    -- `NonScalar` values, and the erased associativity obligation (about the
    -- original `op`, which the caller supplied) is re-stated with `lcProof`.
    unsafeCast <| unsafeBaseIO <|
      @mapReduceM NonScalar NonScalar (unsafeCast xs)
        (fun x => pure ((unsafeCast f : NonScalar → NonScalar) x))
        (unsafeCast op) (unsafeCast init) chunkSize lcProof

/-- Parallel map-reduce with the sequential left fold `(xs.map f).foldl op
init` as its specification. The `Std.Associative op` instance is the caller's
obligation that makes the specification and the parallel runtime agree: the
engine folds each claimed chunk to one partial and combines partials in input
order, so associativity alone (no commutativity, no identity law for `init`)
closes the gap.

`op` runs in parallel both inside chunk folds and in the partial combine's
bounded parallel level (see `mergeReduce`); at most one `op` application per
worker is serial. -/
@[implemented_by mapReduceImpl]
def mapReduce.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) (op : β → β → β) (init : β)
    (chunkSize : Nat := 1) [Std.Associative op] : β :=
  (xs.map f).foldl op init

/-- Parallel `IO` map, fail-fast: the first failure stops workers from
claiming further chunks, and the failure at the smallest input index is
re-raised deterministically (see `workerIO`). `chunkSize` sets the claim
granularity for this call and is clamped to at least one. -/
def mapIO (xs : Array α) (f : α → IO β) (chunkSize : Nat := 1) :
    IO (Array β) := do
  let chunkSize := chunkSize.max 1
  if config.workers == 1 || xs.size ≤ chunkSize then
    xs.mapM f
  else
    let cursor ← IO.mkRef 0
    let failure ← IO.mkRef (none : Option (Nat × IO.Error))
    let outs ← spawnWorkers (workerCount xs.size chunkSize)
      (workerIO cursor failure xs (fun x => (f x).toBaseIO) chunkSize #[] #[])
    match ← failure.get with
    | some (_, e) => throw e
    | none => return merge outs xs.size chunkSize

/-- Parallel `IO` traversal, fail-fast with the same deterministic
smallest-index error reporting as `mapIO`. -/
def forEach (xs : Array α) (f : α → IO Unit) (chunkSize : Nat := 1) :
    IO Unit :=
  discard <| mapIO xs f chunkSize

end Linen
