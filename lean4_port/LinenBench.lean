import Linen

/-!
Microbenchmark for Linen. It compares serial execution, an eager
one-`Task`-per-element strategy, and true static partitioning with the
bounded worker implementation on scheduler-bound, compute-uneven (evenly
spaced and clustered outliers), refcount-heavy, and allocation-heavy
workloads, over the pure, `IO`, and reducing entry points.

Run with `lake exe linenBench [reps]`; use `LEAN_NUM_THREADS` to probe
scaling. Claim granularities are swept in-process via the `chunkSize`
argument: the fixed sizes plus `onewave`, a chunk size producing one wave of
approximately `workers` chunks. Every configuration is executed once untimed
before its samples, and
each configuration reports its back-to-back timings in microseconds -- the
repetition count is the executable's first argument, defaulting to three.
-/

/-! ## Timing harness

An opaque evaluation barrier plus a repeated timer, self-contained. Nothing
in this section knows about Linen. -/

/-- Evaluate a pure thunk inside `IO`, opaque to the compiler, so the work can
be neither hoisted out of the timing loop, sunk past a timestamp, nor shared
between repetitions. (`IO.lazyPure` is not enough: it carries no `noinline`,
so the compiler sees straight through it. This plays the role of criterion's
`black_box`.) -/
@[noinline]
def blackBox (fn : Unit → α) : IO α :=
  pure (fn ())

/-- Time `reps` back-to-back executions, after one untimed execution that
warms this exact configuration. All repetition results are kept, checked
equal to each other after the timing loop, and consumed (checksum, caller
equality checks) outside the timed windows. -/
def timed (reps : Nat) (label : String) (run : IO (Array Nat)) : IO (Array Nat) := do
  let _ ← run
  let mut times : Array Nat := #[]
  let mut results : Array (Array Nat) := #[]
  for _ in [0:reps] do
    let start ← IO.monoNanosNow
    let result ← run
    let elapsed ← IO.monoNanosNow
    times := times.push ((elapsed - start) / 1000)
    results := results.push result
  let some first := results[0]?
    | throw (IO.userError s!"{label}: no repetitions")
  for result in results do
    unless result == first do
      throw (IO.userError s!"{label}: repetitions disagree")
  let checksum := first.foldl (· ^^^ ·) 0 % (2 ^ 64)
  IO.println s!"{label}: {times} us (checksum {checksum})"
  return first

/-! ## Baselines and workloads -/

/-- The eager strategy for pure maps: one `Task` per element. It pays no
`Except` boxing, unlike `eagerTaskMapIO`, so it is the cheaper of the two
baselines. -/
def eagerTaskMap (xs : Array α) (f : α → β) : Array β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map (·.get)

/-- The eager strategy for `IO` maps: one `IO.asTask` per element, joined in
index order. -/
def eagerTaskMapIO (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let tasks ← xs.mapM fun x => IO.asTask (f x)
  tasks.mapM fun t => IO.ofExcept t.get

@[noinline]
def mix : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc => mix fuel ((acc * 1664525 + 1013904223) % 4294967291)

/-- Mostly medium elements with regularly spaced expensive outliers. The even
spacing means large contiguous partitions receive near-equal outlier counts,
so this distribution challenges per-element scheduling overhead, not
partition balance. -/
@[noinline]
def unevenWork (i : Nat) : Nat :=
  mix (if i % 97 == 0 then 4000 else 200) (i + 1)

/-- Uniformly cheap elements with every expensive element clustered in the
final sixteenth, so contiguous static partitions leave the expensive suffix
on only a small subset of workers while small dynamic claims spread it. -/
@[noinline]
def clusteredWork (size i : Nat) : Nat :=
  mix (if i ≥ size - size / 16 then 4000 else 200) (i + 1)

/-- True static partitioning: segment `w` is assigned to task `w` directly,
with no claim cursor -- the no-dynamic-scheduling control. -/
def staticTaskMap (workers : Nat) (xs : Array α) (f : α → Nat) : Array Nat :=
  let chunk := (xs.size + workers - 1) / workers
  let tasks := (Array.range workers).map fun w =>
    Task.spawn fun _ => Id.run do
      let mut out := Array.mkEmpty chunk
      for i in [w * chunk : ((w + 1) * chunk).min xs.size] do
        if let some x := xs[i]? then
          out := out.push (f x)
      return out
  (tasks.map (·.get)).flatten

/-- Builds the boxed workload's input: 50000 distinct small arrays, so every
element read is a refcount operation on its own object -- refcount traffic
without cross-worker contention on any single refcount word.

A function rather than a constant on purpose: module-level constants and
extracted closed terms are marked persistent at initialisation, which makes
refcount operations on them no-ops and would silently null the refcount side
of the persistent/mutable comparison. Call it through `blackBox` so the
allocation genuinely happens at runtime. -/
def mkBoxedInputs (_ : Unit) : Array (Array Nat) :=
  (Array.range 50000).map fun i => Array.range (i % 64)

private unsafe def persistImpl (a : α) : BaseIO α :=
  Runtime.markPersistent a

/-- Mark an object graph persistent: reference-count operations on it become
no-ops (the objects are never freed). The specification is the identity;
marking is purely a runtime effect. -/
@[implemented_by persistImpl]
def persist (a : α) : BaseIO α := pure a

/-! ## Benchmark cases -/

def chunkSweep : List Nat := [1, 4, 16, 64]

/-- The swept claim granularities: the fixed sizes plus a `onewave` split of
one contiguous chunk per configured worker. The chunks of the `onewave` split
are still handed out by the shared dynamic cursor -- a fast worker may claim
two -- so it minimises claim traffic without fixing the assignment; the fixed
assignment control is `staticTaskMap`. -/
def sweeps (size : Nat) : List (String × Nat) :=
  chunkSweep.map (fun c => (s!"c={c}", c)) ++
    [("onewave", (size + Linen.config.workers - 1) / Linen.config.workers)]

def benchCase (reps : Nat) (label : String) (xs : Array α) (f : α → Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, map serial" (blackBox fun _ => xs.map f)
  let eager ← timed reps s!"{label}, map eager" (blackBox fun _ => eagerTaskMap xs f)
  let static ← timed reps s!"{label}, map static"
    (blackBox fun _ => staticTaskMap Linen.config.workers xs f)
  unless serial == eager && serial == static do
    throw (IO.userError s!"{label}: map implementations disagree")
  for (tag, chunk) in sweeps xs.size do
    let linen ← timed reps s!"{label}, map Linen {tag}"
      (blackBox fun _ => Linen.map xs f (chunkSize := chunk))
    unless serial == linen do
      throw (IO.userError s!"{label}: map implementations disagree")

/-- Every element allocates a fresh small array, and the combinator's final
`flatten` is a serial pass over the boxed results -- allocation pressure on
the parallel side, allocator/copy work on the serial side. -/
def benchCaseFlat (reps : Nat) (label : String) (xs : Array Nat) (f : Nat → Array Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, flatMap serial"
    (blackBox fun _ => (xs.map f).flatten)
  let eager ← timed reps s!"{label}, flatMap eager"
    (blackBox fun _ => (eagerTaskMap xs f).flatten)
  unless serial == eager do
    throw (IO.userError s!"{label}: flatMap implementations disagree")
  for (tag, chunk) in sweeps xs.size do
    let linen ← timed reps s!"{label}, flatMap Linen {tag}"
      (blackBox fun _ => Linen.flatMap xs f (chunkSize := chunk))
    unless serial == linen do
      throw (IO.userError s!"{label}: flatMap implementations disagree")

/-- Pure actions through the `IO` entry point: this stresses `mapIO`'s
scheduling and error-representation overhead, not real I/O or failure
handling. -/
def benchCaseIO (reps : Nat) (label : String) (xs : Array Nat) (f : Nat → Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, mapIO serial" (xs.mapM (fun i => pure (f i)))
  let eager ← timed reps s!"{label}, mapIO eager" (eagerTaskMapIO xs (fun i => pure (f i)))
  unless serial == eager do
    throw (IO.userError s!"{label}: mapIO implementations disagree")
  for (tag, chunk) in sweeps xs.size do
    let linen ← timed reps s!"{label}, mapIO Linen {tag}"
      (Linen.mapIO xs (fun i => pure (f i)) (chunkSize := chunk))
    unless serial == linen do
      throw (IO.userError s!"{label}: mapIO implementations disagree")

def benchCaseReduce (reps : Nat) (label : String) (xs : Array Nat) (f : Nat → Nat) : IO Unit := do
  -- Reductions produce one value; a singleton array reuses the timing plumbing.
  let serial ← timed reps s!"{label}, reduce serial map+fold"
    (blackBox fun _ => #[(xs.map f).foldl (· + ·) 0])
  let eager ← timed reps s!"{label}, reduce eager+fold"
    (blackBox fun _ => #[(eagerTaskMap xs f).foldl (· + ·) 0])
  unless serial == eager do
    throw (IO.userError s!"{label}: reduce implementations disagree")
  -- Materialised map-plus-fold and fused reduction run at the same chunk
  -- size, so their difference isolates fusion rather than mixing in
  -- granularity effects.
  for (tag, chunk) in sweeps xs.size do
    let materialised ← timed reps s!"{label}, reduce Linen map+fold {tag}"
      (blackBox fun _ => #[(Linen.map xs f (chunkSize := chunk)).foldl (· + ·) 0])
    let fused ← timed reps s!"{label}, reduce Linen fused {tag}"
      (blackBox fun _ => #[Linen.mapReduce xs f (· + ·) 0 (chunkSize := chunk)])
    unless serial == materialised && serial == fused do
      throw (IO.userError s!"{label}: reduce implementations disagree")

/-- Big numbers make `(· + ·)` an expensive combining operation (one
multi-kilobyte limb addition per application), so reducing them with an `id`
mapper stresses the engine's parallelisation of the `op` work itself -- both
in the chunk folds and in the partial combine's bounded parallel level. -/
def bigNums : Array Nat :=
  (Array.range 5000).map fun i => 2 ^ 64000 + i

/-- Pure reduction (`id` mapper) against a serial fold. With cheap elements
this stresses the reduction machinery itself -- per-chunk folds, the ordered
partial merge, and the memory-bandwidth ceiling of scanning the input. With
expensive elements (`bigNums`) it probes how much of the combining work the
engine parallelises at each chunk size. -/
def benchCaseReduceId (reps : Nat) (label : String) (xs : Array Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, reduce serial fold"
    (blackBox fun _ => #[xs.foldl (· + ·) 0])
  for (tag, chunk) in sweeps xs.size do
    let fused ← timed reps s!"{label}, reduce id fused {tag}"
      (blackBox fun _ => #[Linen.mapReduce xs id (· + ·) 0 (chunkSize := chunk)])
    unless serial == fused do
      throw (IO.userError s!"{label}: reduce implementations disagree")

/-- Check every engine end-to-end before any timing; per-configuration
warming is handled by `timed`. -/
def sanityChecks : IO Unit := do
  let xs := Array.range 4096
  let expected := xs.map (· + 1)
  unless eagerTaskMap xs (· + 1) == expected do
    throw (IO.userError "sanity: eager map")
  unless Linen.map xs (· + 1) == expected do
    throw (IO.userError "sanity: Linen.map")
  unless (← eagerTaskMapIO xs (fun i => pure (i + 1))) == expected do
    throw (IO.userError "sanity: eager mapIO")
  unless (← Linen.mapIO xs (fun i => pure (i + 1))) == expected do
    throw (IO.userError "sanity: Linen.mapIO")
  unless Linen.mapReduce xs (· + 1) (· + ·) 0 == expected.foldl (· + ·) 0 do
    throw (IO.userError "sanity: Linen.mapReduce")

def main (args : List String) : IO UInt32 := do
  let reps := ((args.head?.bind (·.toNat?)).getD 3).max 1
  let os ← Std.Async.System.getSystemInfo
  IO.println s!"host: {os.name} {os.release} {os.machine}"
  IO.println s!"env: LINEN_WORKERS={(← IO.getEnv "LINEN_WORKERS").getD "-"} \
    LEAN_NUM_THREADS={(← IO.getEnv "LEAN_NUM_THREADS").getD "-"}"
  IO.println s!"Linen config: {repr Linen.config}, reps: {reps}"
  sanityChecks
  benchCase reps "scheduler" (Array.range 200000) (· + 1)
  benchCase reps "uneven" (Array.range 50000) unevenWork
  benchCase reps "clustered" (Array.range 50000) (clusteredWork 50000)
  benchCaseFlat reps "alloc" (Array.range 100000) (fun i => Array.range (i % 7))
  benchCaseIO reps "scheduler" (Array.range 200000) (· + 1)
  benchCaseIO reps "uneven" (Array.range 50000) unevenWork
  benchCaseReduce reps "scheduler" (Array.range 200000) (· + 1)
  benchCaseReduce reps "uneven" (Array.range 50000) unevenWork
  benchCaseReduceId reps "sum" (Array.range 1000000)
  benchCaseReduceId reps "bigsum" bigNums
  -- The refcount A/B runs last: `persist` retains its object graphs for the
  -- rest of the process, so running it earlier would let the retained memory
  -- shadow unrelated cases.
  -- Uncontended: the same workload on a mutable and a persistent copy.
  -- Element reads on the persistent copy skip the atomic refcount update
  -- (the refcount call itself remains), so the comparison estimates the
  -- effect of skipping the atomic updates.
  let boxedInputs ← blackBox mkBoxedInputs
  benchCase reps "boxed" boxedInputs (·.foldl (· + ·) 0)
  let persistentInputs ← persist (← blackBox mkBoxedInputs)
  benchCase reps "boxed-persistent" persistentInputs (·.foldl (· + ·) 0)
  -- Contended: every element is the same shared object, so all workers hit a
  -- single refcount word -- the cache-line ping-pong case.
  let hot ← blackBox fun _ => Array.range 64
  benchCase reps "shared" (Array.replicate 50000 hot) (·.foldl (· + ·) 0)
  let hotPersistent ← persist (← blackBox fun _ => Array.range 64)
  benchCase reps "shared-persistent" (Array.replicate 50000 hotPersistent) (·.foldl (· + ·) 0)
  return 0
