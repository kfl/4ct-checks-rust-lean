import Linen

/-!
Microbenchmark suite for Linen. It compares serial execution, one task per
element, static partitions, and Linen's bounded dynamic workers across cheap,
uneven, clustered, allocating, and refcount workloads. The suite covers pure
maps, `IO` maps, reductions, and all four serial/Linen choices for two nested
map levels.

Run with `lake exe linenBench [reps]`. `LINEN_WORKERS` overrides
`LEAN_NUM_THREADS`; unset it when using `LEAN_NUM_THREADS` to measure scaling.
Most cases sweep fixed `chunkSize` values plus `onewave`, which produces at
most one chunk per configured worker. Each configuration has one untimed
warmup followed by back-to-back samples in microseconds. The first argument is
the repetition count and defaults to three.
-/

/-! ## Timing harness

An opaque evaluation barrier plus a repeated timer.
Self-contained. Nothing in this section knows about Linen. -/

/-- Invoke a pure thunk through a no-inline `IO` boundary, hiding its body from
call-site optimization across the timestamps. `IO.lazyPure` is inline and does
not provide this boundary. -/
@[noinline]
private def blackBox (fn : Unit → α) : IO α :=
  pure (fn ())

/-- Warm one configuration once, time `reps` executions, then verify the
results and print the samples and checksum. Verification is outside the timed
windows. -/
private def timed (reps : Nat) (label : String)
    (run : IO (Array Nat)) : IO (Array Nat) := do
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

/-- Pure-map baseline with one `Task` per element. -/
private def eagerTaskMap (xs : Array α) (f : α → β) : Array β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map (·.get)

/-- `IO`-map baseline with one `IO.asTask` per element, joined in input order. -/
private def eagerTaskMapIO (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let tasks ← xs.mapM fun x => IO.asTask (f x)
  tasks.mapM fun t => IO.ofExcept t.get

/-- Deterministic, non-inlined CPU work with tunable iteration count. -/
@[noinline]
private def mix : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc => mix fuel ((acc * 1664525 + 1013904223) % 4294967291)

/-- Medium-cost elements with regularly spaced expensive outliers. Large
contiguous partitions receive nearly equal outlier counts, largely controlling
for static partition imbalance. -/
@[noinline]
private def unevenWork (i : Nat) : Nat :=
  mix (if i % 97 == 0 then 4000 else 200) (i + 1)

/-- Cheap elements followed by an expensive final sixteenth. Contiguous static
partitions assign that suffix to few workers, while small dynamic claims can
distribute it. -/
@[noinline]
private def clusteredWork (size i : Nat) : Nat :=
  mix (if i ≥ size - size / 16 then 4000 else 200) (i + 1)

/-- Static-partition control: task `w` receives segment `w` directly, without
a claim cursor. -/
private def staticTaskMap (workers : Nat) (xs : Array α)
    (f : α → Nat) : Array Nat :=
  let chunk := (xs.size + workers - 1) / workers
  let tasks := (Array.range workers).map fun w =>
    Task.spawn fun _ => Id.run do
      let mut out := Array.mkEmpty chunk
      for i in [w * chunk : ((w + 1) * chunk).min xs.size] do
        if let some x := xs[i]? then
          out := out.push (f x)
      return out
  (tasks.map (·.get)).flatten

/-- Build 50,000 small arrays at runtime. Separate inner objects generate
refcount traffic without contention on one shared refcount.

This must remain a function called through `blackBox`: extracted constants are
marked persistent at initialization, which would eliminate the refcount
traffic intended by the mutable/persistent comparison. -/
private def mkBoxedInputs (_ : Unit) : Array (Array Nat) :=
  (Array.range 50000).map fun i => Array.range (i % 64)

private unsafe def persistImpl (a : α) : BaseIO α :=
  Runtime.markPersistent a

/-- Mark an object graph persistent, making reference-count operations no-ops.
The specification is the identity; marking is only a runtime effect. -/
@[implemented_by persistImpl]
private def persist (a : α) : BaseIO α := pure a

/-! ## Benchmark cases -/

/-- Fixed claim sizes used by the benchmark cases. -/
private def chunkSweep : List Nat := [1, 4, 16, 64]

/-- Fixed claim sizes plus `onewave`, which creates at most one chunk per
configured worker. `onewave` still uses dynamic claiming; `staticTaskMap` is
the fixed-assignment control. -/
private def sweeps (size : Nat) : List (String × Nat) :=
  chunkSweep.map (fun c => (s!"c={c}", c)) ++
    [("onewave", (size + Linen.config.workers - 1) / Linen.config.workers)]

/-- Compare serial, eager, static, and Linen pure maps. -/
private def benchCase (reps : Nat) (label : String) (xs : Array α)
    (f : α → Nat) : IO Unit := do
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

/-- Compare serial, eager, and Linen map-then-flatten. With an allocating
mapper, allocation occurs during the mapped phase; every implementation
flattens the boxed results serially. -/
private def benchCaseFlat (reps : Nat) (label : String) (xs : Array Nat)
    (f : Nat → Array Nat) : IO Unit := do
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

/-- Run pure work through the `IO` entry point, measuring its scheduling and
error-representation overhead rather than real I/O or failures. -/
private def benchCaseIO (reps : Nat) (label : String) (xs : Array Nat)
    (f : Nat → Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, mapIO serial" (xs.mapM (fun i => pure (f i)))
  let eager ← timed reps s!"{label}, mapIO eager" (eagerTaskMapIO xs (fun i => pure (f i)))
  unless serial == eager do
    throw (IO.userError s!"{label}: mapIO implementations disagree")
  for (tag, chunk) in sweeps xs.size do
    let linen ← timed reps s!"{label}, mapIO Linen {tag}"
      (Linen.mapIO xs (fun i => pure (f i)) (chunkSize := chunk))
    unless serial == linen do
      throw (IO.userError s!"{label}: mapIO implementations disagree")

/-- Compare serial, eager, and Linen map-plus-fold with Linen's fused
`mapReduce`, using the same claim sizes for the two Linen paths. -/
private def benchCaseReduce (reps : Nat) (label : String) (xs : Array Nat)
    (f : Nat → Nat) : IO Unit := do
  -- Reductions produce one value; a singleton array reuses the timing plumbing.
  let serial ← timed reps s!"{label}, reduce serial map+fold"
    (blackBox fun _ => #[(xs.map f).foldl (· + ·) 0])
  let eager ← timed reps s!"{label}, reduce eager+fold"
    (blackBox fun _ => #[(eagerTaskMap xs f).foldl (· + ·) 0])
  unless serial == eager do
    throw (IO.userError s!"{label}: reduce implementations disagree")
  -- Holding chunk size constant avoids confounding this comparison with claim
  -- granularity.
  for (tag, chunk) in sweeps xs.size do
    let materialised ← timed reps s!"{label}, reduce Linen map+fold {tag}"
      (blackBox fun _ => #[(Linen.map xs f (chunkSize := chunk)).foldl (· + ·) 0])
    let fused ← timed reps s!"{label}, reduce Linen fused {tag}"
      (blackBox fun _ => #[Linen.mapReduce xs f (· + ·) 0 (chunkSize := chunk)])
    unless serial == materialised && serial == fused do
      throw (IO.userError s!"{label}: reduce implementations disagree")

/-- Inputs whose additions operate on roughly 64,000-bit `Nat` values, making
addition expensive in chunk folds and, when used, the parallel partial
combine. -/
private def bigNums : Array Nat :=
  (Array.range 5000).map fun i => 2 ^ 64000 + i

/-- Compare fused reduction with an identity mapper against a serial fold.
Cheap inputs expose reduction overhead; `bigNums` makes `op` dominate. -/
private def benchCaseReduceId (reps : Nat) (label : String)
    (xs : Array Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, reduce serial fold"
    (blackBox fun _ => #[xs.foldl (· + ·) 0])
  for (tag, chunk) in sweeps xs.size do
    let fused ← timed reps s!"{label}, reduce id fused {tag}"
      (blackBox fun _ => #[Linen.mapReduce xs id (· + ·) 0 (chunkSize := chunk)])
    unless serial == fused do
      throw (IO.userError s!"{label}: reduce implementations disagree")

/-- Compare all four serial/Linen choices for two nested map levels. Each group
maps uneven work over its elements and then folds the results. When both levels
use Linen, every active outer worker can start an inner worker team, exposing
nested task-pool overhead. Both Linen levels use the default chunk size. -/
private def benchCaseNested (reps : Nat) (label : String)
    (groups inner : Nat) : IO Unit := do
  let gs := Array.range groups
  let innerXs := Array.range inner
  let serialGroup := fun g =>
    (innerXs.map (fun i => unevenWork (g * inner + i))).foldl (· + ·) 0
  let linenGroup := fun g =>
    (Linen.map innerXs (fun i => unevenWork (g * inner + i))).foldl (· + ·) 0
  let serial ← timed reps s!"{label}, outer serial / inner serial"
    (blackBox fun _ => gs.map serialGroup)
  let seqPar ← timed reps s!"{label}, outer serial / inner Linen"
    (blackBox fun _ => gs.map linenGroup)
  let parSeq ← timed reps s!"{label}, outer Linen / inner serial"
    (blackBox fun _ => Linen.map gs serialGroup)
  let parPar ← timed reps s!"{label}, outer Linen / inner Linen"
    (blackBox fun _ => Linen.map gs linenGroup)
  unless serial == seqPar && serial == parSeq && serial == parPar do
    throw (IO.userError s!"{label}: nested compositions disagree")

/-- Smoke-check the core eager, map, mapIO, and mapReduce paths before timing.
`timed` handles per-configuration warmup. -/
private def sanityChecks : IO Unit := do
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
  benchCaseNested reps "nested-wide" 300 300
  benchCaseNested reps "nested-narrow" 8 11250
  benchCaseFlat reps "alloc" (Array.range 100000) (fun i => Array.range (i % 7))
  benchCaseIO reps "scheduler" (Array.range 200000) (· + 1)
  benchCaseIO reps "uneven" (Array.range 50000) unevenWork
  benchCaseReduce reps "scheduler" (Array.range 200000) (· + 1)
  benchCaseReduce reps "uneven" (Array.range 50000) unevenWork
  benchCaseReduceId reps "sum" (Array.range 1000000)
  benchCaseReduceId reps "bigsum" bigNums
  -- The refcount comparisons run last because `persist` retains its object
  -- graphs for the rest of the process, increasing memory use in later cases.
  -- Uncontended: equivalent mutable and persistent inputs.
  -- Element reads from the persistent inputs skip the atomic refcount update
  -- (the refcount call itself remains), so the comparison estimates the
  -- effect of skipping the atomic updates.
  let boxedInputs ← blackBox mkBoxedInputs
  benchCase reps "boxed" boxedInputs (·.foldl (· + ·) 0)
  let persistentInputs ← persist (← blackBox mkBoxedInputs)
  benchCase reps "boxed-persistent" persistentInputs (·.foldl (· + ·) 0)
  -- Contended: every element is the same shared object. On the mutable input,
  -- all workers update one refcount cache line.
  let hot ← blackBox fun _ => Array.range 64
  benchCase reps "shared" (Array.replicate 50000 hot) (·.foldl (· + ·) 0)
  let hotPersistent ← persist (← blackBox fun _ => Array.range 64)
  benchCase reps "shared-persistent" (Array.replicate 50000 hotPersistent) (·.foldl (· + ·) 0)
  return 0
