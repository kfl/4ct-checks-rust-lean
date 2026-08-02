import Linen

/-!
Microbenchmark suite for Linen. It compares serial execution, one task per
element, static partitions, and Linen's bounded dynamic workers across cheap,
uneven, clustered, allocating, and refcount workloads. The suite covers pure
maps, `IO` maps, reductions, and nested workloads with stable widths, a
draining outer tail, repeated short regions, allocating fan-out, and three
parallel levels.

Run with `lake exe linenBench [reps] [filters]`, where `filters` is a
comma-separated list of case-name substrings selecting a subset of the suite
(for the focused growth-policy A/B). `LINEN_WORKERS` overrides
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

/-- Time a Linen configuration and report the worker-budget traffic caused
by its warmup and measured repetitions; the printed label carries the
execution count so readers can normalise to per-execution means. Counter
reads stay outside the timed windows. -/
private def timedWithBudget (reps : Nat) (label : String)
    (run : IO (Array Nat)) : IO (Array Nat) := do
  let before ← Linen.budgetStats
  let result ← timed reps label run
  let after ← Linen.budgetStats
  let attempts := after.attempts - before.attempts
  let deniedBudget := after.deniedBudget - before.deniedBudget
  IO.println s!"{label}, budget delta over {reps + 1} executions: \
    spawned={after.spawnedTasks - before.spawnedTasks} \
    grown={after.grownTasks - before.grownTasks} \
    granted={attempts - deniedBudget} \
    releases={after.releases - before.releases} \
    deniedBudget={deniedBudget} \
    deniedRegion={after.deniedRegion - before.deniedRegion} \
    underflows={after.underflows - before.underflows}"
  return result

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

/-- Compare `Array.ofFn`, indexed `Linen.map`, and `Linen.tabulate` on the
same index function: the serial specification, the map instantiation of
the engine reading an index array, and direct tabulation with no input
array. -/
private def benchCaseTabulate (reps : Nat) (label : String) (n : Nat)
    (f : Nat → Nat) : IO Unit := do
  let idx := Array.range n
  let serial ← timed reps s!"{label}, tabulate ofFn serial"
    (blackBox fun _ => Array.ofFn (fun i : Fin n => f i.1))
  for (tag, chunk) in sweeps n do
    let viaMap ← timed reps s!"{label}, via prebuilt range map {tag}"
      (blackBox fun _ => Linen.map idx f (chunkSize := chunk))
    let linen ← timed reps s!"{label}, tabulate Linen {tag}"
      (blackBox fun _ => Linen.tabulate n (fun i => f i.1) (chunkSize := chunk))
    unless serial == viaMap && serial == linen do
      throw (IO.userError s!"{label}: tabulate implementations disagree")

/-- Direct fallible tabulation on a cheap index function, against `mapIO`
over a prebuilt range. The factory boundary builds `tabulateIO`'s
immediate callback per worker, so a gap between these controls isolates
how `mapIO`'s composed reading callback is constructed and specialised
rather than any shared machinery. -/
private def benchCaseTabulateIO (reps : Nat) (label : String) (n : Nat)
    (f : Nat → Nat) : IO Unit := do
  let idx := Array.range n
  let serial ← timed reps s!"{label}, mapIO serial over range"
    (idx.mapM (fun i => pure (f i)))
  for (tag, chunk) in sweeps n do
    let viaMap ← timed reps s!"{label}, via prebuilt range mapIO {tag}"
      (Linen.mapIO idx (fun i => pure (f i)) (chunkSize := chunk))
    let linen ← timed reps s!"{label}, tabulateIO Linen {tag}"
      (Linen.tabulateIO n (fun i => pure (f i.1)) (chunkSize := chunk))
    unless serial == viaMap && serial == linen do
      throw (IO.userError s!"{label}: tabulateIO implementations disagree")

/-- Nested tabulation: an outer tabulation whose entries each fold an inner
tabulation, with no input arrays at either level. -/
private def benchCaseTabulateNested (reps : Nat) (groups inner : Nat) :
    IO Unit := do
  let serialAll ← timed reps "tabulate-nested, all serial"
    (blackBox fun _ => Array.ofFn fun g : Fin groups =>
      (Array.ofFn fun i : Fin inner =>
        unevenWork (g.1 * inner + i.1)).foldl (· + ·) 0)
  let outerLinen ← timed reps "tabulate-nested, outer Linen"
    (blackBox fun _ => Linen.tabulate groups fun g =>
      (Array.ofFn fun i : Fin inner =>
        unevenWork (g.1 * inner + i.1)).foldl (· + ·) 0)
  let bothLinen ← timed reps "tabulate-nested, outer + inner Linen"
    (blackBox fun _ => Linen.tabulate groups fun g =>
      (Linen.tabulate inner fun i =>
        unevenWork (g.1 * inner + i.1)).foldl (· + ·) 0)
  unless serialAll == outerLinen && serialAll == bothLinen do
    throw (IO.userError "tabulate-nested: implementations disagree")

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

/-- Compare all four serial/Linen choices for two nested map levels. Every
composition containing Linen also reports its worker-budget traffic. -/
private def benchNestedGroups (reps : Nat) (label : String) (gs : Array Nat)
    (serialGroup linenGroup : Nat → Nat) : IO Unit := do
  let serial ← timed reps s!"{label}, outer serial / inner serial"
    (blackBox fun _ => gs.map serialGroup)
  let seqPar ← timedWithBudget reps s!"{label}, outer serial / inner Linen"
    (blackBox fun _ => gs.map linenGroup)
  let parSeq ← timedWithBudget reps s!"{label}, outer Linen / inner serial"
    (blackBox fun _ => Linen.map gs serialGroup)
  let parPar ← timedWithBudget reps s!"{label}, outer Linen / inner Linen"
    (blackBox fun _ => Linen.map gs linenGroup)
  unless serial == seqPar && serial == parSeq && serial == parPar do
    throw (IO.userError s!"{label}: nested compositions disagree")

/-- Equal-sized groups with regularly distributed expensive elements. Wide
and narrow outer levels expose the two steady-state composition choices. -/
private def benchCaseNested (reps : Nat) (label : String)
    (groups inner : Nat) : IO Unit := do
  let gs := Array.range groups
  let innerXs := Array.range inner
  let serialGroup := fun g =>
    (innerXs.map (fun i => unevenWork (g * inner + i))).foldl (· + ·) 0
  let linenGroup := fun g =>
    (Linen.map innerXs (fun i => unevenWork (g * inner + i))).foldl (· + ·) 0
  benchNestedGroups reps label gs serialGroup linenGroup

/-- A wide outer map that drains to one long-lived, internally parallel group.
The heavy group contains many medium claims rather than one indivisible
element, allowing it to absorb slots released by retiring outer workers. -/
private def benchCaseNestedDrainingTail (reps : Nat) : IO Unit := do
  let groups := 512
  let inner := 128
  let gs := Array.range groups
  let innerXs := Array.range inner
  let work := fun g i =>
    mix (if g == 0 then 50000 else 200) (g * inner + i + 1)
  let serialGroup := fun g =>
    (innerXs.map (work g)).foldl (· + ·) 0
  let linenGroup := fun g =>
    (Linen.map innerXs (work g)).foldl (· + ·) 0
  benchNestedGroups reps "nested-draining-tail" gs serialGroup linenGroup

/-- Each outer item opens several successive short inner regions. Total work
is comparable to the other nested cases, but repeated setup and joins expose
the fixed cost of nested regions under a saturated outer level. -/
private def benchCaseNestedRepeated (reps : Nat) : IO Unit := do
  let groups := 256
  let rounds := 8
  let inner := 32
  let gs := Array.range groups
  let innerXs := Array.range inner
  let serialGroup := fun g => Id.run do
    let mut total := 0
    for r in [0:rounds] do
      for i in [0:inner] do
        total := total + mix 200 (g * rounds * inner + r * inner + i + 1)
    return total
  let linenGroup := fun g => Id.run do
    let mut total := 0
    for r in [0:rounds] do
      let base := g * rounds * inner + r * inner
      total := total +
        (Linen.map innerXs (fun i => mix 200 (base + i + 1))).foldl (· + ·) 0
    return total
  benchNestedGroups reps "nested-repeated" gs serialGroup linenGroup

/-- Deterministic variable fan-out with small allocations. Empty, singleton,
and wider results exercise nested `flatMap` buffering and ordered flattening
without depending on an application data format. -/
@[noinline]
private def fanoutWork (seed : Nat) : Array Nat :=
  let value := mix (if seed % 97 == 0 then 800 else 200) (seed + 1)
  let width := if seed % 11 == 0 then 0 else if seed % 29 == 0 then 8 else seed % 4 + 1
  (Array.range width).map (value + ·)

private def benchCaseNestedFanout (reps : Nat) : IO Unit := do
  let groups := 300
  let inner := 256
  let gs := Array.range groups
  let innerXs := Array.range inner
  let serialGroup := fun g =>
    ((innerXs.map fun i => fanoutWork (g * inner + i)).flatten).foldl (· + ·) 0
  let linenGroup := fun g =>
    (Linen.flatMap innerXs (fun i => fanoutWork (g * inner + i))).foldl (· + ·) 0
  benchNestedGroups reps "nested-fanout" gs serialGroup linenGroup

/-- Three nested map levels with only 64 outer groups. On wide machines the
middle level can use otherwise idle capacity; the all-Linen row also exposes
the known conservatism of parents retaining slots across nested joins. -/
private def benchCaseNestedDepth3 (reps : Nat) : IO Unit := do
  let outerXs := Array.range 64
  let middleXs := Array.range 16
  let innerXs := Array.range 64
  let leafSerial := fun g m =>
    (innerXs.map fun i => mix 200 (g * 1024 + m * 64 + i + 1)).foldl (· + ·) 0
  let leafLinen := fun g m =>
    (Linen.map innerXs fun i => mix 200 (g * 1024 + m * 64 + i + 1)).foldl (· + ·) 0
  let groupSerial := fun g => (middleXs.map (leafSerial g)).foldl (· + ·) 0
  let groupMiddle := fun g => (Linen.map middleXs (leafSerial g)).foldl (· + ·) 0
  let groupAll := fun g => (Linen.map middleXs (leafLinen g)).foldl (· + ·) 0
  let serial ← timed reps "nested-depth3, all serial"
    (blackBox fun _ => outerXs.map groupSerial)
  let outer ← timedWithBudget reps "nested-depth3, outer Linen"
    (blackBox fun _ => Linen.map outerXs groupSerial)
  let outerMiddle ← timedWithBudget reps "nested-depth3, outer + middle Linen"
    (blackBox fun _ => Linen.map outerXs groupMiddle)
  let all ← timedWithBudget reps "nested-depth3, all levels Linen"
    (blackBox fun _ => Linen.map outerXs groupAll)
  unless serial == outer && serial == outerMiddle && serial == all do
    throw (IO.userError "nested-depth3: compositions disagree")

/-- Contention-free team ramp: a serial outer loop opens one inner region at
a time, so no other region competes for the budget. Crossing claim count
with per-claim cost separates how large the team ramp grows from whether it
pays. Total element count is held approximately constant within each cost
tier (Nat division truncates the group count for claim counts that do not
divide it), so rows in a tier do near-identical work in differently shaped
regions. The claim counts bracket typical worker counts, so the rows where
claims approximate the team cap -- where the remaining-work gate is most
active during formation -- are observable directly. -/
private def benchCaseTeamRamp (reps : Nat) : IO Unit := do
  let total := 16384
  for (claims, fuel, tag) in
      [(32, 200, "cheap"), (96, 200, "cheap"), (128, 200, "cheap"),
       (160, 200, "cheap"), (256, 200, "cheap"), (512, 200, "cheap"),
       (32, 4000, "medium"), (96, 4000, "medium"), (128, 4000, "medium"),
       (160, 4000, "medium"), (256, 4000, "medium"), (512, 4000, "medium")] do
    let gs := Array.range (total / claims)
    let innerXs := Array.range claims
    let f := fun (g i : Nat) => mix fuel (g * claims + i + 1)
    let serial ← timed reps s!"team-ramp {claims}x{tag}, serial"
      (blackBox fun _ => gs.map fun g => (innerXs.map (f g)).foldl (· + ·) 0)
    let linen ← timedWithBudget reps s!"team-ramp {claims}x{tag}, inner Linen"
      (blackBox fun _ => gs.map fun g => (Linen.map innerXs (f g)).foldl (· + ·) 0)
    unless serial == linen do
      throw (IO.userError s!"team-ramp {claims}x{tag}: implementations disagree")

/-- Draining tail matched on both axes: the light groups perform the same
total work as many cheap claims or as few expensive claims, and the heavy
first group performs approximately the same total work as 128 or 512 claims.
Crossing the two separates competition for released slots (light-claim
attempt frequency) from ramp runway (the heavy region's remaining
opportunities to grow). -/
private def benchCaseDrainingMatched (reps : Nat) : IO Unit := do
  let groups := 512
  for (heavyClaims, heavyFuel) in [(128, 50000), (512, 12500)] do
   let innerHeavy := Array.range heavyClaims
   let heavy := fun (i : Nat) => mix heavyFuel (i + 1)
   for (lightClaims, lightFuel, ltag) in [(128, 200, "fine"), (8, 3200, "coarse")] do
    let tag := s!"{ltag}-h{heavyClaims}"
    let gs := Array.range groups
    let innerLight := Array.range lightClaims
    let light := fun (g i : Nat) => mix lightFuel (g * lightClaims + i + 1)
    let serialGroup := fun g =>
      if g == 0 then (innerHeavy.map heavy).foldl (· + ·) 0
      else (innerLight.map (light g)).foldl (· + ·) 0
    let linenGroup := fun g =>
      if g == 0 then (Linen.map innerHeavy heavy).foldl (· + ·) 0
      else (Linen.map innerLight (light g)).foldl (· + ·) 0
    let serial ← timed reps s!"draining-matched {tag}, serial"
      (blackBox fun _ => gs.map serialGroup)
    let parSeq ← timed reps s!"draining-matched {tag}, outer Linen / inner serial"
      (blackBox fun _ => Linen.map gs serialGroup)
    let parPar ← timedWithBudget reps s!"draining-matched {tag}, outer Linen / inner Linen"
      (blackBox fun _ => Linen.map gs linenGroup)
    unless serial == parSeq && serial == parPar do
      throw (IO.userError s!"draining-matched {tag}: implementations disagree")

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
  let filters := (args[1]?.map (·.splitOn ",")).getD []
  let want (name : String) : Bool :=
    filters.isEmpty || filters.any fun f => (name.splitOn f).length > 1
  let os ← Std.Async.System.getSystemInfo
  IO.println s!"host: {os.name} {os.release} {os.machine}"
  IO.println s!"env: LINEN_WORKERS={(← IO.getEnv "LINEN_WORKERS").getD "-"} \
    LEAN_NUM_THREADS={(← IO.getEnv "LEAN_NUM_THREADS").getD "-"}"
  IO.println s!"Linen config: {repr Linen.config}, reps: {reps}\
    {if filters.isEmpty then "" else s!", filter: {filters}"}"
  sanityChecks
  -- The refcount comparisons run last because `persist` retains its object
  -- graphs for the rest of the process, increasing memory use in later cases.
  -- Uncontended cases use equivalent mutable and persistent inputs; element
  -- reads from persistent inputs skip the atomic refcount update (the
  -- refcount call itself remains), estimating the cost of atomic updates.
  -- Contended cases replicate one shared object so all workers update one
  -- refcount cache line.
  let benches : List (String × IO Unit) := [
    ("scheduler-map", benchCase reps "scheduler" (Array.range 200000) (· + 1)),
    ("tabulate-cheap", benchCaseTabulate reps "tabulate-cheap" 200000 (· * 2 + 1)),
    ("tabulate-uneven", benchCaseTabulate reps "tabulate-uneven" 50000 unevenWork),
    ("tabulate-nested", benchCaseTabulateNested reps 300 300),
    ("tabulate-io-cheap",
      benchCaseTabulateIO reps "tabulate-io-cheap" 200000 (· * 2 + 1)),
    ("uneven-map", benchCase reps "uneven" (Array.range 50000) unevenWork),
    ("clustered-map", benchCase reps "clustered" (Array.range 50000) (clusteredWork 50000)),
    ("nested-wide", benchCaseNested reps "nested-wide" 300 300),
    ("nested-narrow", benchCaseNested reps "nested-narrow" 8 11250),
    ("nested-draining-tail", benchCaseNestedDrainingTail reps),
    ("nested-repeated", benchCaseNestedRepeated reps),
    ("nested-fanout", benchCaseNestedFanout reps),
    ("nested-depth3", benchCaseNestedDepth3 reps),
    ("team-ramp", benchCaseTeamRamp reps),
    ("draining-matched", benchCaseDrainingMatched reps),
    ("alloc-flat", benchCaseFlat reps "alloc" (Array.range 100000) (fun i => Array.range (i % 7))),
    ("scheduler-io", benchCaseIO reps "scheduler" (Array.range 200000) (· + 1)),
    ("uneven-io", benchCaseIO reps "uneven" (Array.range 50000) unevenWork),
    ("scheduler-reduce", benchCaseReduce reps "scheduler" (Array.range 200000) (· + 1)),
    ("uneven-reduce", benchCaseReduce reps "uneven" (Array.range 50000) unevenWork),
    ("sum-reduce", benchCaseReduceId reps "sum" (Array.range 1000000)),
    ("bigsum-reduce", benchCaseReduceId reps "bigsum" bigNums),
    ("boxed-rc", do
      let boxedInputs ← blackBox mkBoxedInputs
      benchCase reps "boxed" boxedInputs (·.foldl (· + ·) 0)),
    ("boxed-persistent-rc", do
      let persistentInputs ← persist (← blackBox mkBoxedInputs)
      benchCase reps "boxed-persistent" persistentInputs (·.foldl (· + ·) 0)),
    ("shared-rc", do
      let hot ← blackBox fun _ => Array.range 64
      benchCase reps "shared" (Array.replicate 50000 hot) (·.foldl (· + ·) 0)),
    ("shared-persistent-rc", do
      let hotPersistent ← persist (← blackBox fun _ => Array.range 64)
      benchCase reps "shared-persistent" (Array.replicate 50000 hotPersistent) (·.foldl (· + ·) 0))]
  for (name, bench) in benches do
    if want name then bench
  let st ← Linen.budgetStats
  IO.println s!"budget: peak={st.peak} spawnedTasks={st.spawnedTasks} \
    grownTasks={st.grownTasks} granted={st.attempts - st.deniedBudget} \
    releases={st.releases} underflows={st.underflows}"
  return 0
