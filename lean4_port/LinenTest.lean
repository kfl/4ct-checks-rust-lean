import Linen

/-!
Contract tests for Linen's order-preserving parallel combinators.
-/

abbrev Counter := IO.Ref Nat

def expect (c : Counter) (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"ok   - {name}"
  else
    IO.eprintln s!"FAIL - {name}"
    c.modify (· + 1)

def combinatorTests (c : Counter) : IO Unit := do
  let inputs := Array.range 257
  expect c "map ordered"
    (Linen.map inputs (fun i => i * i + 3) == inputs.map (fun i => i * i + 3))
  expect c "filterMap ordered"
    (Linen.filterMap inputs (fun i => if i % 7 == 0 then some (i + 1) else none) ==
      inputs.filterMap (fun i => if i % 7 == 0 then some (i + 1) else none))
  expect c "flatMap ordered"
    (Linen.flatMap #[1, 2, 3, 4] (fun i => #[i, i + 10]) == #[1, 11, 2, 12, 3, 13, 4, 14])
  let nested := Linen.map #[1, 2, 3, 4] fun i =>
    (Linen.map (Array.range (i * 11)) (fun j => i + j)).foldl (· + ·) 0
  let nestedSeq := #[1, 2, 3, 4].map fun i =>
    ((Array.range (i * 11)).map (fun j => i + j)).foldl (· + ·) 0
  expect c "map nested" (nested == nestedSeq)
  let wide := Linen.map (Array.range 64) fun g =>
    (Linen.map (Array.range 128) (fun j => g * 131 + j)).foldl (· + ·) 0
  let wideSeq := (Array.range 64).map fun g =>
    ((Array.range 128).map (fun j => g * 131 + j)).foldl (· + ·) 0
  expect c "map nested wide" (wide == wideSeq)
  let monadic ← Linen.mapIO inputs fun i => pure (i * 3)
  expect c "mapIO ordered" (monadic == inputs.map (· * 3))
  expect c "map empty" (Linen.map (#[] : Array Nat) (· + 1) == #[])
  expect c "map singleton" (Linen.map #[7] (· * 2) == #[14])
  for chunk in [1, 3, 300] do
    expect c s!"map small c={chunk}"
      (Linen.map #[1, 2, 3] (· + 10) (chunkSize := chunk) == #[11, 12, 13])
  expect c "map serial (chunk beyond size)"
    (Linen.map inputs (· * 7) (chunkSize := 1000) == inputs.map (· * 7))
  expect c "tabulate ordered"
    (Linen.tabulate 257 (fun i => i.1 * i.1 + 3)
      == Array.ofFn (fun i : Fin 257 => i.1 * i.1 + 3))
  expect c "tabulate empty" (Linen.tabulate 0 (fun i => i.1) == #[])
  expect c "tabulate singleton" (Linen.tabulate 1 (fun i => i.1 + 9) == #[9])
  for chunk in [1, 3, 300] do
    expect c s!"tabulate small c={chunk}"
      (Linen.tabulate 3 (fun i => i.1 + 10) (chunkSize := chunk)
        == #[10, 11, 12])
  expect c "tabulateM empty" ((← Linen.tabulateM 0 (fun i => pure i.1)) == #[])
  expect c "tabulateIO empty" ((← Linen.tabulateIO 0 (fun i => pure i.1)) == #[])
  for chunk in [1, 3, 300] do
    let tabM ← Linen.tabulateM 257 (fun i => pure (i.1 * 3)) (chunkSize := chunk)
    expect c s!"tabulateM ordered c={chunk}"
      (tabM == Array.ofFn (fun i : Fin 257 => i.1 * 3))
    let tabIO ← Linen.tabulateIO 257 (fun i => pure (i.1 + 1)) (chunkSize := chunk)
    expect c s!"tabulateIO ordered c={chunk}"
      (tabIO == Array.ofFn (fun i : Fin 257 => i.1 + 1))

def reduceTests (c : Counter) : IO Unit := do
  let inputs := Array.range 257
  let seqSum := (inputs.map (fun i => i * i)).foldl (· + ·) 7
  let seqCat := (inputs.map (fun i => [i])).foldl (· ++ ·) []
  for chunk in [1, 3, 16, 1000] do
    expect c s!"mapReduce sum c={chunk}"
      (Linen.mapReduce inputs (fun i => i * i) (· + ·) 7 (chunkSize := chunk) == seqSum)
    expect c s!"mapReduce non-commutative c={chunk}"
      (Linen.mapReduce inputs (fun i => [i]) (· ++ ·) [] (chunkSize := chunk) == seqCat)
  let monadic ← Linen.mapReduceM inputs (fun i => pure (i * 3)) (· + ·) 0
  expect c "mapReduceM sum" (monadic == (inputs.map (· * 3)).foldl (· + ·) 0)
  expect c "mapReduce empty" (Linen.mapReduce #[] (fun i => [i]) (· ++ ·) [7] == [7])
  expect c "mapReduce singleton non-commutative"
    (Linen.mapReduce #[5] (fun i => [i]) (· ++ ·) [1] == [1, 5])

def errorTests (c : Counter) : IO Unit := do
  let captureFirstError : IO String := do
    try
      discard <| Linen.mapIO #[0, 1, 2, 3] fun i => do
        if i == 1 then throw (IO.userError "first-index-error")
        if i == 3 then throw (IO.userError "later-index-error")
      pure "no error"
    catch e =>
      pure (toString e)
  let firstError ← captureFirstError
  expect c "mapIO first error in index order"
    (firstError.contains "first-index-error" && !firstError.contains "later-index-error")
  let captureTabError (chunk : Nat) : IO String := do
    try
      discard <| Linen.tabulateIO 4 (fun i => do
        if i.1 == 1 then throw (IO.userError "first-index-error")
        if i.1 == 3 then throw (IO.userError "later-index-error")
        pure i.1) (chunkSize := chunk)
      pure "no error"
    catch e =>
      pure (toString e)
  for chunk in [1, 2, 8] do
    let tabError ← captureTabError chunk
    expect c s!"tabulateIO first error in index order c={chunk}"
      (tabError.contains "first-index-error"
        && !tabError.contains "later-index-error")

def budgetTests (c : Counter) : IO Unit := do
  expect c "worker budget drained" ((← Linen.activeSlots) == 0)
  let st ← Linen.budgetStats
  expect c "no release underflows" (st.underflows == 0)
  expect c "reservations balanced"
    (st.attempts - st.deniedBudget == st.releases)
  expect c "peak within budget" (st.peak ≤ Linen.config.workers)
  expect c "grown within spawned" (st.grownTasks ≤ st.spawnedTasks)

def main : IO UInt32 := do
  let c ← IO.mkRef 0
  combinatorTests c
  reduceTests c
  errorTests c
  budgetTests c
  let failures ← c.get
  if failures == 0 then
    IO.println "all Linen tests passed"
    return 0
  else
    IO.eprintln s!"{failures} Linen test(s) failed"
    return 1
