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
  let monadic ← Linen.mapIO inputs fun i => pure (i * 3)
  expect c "mapIO ordered" (monadic == inputs.map (· * 3))

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

def main : IO UInt32 := do
  let c ← IO.mkRef 0
  combinatorTests c
  errorTests c
  let failures ← c.get
  if failures == 0 then
    IO.println "all Linen tests passed"
    return 0
  else
    IO.eprintln s!"{failures} Linen test(s) failed"
    return 1
