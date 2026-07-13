import NearLinear4ct.Cartwheel

/-!
Verification drivers (Appendix A.10).

The Lemma A.4/A.5/A.6 checks: `runCheckDeg8`, `runCheck7triangle`, `runCheckDeg7`
and their helpers.

The checks are parallel at two nested levels: `parForEach` over the checked
cartwheels, and inside each, `combineEachCartwheel`'s candidate sweep as an
order-preserving `parFlatMap` (see Cartwheel.lean). The inner level makes
every cartwheel's work thousands of tasks wide, so the scheduler absorbs
per-cartwheel cost skew at any thread count; the outer level spreads task
creation itself across workers (a serial outer loop measurably bottlenecks
on spawning). Workers blocking on inner tasks are replaced by the Lean task
pool, so the nesting does not starve. A failing proof obligation throws in
its worker; `parForEach` re-raises it, so the process exits non-zero.

The asserts here ARE the proof → `proofAssert` (always-on, aborts), never
`panic!` (which Lean would swallow). This includes the `assert(false)`
"impossible" branches: a malformed input must abort, not be silently accepted.
-/

namespace NearLinear4ct

/-- The configuration of three mutually adjacent degree-7 vertices. -/
def get7triangle : Configuration :=
  let t7 := PseudoConfiguration.fromVRotations 3
    #[#[1, 2, -1], #[2, 0, -1], #[0, 1, -1]] #[dgExact7, dgExact7, dgExact7]
  Configuration.new 0 3 t7.darts t7.degrees
where dgExact7 : Degree := Degree.exact 7

/-- Drop cartwheels with a vertex of fixed degree `k`; collapse `[k-1, 9]` ranges
to fixed `k-1` (A.10.1).

The observable result is "remove iff some vertex is fixed `k`, else collapse
every `[k-1,9]`", expressed here directly. -/
def deleteDegreeFromKTo9 (cartwheels : Array CartWheel) (k : Nat) : Array CartWheel :=
  cartwheels.filterMap fun cw =>
    if cw.degrees.any (fun d => d.lower == k && d.upper == k) then
      none                                    -- a vertex of fixed degree k → remove
    else
      let degrees := cw.degrees.map fun d =>
        if d.lower == k - 1 && d.upper == CARTWHEEL_DEG_MAX then ⟨d.lower, k - 1⟩ else d
      some { cw with degrees := degrees }

/-- Drop cartwheels that contain a 7-triangle. -/
def delete7triangle (cartwheels : Array CartWheel) : Array CartWheel :=
  let confs := #[get7triangle]
  cartwheels.filter fun cw =>
    !cw.toPseudoConfiguration.blockedByReducibleConfiguration 0 confs

/-- The fixed obstruction configuration `X` (A.10.8). -/
def getX : PseudoConfiguration :=
  PseudoConfiguration.fromVRotations 17
    #[#[1, 2, 3, 4, 5, 6, 7, 8], #[0, 8, 11, 12, 2], #[0, 1, 12, -1, 3], #[0, 2, -1, 13, 4],
      #[0, 3, 13, 14, 5], #[0, 4, 14, 15, 16, -1, 6], #[0, 5, -1, 7], #[0, 6, -1, 8],
      #[0, 7, -1, 9, 10, 11, 1], #[8, -1, 10], #[8, 9, -1, 11], #[1, 8, 10, -1, 12],
      #[1, 11, -1, 2], #[3, -1, 14, 4], #[4, 13, -1, 15, 5], #[5, 14, -1, 16], #[5, 15, -1]]
    #[Degree.exact 8, Degree.exact 5, Degree.exact 5, Degree.exact 5, Degree.exact 5,
      Degree.exact 7, Degree.exact 5, Degree.exact 5, Degree.exact 7, Degree.exact 5,
      Degree.exact 5, Degree.exact 8, Degree.exact 5, Degree.exact 5, Degree.exact 8,
      Degree.exact 5, Degree.exact 5]

/-- Whether `X` embeds into `z` rooted at vertex `v`, over the 8 rotations of the
root dart. -/
def containX (z : PseudoConfiguration) (v : Nat) : Bool := Id.run do
  let x := getX
  let dartZ := (z.anyDart v).get!
  let mut dartX := (x.anyDart 0).get!
  for _ in [0:8] do
    if PseudoConfiguration.homomorphismExists x dartX z dartZ Degree.includes then
      return true
    dartX := (x.darts[dartX]!).succ.idx!
  return false

-- --- Lemma A.4: a vertex of degree 8 -----------------------------------------

/-- Degree-8 centre with a degree-8 spoke: no combination may survive. -/
def check88 (cartwheel : CartWheel) (darts8 : Array Nat) (cartwheels : Array CartWheel)
    (confs : Array Configuration) : IO Unit := do
  for dart in darts8 do
    let rev := (cartwheel.darts[dart]!).rev
    let combined := cartwheel.toPseudoConfiguration.combineEachCartwheel rev cartwheels confs
    proofAssert combined.isEmpty "check88: a combination survived"

/-- Degree-8 centre with a single degree-7 spoke: no combination may survive. -/
def check87 (cartwheel : CartWheel) (darts7 : Array Nat) (cartwheels : Array CartWheel)
    (confs : Array Configuration) : IO Unit := do
  let rev := (cartwheel.darts[darts7[0]!]!).rev
  let combined := cartwheel.toPseudoConfiguration.combineEachCartwheel rev cartwheels confs
  proofAssert combined.isEmpty "check87: a combination survived"

/-- Degree-8 centre with multiple degree-7 spokes: every combination must contain `X`. -/
def check787 (cartwheel : CartWheel) (darts7 : Array Nat) (cartwheels : Array CartWheel)
    (confs : Array Configuration) : IO Unit := do
  let n := darts7.size
  let mut dist : Array Nat := Array.replicate n 0
  for i in [0:n] do
    let mut dart1 := darts7[i]!
    let dart2 := if i == n - 1 then darts7[0]! else darts7[i+1]!
    let mut d := 0
    while dart1 != dart2 do
      dart1 := (cartwheel.darts[dart1]!).succ.idx!
      d := d + 1
    dist := dist.set! i d
  let minDist := dist.foldl Nat.min dist[0]!
  for i in [0:n] do
    if dist[i]! > minDist then continue
    let dart1 := darts7[i]!
    let dart2 := if i == n - 1 then darts7[0]! else darts7[i+1]!
    let rev1 := (cartwheel.darts[dart1]!).rev
    let rev2 := (cartwheel.darts[dart2]!).rev
    let combinedSet :=
      cartwheel.toPseudoConfiguration.combineEachCartwheelTwice rev1 rev2 cartwheels confs
    for (combined, mappingsCw) in combinedSet do
      let center := (mappingsCw.vmap[cartwheel.center]!).idx!
      proofAssert (containX combined center) "check787: combination must contain X"

/-- The round-robin slice `{xs[k] | k ≡ i (mod n)}` a `--shard i/n` worker owns
(`none` keeps everything). Only the list of cartwheels *checked* shrinks; each
check still combines against the full candidate set, so the union of the `n`
shards performs exactly the unsharded check. -/
def shardSlice (shard : Option (Nat × Nat)) (xs : Array α) : Array α :=
  match shard with
  | .none => xs
  | .some (i, n) => (Array.range xs.size).filterMap fun k =>
      if k % n == i then xs[k]? else none

/-- Lemma A.4 check: a vertex of degree 8. -/
def checkDeg8 (allCartwheels : Array CartWheel) (confs : Array Configuration)
    (shard : Option (Nat × Nat) := none) : IO Unit := do
  let cartwheels := deleteDegreeFromKTo9 allCartwheels 9
  IO.println s!"After removing cartwheels with degree 9, {cartwheels.size} cartwheels remain."
  parForEach (shardSlice shard cartwheels) fun cartwheel => do
    if cartwheel.degrees[cartwheel.center]! != Degree.exact 8 then return
    let centerDarts := cartwheel.centerDartsByDegree
    if !(centerDarts[8]!).isEmpty then
      check88 cartwheel centerDarts[8]! cartwheels confs
    else if (centerDarts[7]!).size == 1 then
      check87 cartwheel centerDarts[7]! cartwheels confs
    else if (centerDarts[7]!).size > 1 then
      check787 cartwheel centerDarts[7]! cartwheels confs
    else
      proofAssert false "checkDeg8: degree-8 centre with no degree-7/8 spokes"
  IO.println "Finished checking degree 8 vertices."

def runCheckDeg8 (cartwheeldir confdir : System.FilePath)
    (shard : Option (Nat × Nat) := none) : IO Unit := do
  let cartwheels ← getCartwheels cartwheeldir
  let confs ← Configuration.getConfs confdir
  checkDeg8 cartwheels confs shard

-- --- Lemma A.5: a 7-triangle -------------------------------------------------

/-- Lemma A.5 check: a 7-triangle. -/
def check7triangle (allCartwheels : Array CartWheel) (confs : Array Configuration)
    (shard : Option (Nat × Nat) := none) : IO Unit := do
  let cartwheels := deleteDegreeFromKTo9 (deleteDegreeFromKTo9 allCartwheels 9) 8
  IO.println s!"After removing cartwheels with degree 8 and 9, {cartwheels.size} remain."
  parForEach (shardSlice shard cartwheels) fun cartwheel => do
    for e in cartwheel.centerDarts do
      let f := (cartwheel.darts[e]!).succ.idx!
      let revE := (cartwheel.darts[e]!).rev
      let revF := (cartwheel.darts[f]!).rev
      let vE := (cartwheel.darts[revE]!).head
      let vF := (cartwheel.darts[revF]!).head
      proofAssert (cartwheel.degrees[vE]!).fixed "check_7triangle: v_e degree not fixed"
      proofAssert (cartwheel.degrees[vF]!).fixed "check_7triangle: v_f degree not fixed"
      if (cartwheel.degrees[vE]!).lower == 7 && (cartwheel.degrees[vF]!).lower == 7 then
        let combined :=
          cartwheel.toPseudoConfiguration.combineEachCartwheelTwice revE revF cartwheels confs
        proofAssert combined.isEmpty "check_7triangle: a combination survived"
  IO.println "Finished checking 7-triangles."

def runCheck7triangle (cartwheeldir confdir : System.FilePath)
    (shard : Option (Nat × Nat) := none) : IO Unit := do
  let cartwheels ← getCartwheels cartwheeldir
  let confs ← Configuration.getConfs confdir
  check7triangle cartwheels confs shard

-- --- Lemma A.6: a vertex of degree 7 -----------------------------------------

/-- Degree-7 centre with a single degree-7 spoke: no combination may survive. -/
def check77 (cartwheel : CartWheel) (darts7 : Array Nat) (cartwheels : Array CartWheel)
    (confs : Array Configuration) : IO Unit := do
  let rev := (cartwheel.darts[darts7[0]!]!).rev
  let combined := cartwheel.toPseudoConfiguration.combineEachCartwheel rev cartwheels confs
  proofAssert combined.isEmpty "check77: a combination survived"

/-- Degree-7 centre with multiple degree-7 spokes: no combination may survive. -/
def check777 (cartwheel : CartWheel) (darts7 : Array Nat) (cartwheels : Array CartWheel)
    (confs : Array Configuration) : IO Unit := do
  for i in [0:darts7.size] do
    let rev1 := (cartwheel.darts[darts7[i]!]!).rev
    for j in [0:i] do
      let rev2 := (cartwheel.darts[darts7[j]!]!).rev
      let combined :=
        cartwheel.toPseudoConfiguration.combineEachCartwheelTwice rev1 rev2 cartwheels confs
      proofAssert combined.isEmpty "check777: a combination survived"

/-- Lemma A.6 check: a vertex of degree 7. -/
def checkDeg7 (allCartwheels : Array CartWheel) (confs0 : Array Configuration)
    (shard : Option (Nat × Nat) := none) : IO Unit := do
  let cartwheels := delete7triangle (deleteDegreeFromKTo9 (deleteDegreeFromKTo9 allCartwheels 9) 8)
  IO.println s!"After removing degree 8/9 and 7-triangle cartwheels, {cartwheels.size} remain."
  let confs := confs0.push get7triangle
  parForEach (shardSlice shard cartwheels) fun cartwheel => do
    let centerDarts := cartwheel.centerDartsByDegree
    if (centerDarts[7]!).size == 1 then
      check77 cartwheel centerDarts[7]! cartwheels confs
    else if (centerDarts[7]!).size > 1 then
      check777 cartwheel centerDarts[7]! cartwheels confs
    else
      proofAssert false "checkDeg7: degree-7 centre with no degree-7 spokes"
  IO.println "Finished checking degree 7 vertices."

def runCheckDeg7 (cartwheeldir confdir : System.FilePath)
    (shard : Option (Nat × Nat) := none) : IO Unit := do
  let cartwheels ← getCartwheels cartwheeldir
  let confs ← Configuration.getConfs confdir
  checkDeg7 cartwheels confs shard

end NearLinear4ct
