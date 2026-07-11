import NearLinear4ct.Rule

/-!
Phase 5 — the enumeration engine. Port of `../src/cartwheel.{hpp,cpp}`
(Appendix A.9).

`CartWheel extends PseudoConfiguration` and adds `center` + `centerDarts` (the
darts of the centre vertex, in rotation order). Covers wheel/cartwheel
enumeration, in/out-rule fixing, charge-bound pruning, refinement, and
`enumBadCartwheels`.

This file also hosts the remaining **charge methods** on `PseudoConfiguration`
(`alwaysApply`/`neverApply`/`amountOf*`/`dominantlyApply`) and the
**cartwheel-combination** methods (`combineEachCartwheel*`) — in C++ these are
`PseudoConfiguration` members that consume `Rule`/`CartWheel`; Lean has no forward
declarations, so they live here (after those types exist), exactly as the Rust
port placed them.

R5: the enumeration relies on `assert`s as invariants — but in `enumBadCartwheels`
those are genuine **proof obligations** (the final charge must be 0, etc.), so
they go through `proofAssert` (L1: must abort). The enumeration-internal sanity
`assert`s (`A ≥ 0`, `U_R` non-empty, degree in `[5,9]`) are structural invariants
of correct input; they use `panic!` (loud, and unreachable on wellformed data).
-/

namespace NearLinear4ct

-- --- P5: charge methods on PseudoConfiguration (consume Rule) -----------------
namespace PseudoConfiguration

/-- Whether `rule` always applies at `dartId` — its degrees include this
configuration's (C++ `always_apply`, A.9.1). -/
def alwaysApply (pc : PseudoConfiguration) (dartId : Nat) (rule : Rule) : Bool :=
  homomorphismExists rule.toPseudoConfiguration rule.stId pc dartId Degree.includes

/-- Whether `rule` can never apply at `dartId` — no degree-overlapping
homomorphism exists (C++ `never_apply`, A.9.2). -/
def neverApply (pc : PseudoConfiguration) (dartId : Nat) (rule : Rule) : Bool :=
  !homomorphismExists rule.toPseudoConfiguration rule.stId pc dartId Degree.hasIntersection

/-- Total charge guaranteed to be sent along `dartId` (C++ `amount_of_charge_send`,
A.9.3). -/
def amountOfChargeSend (pc : PseudoConfiguration) (dartId : Nat) (rules : Array Rule) : Int :=
  Id.run do
  let mut amount : Int := 0
  for rule in rules do
    if pc.alwaysApply dartId rule then amount := amount + rule.amount
  return amount

/-- Maximum charge that could possibly be sent along `dartId` over the applicable
combined rules (C++ `amount_of_possible_charge_send`, A.9.4). -/
def amountOfPossibleChargeSend (pc : PseudoConfiguration) (dartId : Nat)
    (combinedRules : Array CombinedRule) : Int := Id.run do
  let mut amount : Int := 0
  for cr in combinedRules do
    if pc.neverApply dartId cr.toRule then continue
    amount := max amount cr.amount
  return amount

/-- Whether `rule` dominantly applies at `dartId` (C++ `dominantly_apply`,
A.9.15). -/
def dominantlyApply (pc : PseudoConfiguration) (dartId : Nat) (rule : Rule) : Bool :=
  let gDominant := fun (degR degC : Degree) =>
    Degree.hasIntersection degR degC && (degR.upper == INFTY || decide (degC.upper < CARTWHEEL_DEG_MAX))
  homomorphismExists rule.toPseudoConfiguration rule.stId pc dartId gDominant

end PseudoConfiguration

/-- A cartwheel: a pseudo-configuration with a distinguished centre vertex and its
darts in rotation order (C++ `CartWheel`). -/
structure CartWheel extends PseudoConfiguration where
  center : Nat
  centerDarts : Array Nat
deriving DecidableEq, Repr, Inhabited, BEq

/-- The centre's darts in rotation order (the centre is interior, so the rotation
is closed and has no boundary `none`). -/
private def centerDartsOf (pc : PseudoConfiguration) (center : Nat) : Array Nat :=
  (pc.getERotations[center]!).map (·.get!)

private def cwParseInt (tok : String) : Int :=
  match tok.toInt? with
  | some v => v
  | none => panic! s!"expected integer token, got {tok}"

private def cwLineToks (line : String) : Array String :=
  ((line.split Char.isWhitespace).filterMap (fun s =>
    if s.isEmpty then none else some s.toString)).toArray

namespace CartWheel

/-- C++ `CartWheel(center, center_darts, N, darts, degrees)`. -/
def new (center : Nat) (centerDarts : Array Nat) (n : Nat) (darts : Array Dart)
    (degrees : Array Degree) : CartWheel :=
  { toPseudoConfiguration := PseudoConfiguration.new n darts degrees
    center := center, centerDarts := centerDarts }

/-- Serialise to the `.cartwheel` text format (C++ `to_file`/`write`). The layout
(incl. the trailing space per vertex line) matches the C++. -/
def write (cw : CartWheel) : String := Id.run do
  let darts := cw.darts
  let mut res := s!"\n{cw.n} {cw.center + 1}\n"
  let eRotations := cw.getERotations
  for v in [0:cw.n] do
    let upper := if (cw.degrees[v]!).upper == INFTY then 0 else (cw.degrees[v]!).upper
    res := res ++ s!"{v + 1} {(cw.degrees[v]!).lower} {upper} "
    for dartId in eRotations[v]! do
      match dartId with
      | none => res := res ++ "-1 "
      | some e => res := res ++ s!"{(darts[(darts[e]!).rev]!).head + 1} "
    res := res ++ "\n"
  return res

def toFile (cw : CartWheel) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path cw.write

/-- Build the canonical cartwheel for a centre of degree `d` with the given
neighbour degrees, expanding second-neighbours (C++ `generate_cartwheel`,
A.9 generation). The C++ `assert(A >= 0)` is a structural invariant → `panic!`. -/
def generateCartwheel (d : Nat) (degrees : Array Int) : CartWheel := Id.run do
  let mut rotations : Array (Array Int) := Array.replicate (d + 1) #[]
  -- centre's rotation: 1..d
  rotations := rotations.set! 0 ((Array.range d).map (fun i => Int.ofNat i + 1))
  for i in [1:d+1] do
    let iNext := if i < d then i + 1 else 1
    let iPrev := if i > 1 then i - 1 else d
    rotations := rotations.set! i #[(iNext : Int), 0, (iPrev : Int)]
  let mut k := d + 1                          -- next vertex id to assign
  for i in [1:d+1] do
    if degrees[i-1]! == CARTWHEEL_DEG_MAX then continue
    let a := degrees[i-1]! - (rotations[i]!).size          -- # second neighbours
    if a < 0 then panic! "generate_cartwheel: negative second-neighbour count"
    for _ in [0:a.toNat] do
      let iLast := (rotations[i]!).back!
      rotations := rotations.push #[(i : Int), iLast]       -- rotations[k]
      rotations := rotations.set! i ((rotations[i]!).push (k : Int))
      rotations := rotations.set! iLast.toNat (#[(k : Int)] ++ rotations[iLast.toNat]!)
      k := k + 1
    let iFirst := (rotations[i]!)[0]!
    let iLast := (rotations[i]!).back!
    rotations := rotations.set! iFirst.toNat ((rotations[iFirst.toNat]!).push iLast)
    rotations := rotations.set! iLast.toNat (#[iFirst] ++ rotations[iLast.toNat]!)
  for i in [1:k] do
    if i > d || degrees[i-1]! == CARTWHEEL_DEG_MAX then
      rotations := rotations.set! i ((rotations[i]!).push (-1))
  let mut allDegrees : Array Degree := Array.replicate k ⟨CARTWHEEL_DEG_MIN, CARTWHEEL_DEG_MAX⟩
  allDegrees := allDegrees.set! 0 (Degree.exact d)
  for i in [1:d+1] do
    allDegrees := allDegrees.set! i (Degree.exact degrees[i-1]!.toNat)
  let pc := PseudoConfiguration.fromVRotations k rotations allDegrees
  return { toPseudoConfiguration := pc, center := 0, centerDarts := centerDartsOf pc 0 }

/-- Parse one cartwheel from text (C++ `from_file`). Tolerates the leading blank
line that `write` emits. -/
def ofString (content : String) : CartWheel := Id.run do
  let lines := (content.splitOn "\n").toArray
  let mut idx := 0
  while (lines[idx]!).trimAscii.toString.isEmpty do idx := idx + 1
  let header := cwLineToks lines[idx]!
  idx := idx + 1
  let n := (cwParseInt header[0]!).toNat
  let center := (cwParseInt header[1]!).toNat - 1
  let mut degrees : Array Degree := Array.replicate n ⟨1, INFTY⟩
  let mut rotationVertices : Array (Array Int) := Array.replicate n #[]
  for u in [0:n] do
    let toks := cwLineToks lines[idx]!
    idx := idx + 1
    let lower := (cwParseInt toks[1]!).toNat
    let upperRaw := (cwParseInt toks[2]!).toNat
    let upper := if upperRaw == 0 then INFTY else upperRaw
    degrees := degrees.set! u ⟨lower, upper⟩
    let mut rotU : Array Int := #[]
    for j in [3:toks.size] do
      let v := cwParseInt toks[j]!
      rotU := rotU.push (if v != -1 then v - 1 else v)
    rotationVertices := rotationVertices.set! u rotU
  let pc := PseudoConfiguration.fromVRotations n rotationVertices degrees
  return { toPseudoConfiguration := pc, center := center, centerDarts := centerDartsOf pc center }

end CartWheel

instance : FromFile CartWheel where
  fromFile path := do return CartWheel.ofString (← IO.FS.readFile path)

/-- Load every `.cartwheel` file in `cartwheeldir` (C++ `get_cartwheels`). -/
def getCartwheels (cartwheeldir : System.FilePath) : IO (Array CartWheel) := do
  let cws ← getObjects CartWheel cartwheeldir ".cartwheel"
  IO.println s!"Total {cws.size} cartwheels loaded."
  return cws

/-- Recursive helper for `enumWheelTuples`: assign neighbour `i`'s degree from
index `iLowest` upward, collecting the lex-min neighbour-degree tuples (C++ nested
`enum_degree` lambda, with wheel *generation* split out so it can be parallelised).
`partial` (L5). -/
private partial def enumWheelDegrees (centerDegree : Nat) (degrees : Array Int) (i iLowest : Nat)
    (acc : Array (Array Int)) : Array (Array Int) := Id.run do
  if i == centerDegree then
    if lexMin degrees then return acc.push degrees
    return acc
  let mut acc := acc
  for j in [iLowest:CARTWHEEL_DEGREES_SIZE] do
    acc := enumWheelDegrees centerDegree (degrees.set! i CARTWHEEL_DEGREES[j]!) (i + 1) iLowest acc
  return acc

namespace CartWheel

/-- The lex-min neighbour-degree tuples for a centre of degree `centerDegree`, in
enumeration order (C++ `enum_wheels`' inner traversal). -/
def enumWheelTuples (centerDegree : Nat) : Array (Array Int) := Id.run do
  let mut tuples : Array (Array Int) := #[]
  let degrees : Array Int := Array.replicate centerDegree 0
  for j in [0:CARTWHEEL_DEGREES_SIZE] do
    tuples := enumWheelDegrees centerDegree (degrees.set! 0 CARTWHEEL_DEGREES[j]!) 1 j tuples
  return tuples

/-- Enumerate all wheels with the given centre degree, up to rotation (`lexMin`)
(C++ `enum_wheels`). -/
def enumWheels (centerDegree : Nat) : Array CartWheel :=
  (enumWheelTuples centerDegree).map (generateCartwheel centerDegree)

/-- Enumerate all ways to make every non-tail range degree concrete
(C++ `concrete_degree_except_tail`, A.9.10). -/
def concreteDegreeExceptTail (cw : CartWheel) : Array CartWheel := Id.run do
  let mut cartwheels : Array CartWheel := #[cw]
  for v in [0:cw.n] do
    -- already fixed, or a tail degree range [d, 9]
    if (cw.degrees[v]!).fixed || (cw.degrees[v]!).upper == CARTWHEEL_DEG_MAX then continue
    let mut newCartwheels : Array CartWheel := #[]
    for di in [0:CARTWHEEL_DEGREES_SIZE - 1] do
      let dval := CARTWHEEL_DEGREES[di]!
      if Degree.includes (cw.degrees[v]!) (Degree.exact dval) then
        for cartwheel in cartwheels do
          newCartwheels := newCartwheels.push
            { cartwheel with degrees := cartwheel.degrees.set! v (Degree.exact dval) }
    cartwheels := newCartwheels
  return cartwheels

/-- Intersect degrees with a rule applied at `dartId`, then concretise
(C++ `update_degree_by_rule`, A.9.9). -/
def updateDegreeByRule (cw : CartWheel) (dartId : Nat) (rule : Rule) : Array CartWheel :=
  match PseudoConfiguration.homomorphism rule.toPseudoConfiguration rule.stId
      cw.toPseudoConfiguration dartId Degree.hasIntersection with
  | none => #[]
  | some rule2cw => Id.run do
    let mut updated := cw
    for vRule in [0:rule.n] do
      let vCw := (rule2cw.vmap[vRule]!).idx!
      let newDeg := Degree.intersection (updated.degrees[vCw]!) (rule.degrees[vRule]!)
      updated := { updated with degrees := updated.degrees.set! vCw newDeg }
    return updated.concreteDegreeExceptTail

/-- Prune if a fixed spoke rule applies that the combination doesn't record
(C++ `prune_by_non_associated_rule`, A.9.12). The C++ `assert` is a real
invariant; it is implied by the same predicate the loop tests, so we keep it as a
`panic!` guard. -/
def pruneByNonAssociatedRule (cw : CartWheel) (combinedRuleWithSpokes : Array CombinedRule)
    (rules : Array Rule) : Bool := Id.run do
  for j in [0:combinedRuleWithSpokes.size] do
    for k in [0:rules.size] do
      let applies := cw.toPseudoConfiguration.alwaysApply (cw.centerDarts[j]!) rules[k]!
      if (combinedRuleWithSpokes[j]!).combinedFlag[k]! && !applies then
        panic! "prune_by_non_associated_rule invariant violated"
      if !(combinedRuleWithSpokes[j]!).combinedFlag[k]! && applies then
        return true
  return false

/-- Upper bound on the final charge at the centre (C++ `upper_bound_of_charge`,
A.9.13). -/
def upperBoundOfCharge (cw : CartWheel) (combinedRuleWithSpokes : Array CombinedRule)
    (rules : Array Rule) (combinedRules : Array CombinedRule) : Int := Id.run do
  let degreeCenter := (cw.degrees[cw.center]!).lower
  let mut inChargeSum : Int := 0
  for cr in combinedRuleWithSpokes do
    inChargeSum := inChargeSum + cr.amount
  for j in [combinedRuleWithSpokes.size:degreeCenter] do
    inChargeSum := inChargeSum +
      cw.toPseudoConfiguration.amountOfPossibleChargeSend (cw.centerDarts[j]!) combinedRules
  let mut outChargeSum : Int := 0
  for i in [0:degreeCenter] do
    let fromCenter := (cw.darts[cw.centerDarts[i]!]!).rev
    outChargeSum := outChargeSum + cw.toPseudoConfiguration.amountOfChargeSend fromCenter rules
  let initialCharge : Int := 10 * (6 - (degreeCenter : Int))
  return initialCharge - outChargeSum + inChargeSum

/-- Whether this cartwheel can be discarded (C++ `prune`, A.9.11). -/
def prune (cw : CartWheel) (combinedRuleWithSpokes : Array CombinedRule) (rules : Array Rule)
    (combinedRules : Array CombinedRule) (confs : Array Configuration) : Bool :=
  cw.pruneByNonAssociatedRule combinedRuleWithSpokes rules
  || decide (cw.upperBoundOfCharge combinedRuleWithSpokes rules combinedRules < 0)
  || cw.toPseudoConfiguration.blockedByReducibleConfiguration cw.center confs

/-- Enumerate wheels of the given centre degree that survive the initial pruning
(C++ `enum_possible_bad_wheels`, A.9.20-adjacent).

The per-wheel `prune` is pure and read-only over the shared `rules`/`combinedRules`
/`confs`, so the filter is embarrassingly parallel (R4). It is run with `parMap`
(order-preserving), giving a wall-clock speedup on many cores while producing the
**identical** surviving-wheel list (and hence identical `d{c}_{i}` output files) —
note the C++ runs this step serially. -/
def enumPossibleBadWheels (centerDegree : Nat) (rules : Array Rule)
    (combinedRules : Array CombinedRule) (confs : Array Configuration) : Array CartWheel :=
  -- Fuse generation + pruning into one parallel pass over the degree-tuples, so the
  -- wheel construction is parallelised alongside the prune. Order-preserving
  -- ⇒ identical survivor list / output files.
  parFilterMap (enumWheelTuples centerDegree) fun degs =>
    let wheel := generateCartwheel centerDegree degs
    if wheel.prune #[] rules combinedRules confs then none else some wheel

/-- Fix the rules sent from neighbours to the centre, one spoke at a time, pruning
in between (C++ `fix_in_rules`, A.9.8). -/
def fixInRules (cw : CartWheel) (rules : Array Rule) (combinedRules : Array CombinedRule)
    (confs : Array Configuration) : Array (CartWheel × Array CombinedRule) := Id.run do
  let degreeCenter := (cw.degrees[cw.center]!).lower
  let mut cartwheels : Array (CartWheel × Array CombinedRule) := #[(cw, #[])]
  for i in [0:degreeCenter] do
    let mut newCartwheels : Array (CartWheel × Array CombinedRule) := #[]
    for (cartwheel, combinedRuleWithSpokes) in cartwheels do
      for combinedRule in combinedRules do
        let updatedCartwheels := cartwheel.updateDegreeByRule (cartwheel.centerDarts[i]!) combinedRule.toRule
        for updatedCartwheel in updatedCartwheels do
          let updatedSpokes := combinedRuleWithSpokes.push combinedRule
          if updatedCartwheel.prune updatedSpokes rules combinedRules confs then continue
          newCartwheels := newCartwheels.push (updatedCartwheel, updatedSpokes)
    cartwheels := newCartwheels
  return cartwheels

/-- Whether spoke `i` should be refined for `rule` (C++ `should_refine`, A.9.16). -/
def shouldRefine (cw : CartWheel) (i : Nat) (rule : Rule) : Bool :=
  let fromCenter := (cw.darts[cw.centerDarts[i]!]!).rev
  !cw.toPseudoConfiguration.alwaysApply fromCenter rule
    && cw.toPseudoConfiguration.dominantlyApply fromCenter rule

/-- The refinement where every `U_R` vertex takes the rule's lower bound
(C++ `refine_always`, A.9.18). -/
def refineAlways (cw : CartWheel) (uR : Array Nat) (rule2cw : Mappings) (rule : Rule) : CartWheel :=
    Id.run do
  let mut cAlways := cw
  for vRule in uR do
    let vCw := (rule2cw.vmap[vRule]!).idx!
    let newDeg : Degree := ⟨(rule.degrees[vRule]!).lower, (cAlways.degrees[vCw]!).upper⟩
    cAlways := { cAlways with degrees := cAlways.degrees.set! vCw newDeg }
  return cAlways

/-- The refinements where each `U_R` vertex in turn stays below the rule's lower
bound (C++ `refine_never`, A.9.19). -/
def refineNever (cw : CartWheel) (uR : Array Nat) (rule2cw : Mappings) (rule : Rule) :
    Array CartWheel := Id.run do
  let mut cNever : Array CartWheel := #[]
  for vRule in uR do
    let vCw := (rule2cw.vmap[vRule]!).idx!
    let newDeg : Degree := ⟨(cw.degrees[vCw]!).lower, (rule.degrees[vRule]!).lower - 1⟩
    let base : CartWheel := { cw with degrees := cw.degrees.set! vCw newDeg }
    cNever := cNever ++ base.concreteDegreeExceptTail
  return cNever

/-- Split into the "always applies" and "never applies" refinements at spoke `i`
for `rule` (C++ `refinement`, A.9.17). The `U_R`-nonempty `assert` is a structural
invariant guaranteed by `should_refine` → `panic!`. -/
def refinement (cw : CartWheel) (i : Nat) (rule : Rule) : Array CartWheel := Id.run do
  let fromCenter := (cw.darts[cw.centerDarts[i]!]!).rev
  let rule2cw := (PseudoConfiguration.homomorphism rule.toPseudoConfiguration rule.stId
    cw.toPseudoConfiguration fromCenter Degree.hasIntersection).get!
  let mut uR : Array Nat := #[]
  for vRule in [0:rule.n] do
    let vCw := (rule2cw.vmap[vRule]!).idx!
    if (cw.degrees[vCw]!).upper == CARTWHEEL_DEG_MAX
        && decide ((cw.degrees[vCw]!).lower < (rule.degrees[vRule]!).lower) then
      uR := uR.push vRule
  if uR.isEmpty then panic! "refinement: U_R is empty"
  let cAlways := cw.refineAlways uR rule2cw rule
  return (cw.refineNever uR rule2cw rule).push cAlways

/-- The first `(spoke i, rule)` pair (spokes outer, rules inner) that should be
refined, or `none` if the cartwheel is fully fixed. This names what the C++
`refined_flag` + double-`break` (and the Rust `break 'search`) encode: select the
first applicable pair. The early `return` inside `Id.run do` exits *both* loops,
so no flag is needed (cf. the paper's Algorithm A.9.14, lines 8–27). -/
def firstRefinable (cw : CartWheel) (degreeCenter : Nat) (rules : Array Rule) :
    Option (Nat × Rule) := Id.run do
  for i in [0:degreeCenter] do
    for rule in rules do
      if cw.shouldRefine i rule then
        return some (i, rule)
  return none

/-- Fix the rules sent from the centre to neighbours by repeated refinement
(C++ `fix_out_rules`, A.9.14). FIFO worklist matching the C++ `std::queue`. -/
def fixOutRules (cw : CartWheel) (cartwheelsInFixed : Array (CartWheel × Array CombinedRule))
    (rules : Array Rule) (combinedRules : Array CombinedRule) (confs : Array Configuration) :
    Array (CartWheel × Array CombinedRule) := Id.run do
  let degreeCenter := (cw.degrees[cw.center]!).lower
  let mut queue : Queue (CartWheel × Array CombinedRule) := Queue.ofArray cartwheelsInFixed
  let mut cartwheels : Array (CartWheel × Array CombinedRule) := #[]
  while !queue.isEmpty do
    let ((cartwheel, combinedRuleWithSpokes), queue') := queue.pop!
    queue := queue'
    match cartwheel.firstRefinable degreeCenter rules with
    | none => cartwheels := cartwheels.push (cartwheel, combinedRuleWithSpokes)
    | some (i, rule) =>
      for refinedCartwheel in cartwheel.refinement i rule do
        if refinedCartwheel.prune combinedRuleWithSpokes rules combinedRules confs then continue
        queue := queue.push (refinedCartwheel, combinedRuleWithSpokes)
  return cartwheels

/-- Group the centre's darts by the (fixed) degree of the neighbour they point to
(C++ `center_darts_by_degree`, A.9.22). Returns a length-`CARTWHEEL_DEG_MAX+1`
array. The degree-range `assert` is a structural invariant → `panic!`. -/
def centerDartsByDegree (cw : CartWheel) : Array (Array Nat) := Id.run do
  let mut byDegree : Array (Array Nat) := Array.replicate (CARTWHEEL_DEG_MAX + 1) #[]
  for dartId in cw.centerDarts do
    let neighbor := (cw.darts[(cw.darts[dartId]!).rev]!).head
    let deg := (cw.degrees[neighbor]!).lower
    if decide (deg < CARTWHEEL_DEG_MIN) || decide (deg > CARTWHEEL_DEG_MAX) then
      panic! "center_darts_by_degree: neighbour degree out of [5,9]"
    byDegree := byDegree.set! deg ((byDegree[deg]!).push dartId)
  return byDegree

/-- The overall enumeration: fix in-rules, fix out-rules, and keep the surviving
cartwheels (C++ `enum_bad_cartwheels`, A.9.21). The three trailing `assert`s are
genuine **proof obligations** (`proofAssert` — must abort, L1). -/
def enumBadCartwheels (cw : CartWheel) (rules : Array Rule) (combinedRules : Array CombinedRule)
    (confs : Array Configuration) : IO (Array CartWheel) := do
  let cartwheelsInFixed := cw.fixInRules rules combinedRules confs
  let cartwheelsFixed := cw.fixOutRules cartwheelsInFixed rules combinedRules confs
  let mut cartwheels : Array CartWheel := #[]
  for (cartwheel, combinedRuleWithSpokes) in cartwheelsFixed do
    let c := cartwheel.upperBoundOfCharge combinedRuleWithSpokes rules combinedRules
    let d := (cartwheel.degrees[cartwheel.center]!).lower
    let dartsByDeg := cartwheel.centerDartsByDegree
    proofAssert (c == 0) s!"final charge must be 0, got {c}"
    proofAssert (d == 7 || d == 8) s!"centre degree must be 7 or 8, got {d}"
    proofAssert ((dartsByDeg[7]!).size + (dartsByDeg[8]!).size + (dartsByDeg[9]!).size > 0)
      "cartwheel must have a degree-7/8/9 neighbour"
    cartwheels := cartwheels.push cartwheel
  return cartwheels

end CartWheel

-- --- P5: cartwheel-combination on PseudoConfiguration (consume CartWheel) -----
namespace PseudoConfiguration

/-- Glue each cartwheel onto `dart`, keeping results not blocked by a reducible
configuration (C++ `combine_each_cartwheel`, A.10.2). -/
def combineEachCartwheel (pc : PseudoConfiguration) (dart : Nat) (cartwheels : Array CartWheel)
    (confs : Array Configuration) : Array (PseudoConfiguration × Mappings) := Id.run do
  let mut zs : Array (PseudoConfiguration × Mappings) := #[]
  for cartwheel in cartwheels do
    for centerDart in cartwheel.centerDarts do
      let fhs := freeHomomorphismPair pc cartwheel.toPseudoConfiguration dart centerDart
      for (zStar, mappingsPc, _) in fhs do
        if zStar.blockedByReducibleConfiguration 0 confs then continue
        zs := zs.push (zStar, mappingsPc)
  return zs

/-- Glue cartwheels onto two darts in sequence (C++ `combine_each_cartwheel_twice`,
A.10.3). -/
def combineEachCartwheelTwice (pc : PseudoConfiguration) (dart1 dart2 : Nat)
    (cartwheels : Array CartWheel) (confs : Array Configuration) :
    Array (PseudoConfiguration × Mappings) := Id.run do
  let mut zStarStars : Array (PseudoConfiguration × Mappings) := #[]
  for (zStar, cw2zStar) in pc.combineEachCartwheel dart1 cartwheels confs do
    let mappedDart2 := (cw2zStar.dmap[dart2]!).idx!
    for (z, zStar2z) in zStar.combineEachCartwheel mappedDart2 cartwheels confs do
      zStarStars := zStarStars.push (z, cw2zStar.compose zStar2z)
  return zStarStars

end PseudoConfiguration

/-- Driver for Lemma A.3 step 1 (C++ `run_enum_wheels`). -/
def runEnumWheels (centerDegree : Nat) (confdir ruledir combinedRuledir outdir : System.FilePath) :
    IO Unit := do
  let confs ← Configuration.getConfs confdir
  let rules ← getRules ruledir
  let combinedRules ← getCombinedRules combinedRuledir
  let wheels := CartWheel.enumPossibleBadWheels centerDegree rules combinedRules confs
  IO.println s!"Generated {wheels.size} wheels."
  for i in [0:wheels.size] do
    wheels[i]!.toFile (outdir / s!"d{centerDegree}_{i}.cartwheel")

/-- Driver for Lemma A.3 step 2 (C++ `run_enum_cartwheels`). -/
def runEnumCartwheels (wheelFile confdir ruledir combinedRuledir outdir : System.FilePath) :
    IO Unit := do
  let cartwheel := CartWheel.ofString (← IO.FS.readFile wheelFile)
  let confs ← Configuration.getConfs confdir
  let rules ← getRules ruledir
  let combinedRules ← getCombinedRules combinedRuledir
  let enumedWheels ← cartwheel.enumBadCartwheels rules combinedRules confs
  IO.println s!"Total {enumedWheels.size} cartwheels after enumerating degrees."
  let basename := wheelFile.fileStem.getD "wheel"
  for i in [0:enumedWheels.size] do
    enumedWheels[i]!.toFile (outdir / s!"{basename}_{i}.cartwheel")

end NearLinear4ct
