import NearLinear4ct.Configuration

/-!
Phase 4 — discharging rules. Port of `../src/rule.{hpp,cpp}` (Appendix A.8).

`Rule extends PseudoConfiguration` and adds `stId` (the charge-carrying dart) and
`amount`. `CombinedRule extends Rule` and adds the `combinedFlag` bitvector (L6).

R3/R7: `combinedFlag` indexes rules "ordered by filename" (`../FORMAT.md`),
coupled to the deterministic load order from `getObjects`. The `write` output is
the proof artifact, so its bytes (including the trailing space after each vertex
line) must match the C++.

Parsing is **line-based**: a vertex's rotation is the rest of its line (variable
length), unlike the token-based configuration parser.
-/

namespace NearLinear4ct

/-- A discharging rule (C++ `Rule`). `stId` is the dart from `t` to `s` (charge
sender→receiver); `amount` is the charge. -/
structure Rule extends PseudoConfiguration where
  stId : Nat
  amount : Int
deriving DecidableEq, Repr, Inhabited, BEq

/-- A combination of rules with its inclusion bitvector (C++ `CombinedRule`). -/
structure CombinedRule extends Rule where
  combinedFlag : Array Bool
deriving DecidableEq, Repr, Inhabited, BEq

private def parseInt (tok : String) : Int :=
  match tok.toInt? with
  | some v => v
  | none => panic! s!"expected integer token, got {tok}"

/-- Split a line into whitespace tokens (C++ `boost::trim` + stream-split). -/
private def lineToks (line : String) : Array String :=
  ((line.split Char.isWhitespace).filterMap (fun s =>
    if s.isEmpty then none else some s.toString)).toArray

namespace Rule

/-- C++ `Rule(st_id, amount, N, darts, degrees)`. -/
def new (stId : Nat) (amount : Int) (n : Nat) (darts : Array Dart) (degrees : Array Degree) : Rule :=
  { toPseudoConfiguration := PseudoConfiguration.new n darts degrees, stId := stId, amount := amount }

/-- Parse one rule from `lines` starting at `cursor` (after the leading blank
line), returning the rule and the advanced cursor (C++ `Rule::read`). -/
def parse (lines : Array String) (cursor : Nat) : Rule × Nat := Id.run do
  let mut cur := cursor + 1                     -- skip the format's leading blank line
  let header := lineToks lines[cur]!
  cur := cur + 1
  let n := (parseInt header[0]!).toNat
  let s := parseInt header[1]! - 1
  let t := parseInt header[2]! - 1
  let amount := parseInt header[3]!
  let mut degrees : Array Degree := Array.replicate n ⟨1, INFTY⟩
  let mut rotationVertices : Array (Array Int) := Array.replicate n #[]
  for u in [0:n] do
    let toks := lineToks lines[cur]!
    cur := cur + 1
    let lower := (parseInt toks[1]!).toNat
    let upperRaw := (parseInt toks[2]!).toNat
    let upper := if upperRaw == 0 then INFTY else upperRaw
    degrees := degrees.set! u ⟨lower, upper⟩
    let mut rotU : Array Int := #[]
    for k in [3:toks.size] do
      let v := parseInt toks[k]!
      rotU := rotU.push (if v != -1 then v - 1 else v)
    rotationVertices := rotationVertices.set! u rotU
  let pc := PseudoConfiguration.fromVRotations n rotationVertices degrees
  let st := pc.getDarts t.toNat s.toNat
  return ({ toPseudoConfiguration := pc, stId := st[0]!, amount := amount }, cur)

/-- Serialise to the `.rule` text format (C++ `write`). The output is the proof
artifact; byte layout matches the C++ exactly (note the trailing space after each
vertex's neighbour list). -/
def write (rule : Rule) : String := Id.run do
  let darts := rule.darts
  let mut res := s!"\n{rule.n} {(darts[(darts[rule.stId]!).rev]!).head + 1} {(darts[rule.stId]!).head + 1} {rule.amount}\n"
  let eRotations := rule.getERotations
  for v in [0:rule.n] do
    let upper := if (rule.degrees[v]!).upper == INFTY then 0 else (rule.degrees[v]!).upper
    res := res ++ s!"{v + 1} {(rule.degrees[v]!).lower} {upper} "
    for dartId in eRotations[v]! do
      match dartId with
      | none => res := res ++ "-1 "
      | some e => res := res ++ s!"{(darts[(darts[e]!).rev]!).head + 1} "
    res := res ++ "\n"
  return res

/-- Write to a file (C++ `to_file`). -/
def toFile (rule : Rule) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path rule.write

/-- Validate at the I/O boundary that the charge dart is in bounds: every
consumer dereferences `darts[stId]` (`write`, homomorphism seeding,
`addRuleToCombination`). -/
def assertStIdValid (rule : Rule) (ctx : String) : IO Unit :=
  proofAssert (rule.stId < rule.darts.size)
    s!"{ctx}: charge dart {rule.stId} out of bounds (|darts| = {rule.darts.size})"

end Rule

instance : FromFile Rule where
  fromFile path := do
    let content ← IO.FS.readFile path
    return (Rule.parse (content.splitOn "\n").toArray 0).1

/-- Load every `.rule` file in `ruledir`, sorted by filename (C++ `get_rules`). -/
def getRules (ruledir : System.FilePath) : IO (Array Rule) := do
  let rules ← getObjects Rule ruledir ".rule"
  for r in rules do
    Configuration.assertDegreesValid r.degrees "rule"
    r.assertStIdValid "rule"
    Configuration.assertDartCountPackable r.darts "rule"
  IO.println s!"Total {rules.size} rules loaded."
  return rules

namespace CombinedRule

/-- C++ `CombinedRule(combined_flag, st_id, amount, N, darts, degrees)`. -/
def new (combinedFlag : Array Bool) (stId : Nat) (amount : Int) (n : Nat) (darts : Array Dart)
    (degrees : Array Degree) : CombinedRule :=
  { toRule := Rule.new stId amount n darts degrees, combinedFlag := combinedFlag }

/-- Serialise: the rule text followed by the flag bits (C++ `to_file`). -/
def write (cr : CombinedRule) : String := Id.run do
  let mut res := cr.toRule.write
  for flag in cr.combinedFlag do
    res := res ++ (if flag then "1" else "0")
  res := res ++ "\n"
  return res

def toFile (cr : CombinedRule) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path cr.write

/-- Extend this combination by also applying `rules[i]`, dropping results that are
blocked by a reducible configuration (C++ `add_rule_to_combination`, A.8.1). -/
def addRuleToCombination (cr : CombinedRule) (rules : Array Rule) (i : Nat)
    (confs : Array Configuration) : Array CombinedRule := Id.run do
  let zTildes := PseudoConfiguration.freeHomomorphismPair
    cr.toRule.toPseudoConfiguration rules[i]!.toPseudoConfiguration cr.stId rules[i]!.stId
  let newFlag := cr.combinedFlag.set! i true
  let rTildes : Array CombinedRule := zTildes.map fun (zTilde, mappingsCombination, _) =>
    CombinedRule.new newFlag (mappingsCombination.dmap[cr.stId]!).idx!
      (cr.amount + rules[i]!.amount) zTilde.n zTilde.darts zTilde.degrees
  if confs.isEmpty then return rTildes
  return rTildes.filter fun rTilde =>
    let center := (rTilde.darts[rTilde.stId]!).head
    !rTilde.toPseudoConfiguration.blockedByReducibleConfiguration center confs

end CombinedRule

instance : FromFile CombinedRule where
  fromFile path := do
    let content ← IO.FS.readFile path
    let lines := (content.splitOn "\n").toArray
    let (rule, cur) := Rule.parse lines 0
    -- the next non-empty line is the 0/1 flag string (C++ `ifs >> line`)
    let flagLine := ((lines.extract cur lines.size).filterMap (fun l =>
      let t := l.trimAscii.toString
      if t.isEmpty then none else some t))[0]!
    let combinedFlag := (flagLine.toList.map fun c =>
      match c with
      | '0' => false
      | '1' => true
      | other => panic! s!"Invalid combined flag '{other}' in {path}").toArray
    return { toRule := rule, combinedFlag := combinedFlag }

/-- Load every `.combined_rule` file in `combinedRuledir` (C++
`get_combined_rules`). -/
def getCombinedRules (combinedRuledir : System.FilePath) : IO (Array CombinedRule) := do
  let crs ← getObjects CombinedRule combinedRuledir ".combined_rule"
  for cr in crs do
    cr.toRule.assertStIdValid "combined rule"
    Configuration.assertDartCountPackable cr.darts "combined rule"
  IO.println s!"Total {crs.size} combined rules loaded."
  return crs

/-- Enumerate all combined rules reachable from the given rules (C++
`combine_rules`, A.8.2).

Each round's expansion is `next := combinedRules ++ ⋃ combination,
combination.addRuleToCombination …`; the rounds are sequential, but *within* a
round each `addRuleToCombination` is independent and read-only over the shared
`rules`/`confs`. So the expansion runs with the order-preserving `parMap` (its
heavy step is the reducible-config blocking — the same containment hot path) — a
wall-clock speedup yielding the **identical** combined-rule list (hence identical
output files), the same trick used for `enum_possible_bad_wheels`. -/
def combineRules (rules : Array Rule) (confs : Array Configuration) : Array CombinedRule := Id.run do
  let defaultFlag := Array.replicate rules.size false
  let z0 := CombinedRule.new defaultFlag 0 0 2
    #[⟨0, 1, OptIdx.none, OptIdx.none⟩, ⟨1, 0, OptIdx.none, OptIdx.none⟩] #[⟨1, INFTY⟩, ⟨1, INFTY⟩]
  let mut combinedRules : Array CombinedRule := #[z0]
  for i in [0:rules.size] do
    combinedRules := combinedRules ++
      parFlatMap combinedRules (fun combination => combination.addRuleToCombination rules i confs)
  return combinedRules

/-- Driver for Lemma A.1 / A.2 (C++ `run_combine_rules`). -/
def runCombineRules (confdir ruledir outdir : System.FilePath) : IO Unit := do
  let confs ← Configuration.getConfs confdir
  let rules ← getRules ruledir
  let combinedRules := combineRules rules confs
  IO.println s!"Generated {combinedRules.size} combined rules."
  for i in [0:combinedRules.size] do
    combinedRules[i]!.toFile (outdir / s!"combined_rule_{i + 1}.combined_rule")

end NearLinear4ct
