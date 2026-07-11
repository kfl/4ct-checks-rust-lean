import NearLinear4ct.PseudoConfiguration

/-!
Phase 4 — file-backed reducible configurations. Port of
`../src/configuration.{hpp,cpp}` (Appendix A.6).

`Configuration extends PseudoConfiguration` and adds a root `dartId` (L6).

R2 (resolved): the C++ `using std::map/std::set` here are dead — the adjacency
scratch `suc` is a plain 2-D vector with a `-1` sentinel, mirrored as
`Array (Array Int)`. R7: `from_file` parsing must reproduce the C++ structures
byte-for-byte.

This file also hosts the **reducible-configuration cluster** on
`PseudoConfiguration` (`containConf`, `dartsByDegree`, `rootedContainConf`,
`blockedByReducibleConfiguration`, `representativeDegree`). In C++ these are
`PseudoConfiguration` methods that consume `Configuration` via a forward
declaration; Lean has no forward declarations, so they live here (after
`Configuration` exists), exactly as the Rust port placed them — needed so
`rule::combineRules` (P4) compiles.
-/

namespace NearLinear4ct

/-- A reducible configuration: a pseudo-configuration with a distinguished root
dart (C++ `Configuration`). -/
structure Configuration extends PseudoConfiguration where
  dartId : Nat
deriving DecidableEq, Repr, Inhabited, BEq

namespace Configuration

/-- C++ `Configuration(dart_id, N, darts, degrees)`. -/
def new (dartId n : Nat) (darts : Array Dart) (degrees : Array Degree) : Configuration :=
  { toPseudoConfiguration := PseudoConfiguration.new n darts degrees, dartId := dartId }

/-- Reflect the configuration by swapping each dart's `succ`/`pred` (C++ `mirror`). -/
def mirror (conf : Configuration) : Configuration :=
  let darts := conf.darts.map fun d => { d with succ := d.pred, pred := d.succ }
  Configuration.new conf.dartId conf.n darts conf.degrees

end Configuration

/-- Mirror image of every configuration (C++ `get_mirrors`). -/
def getMirrors (confs : Array Configuration) : Array Configuration :=
  confs.map Configuration.mirror

/-- Find internal vertices that are cut-vertices, returning their two ring
neighbours (C++ `find_cut_pairs`, A.6.2). The C++ `assert`/`throw` for an invalid
cut-vertex become `panic!` (input wellformedness, not a proof obligation). -/
def findCutPairs (n r : Nat) (rotations : Array (Array Int)) : Array (Nat × Nat) := Id.run do
  let mut p : Array (Nat × Nat) := #[]
  for i in [r:n] do
    let rot := rotations[i]!
    let d := rot.size
    let mut uR : Array Nat := #[]
    let mut t : Nat := 0
    for j in [0:d] do
      let k1 := rot[j]!
      if k1 < r then uR := uR.push k1.toNat
      let k2 := rot[(j + 1) % d]!
      if k1 < r && k2 ≥ (r : Int) then t := t + 1
    if t ≥ 2 && uR.size != 2 then
      panic! s!"Invalid configuration (vertex {i} is an invalid cut-vertex"
    if t == 2 && uR.size == 2 then
      p := p.push (uR[0]!, uR[1]!)
  return p

/-- The dart whose (head-degree, tail-degree) pair is lexicographically largest
among fixed-degree endpoints (C++ `maximum_degree_dart`, A.6.4). -/
def maximumDegreeDart (z : PseudoConfiguration) : Nat := Id.run do
  let mut f : Option Nat := none
  let mut dF : Int × Int := (0, 0)
  for i in [0:z.darts.size] do
    let dart := z.darts[i]!
    let y := dart.head
    let x := (z.darts[dart.rev]!).head
    if !(z.degrees[y]!).fixed || !(z.degrees[x]!).fixed then continue
    let dE : Int × Int := ((z.degrees[y]!).lower, (z.degrees[x]!).lower)
    -- lexicographic `>` on the pair (the C++ `pair operator>`)
    if dE.1 > dF.1 || (dE.1 == dF.1 && dE.2 > dF.2) then
      f := some i
      dF := dE
  return f.get!

/-- Remove the `remove`-marked ring vertices, renumber, and rebuild as a
`PseudoConfiguration` (C++ `remove_ring`, A.6.3). -/
def removeRing (n r : Nat) (degrees : Array Degree) (rotations : Array (Array Int))
    (remove : Array Bool) : PseudoConfiguration := Id.run do
  -- Step 1: new vertex ids (removed ring vertices get none).
  let mut old2new : Array (Option Nat) := Array.replicate n none
  let mut newId : Nat := 0
  for i in [0:n] do
    if i < r && remove[i]! then continue
    old2new := old2new.set! i (some newId)
    newId := newId + 1
  let newN := newId
  -- Step 2: new rotations; a removed neighbour becomes a `-1` boundary.
  let mut newRotations : Array (Array Int) := Array.replicate newN #[]
  for i in [0:n] do
    if i < r && remove[i]! then continue
    let k := (old2new[i]!).get!
    let mut rotK := newRotations[k]!
    for j in rotations[i]! do
      if j == -1 then rotK := rotK.push (-1)
      else
        rotK := rotK.push (match old2new[j.toNat]! with | some x => (x : Int) | none => -1)
    newRotations := newRotations.set! k rotK
  -- Step 3: new degrees.
  let mut newDegrees : Array Degree := Array.replicate newN ⟨1, INFTY⟩
  for i in [0:r] do
    if remove[i]! then continue
    let k := (old2new[i]!).get!
    let d := (newRotations[k]!).filter (· != -1) |>.size
    newDegrees := newDegrees.set! k ⟨d + 1, INFTY⟩
  for i in [r:n] do
    let k := (old2new[i]!).get!
    newDegrees := newDegrees.set! k (degrees[i]!)
  return PseudoConfiguration.fromVRotations newN newRotations newDegrees

/-- Expand cut-vertices: for each subset of cut-pairs, remove the unselected ring
vertices and build a configuration (C++ `extend_from_cut_vertices`, A.6.1). -/
def extendFromCutVertices (n r : Nat) (degrees : Array Degree) (rotations : Array (Array Int)) :
    Array Configuration := Id.run do
  let p := findCutPairs n r rotations
  let pSize := p.size
  let mut configurations : Array Configuration := #[]
  for s in [0:(1 <<< pSize)] do
    let mut remove : Array Bool := Array.replicate r true
    for i in [0:pSize] do
      let (a, b) := p[i]!
      if s &&& (1 <<< i) != 0 then remove := remove.set! a false
      else remove := remove.set! b false
    let z := removeRing n r degrees rotations remove
    let dart := maximumDegreeDart z
    configurations := configurations.push (Configuration.new dart z.n z.darts z.degrees)
  return configurations

namespace Configuration

/-- Parse a `.conf` file into one or more configurations (C++ `from_file`).

Internal vertices list clockwise rotations; the ring vertices' rotations are
reconstructed from the successor relation `suc`. Cut-vertices expand to several
configurations, and each is paired with its mirror. Token-based (the degree gives
the neighbour count), so a flat whitespace token stream suffices. -/
def fromFile (path : System.FilePath) : IO (Array Configuration) := do
  let content ← IO.FS.readFile path
  -- whitespace-token stream (C++ `ifs >> x`), dropping empties from runs/newlines
  let toks := (content.split Char.isWhitespace).filterMap (fun s =>
    if s.isEmpty then none else some s)
  let tokArr := toks.toArray
  let mut idx : Nat := 0
  -- token reader over the captured array (C++ `ifs >> x`, with `--v` done by callers)
  let readAt (i : Nat) : Int :=
    match (tokArr[i]!).toInt? with
    | some v => v
    | none => panic! s!"integer token expected, got {tokArr[i]!}"
  let n := (readAt idx).toNat; idx := idx + 1
  let r := (readAt idx).toNat; idx := idx + 1
  let mut degrees : Array Degree := Array.replicate n ⟨1, INFTY⟩
  let mut rotations : Array (Array Int) := Array.replicate n #[]
  let mut suc : Array (Array Int) := Array.replicate r (Array.replicate n (-1))
  for u in [r:n] do
    let t := (readAt idx).toNat; idx := idx + 1
    if t != u + 1 then panic! s!"configuration vertex index mismatch: {t} != {u+1}"
    let deg := (readAt idx).toNat; idx := idx + 1
    degrees := degrees.set! u (Degree.exact deg)
    let mut rotU : Array Int := #[]
    for _ in [0:deg] do
      rotU := rotU.push (readAt idx - 1); idx := idx + 1
    rotations := rotations.set! u rotU
    for j in [0:deg] do
      let v := rotU[j]!
      let pre := rotU[(j + deg - 1) % deg]!
      let nxt := rotU[(j + 1) % deg]!
      if v < r then
        suc := suc.set! v.toNat ((suc[v.toNat]!).set! nxt.toNat (u : Int))
        suc := suc.set! v.toNat ((suc[v.toNat]!).set! u pre)
  -- reconstruct ring vertices' rotations by walking `suc`
  for v in [0:r] do
    let start := (v + 1) % r
    let endv := (v + r - 1) % r
    let mut rotV : Array Int := #[]
    let mut curr : Int := start
    while curr != -1 do
      rotV := rotV.push curr
      curr := (suc[v]!)[curr.toNat]!
    if rotV.back! != (endv : Int) then
      panic! s!"Invalid configuration file: {path}"
    rotV := rotV.push (-1)        -- boundary
    rotations := rotations.set! v rotV
  let configurations := extendFromCutVertices n r degrees rotations
  return configurations ++ getMirrors configurations

/-- Validate at the I/O boundary that every degree lower bound is `≥ 1`. Degrees are
vertex-degree bounds, never `< 1`; a smaller value means a corrupt input file (or a
negative that `.toNat` clamped to `0` at the parser). Enforcing it here is what makes
the `Nat` degree representation sound — in particular it discharges the `lower ≥ 1`
assumption of the `Cartwheel` `lower - 1` refinement (`PROOFS.md`). `proofAssert`
aborts (the C++ `assert`), so a bad file fails loudly rather than silently. -/
def assertDegreesValid (degrees : Array Degree) (ctx : String) : IO Unit := do
  for d in degrees do
    proofAssert (d.lower ≥ 1)
      s!"{ctx}: degree lower bound must be ≥ 1 (corrupt input?), got {d.lower}"

/-- Load every `.conf` file in `confdir` (C++ `get_confs`).

The 8200 files are read + parsed in parallel (`parMapM`): independent IO + CPU per
file, so this overlaps across cores instead of a serial loop. Containment only
asks *whether* some config matches (`containConf` is an order-independent `any`),
so the load order does not affect output — byte-identical (confirmed by the
differential). -/
def getConfs (confdir : System.FilePath) : IO (Array Configuration) := do
  let paths := (← confdir.readDir).filterMap fun entry =>
    if entry.path.extension == some "conf" then some entry.path else none
  let perFile ← parMapM paths fromFile
  let confs := perFile.flatten
  for c in confs do assertDegreesValid c.degrees "configuration"
  IO.println s!"Total {confs.size} configurations loaded."
  return confs

end Configuration

-- --- P4: reducible-configuration cluster (on PseudoConfiguration) -------------
namespace PseudoConfiguration

/-- Bucket darts by the fixed (head-degree, tail-degree) of their endpoints,
dropping endpoints above `CONF_DEG_MAX` (C++ `darts_by_degree`, A.6.7). -/
def dartsByDegree (pc : PseudoConfiguration) : Array (Array (Array Nat)) := Id.run do
  let size := CONF_DEG_MAX + 1
  let mut buckets : Array (Array (Array Nat)) := Array.replicate size (Array.replicate size #[])
  for i in [0:pc.darts.size] do
    let e := pc.darts[i]!
    let y := e.head
    let x := (pc.darts[e.rev]!).head
    let dY := (pc.degrees[y]!).lower
    let dX := (pc.degrees[x]!).lower
    if dY > CONF_DEG_MAX || dX > CONF_DEG_MAX then continue
    buckets := buckets.set! dY ((buckets[dY]!).set! dX (((buckets[dY]!)[dX]!).push i))
  return buckets

/-- Whether `conf` embeds into `pc` rooted at `dartId`, with the configuration's
degrees included in `pc`'s (C++ `rooted_contain_conf`, A.6.8). -/
def rootedContainConf (pc : PseudoConfiguration) (dartId : Nat) (conf : Configuration) : Bool :=
  PseudoConfiguration.homomorphismExists conf.toPseudoConfiguration conf.dartId pc dartId
    Degree.includes

/-- Whether this configuration contains any reducible configuration in `confs`
(C++ `contain_conf`, A.6.6). Serial with early-exit: a config-level `parAny` was
measured and rejected (nested → worker-pool deadlock; non-nested → millions of
µs-overhead tasks over tiny config-checks, and the early-exit lost — both far
slower). The right parallelism granularity is the outer wheel/combination level.

(Two refinements were prototyped + measured *not worthwhile* and dropped, see
`PERF.md` §P13: reusing one generation-stamped scratch across the inner embedding
checks — *slower*, the per-call alloc is already cheap; and pre-grouping `confs` by
root-degree key to skip non-matching configs — *neutral*, the loop already skips
them via an empty dart bucket, so the per-config key work is not redundant.)

P14: the sweep is `Array.any` (short-circuiting — so the spec's first-match exit is
preserved, where `foldl` would not) rather than nested `for … do … return`, avoiding
the `forIn`/`ForInStep` closure + heartbeat lowering that cost `homCore` ~1.21×
(`PERF.md` §P13). A candidate dart is skipped when the spec's `dY > 8` guard fires (a
high-degree root maps only the dart whose head is the wheel `center`). -/
def containConf (pc : PseudoConfiguration) (center : Nat) (confs : Array Configuration) : Bool :=
  let dbd := pc.dartsByDegree
  confs.any fun conf =>
    let f := conf.darts[conf.dartId]!
    let dY := (conf.degrees[f.head]!).lower
    let dX := (conf.degrees[(conf.darts[f.rev]!).head]!).lower
    ((dbd[dY]!)[dX]!).any fun fStar =>
      (dY ≤ 8 || (pc.darts[fStar]!).head == center) && pc.rootedContainConf fStar conf

/-- Enumerate the fixed-degree representatives (C++ `representative_degree`,
A.7.2). High degrees collapse to a single `exact upper` instead of expanding. -/
def representativeDegree (pc : PseudoConfiguration) (center : Nat) :
    Array PseudoConfiguration := Id.run do
  let n := pc.n
  let mut t : Array (Array Degree) := #[Array.replicate n ⟨1, INFTY⟩]
  for v in [0:n] do
    let degV := pc.degrees[v]!
    let highThreshold : Nat := if v == center then CONF_DEG_MAX else 8
    let choices : Array Degree :=
      if degV.upper > highThreshold then #[Degree.exact degV.upper]
      -- coerce to `Int` for the count: an *empty* range (`upper < lower`, a legitimate
      -- `intersection` result) gives `≤ 0` ⇒ no choices, as in C++. `Nat` subtraction
      -- would truncate to `0` and yield one spurious choice.
      else (Array.range ((degV.upper : Int) - degV.lower + 1).toNat).map
        (fun k => Degree.exact (degV.lower + k))
    let mut newT : Array (Array Degree) := #[]
    for degs in t do
      for d in choices do
        newT := newT.push (degs.set! v d)
    t := newT
  return t.map (fun deg => PseudoConfiguration.new n pc.darts deg)

/-- Whether every fixed-degree representative contains a reducible configuration
(C++ `blocked_by_reducible_configuration`, A.7.1). -/
def blockedByReducibleConfiguration (pc : PseudoConfiguration) (center : Nat)
    (confs : Array Configuration) : Bool :=
  (pc.representativeDegree center).all (fun z => z.containConf center confs)

end PseudoConfiguration
end NearLinear4ct
