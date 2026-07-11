import NearLinear4ct.PseudoTriangulation
import NearLinear4ct.Degree
import NearLinear4ct.SmallNatPair

/-!
Phase 3 — configuration with degrees. Port of
`../src/pseudo_configuration.{hpp,cpp}` (Appendix A.2 `homomorphism`, A.4
`dartIdentification` / `freeHomomorphism…` / `resolveDegreeIssues` + helpers).

L6 decision: in C++ this *inherits* from `PseudoTriangulation`. Lean models that
directly with `extends` — both the fields (`pc.n`, `pc.darts`) **and** the parent
methods (`pc.firstDart v`, `pc.isBoundary`, …) are reachable by dot notation
(Lean falls through `extends` parents), so this reads closer to the C++ than the
Rust port's composition. The two names overridden by the child
(`debug`, `freeHomomorphism`) are reached on the parent explicitly via
`pc.toPseudoTriangulation.…` (the C++ `this->PseudoTriangulation::…`).

Scope: the methods that consume *derived* types (`Configuration`/`Rule`/
`CartWheel`) — containment, charges, cartwheel combination — are deferred to
P4/P5 (Lean allows the mutual module reference, so they land as later additions).
This file is the self-contained core.
-/

namespace NearLinear4ct

/-- A pseudo-triangulation with a degree range per vertex. -/
structure PseudoConfiguration extends PseudoTriangulation where
  degrees : Array Degree
deriving DecidableEq, Repr, Inhabited, BEq

namespace PseudoConfiguration

/-- C++ `PseudoConfiguration(N, darts, degrees)`. -/
def new (n : Nat) (darts : Array Dart) (degrees : Array Degree) : PseudoConfiguration :=
  { toPseudoTriangulation := ⟨n, darts⟩, degrees := degrees }

/-- Multi-line dump (C++ `debug`). -/
def debug (pc : PseudoConfiguration) : String := Id.run do
  let mut res := pc.toPseudoTriangulation.debug
  for d in pc.degrees do
    res := res ++ s!"Degree({d.lower}, {d.upper}),\n"
  return res

/-- Human-readable rotation view with degrees (C++ `to_string`). -/
def display (pc : PseudoConfiguration) : String := Id.run do
  let mut res := s!"N: {pc.n}\n"
  let edges := pc.darts.map fun d => (d.head, (pc.darts[d.rev]!).head)
  let eRot := pc.getERotations
  for v in [0:pc.n] do
    res := res ++ s!"{v}, deg=({(pc.degrees[v]!).lower}, {(pc.degrees[v]!).upper}): "
    for dartId in eRot[v]! do
      match dartId with
      | none => res := res ++ "nil, "
      | some e => res := res ++ s!"e{e}({(edges[e]!).1}-{(edges[e]!).2}), "
    res := res ++ "\n"
  return res

/-- Build from vertex rotations + degrees (C++ `from_v_rotations`).
The C++ `assert(degrees.size() == N)` is a caller precondition, kept implicit. -/
def fromVRotations (n : Nat) (vRotations : Array (Array Int)) (degrees : Array Degree) :
    PseudoConfiguration :=
  let pt := PseudoTriangulation.fromVRotations n vRotations
  PseudoConfiguration.new n pt.darts degrees

/-- Side-by-side union (C++ `disjoint_union`). -/
def disjointUnion (l r : PseudoConfiguration) : PseudoConfiguration :=
  let pt := PseudoTriangulation.disjointUnion l.toPseudoTriangulation r.toPseudoTriangulation
  PseudoConfiguration.new pt.n pt.darts (l.degrees ++ r.degrees)


/-- Tail-recursive worklist loop of the homomorphism BFS, factored out of the
`while`/`Id.run do` so the state `(q, maps)` threads through **explicit arguments**.
Perceus's borrow/reuse analysis is cleaner on a tail call with linear state than on
the `whileM` closure the `do` loop desugars to (which also carried a per-iteration
heartbeat): `maps.set!` stays in place, `q` is threaded, and `src`/`dst`/`degreeTest`
are read-only so they pass borrowed (no per-iteration RC).

`partial` (L5): the worklist `q` *grows* (each visit pushes ≤ 3 darts), so this is not
structural. Termination argument (to be formalised — see `PROOFS.md` §3): each dart is
*expanded* (the `dmap[f] = none` branch) at most once, so on a **well-formed** graph
the measure `(# unmapped dart cells, q.size)` strictly decreases — a re-pop of a mapped
dart shrinks `q`, a first visit drops the unmapped count. (It is *not* total on
malformed input: an out-of-bounds dart index makes `set!` a no-op and can loop. The
real inputs are well-formed; the byte-exact differential is the current evidence.)

The two maps are `Array OptIdx` — the verified-unboxed `Option Nat` (`OptIdx.lean`),
read in `none`/`some` terms yet stored unboxed (no `some`-cell allocation per `set`).
The worklist entries `(f, f★)` are `SmallNatPair` -- the verified pointer-tagged
pack of two dart indices (`SmallNatPair.lean`; a `Nat × Nat` ctor costs a heap
allocation + free per element, and those pairs were the prune pipeline's dominant
RC/free churn). `@[specialize]` monomorphises `degreeTest` per call site
(`Degree.includes` etc.), eliminating the indirect `lean_apply_2` in the loop. -/
@[specialize] private partial def homCoreGo (src dst : PseudoConfiguration)
    (degreeTest : Degree → Degree → Bool)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Option (IndexMap × IndexMap) :=
  if q.isEmpty then some (vmap, dmap)
  else
    let (packed, q) := q.pop!
    let (f, fStar) := packed.unpackPair
    let dv := dmap[f]!
    if dv.isSome then
      if dv != OptIdx.some fStar then none           -- already mapped, inconsistently
      else homCoreGo src dst degreeTest q vmap dmap
    else
      let dmap := dmap.set! f (OptIdx.some fStar)
      -- bind each dart once (read 4×: head/rev/succ/pred)
      let srcD := src.darts[f]!
      let dstD := dst.darts[fStar]!
      let h := srcD.head
      let hStar := dstD.head
      let vv := vmap[h]!
      if vv.isSome && vv != OptIdx.some hStar then none
      else
        let vmap := vmap.set! h (OptIdx.some hStar)
        if !degreeTest (src.degrees[h]!) (dst.degrees[hStar]!) then none
        -- `src` side open where `dst` is closed ⇒ no homomorphism (the queue would
        -- be discarded on `none`, so failing before the pushes is equivalent).
        else if srcD.succ.isSome && dstD.succ.isNone then none
        else if srcD.pred.isSome && dstD.pred.isNone then none
        else
          let q := q.push (SmallNatPair.pack srcD.rev dstD.rev)
          let q := if srcD.succ.isSome then q.push (SmallNatPair.pack srcD.succ.idx! dstD.succ.idx!) else q
          let q := if srcD.pred.isSome then q.push (SmallNatPair.pack srcD.pred.idx! dstD.pred.idx!) else q
          homCoreGo src dst degreeTest q vmap dmap

/-- Shared BFS core for `homomorphism` / `homomorphismExists` (C++ templated
`homomorphism`, A.2). Seeds the worklist + the vertex (`[0,n)`) and dart
(`[0,darts.size)`) scratch maps and runs `homCoreGo`. -/
@[specialize] private def homCore (src : PseudoConfiguration) (dartFrom : Nat)
    (dst : PseudoConfiguration) (dartTo : Nat)
    (degreeTest : Degree → Degree → Bool) : Option (IndexMap × IndexMap) :=
  homCoreGo src dst degreeTest
    ((Queue.emptyWithCapacity (src.darts.size * 3 + 1)).push (SmallNatPair.pack dartFrom dartTo))
    (Array.replicate src.n OptIdx.none)
    (Array.replicate src.darts.size OptIdx.none)

/-- Whether a homomorphism exists, accepting a vertex degree compatibility test
(C++ `homomorphism(...).has_value()`). The `.isSome`-only hot path
(`rootedContainConf`, `never/always/dominantlyApply`, `containX`) — skips building
the result `Mappings` entirely.

(A `homRootOk` root-degree fast-fail was prototyped + measured here: neutral on
both workloads, because the homomorphism failures are *structural/deep*, not at
the root — the `dartsByDegree` bucket already filters root degrees. Not
worthwhile, so not kept; see `PERF.md`.) -/
@[inline] def homomorphismExists (src : PseudoConfiguration) (dartFrom : Nat)
    (dst : PseudoConfiguration) (dartTo : Nat)
    (degreeTest : Degree → Degree → Bool) : Bool :=
  (homCore src dartFrom dst dartTo degreeTest).isSome

/-- BFS graph homomorphism rooted at a dart pair (C++ templated `homomorphism`,
A.2). Returns the (possibly partial) index maps if a homomorphism exists. -/
def homomorphism (src : PseudoConfiguration) (dartFrom : Nat)
    (dst : PseudoConfiguration) (dartTo : Nat)
    (degreeTest : Degree → Degree → Bool) : Option Mappings :=
  (homCore src dartFrom dst dartTo degreeTest).map fun (v, d) => ⟨v, d⟩

/-- Glue the dart pairs as a combinatorial map and reconcile degrees, if the
result is loop-free and degree-consistent (C++ `dart_identification`, A.4.1). -/
def dartIdentification (pc : PseudoConfiguration) (dartPairs : Array (Nat × Nat)) :
    Option (PseudoConfiguration × Mappings) := Id.run do
  let (zStar, mappings) := pc.toPseudoTriangulation.freeHomomorphism dartPairs
  if zStar.hasLoop then return none          -- a loop error
  let mut degreesStar : Array Degree := Array.replicate zStar.n ⟨1, INFTY⟩
  for v in [0:pc.n] do
    let vStar := (mappings.vmap[v]!).idx!
    if Degree.disjoint (degreesStar[vStar]!) (pc.degrees[v]!) then
      return none                            -- a degree-mismatch error
    degreesStar := degreesStar.set! vStar (Degree.intersection (degreesStar[vStar]!) (pc.degrees[v]!))
  return some (PseudoConfiguration.new zStar.n zStar.darts degreesStar, mappings)

/-- Whether an interior vertex has fewer incident darts than its lower degree
bound (C++ `inner_subdegree_error`, A.4.5). -/
def innerSubdegreeError (pc : PseudoConfiguration) : Bool := Id.run do
  let nIncident := pc.nIncidentDarts
  let isB := pc.isBoundary
  for v in [0:pc.n] do
    if !isB[v]! && decide ((nIncident[v]! : Int) < (pc.degrees[v]!).lower) then
      return true
  return false

/-- Find a fixed-degree vertex whose incidences need adjusting
(C++ `vertex_single_degree_issue`, A.4.6). -/
def vertexSingleDegreeIssue (pc : PseudoConfiguration) : Option Nat := Id.run do
  let nIncident := pc.nIncidentDarts
  let isB := pc.isBoundary
  for v in [0:pc.n] do
    if !(pc.degrees[v]!).fixed then continue
    let inc : Int := nIncident[v]!
    if decide ((pc.degrees[v]!).lower < inc) || (isB[v]! && inc == (pc.degrees[v]!).lower) then
      return some v
  return none

/-- Close a boundary fan at `v` by adding the two darts of a new edge
(C++ `add_boundary_darts`, A.4.8). `none` on a boundary error (`u == w`). -/
def addBoundaryDarts (pc : PseudoConfiguration) (v : Nat) : Option PseudoConfiguration := Id.run do
  let eFirst := (pc.firstDart v).get!
  let eLast := (pc.lastDart v).get!
  let eFirstRev := (pc.darts[eFirst]!).rev
  let eLastRev := (pc.darts[eLast]!).rev
  let u := (pc.darts[eFirstRev]!).head
  let w := (pc.darts[eLastRev]!).head
  if u == w then return none                 -- a boundary error
  let dUW := pc.darts.size
  let dWU := dUW + 1
  let mut darts := pc.darts
  darts := darts.push ⟨u, dWU, OptIdx.none, OptIdx.some eFirstRev⟩
  darts := darts.push ⟨w, dUW, OptIdx.some eLastRev, OptIdx.none⟩
  darts := darts.set! eFirst { darts[eFirst]! with pred := OptIdx.some eLast }
  darts := darts.set! eLast { darts[eLast]! with succ := OptIdx.some eFirst }
  darts := darts.set! eFirstRev { darts[eFirstRev]! with succ := OptIdx.some dUW }
  darts := darts.set! eLastRev { darts[eLastRev]! with pred := OptIdx.some dWU }
  return some (PseudoConfiguration.new pc.n darts pc.degrees)

/-- Resolve the single degree issue at `v` (C++ `fix_single_degree_issue`,
A.4.7). The trailing `panic!` is the C++ `assert(false)` — unreachable, since the
caller only invokes this when one of the two cases holds. -/
def fixSingleDegreeIssue (pc : PseudoConfiguration) (v : Nat) :
    Option (PseudoConfiguration × Mappings) :=
  let nIncident := pc.nIncidentDarts
  let isB := pc.isBoundary
  let inc := nIncident[v]!
  if (pc.degrees[v]!).lower < inc then
    let e := (if isB[v]! then pc.firstDart v else pc.anyDart v).get!
    let f := (pc.sucKTimes e (pc.degrees[v]!).lower).get!
    pc.dartIdentification #[(e, f)]
  else if isB[v]! && inc == (pc.degrees[v]!).lower then
    match pc.addBoundaryDarts v with
    | some pc' => some (pc', Mappings.initialMappings pc.n pc.darts.size)
    | none => none
  else
    panic! "fix_single_degree_issue called without a degree issue"

/-- Split the first range-valued vertex into its lowest degree vs. the rest
(C++ `single_out_lower_degree`, A.4.9). -/
def singleOutLowerDegree (pc : PseudoConfiguration) :
    Option (PseudoConfiguration × PseudoConfiguration) := Id.run do
  let nIncident := pc.nIncidentDarts
  for v in [0:pc.n] do
    let deg := pc.degrees[v]!
    if decide (deg.lower < deg.upper) && decide (deg.lower ≤ (nIncident[v]! : Int)) then
      let z1 := PseudoConfiguration.new pc.n pc.darts (pc.degrees.set! v ⟨deg.lower, deg.lower⟩)
      let z2 := PseudoConfiguration.new pc.n pc.darts (pc.degrees.set! v ⟨deg.lower + 1, deg.upper⟩)
      return some (z1, z2)
  return none

/-- Enumerate the configurations obtained by resolving every degree issue
(over-incident fixed vertices, boundary closures, degree splits) via BFS
(C++ `resolve_degree_issues`, A.4.4). Result order matches the C++ FIFO queue. -/
def resolveDegreeIssues (pc : PseudoConfiguration) : Array (PseudoConfiguration × Mappings) :=
    Id.run do
  let mut z : Array (PseudoConfiguration × Mappings) := #[]
  let initial := Mappings.initialMappings pc.n pc.darts.size
  let mut q : Queue (PseudoConfiguration × Mappings) := Queue.ofArray #[(pc, initial)]
  while !q.isEmpty do
    let ((zTilde, mappingsTilde), q') := q.pop!
    q := q'
    if zTilde.innerSubdegreeError then continue
    match zTilde.vertexSingleDegreeIssue with
    | some v =>
      match zTilde.fixSingleDegreeIssue v with
      | some (zStar, mappingsStar) => q := q.push (zStar, mappingsTilde.compose mappingsStar)
      | none => pure ()
      continue
    | none => pure ()
    match zTilde.singleOutLowerDegree with
    | some (z1, z2) =>
      q := q.push (z1, mappingsTilde)
      q := q.push (z2, mappingsTilde)
      continue
    | none => pure ()
    z := z.push (zTilde, mappingsTilde)
  return z

/-- Identify the dart pairs and resolve any resulting degree issues
(C++ member `free_homomorphism`, A.4.3). -/
def freeHomomorphism (pc : PseudoConfiguration) (dartPairs : Array (Nat × Nat)) :
    Array (PseudoConfiguration × Mappings) :=
  match pc.dartIdentification dartPairs with
  | none => #[]
  | some (zStar, mappings) =>
    zStar.resolveDegreeIssues.map fun (zTilde, mappingsTilde) =>
      (zTilde, mappings.compose mappingsTilde)

/-- Free homomorphism over the disjoint union of `pc0`, `pc1`, identifying
`dartId0` (in `pc0`) with `dartId1` (in `pc1`); returns each result with the two
index maps restricted to each side (C++ static `free_homomorphism`). -/
def freeHomomorphismPair (pc0 pc1 : PseudoConfiguration) (dartId0 dartId1 : Nat) :
    Array (PseudoConfiguration × Mappings × Mappings) :=
  let pc := PseudoConfiguration.disjointUnion pc0 pc1
  let dartId1 := dartId1 + pc0.darts.size
  (pc.freeHomomorphism #[(dartId0, dartId1)]).map fun (identifiedPc, mappings) =>
    let (vmap0, vmap1) := splitMap mappings.vmap pc0.n
    let (dmap0, dmap1) := splitMap mappings.dmap pc0.darts.size
    (identifiedPc, ⟨vmap0, dmap0⟩, ⟨vmap1, dmap1⟩)

end PseudoConfiguration
end NearLinear4ct
