import NearLinear4ct.PseudoTriangulation
import NearLinear4ct.Degree
import NearLinear4ct.SmallNatPair

/-!
Configuration with degrees (Appendix A.2 `homomorphism`, A.4
`dartIdentification` / `freeHomomorphism…` / `resolveDegreeIssues` + helpers).

This `extends` `PseudoTriangulation` -- both the fields (`pc.n`, `pc.darts`) **and**
the parent methods (`pc.firstDart v`, `pc.isBoundary`, …) are reachable by dot
notation (Lean falls through `extends` parents). The two names overridden by the
child (`debug`, `freeHomomorphism`) are reached on the parent explicitly via
`pc.toPseudoTriangulation.…`.

Scope: the methods that consume *derived* types (`Configuration`/`Rule`/
`CartWheel`) -- containment, charges, cartwheel combination -- are deferred (Lean
allows the mutual module reference, so they land as later additions). This file
is the self-contained core.
-/

namespace NearLinear4ct

/-- A pseudo-triangulation with a degree range per vertex. -/
structure PseudoConfiguration extends PseudoTriangulation where
  degrees : Array Degree
deriving DecidableEq, Repr, Inhabited, BEq

namespace PseudoConfiguration

/-- Construct from `(N, darts, degrees)`. -/
protected def new (n : Nat) (darts : Array Dart) (degrees : Array Degree) : PseudoConfiguration :=
  { toPseudoTriangulation := ⟨n, darts⟩, degrees := degrees }

/-- Configuration well-formedness: the graph is `WF` and the degree array
covers exactly the vertices. -/
def WF (pc : PseudoConfiguration) : Prop :=
  pc.toPseudoTriangulation.WF ∧ pc.degrees.size = pc.n

/-- Executable configuration check. -/
def wfCheck (pc : PseudoConfiguration) : Bool :=
  pc.toPseudoTriangulation.wfCheck && pc.degrees.size == pc.n

/-- The executable check decides `WF`. -/
theorem wfCheck_iff {pc : PseudoConfiguration} : pc.wfCheck = true ↔ pc.WF := by
  grind [wfCheck, WF, PseudoTriangulation.wfCheck_iff]

end PseudoConfiguration

/-- A configuration certified at the boundary: the graph and degree array
are well-formed and the dart count fits the packed-pair encoding (erased at
runtime). Certification happens once per object -- `attach!` runs the
executable checks where loaded and combined objects are built -- and the
homomorphism BFS and its lemmas read both facts off the type instead of
threading well-formedness premises. The resolution pipeline's intermediate
states stay raw and keep their proof-side preservation theorems. -/
structure WFConfig extends PseudoConfiguration where
  wfconfig_invariant :
    toPseudoConfiguration.WF
      ∧ toPseudoConfiguration.darts.size ≤ SmallNatPair.pairBase
deriving DecidableEq, Repr

namespace WFConfig

instance : Coe WFConfig PseudoConfiguration := ⟨toPseudoConfiguration⟩

/-- The certified graph and degree-array well-formedness. -/
theorem wf (c : WFConfig) : c.toPseudoConfiguration.WF :=
  c.wfconfig_invariant.1

/-- The certified packability bound (`fst_pack`/`snd_pack` decode below it). -/
theorem packable (c : WFConfig) : c.darts.size ≤ SmallNatPair.pairBase :=
  c.wfconfig_invariant.2

/-- Literal fields: no panicking reads in the initialiser. -/
instance : Inhabited WFConfig :=
  ⟨⟨⟨0, #[]⟩, #[]⟩, ⟨⟨fun i h => absurd h (by simp), rfl⟩, Nat.zero_le _⟩⟩

/-- Check-and-attach at a construction boundary: certify by the executable
checks, or print a `panic!` message and answer the default. The panic branch
is malformed input only -- every corpus object passes, and the I/O gates
additionally assert the stronger `darts.size ≤ 2^31`. -/
def attach! (pc : PseudoConfiguration) : WFConfig :=
  if h : pc.wfCheck && decide (pc.darts.size ≤ SmallNatPair.pairBase) then
    ⟨pc, PseudoConfiguration.wfCheck_iff.mp (by grind), by grind⟩
  else
    panic! "WFConfig.attach!: malformed configuration"

/-- Rebuild with a same-size degree array: the graph is untouched, so
certification transports (the size clause rewrites along `h`). The
degrees-only refinements use this instead of a re-check. -/
def withDegrees (c : WFConfig) (degrees : Array Degree)
    (h : degrees.size = c.degrees.size) : WFConfig :=
  ⟨{ c.toPseudoConfiguration with degrees := degrees },
   ⟨⟨c.wf.1, h.trans c.wf.2⟩, c.packable⟩⟩

end WFConfig

namespace PseudoConfiguration

/-- Multi-line dump. -/
def debug (pc : PseudoConfiguration) : String := Id.run do
  let mut res := pc.toPseudoTriangulation.debug
  for d in pc.degrees do
    res := res ++ s!"Degree({d.lower}, {d.upper}),\n"
  return res

/-- Human-readable rotation view with degrees. -/
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

/-- Each vertex's rotation as 0-based neighbour vertices, `-1` at the
boundary -- the view `fromVRotations` consumes, recovered from the dart
structure. -/
def getVRotations (pc : PseudoConfiguration) : Array (Array Int) := Id.run do
  let darts := pc.darts
  let eRotations := pc.getERotations
  let mut res : Array (Array Int) := Array.mkEmpty pc.n
  for v in [0:pc.n] do
    let mut rotV : Array Int := #[]
    for dartId in eRotations[v]! do
      match dartId with
      | none => rotV := rotV.push (-1)
      | some e => rotV := rotV.push ((darts[(darts[e]!).rev]!).head : Int)
    res := res.push rotV
  return res

/-- Build from vertex rotations + degrees.
The `degrees.size() == N` requirement is a caller precondition, kept implicit. -/
def fromVRotations (n : Nat) (vRotations : Array (Array Int)) (degrees : Array Degree) :
    PseudoConfiguration :=
  let pt := PseudoTriangulation.fromVRotations n vRotations
  PseudoConfiguration.new n pt.darts degrees

/-- Side-by-side union. -/
def disjointUnion (l r : PseudoConfiguration) : PseudoConfiguration :=
  let pt := PseudoTriangulation.disjointUnion l.toPseudoTriangulation r.toPseudoTriangulation
  PseudoConfiguration.new pt.n pt.darts (l.degrees ++ r.degrees)

/-- Queue the obligation `(s, s★)` when both links are interior (`some`); a
boundary link queues nothing. The conditional pushes of `homCoreGo`'s expand
step, named so the proofs speak about one operation instead of its match.

`@[noinline]`: inlined, the match arms duplicate the loop's continuation and
defeat borrow inference; as a call with scalar arguments the loop keeps its
borrowed parameters. -/
@[noinline] def pushLink
    (q : Queue SmallNatPair) : OptIdx → OptIdx → Queue SmallNatPair
  | .some s, .some sStar => q.push (SmallNatPair.pack s sStar)
  | _, _ => q

/-- One-step verdict of the homomorphism BFS: the next state, or the final
answer. It exists so the *proofs* can speak about a single, recursion-free
step.

`@[inline]` on `homStep` + the immediate `match` in `homCoreGo` means this
type never exists at runtime (case-of-known-constructor dissolves it). -/
inductive HomNext where
  | done (r : Option (IndexMap × IndexMap))
  | next (q : Queue SmallNatPair) (vmap dmap : IndexMap)

/-- One step of the homomorphism BFS (the pseudocode's loop body): pop one
obligation `(f, f★)` and process it -- re-check an already-mapped dart, or map
a fresh one and queue its `rev`/`succ`/`pred` obligations. The maps are
`Array OptIdx` and the worklist entries `SmallNatPair` (see those modules for
the encodings).

`@[inline]`: the step exists once in the source but compiles into its driver,
so `homCoreGo`'s loop is exactly the unfactored code. -/
@[inline] def homStep (src dst : WFConfig)
    (degreeTest : Degree → Degree → Bool)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : HomNext :=
  match q.pop? with
  | none => .done (some (vmap, dmap))
  | some (packed, q) =>
    let f := packed.fst
    let fStar := packed.snd
    match dmap[f]! with
    | .some d =>
      if d != fStar then .done none                  -- already mapped, inconsistently
      else .next q vmap dmap
    | .none =>
      let dmap := dmap.set! f (OptIdx.some fStar)
      -- bind each dart once (read 4×: head/rev/succ/pred)
      let srcD := src.darts[f]!
      let dstD := dst.darts[fStar]!
      let h := srcD.head
      let hStar := dstD.head
      let vv := vmap[h]!
      if vv.isSome && vv != OptIdx.some hStar then .done none
      else
        let vmap := vmap.set! h (OptIdx.some hStar)
        if !degreeTest (src.degrees[h]!) (dst.degrees[hStar]!) then .done none
        -- `src` side open where `dst` is closed ⇒ no homomorphism (the queue would
        -- be discarded on `.done none`, so failing before the pushes is equivalent).
        else if srcD.succ.isSome && dstD.succ.isNone then .done none
        else if srcD.pred.isSome && dstD.pred.isNone then .done none
        else
          let q := q.push (SmallNatPair.pack srcD.rev dstD.rev)
          let q := pushLink q srcD.succ dstD.succ
          let q := pushLink q srcD.pred dstD.pred
          .next q vmap dmap

/-- The worklist loop of the homomorphism BFS: drive `homStep` until it
answers -- the hottest loop in the program, kept as a bare tail call with the
state in explicit arguments rather than an `Id.run do`/`while` lowering.

`partial_fixpoint`: the worklist grows (each step pushes ≤ 3 darts), so the
recursion is not structural; the fixpoint exposes the `.partial_correctness`
principle the proofs ride on. *Not* total on malformed input -- an
out-of-bounds dart index makes `set!` a no-op and can loop; totality is
conditional on `WF`.

`@[specialize]` monomorphises `degreeTest` per call site. -/
@[specialize] def homCoreGo (src dst : WFConfig)
    (degreeTest : Degree → Degree → Bool)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Option (IndexMap × IndexMap) :=
  match homStep src dst degreeTest q vmap dmap with
  | .done r => r
  | .next q vmap dmap => homCoreGo src dst degreeTest q vmap dmap
partial_fixpoint

/-- Shared BFS core for `homomorphism` / `homomorphismExists` (A.2). Seeds the
worklist + the vertex (`[0,n)`) and dart
(`[0,darts.size)`) scratch maps and runs `homCoreGo`.
`homCoreGo`/`homCore` are internal to the BFS (not part of the public surface);
they are non-`private` only so `HomomorphismProofs.lean` can reason about them. -/
@[specialize] def homCore (src : WFConfig) (dartFrom : Nat)
    (dst : WFConfig) (dartTo : Nat)
    (degreeTest : Degree → Degree → Bool) : Option (IndexMap × IndexMap) :=
  homCoreGo src dst degreeTest
    ((Queue.emptyWithCapacity (src.darts.size * 3 + 1)).push (SmallNatPair.pack dartFrom dartTo))
    (Array.replicate src.n OptIdx.none)
    (Array.replicate src.darts.size OptIdx.none)

/-- Whether a homomorphism exists, accepting a vertex degree compatibility test.
The `.isSome`-only hot path
(`rootedContainConf`, `never/always/dominantlyApply`, `containX`) -- skips building
the result `Mappings` entirely. -/
@[inline] def homomorphismExists (src : WFConfig) (dartFrom : Nat)
    (dst : WFConfig) (dartTo : Nat)
    (degreeTest : Degree → Degree → Bool) : Bool :=
  (homCore src dartFrom dst dartTo degreeTest).isSome

/-- BFS graph homomorphism rooted at a dart pair (A.2). Returns the (possibly
partial) index maps if a homomorphism exists. -/
def homomorphism (src : WFConfig) (dartFrom : Nat)
    (dst : WFConfig) (dartTo : Nat)
    (degreeTest : Degree → Degree → Bool) : Option Mappings :=
  (homCore src dartFrom dst dartTo degreeTest).map fun (v, d) => ⟨v, d⟩

/-- Glue the dart pairs as a combinatorial map and reconcile degrees, if the
result is loop-free and degree-consistent (A.4.1). -/
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
bound (A.4.5). -/
def innerSubdegreeError (pc : PseudoConfiguration) : Bool := Id.run do
  let nIncident := pc.nIncidentDarts
  let isB := pc.isBoundary
  for v in [0:pc.n] do
    if !isB[v]! && decide ((nIncident[v]! : Int) < (pc.degrees[v]!).lower) then
      return true
  return false

/-- Find a fixed-degree vertex whose incidences need adjusting
(A.4.6). -/
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
(A.4.8). `none` on a boundary error (`u == w`). -/
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

/-- Resolve the single degree issue at `v` (A.4.7). The trailing `panic!` is
unreachable, since the caller only invokes this when one of the two cases holds. -/
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
(A.4.9). -/
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
(A.4.4). Results come back in FIFO (queue) order. -/
def resolveDegreeIssues (pc : PseudoConfiguration) : Array (PseudoConfiguration × Mappings) :=
    Id.run do
  let mut z : Array (PseudoConfiguration × Mappings) := #[]
  let initial := Mappings.initialMappings pc.n pc.darts.size
  let mut q : Queue (PseudoConfiguration × Mappings) := Queue.ofArray #[(pc, initial)]
  while let some ((zTilde, mappingsTilde), q') := q.pop? do
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
(A.4.3). -/
def freeHomomorphism (pc : PseudoConfiguration) (dartPairs : Array (Nat × Nat)) :
    Array (PseudoConfiguration × Mappings) :=
  match pc.dartIdentification dartPairs with
  | none => #[]
  | some (zStar, mappings) =>
    zStar.resolveDegreeIssues.map fun (zTilde, mappingsTilde) =>
      (zTilde, mappings.compose mappingsTilde)

/-- Free homomorphism over the disjoint union of `pc0`, `pc1`, identifying
`dartId0` (in `pc0`) with `dartId1` (in `pc1`); returns each result with the two
index maps restricted to each side. -/
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
