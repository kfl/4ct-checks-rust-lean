import NearLinear4ct.Util
import NearLinear4ct.Mapping

/-!
Combinatorial map (Appendix A.3 `freeHomomorphismTriangulation`, A.5 `fromVRotations`).

A `PseudoTriangulation` is a rotation system on `n` vertices built from darts
(half-edges). `Dart { head, rev, succ, pred }`:
- `head` -- the vertex this dart points at (always present);
- `rev`  -- the reverse dart (always present);
- `succ` / `pred` -- next / previous dart in the rotation around `head`, or `none`
  at a boundary (the C++ `nil = -1`).

In practice: `head`/`rev` are total `Nat`; `succ`/`pred` are `Option Nat`.
-/

namespace NearLinear4ct

/-- A half-edge. `head`/`rev` are total; `succ`/`pred` are `none` at a
boundary, encoded as `OptIdx` rather than `Option Nat` -- the unboxed encoding
that keeps the BFS's per-visit reads free of `Option`-cell RC (why it is
sound: `OptIdx.lean`). -/
structure Dart where
  head : Nat
  rev : Nat
  succ : OptIdx
  pred : OptIdx
deriving DecidableEq, Repr, Inhabited, BEq

namespace Dart

/-- All four dart fields point into the graph: `head` at a vertex (`< n`),
`rev` at a dart (`< D`), and `succ`/`pred` -- when present -- at darts. -/
structure InBounds (n D : Nat) (d : Dart) : Prop where
  head_lt : d.head < n
  rev_lt : d.rev < D
  succ_lt : ∀ j, d.succ.get? = Option.some j → j < D
  pred_lt : ∀ j, d.pred.get? = Option.some j → j < D

/-- Executable `InBounds` (the `succ`/`pred` clauses via `OptIdx.boundedBy`). -/
def inBoundsCheck (n D : Nat) (d : Dart) : Bool :=
  decide (d.head < n) && decide (d.rev < D)
    && d.succ.boundedBy D && d.pred.boundedBy D

/-- The executable check decides `InBounds`. -/
theorem inBoundsCheck_iff {n D : Nat} {d : Dart} :
    d.inBoundsCheck n D = true ↔ d.InBounds n D := by
  grind [inBoundsCheck, InBounds, OptIdx.boundedBy_iff]

end Dart

/-- A rotation system on `n` vertices. -/
structure PseudoTriangulation where
  n : Nat
  darts : Array Dart
deriving DecidableEq, Repr, Inhabited, BEq

/-- Format an optional index as a printed `int` dart (`-1` for nil), per `FORMAT.md`. -/
private def fmtIdx : OptIdx → String
  | .some v => toString v
  | .none => "-1"

/-- Follow the `succ` chain from `eStart`, collecting dart ids (the `getERotations`
inner do-while). A boundary chain is terminated by a trailing `none`. `partial`:
terminates on a finite rotation, but not structurally. -/
private partial def rotationGo (darts : Array Dart) (eStart eCur : Nat)
    (acc : Array (Option Nat)) : Array (Option Nat) :=
  let acc := acc.push (some eCur)
  match (darts[eCur]!).succ with
  | .none => acc.push none
  | .some nxt => if nxt == eStart then acc else rotationGo darts eStart nxt acc

namespace PseudoTriangulation

/-- Tier-1 graph well-formedness: every dart's indices are in bounds.
Index bounds ONLY -- no rotation-system laws. -/
def WF (pt : PseudoTriangulation) : Prop :=
  ∀ i (h : i < pt.darts.size), (pt.darts[i]'h).InBounds pt.n pt.darts.size

/-- Executable well-formedness check (`Test.lean` tripwires and
`WFConfig.attach!` boundary certification). -/
def wfCheck (pt : PseudoTriangulation) : Bool :=
  pt.darts.all fun d => d.inBoundsCheck pt.n pt.darts.size

/-- The executable check decides `WF`. -/
theorem wfCheck_iff {pt : PseudoTriangulation} : pt.wfCheck = true ↔ pt.WF := by
  grind [wfCheck, WF, Array.all_eq_true, Dart.inBoundsCheck_iff]

/-- An in-range panicking read has the bounds supplied by graph
well-formedness. -/
theorem WF.read_inBounds {pt : PseudoTriangulation} (h : pt.WF)
    {i : Nat} (hi : i < pt.darts.size) :
    (pt.darts[i]!).InBounds pt.n pt.darts.size := by
  simpa only [getElem!_pos pt.darts i hi] using h i hi

/-- Multi-line dump of every dart. -/
def debug (pt : PseudoTriangulation) : String := Id.run do
  let mut res := s!"N: {pt.n}\n"
  for d in pt.darts do
    res := res ++ s!"Dart({d.head}, {d.rev}, {fmtIdx d.succ}, {fmtIdx d.pred}),\n"
  return res

/-- Build from clockwise vertex rotations (A.5).

`rotations[a]` lists the neighbours of `a` clockwise; `-1` marks a boundary gap.
The two malformed-input checks become `panic!`: they signal a
corrupt input file, never a proof obligation, so the non-aborting `panic!` (loud
print) is acceptable here. -/
def fromVRotations (n : Nat) (rotations : Array (Array Int)) : PseudoTriangulation := Id.run do
  -- dartOf[a][b] = id of the dart a -> b, if any.
  let mut dartOf : Array (Array (Option Nat)) := Array.replicate n (Array.replicate n none)
  let mut fresh : Nat := 0
  for a in [0:n] do
    for b in rotations[a]! do
      if b == -1 then continue
      let b := b.toNat
      if (dartOf[a]!)[b]!.isSome then
        panic! s!"Multiple darts between {a} and {b}"
      dartOf := dartOf.set! a ((dartOf[a]!).set! b (some fresh))
      fresh := fresh + 1

  let mut darts : Array Dart := Array.replicate fresh ⟨0, 0, OptIdx.none, OptIdx.none⟩
  for a in [0:n] do
    let rot := rotations[a]!
    let size := rot.size
    for i in [0:size] do
      let b := rot[i]!
      if b == -1 then continue
      let b := b.toNat
      let e := ((dartOf[a]!)[b]!).get!
      let rev := match (dartOf[b]!)[a]! with
        | some r => r
        | none => panic! s!"Discrepancy in dart structure between {a} and {b}"
      -- clockwise-after / clockwise-before neighbour (cyclic), `-1` -> `none`
      let s := if i < size - 1 then rot[i + 1]! else rot[0]!
      let succ := if s != -1 then OptIdx.ofOption (dartOf[a]!)[s.toNat]! else OptIdx.none
      let p := if i > 0 then rot[i - 1]! else rot[size - 1]!
      let pred := if p != -1 then OptIdx.ofOption (dartOf[a]!)[p.toNat]! else OptIdx.none
      darts := darts.set! e ⟨a, rev, succ, pred⟩
  return ⟨n, darts⟩

/-- Side-by-side union, shifting `r`'s vertex/dart indices. -/
def disjointUnion (l r : PseudoTriangulation) : PseudoTriangulation :=
  let offset := l.darts.size
  let shifted := r.darts.map fun d =>
    ⟨d.head + l.n, d.rev + offset, d.succ.map (· + offset), d.pred.map (· + offset)⟩
  ⟨l.n + r.n, l.darts ++ shifted⟩

/-- Whether any dart is a self-loop (`head == rev's head`). -/
def hasLoop (pt : PseudoTriangulation) : Bool :=
  pt.darts.any fun d => d.head == (pt.darts[d.rev]!).head

/-- Number of darts pointing at each vertex. -/
def nIncidentDarts (pt : PseudoTriangulation) : Array Nat := Id.run do
  let mut cnt := Array.replicate pt.n 0
  for d in pt.darts do
    cnt := cnt.modify d.head (· + 1)
  return cnt

/-- Which vertices lie on a boundary, i.e. have a dart with no `succ`. -/
def isBoundary (pt : PseudoTriangulation) : Array Bool := Id.run do
  let mut b := Array.replicate pt.n false
  for d in pt.darts do
    if d.succ.isNone then
      b := b.set! d.head true
  return b

/-- First dart of `v` in rotation order (no `pred`); `none` if absent. -/
def firstDart (pt : PseudoTriangulation) (v : Nat) : Option Nat :=
  pt.darts.findIdx? fun d => d.head == v && d.pred.isNone

/-- Last dart of `v` (no `succ`). -/
def lastDart (pt : PseudoTriangulation) (v : Nat) : Option Nat :=
  pt.darts.findIdx? fun d => d.head == v && d.succ.isNone

/-- Any dart of `v`. -/
def anyDart (pt : PseudoTriangulation) (v : Nat) : Option Nat :=
  pt.darts.findIdx? fun d => d.head == v

/-- Whether `succ` and `pred` are mutually inverse where present (the
paper's M3). Both directions are scanned, so a one-sided link is caught even
when its partner is absent. -/
def linkInverseCheck (pt : PseudoTriangulation) : Bool :=
  (List.range pt.darts.size).all fun i =>
    (match (pt.darts[i]!).succ with
      | .some e => (pt.darts[e]!).pred == .some i
      | .none => true) &&
    (match (pt.darts[i]!).pred with
      | .some e => (pt.darts[e]!).succ == .some i
      | .none => true)

/-- Whether `succ` and `pred` stay within their dart's vertex (the paper's
M4). -/
def linkHeadCheck (pt : PseudoTriangulation) : Bool :=
  (List.range pt.darts.size).all fun i =>
    (match (pt.darts[i]!).succ with
      | .some e => (pt.darts[e]!).head == (pt.darts[i]!).head
      | .none => true) &&
    (match (pt.darts[i]!).pred with
      | .some e => (pt.darts[e]!).head == (pt.darts[i]!).head
      | .none => true)

/-- Vertices violating the paper's M6: each vertex has exactly one incidence
list -- cyclic when inner (no open corner), acyclic with a unique open corner
on each side when boundary. Reported per vertex, since intermediate states
may be locally malformed while the vertex under repair is the only one that
matters. The walk is fuelled by the dart count, so malformed links cannot
loop it; walks that leave the vertex are violations regardless of `M4`. -/
def incidenceListErrors (pt : PseudoTriangulation) : Array Nat := Id.run do
  let nInc := pt.nIncidentDarts
  let mut predOpen := Array.replicate pt.n 0
  let mut succOpen := Array.replicate pt.n 0
  for d in pt.darts do
    if d.pred.isNone then predOpen := predOpen.set! d.head (predOpen[d.head]! + 1)
    if d.succ.isNone then succOpen := succOpen.set! d.head (succOpen[d.head]! + 1)
  let mut bad : Array Nat := #[]
  for v in [0:pt.n] do
    if nInc[v]! == 0 then
      if predOpen[v]! != 0 || succOpen[v]! != 0 then bad := bad.push v
      continue
    if predOpen[v]! != succOpen[v]! || predOpen[v]! > 1 then
      bad := bad.push v
      continue
    let isB := predOpen[v]! == 1
    let start? := if isB then pt.firstDart v else pt.anyDart v
    match start? with
    | none => bad := bad.push v
    | some s =>
      let mut cur := s
      let mut count := 1
      let mut closed := false
      let mut stray := false
      for _ in [0:pt.darts.size] do
        match (pt.darts[cur]!).succ with
        | .none =>
          closed := isB
          break
        | .some nxt =>
          if nxt == s then
            closed := !isB
            break
          if (pt.darts[nxt]!).head != v then
            stray := true
            break
          cur := nxt
          count := count + 1
      if stray || !closed || count != nInc[v]! then bad := bad.push v
  return bad

/-- All-vertices form of `incidenceListErrors` (the paper's M6). -/
def incidenceListCheck (pt : PseudoTriangulation) : Bool :=
  pt.incidenceListErrors.isEmpty

/-- All three rotation-system laws (the paper's M3/M4/M6) at once. -/
def rotationLawsCheck (pt : PseudoTriangulation) : Bool :=
  pt.linkInverseCheck && pt.linkHeadCheck && pt.incidenceListCheck

/-- Follow `succ` `k` times from `e`; `none` if a boundary is hit. -/
def sucKTimes (pt : PseudoTriangulation) (e k : Nat) : Option Nat := Id.run do
  let mut curr := e
  for _ in [0:k] do
    match (pt.darts[curr]!).succ with
    | .none => return none
    | .some nxt => curr := nxt
  return some curr

/-- Untrusted reachability witnesses: a per-vertex start dart (one dart
scan, preferring a `pred`-open dart so boundary rotations start at their
first corner) and the per-dart walk index from that start; unset slots keep
the sentinel `darts.size`. Only the verifier `incidenceReachCheck` is
bridged, so this builder needs no specification -- a wrong witness merely
fails the check. -/
def walkWitness (pt : PseudoTriangulation) : Array Nat × Array Nat := Id.run do
  let sentinel := pt.darts.size
  let mut starts := Array.replicate pt.n sentinel
  for i in [0:pt.darts.size] do
    let d := pt.darts[i]!
    if d.pred.isNone || starts[d.head]! == sentinel then
      starts := starts.set! d.head i
  let mut idx := Array.replicate pt.darts.size sentinel
  for v in [0:pt.n] do
    let s := starts[v]!
    if s == sentinel then continue
    idx := idx.set! s 0
    let mut cur := s
    for k in [0:pt.darts.size] do
      match (pt.darts[cur]!).succ with
      | .none => break
      | .some nxt =>
        if nxt == s then break
        idx := idx.set! nxt (k + 1)
        cur := nxt
  return (starts, idx)

/-- Verified reachability: every dart's witness index is locally justified
-- an index `0` dart is its vertex's stored start, a positive index steps
back through `pred`. Any witness passing this scan proves each dart
connected to its vertex's start by induction on the index (with M3 turning
the `pred` edge forward), which is exactly the fiber connectivity the
conversion theorem turns into M6. Builder and scan are linear in vertices
plus darts. -/
def incidenceReachCheck (pt : PseudoTriangulation) : Bool :=
  let w := pt.walkWitness
  let starts := w.1
  let idx := w.2
  (List.range pt.darts.size).all fun d =>
    if idx[d]! == 0 then
      starts[(pt.darts[d]!).head]! == d
    else
      match (pt.darts[d]!).pred with
      | .some p => idx[p]! + 1 == idx[d]!
      | .none => false

/-- The certified gate for the rotation laws: the two link scans plus the
verified reachability witness. `rotationLawsCheck` stays the per-vertex
diagnostic for sweeps; this variant has the proof-friendly contract --
`rotationLawsCertify_rotational` converts a pass into
`DartGraph.Rotational` (and only that; validity is certified separately). -/
def rotationLawsCertify (pt : PseudoTriangulation) : Bool :=
  pt.linkInverseCheck && pt.linkHeadCheck && pt.incidenceReachCheck

/-- For each vertex, the cyclic rotation of its darts. A boundary rotation is
terminated by a trailing `none`. -/
def getERotations (pt : PseudoTriangulation) : Array (Array (Option Nat)) := Id.run do
  let isB := pt.isBoundary
  let mut result : Array (Array (Option Nat)) := Array.mkEmpty pt.n
  for v in [0:pt.n] do
    let eStart := (if isB[v]! then pt.firstDart v else pt.anyDart v).get!
    result := result.push (rotationGo pt.darts eStart eStart #[])
  return result

/-- Human-readable rotation view (renamed -- `show` is a Lean keyword). -/
def display (pt : PseudoTriangulation) : String := Id.run do
  let mut res := s!"N: {pt.n}\n"
  let edges := pt.darts.map fun d => (d.head, (pt.darts[d.rev]!).head)
  let eRot := pt.getERotations
  for v in [0:pt.n] do
    res := res ++ s!"{v}: "
    for dartId in eRot[v]! do
      match dartId with
      | none => res := res ++ "nil, "
      | some e => res := res ++ s!"e{e}({(edges[e]!).1}-{(edges[e]!).2}), "
    res := res ++ "\n"
  return res

/-- All darts from `head` to `tail`. -/
def getDarts (pt : PseudoTriangulation) (head tail : Nat) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  for i in [0:pt.darts.size] do
    let d := pt.darts[i]!
    if d.head == head && (pt.darts[d.rev]!).head == tail then
      result := result.push i
  return result

/-- Glue the `succ` links at the two representatives: both sides closed queues
a new gluing obligation; only the representative's side open copies the link
from the other dart; otherwise nothing changes.

`@[inline]` so the result pair vanishes at the call site and the array/queue
updates stay in place. -/
@[inline] def glueSucc (darts : Array Dart) (q : Queue (Nat × Nat))
    (eStar fStar : Nat) : Array Dart × Queue (Nat × Nat) :=
  match (darts[eStar]!).succ, (darts[fStar]!).succ with
  | .some e', .some f' => (darts, q.push (e', f'))
  | .some e', .none => (darts.set! fStar { darts[fStar]! with succ := .some e' }, q)
  | _, _ => (darts, q)

/-- As `glueSucc`, for the `pred` links. -/
@[inline] def gluePred (darts : Array Dart) (q : Queue (Nat × Nat))
    (eStar fStar : Nat) : Array Dart × Queue (Nat × Nat) :=
  match (darts[eStar]!).pred, (darts[fStar]!).pred with
  | .some e', .some f' => (darts, q.push (e', f'))
  | .some e', .none => (darts.set! fStar { darts[fStar]! with pred := .some e' }, q)
  | _, _ => (darts, q)

/-- The exit state of `freeHomomorphism`'s gluing worklist: the rewritten
darts and the two union-find forests, with the worklist exhausted. -/
structure HomomorphismClosure where
  darts : Array Dart
  ufV : Unionfind
  ufD : Unionfind

/-- The gluing closure of the requested dart identifications: the stateful
worklist phase of `freeHomomorphism`.

A `Queue` (`Util.Queue`) over the gluing obligations gives FIFO order (needed for
byte-identical results). -/
def glueClosure (pt : PseudoTriangulation) (dartPairs : Array (Nat × Nat)) :
    HomomorphismClosure := Id.run do
  let mut darts := pt.darts          -- copy: succ/pred get rewritten as we glue
  let mut ufV := Unionfind.new pt.n
  let mut ufD := Unionfind.new darts.size
  let mut q : Queue (Nat × Nat) := Queue.ofArray dartPairs
  while let some ((e, f), q') := q.pop? do
    q := q'
    if ufD.same e f then continue
    let hE := (darts[e]!).head
    let hF := (darts[f]!).head
    if !ufV.same hE hF then
      ufV := ufV.unite hE hF
    let eStar := ufD.root e
    let fStar := ufD.root f
    ufD := ufD.unite eStar fStar     -- fStar becomes the representative
    let eRev := (darts[eStar]!).rev
    let fRev := (darts[fStar]!).rev
    q := q.push (eRev, fRev)
    (darts, q) := glueSucc darts q eStar fStar
    (darts, q) := gluePred darts q eStar fStar
  return ⟨darts, ufV, ufD⟩

/-- The dart emitted for one surviving representative: `head` and `rev`
through the relabellings, `succ`/`pred` propagated directly (`dMap[s]!` is
already an `OptIdx`, so a boundary `none` stays `none`). -/
@[inline] def renumberDart (vMap dMap : IndexMap) (d : Dart) : Dart :=
  { head := (vMap[d.head]!).idx!
  , rev := (dMap[d.rev]!).idx!
  , succ := match d.succ with | .some s => dMap[s]! | .none => .none
  , pred := match d.pred with | .some p => dMap[p]! | .none => .none }

/-- The pure renumbering phase of `freeHomomorphism`: the two quotient
relabellings (`Unionfind.relabel`) and the quotient graph over the surviving
representatives. -/
def materialiseQuotient (c : HomomorphismClosure) :
    PseudoTriangulation × Mappings :=
  let vMap := c.ufV.relabel
  let dMap := c.ufD.relabel
  let dartsStar := c.ufD.allRoots.map fun d => renumberDart vMap dMap c.darts[d]!
  (⟨c.ufV.numRoots, dartsStar⟩, ⟨vMap, dMap⟩)

/-- Free homomorphism gluing the given dart pairs, returning the quotient and the
index `Mappings` onto it (A.3): the gluing worklist, then the renumbering of
the surviving representatives. -/
def freeHomomorphism (pt : PseudoTriangulation) (dartPairs : Array (Nat × Nat)) :
    PseudoTriangulation × Mappings :=
  materialiseQuotient (pt.glueClosure dartPairs)

/-- Free homomorphism over the disjoint union of `pt0`, `pt1`, identifying
`dartId0` (in `pt0`) with `dartId1` (in `pt1`); returns the quotient and the two
index maps restricted to each side. Named
`…Pair` since Lean lacks overloading. -/
def freeHomomorphismPair (pt0 pt1 : PseudoTriangulation) (dartId0 dartId1 : Nat) :
    PseudoTriangulation × Mappings × Mappings :=
  let pt := disjointUnion pt0 pt1
  let dartId1 := dartId1 + pt0.darts.size
  let (identifiedPt, mappings) := pt.freeHomomorphism #[(dartId0, dartId1)]
  let (vmap0, vmap1) := splitMap mappings.vmap pt0.n
  let (dmap0, dmap1) := splitMap mappings.dmap pt0.darts.size
  (identifiedPt, ⟨vmap0, dmap0⟩, ⟨vmap1, dmap1⟩)

end PseudoTriangulation
end NearLinear4ct
