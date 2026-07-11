import NearLinear4ct.Util
import NearLinear4ct.Mapping

/-!
Phase 2 — combinatorial map. Port of `../src/pseudo_triangulation.{hpp,cpp}`
(Appendix A.3 `freeHomomorphismTriangulation`, A.5 `fromVRotations`).

A `PseudoTriangulation` is a rotation system on `n` vertices built from darts
(half-edges). `Dart { head, rev, succ, pred }`:
- `head` — the vertex this dart points at (always present);
- `rev`  — the reverse dart (always present);
- `succ` / `pred` — next / previous dart in the rotation around `head`, or `none`
  at a boundary (R1: the C++ `nil = -1`).

R1 in practice: `head`/`rev` are total `Nat`; `succ`/`pred` are `Option Nat`.
-/

namespace NearLinear4ct

/-- A half-edge. `head`/`rev` are total; `succ`/`pred` are `none` at a boundary. -/
structure Dart where
  head : Nat
  rev : Nat
  succ : Option Nat
  pred : Option Nat
deriving DecidableEq, Repr, Inhabited, BEq

/-- A rotation system on `n` vertices. -/
structure PseudoTriangulation where
  n : Nat
  darts : Array Dart
deriving DecidableEq, Repr, Inhabited, BEq

/-- Format an optional index the way the C++ printed `int` darts (`-1` for nil). -/
private def fmtIdx : Option Nat → String
  | some v => toString v
  | none => "-1"

/-- Follow the `succ` chain from `eStart`, collecting dart ids (`get_e_rotations`
inner do-while). A boundary chain is terminated by a trailing `none`. `partial`
(L5): terminates on a finite rotation, but not structurally. -/
private partial def rotationGo (darts : Array Dart) (eStart eCur : Nat)
    (acc : Array (Option Nat)) : Array (Option Nat) :=
  let acc := acc.push (some eCur)
  match (darts[eCur]!).succ with
  | none => acc.push none
  | some nxt => if nxt == eStart then acc else rotationGo darts eStart nxt acc

namespace PseudoTriangulation

/-- Multi-line dump of every dart (C++ `debug`). -/
def debug (pt : PseudoTriangulation) : String := Id.run do
  let mut res := s!"N: {pt.n}\n"
  for d in pt.darts do
    res := res ++ s!"Dart({d.head}, {d.rev}, {fmtIdx d.succ}, {fmtIdx d.pred}),\n"
  return res

/-- Build from clockwise vertex rotations (C++ `from_v_rotations`, A.5).

`rotations[a]` lists the neighbours of `a` clockwise; `-1` marks a boundary gap.
The two malformed-input checks (C++ `throw`) become `panic!`: they signal a
corrupt input file, never a proof obligation, so the non-aborting `panic!` (loud
print) is acceptable here (L1). -/
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

  let mut darts : Array Dart := Array.replicate fresh ⟨0, 0, none, none⟩
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
      let succ := if s != -1 then (dartOf[a]!)[s.toNat]! else none
      let p := if i > 0 then rot[i - 1]! else rot[size - 1]!
      let pred := if p != -1 then (dartOf[a]!)[p.toNat]! else none
      darts := darts.set! e ⟨a, rev, succ, pred⟩
  return ⟨n, darts⟩

/-- Side-by-side union, shifting `r`'s vertex/dart indices (C++ `disjoint_union`). -/
def disjointUnion (l r : PseudoTriangulation) : PseudoTriangulation :=
  let offset := l.darts.size
  let shifted := r.darts.map fun d =>
    ⟨d.head + l.n, d.rev + offset, d.succ.map (· + offset), d.pred.map (· + offset)⟩
  ⟨l.n + r.n, l.darts ++ shifted⟩

/-- Whether any dart is a self-loop (`head == rev's head`) (C++ `has_loop`). -/
def hasLoop (pt : PseudoTriangulation) : Bool :=
  pt.darts.any fun d => d.head == (pt.darts[d.rev]!).head

/-- Number of darts pointing at each vertex (C++ `n_incident_darts`). -/
def nIncidentDarts (pt : PseudoTriangulation) : Array Nat := Id.run do
  let mut cnt := Array.replicate pt.n 0
  for d in pt.darts do
    cnt := cnt.modify d.head (· + 1)
  return cnt

/-- Which vertices lie on a boundary, i.e. have a dart with no `succ`
(C++ `is_boundary`). -/
def isBoundary (pt : PseudoTriangulation) : Array Bool := Id.run do
  let mut b := Array.replicate pt.n false
  for d in pt.darts do
    if d.succ.isNone then
      b := b.set! d.head true
  return b

/-- First dart of `v` in rotation order (no `pred`); `none` if absent
(C++ `first_dart`, where `nil` -> `none`). -/
def firstDart (pt : PseudoTriangulation) (v : Nat) : Option Nat :=
  pt.darts.findIdx? fun d => d.head == v && d.pred.isNone

/-- Last dart of `v` (no `succ`) (C++ `last_dart`). -/
def lastDart (pt : PseudoTriangulation) (v : Nat) : Option Nat :=
  pt.darts.findIdx? fun d => d.head == v && d.succ.isNone

/-- Any dart of `v` (C++ `any_dart`). -/
def anyDart (pt : PseudoTriangulation) (v : Nat) : Option Nat :=
  pt.darts.findIdx? fun d => d.head == v

/-- Follow `succ` `k` times from `e`; `none` if a boundary is hit
(C++ `suc_k_times`). -/
def sucKTimes (pt : PseudoTriangulation) (e k : Nat) : Option Nat := Id.run do
  let mut curr := e
  for _ in [0:k] do
    match (pt.darts[curr]!).succ with
    | none => return none
    | some nxt => curr := nxt
  return some curr

/-- For each vertex, the cyclic rotation of its darts. A boundary rotation is
terminated by a trailing `none` (C++ `get_e_rotations`). -/
def getERotations (pt : PseudoTriangulation) : Array (Array (Option Nat)) := Id.run do
  let isB := pt.isBoundary
  let mut result : Array (Array (Option Nat)) := Array.mkEmpty pt.n
  for v in [0:pt.n] do
    let eStart := (if isB[v]! then pt.firstDart v else pt.anyDart v).get!
    result := result.push (rotationGo pt.darts eStart eStart #[])
  return result

/-- Human-readable rotation view (C++ `to_string`; renamed — `show` is a Lean
keyword). -/
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

/-- All darts from `head` to `tail` (C++ `get_darts`). -/
def getDarts (pt : PseudoTriangulation) (head tail : Nat) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  for i in [0:pt.darts.size] do
    let d := pt.darts[i]!
    if d.head == head && (pt.darts[d.rev]!).head == tail then
      result := result.push i
  return result

/-- Free homomorphism gluing the given dart pairs, returning the quotient and the
index `Mappings` onto it (C++ member `free_homomorphism`, A.3).

A `Queue` (`Util.Queue`) over the gluing obligations gives the C++ `std::queue`
FIFO order (needed for byte-identical results). -/
def freeHomomorphism (pt : PseudoTriangulation) (dartPairs : Array (Nat × Nat)) :
    PseudoTriangulation × Mappings := Id.run do
  let mut darts := pt.darts          -- copy: succ/pred get rewritten as we glue
  let mut ufV := Unionfind.new pt.n
  let mut ufD := Unionfind.new darts.size
  let mut q : Queue (Nat × Nat) := Queue.ofArray dartPairs
  while !q.isEmpty do
    let ((e, f), q') := q.pop!
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
    let eSucc := (darts[eStar]!).succ
    let fSucc := (darts[fStar]!).succ
    if let (some es, some fs) := (eSucc, fSucc) then
      q := q.push (es, fs)
    let ePred := (darts[eStar]!).pred
    let fPred := (darts[fStar]!).pred
    if let (some ep, some fp) := (ePred, fPred) then
      q := q.push (ep, fp)
    -- fill in the representative's open sides from the other dart
    if eSucc.isSome && fSucc.isNone then
      darts := darts.set! fStar { darts[fStar]! with succ := eSucc }
    if ePred.isSome && fPred.isNone then
      darts := darts.set! fStar { darts[fStar]! with pred := ePred }

  -- renumber survivors: each_root (total, lifted to `some`) ∘ index_roots (compacted)
  let vMap := composeMap (ufV.eachRoot.map OptIdx.some) ufV.indexRoots
  let dMap := composeMap (ufD.eachRoot.map OptIdx.some) ufD.indexRoots
  let mut dartsStar : Array Dart := #[]
  for d in ufD.allRoots do
    let dd := darts[d]!
    let hd := (vMap[dd.head]!).idx!
    let rv := (dMap[dd.rev]!).idx!
    let succ := dd.succ.bind fun s => (dMap[s]!).get?
    let pred := dd.pred.bind fun p => (dMap[p]!).get?
    dartsStar := dartsStar.push ⟨hd, rv, succ, pred⟩
  return (⟨ufV.numRoots, dartsStar⟩, ⟨vMap, dMap⟩)

/-- Free homomorphism over the disjoint union of `pt0`, `pt1`, identifying
`dartId0` (in `pt0`) with `dartId1` (in `pt1`); returns the quotient and the two
index maps restricted to each side (C++ static `free_homomorphism`). Named
`…Pair` since Lean lacks the C++ overload. -/
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
