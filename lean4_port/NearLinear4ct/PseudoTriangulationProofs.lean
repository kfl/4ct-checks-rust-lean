import NearLinear4ct.Configuration
import NearLinear4ct.MappingProofs
import NearLinear4ct.UtilProofs
import Std.Tactic.Do

/-!
Tier-1 well-formedness of the combinatorial map.

`Dart.InBounds` / `PseudoTriangulation.WF` / `PseudoConfiguration.WF` state
**index bounds only**: every `head` names a vertex, every `rev`/`succ`/`pred`
names a dart. No rotation-system laws (rev involution, succ/pred inverse) are
stated -- those are tier-2 and must first be falsified empirically on the
corpus, since intermediates of the gluing (A.3) may violate them.

This is the graph-side counterpart of `IndexMap.WF` (`MappingProofs.lean`),
and it is exactly the hypothesis the `homCoreGo` termination argument needs:
on a `WF` graph every worklist push (`rev`/`succ`/
`pred`, Algorithm A.2) stays in `[0, darts.size)`, so `dmap.set!` always
marks. Three layers, as in `MappingProofs`:

- Props (`InBounds`/`WF`) in `Nat`-with-bounds vocabulary;
- executable checkers (`inBoundsCheck`/`wfCheck`) with decidability bridges
  (`_iff`), for `Test.lean` tripwires and I/O-boundary `proofAssert`s;
- `Fin`-typed read-only views (`headOf`/`revOf`/`succOf?`/`predOf?`), each
  taking the `WF` proof -- zero runtime presence, but they let the
  homomorphism-soundness statement (`HomomorphismProofs.lean`) be *written*
  against total functions between finite index sets (a rooted graph map
  `Fin |D_src| → Fin |D_dst|`).

Preservation: `disjointUnion` (A.3's side-by-side union) and the
configuration `mirror` keep `WF`.
-/

namespace NearLinear4ct

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

/-- `InBounds` weakens along larger index sets. -/
theorem InBounds.mono {n D n' D' : Nat} {d : Dart}
    (h : d.InBounds n D) (hn : n ≤ n') (hD : D ≤ D') : d.InBounds n' D' := by
  grind [InBounds]

end Dart

namespace PseudoTriangulation

/-- Tier-1 graph well-formedness: every dart's indices are in bounds.
Index bounds ONLY -- no rotation-system laws. -/
def WF (pt : PseudoTriangulation) : Prop :=
  ∀ i (h : i < pt.darts.size), (pt.darts[i]'h).InBounds pt.n pt.darts.size

/-- Executable well-formedness check (`Test.lean` tripwires; boundary
`proofAssert` if a graph ever crosses the I/O boundary). -/
def wfCheck (pt : PseudoTriangulation) : Bool :=
  pt.darts.all fun d => d.inBoundsCheck pt.n pt.darts.size

/-- The executable check decides `WF`. -/
theorem wfCheck_iff {pt : PseudoTriangulation} : pt.wfCheck = true ↔ pt.WF := by
  grind [wfCheck, WF, Array.all_eq_true, Dart.inBoundsCheck_iff]

/-! ### Fin-typed read-only views

Each takes the `WF` proof and decodes a raw field into `Fin` -- the graph-side
analogue of `IndexMap.toFun` (`MappingProofs.lean`). Proof-carrying only: no
runtime code calls these; their purpose is that the homomorphism-soundness
statement (`HomomorphismProofs.lean`) can be written against total functions
between finite index sets.
Each has a `_val` coherence lemma tying the view to the raw field, so every
view theorem is a transport of a raw-field theorem (the `toFun_val`
pattern). -/

/-- The vertex a dart points at, as a function `Fin |D| → Fin n`. -/
def headOf (pt : PseudoTriangulation) (h : pt.WF) (f : Fin pt.darts.size) :
    Fin pt.n :=
  ⟨(pt.darts[f.val]'f.isLt).head, (h f.val f.isLt).head_lt⟩

@[simp] theorem headOf_val {pt : PseudoTriangulation} (h : pt.WF)
    (f : Fin pt.darts.size) :
    (pt.headOf h f).val = (pt.darts[f.val]'f.isLt).head := rfl

/-- The reverse dart, as a function `Fin |D| → Fin |D|`. -/
def revOf (pt : PseudoTriangulation) (h : pt.WF) (f : Fin pt.darts.size) :
    Fin pt.darts.size :=
  ⟨(pt.darts[f.val]'f.isLt).rev, (h f.val f.isLt).rev_lt⟩

@[simp] theorem revOf_val {pt : PseudoTriangulation} (h : pt.WF)
    (f : Fin pt.darts.size) :
    (pt.revOf h f).val = (pt.darts[f.val]'f.isLt).rev := rfl

/-- The next dart in the rotation (`none` at a boundary), decoded to
`Option (Fin |D|)`. -/
def succOf? (pt : PseudoTriangulation) (h : pt.WF) (f : Fin pt.darts.size) :
    Option (Fin pt.darts.size) :=
  (pt.darts[f.val]'f.isLt).succ.toFin? (h f.val f.isLt).succ_lt

/-- Coherence: `succOf?` is the raw `succ` under `Fin.val`. -/
theorem succOf?_val {pt : PseudoTriangulation} (h : pt.WF)
    (f : Fin pt.darts.size) :
    (pt.succOf? h f).map Fin.val = (pt.darts[f.val]'f.isLt).succ.get? := by
  unfold succOf?
  simp

/-- The previous dart in the rotation (`none` at a boundary), decoded to
`Option (Fin |D|)`. -/
def predOf? (pt : PseudoTriangulation) (h : pt.WF) (f : Fin pt.darts.size) :
    Option (Fin pt.darts.size) :=
  (pt.darts[f.val]'f.isLt).pred.toFin? (h f.val f.isLt).pred_lt

/-- Coherence: `predOf?` is the raw `pred` under `Fin.val`. -/
theorem predOf?_val {pt : PseudoTriangulation} (h : pt.WF)
    (f : Fin pt.darts.size) :
    (pt.predOf? h f).map Fin.val = (pt.darts[f.val]'f.isLt).pred.get? := by
  unfold predOf?
  simp

/-! ### Preservation -/

/-- The shifted copy `disjointUnion` makes of a right-side dart stays in
bounds: vertices shift past the `n'` left vertices, darts past the `D'` left
darts. -/
private theorem dart_shift_inBounds {n D n' D' : Nat} {d : Dart}
    (h : d.InBounds n D) :
    Dart.InBounds (n' + n) (D' + D)
      ⟨d.head + n', d.rev + D', d.succ.map (· + D'), d.pred.map (· + D')⟩ := by
  grind [Dart.InBounds, OptIdx.get?_map, Option.map_eq_some_iff]

/-- `disjointUnion`'s fields, definitionally (the `let`s zeta-reduced), so
`simp` can rewrite under `getElem`. -/
private theorem disjointUnion_n (l r : PseudoTriangulation) :
    (l.disjointUnion r).n = l.n + r.n := rfl

private theorem disjointUnion_darts (l r : PseudoTriangulation) :
    (l.disjointUnion r).darts
      = l.darts ++ r.darts.map (fun d =>
          ⟨d.head + l.n, d.rev + l.darts.size,
           d.succ.map (· + l.darts.size), d.pred.map (· + l.darts.size)⟩) := rfl

/-- `disjointUnion` (A.3's side-by-side union) preserves well-formedness:
the left copy's bounds weaken into the union, the right copy's shift by
`l.n` / `l.darts.size` lands past the left block. -/
theorem disjointUnion_wf {l r : PseudoTriangulation}
    (hl : l.WF) (hr : r.WF) : (l.disjointUnion r).WF := by
  intro i h
  by_cases hi : i < l.darts.size
  · grind [WF, disjointUnion_darts, disjointUnion_n, Dart.InBounds.mono]
  · have hd := dart_shift_inBounds (n' := l.n) (D' := l.darts.size)
        (hr (i - l.darts.size) (by grind [disjointUnion_darts]))
    grind [WF, disjointUnion_darts, disjointUnion_n]

/-! ### Construction

`fromVRotations` (A.1's rotation-system loader) produces a `WF` triangulation.
The proof runs `Std.Do`'s `mvcgen` over the two-phase `do`-block: phase 1 builds
the `dartOf`/`fresh` id table, phase 2 emits one `Dart` per id. The two loop
invariants -- `DartOfWF` for phase 1, structural `InBounds` for phase 2 -- are
threaded automatically; every dart bound flows from the id table, so no
hypothesis on the *rotation entries* is needed. -/

section Construction
open Std.Do
set_option mvcgen.warning false

/-- `wp` of a `panic` in `Id`: it reduces to the default value. `Std.Do` ships
no `panic` spec, so this is the reusable one-liner. -/
@[local simp] private theorem wp_panicWithPosWithDecl {α} [Inhabited α]
    (m d : String) (l c : Nat) (s : String) (Q : PostCond α PostShape.pure) :
    wp⟦(panicWithPosWithDecl m d l c s : Id α)⟧ Q = Q.1 default := rfl

/-- Value-level `panic` in `Nat` *is* the default, `0`. `grind` treats `panic`
as opaque, so a case split into a `panic!` branch needs this to close. -/
@[local simp] private theorem panicWithPosWithDecl_nat
    (m d : String) (l c : Nat) (s : String) :
    (panicWithPosWithDecl m d l c s : Nat) = 0 := rfl

/-- `getElem!` after `setIfInBounds`: the reusable `!`-form bridge (Std ships
only the proof-carrying `getElem_setIfInBounds`). -/
private theorem getElem!_setIfInBounds {α} [Inhabited α] (xs : Array α)
    (i j : Nat) (a : α) :
    (xs.setIfInBounds i a)[j]! = if i = j ∧ j < xs.size then a else xs[j]! := by
  by_cases hj : j < xs.size
  · rw [getElem!_pos (xs.setIfInBounds i a) j (by rw [Array.size_setIfInBounds]; exact hj),
      getElem!_pos xs j hj, Array.getElem_setIfInBounds]
    all_goals grind
  · rw [getElem!_neg (xs.setIfInBounds i a) j (by rw [Array.size_setIfInBounds]; exact hj),
      getElem!_neg xs j hj]
    grind

/-- `getElem!` into a nested `replicate` is `none`. -/
private theorem getElem!_replicate_replicate {n a b : Nat} :
    ((Array.replicate n (Array.replicate n (none : Option Nat)))[a]!)[b]! = none := by
  by_cases ha : a < n
  · rw [getElem!_pos _ a (by simpa using ha), Array.getElem_replicate]
    by_cases hb : b < n
    · rw [getElem!_pos _ b (by simpa using hb), Array.getElem_replicate]
    · rw [getElem!_neg _ b (by simpa using hb)]; rfl
  · rw [getElem!_neg _ a (by simpa using ha)]; rfl

/-- Phase-1 loop invariant: the id table has the right shape and every id it
hands out is `< fresh` (so it indexes into the phase-2 dart array). -/
private def DartOfWF (n : Nat) (dartOf : Array (Array (Option Nat))) (fresh : Nat) : Prop :=
  dartOf.size = n ∧ (∀ a, a < n → (dartOf[a]!).size = n) ∧
  (∀ (a b v : Nat), (dartOf[a]!)[b]! = some v → v < fresh) ∧
  (0 < fresh → 0 < n)

private theorem dartOfWF_init (n : Nat) :
    DartOfWF n (Array.replicate n (Array.replicate n none)) 0 := by
  grind [DartOfWF, getElem!_replicate_replicate]

private theorem dartOfWF_set (n : Nat) (dartOf : Array (Array (Option Nat)))
    (fresh a b : Nat) (hwf : DartOfWF n dartOf fresh) (ha : a < n) :
    DartOfWF n (dartOf.setIfInBounds a ((dartOf[a]!).setIfInBounds b (some fresh)))
      (fresh + 1) := by
  grind [DartOfWF, getElem!_setIfInBounds]

/-- Every dart in the initial `replicate`-filled array is in bounds (all fields
are `0`/`none`; `head = 0 < n` holds because `fresh > 0 ⇒ n > 0`). -/
private theorem inBounds_replicate_default (n fresh : Nat) (d : Dart)
    (hd : d.head = 0 ∧ d.rev = 0 ∧ d.succ = OptIdx.none ∧ d.pred = OptIdx.none)
    (hn : 0 < fresh → 0 < n) (i : Nat) (hi : i < (Array.replicate fresh d).size) :
    ((Array.replicate fresh d)[i]'hi).InBounds n (Array.replicate fresh d).size := by
  grind [Dart.InBounds, Array.size_replicate, OptIdx.get?_none]

/-- `InBounds` is preserved by a phase-2 write, provided the written dart is in
bounds whenever its target index is valid. -/
private theorem inBounds_set (n : Nat) (darts : Array Dart) (e : Nat) (d : Dart)
    (hIH : ∀ i (hi : i < darts.size), (darts[i]'hi).InBounds n darts.size)
    (hd : e < darts.size → d.InBounds n darts.size) (i : Nat)
    (hi : i < (darts.setIfInBounds e d).size) :
    ((darts.setIfInBounds e d)[i]'hi).InBounds n (darts.setIfInBounds e d).size := by
  rw [Array.size_setIfInBounds] at hi ⊢
  rw [Array.getElem_setIfInBounds]
  split
  · rename_i he; exact hd (by omega)
  · exact hIH i hi

/-- Membership in the legacy range's list bounds the element. -/
private theorem lt_of_mem_range_toList {n cur : Nat} {pref suff : List Nat}
    (h : [0:n].toList = pref ++ cur :: suff) : cur < n := by
  have : cur ∈ ([0:n] : Std.Legacy.Range).toList := by rw [h]; simp
  simpa [Std.Legacy.Range.toList] using this

section
-- The transparency linter flags `mvcgen`'s own `Invariant` encoding (the `⇓`
-- postconditions), not this proof's text; nothing here to rephrase.
set_option linter.tacticCheckInstances false

/-- `fromVRotations` always produces a well-formed triangulation, *regardless*
of whether the input rotations are valid: structural `InBounds` follows entirely
from the phase-1 `DartOfWF` invariant (dart ids `< fresh = darts.size`) and range
membership (`head = cur < n`), never from the rotation entries themselves. -/
theorem fromVRotations_wf (n : Nat) (rotations : Array (Array Int)) :
    (PseudoTriangulation.fromVRotations n rotations).WF := by
  generalize h : PseudoTriangulation.fromVRotations n rotations = pt
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨_xs, dartOf, fresh⟩ => ⌜DartOfWF n dartOf fresh⌝
  case inv2 => exact ⇓⟨_xs, dartOf, fresh⟩ => ⌜DartOfWF n dartOf fresh⌝
  case inv3 => exact ⇓⟨_xs, darts⟩ =>
    ⌜darts.size = (‹MProd (Array (Array (Option Nat))) Nat›).snd ∧
      ∀ i (hi : i < darts.size), (darts[i]'hi).InBounds n darts.size⌝
  case inv4 => exact ⇓⟨_xs, darts⟩ =>
    ⌜darts.size = (‹MProd (Array (Array (Option Nat))) Nat›).snd ∧
      ∀ i (hi : i < darts.size), (darts[i]'hi).InBounds n darts.size⌝
  all_goals mleave
  case vc6 => exact dartOfWF_init n
  case vc2 => exact dartOfWF_set n _ _ _ _ (by assumption) (lt_of_mem_range_toList (by assumption))
  case vc3 => exact dartOfWF_set n _ _ _ _ (by assumption) (lt_of_mem_range_toList (by assumption))
  case vc11 =>
    rename_i r hwf
    exact ⟨by simp, fun i hi =>
      inBounds_replicate_default n r.snd _ ⟨rfl, rfl, rfl, rfl⟩ hwf.2.2.2 i hi⟩
  case vc12 => rename_i hinv; exact hinv.2
  case vc8 =>
    have hinv := ‹_ ∧ ∀ _ (_ : _ < _), Dart.InBounds n _ _›
    have hwf : DartOfWF n _ _ := ‹DartOfWF n _ _›
    obtain ⟨hsz, hIH⟩ := hinv
    refine ⟨by grind [Array.size_setIfInBounds], ?_⟩
    apply inBounds_set n _ _ _ hIH
    intro he
    refine ⟨lt_of_mem_range_toList (by assumption), ?_, ?_, ?_⟩ <;>
      simp only [hsz] <;>
      grind [DartOfWF, OptIdx.get?_ofOption, OptIdx.get?_none, panicWithPosWithDecl_nat]
  all_goals assumption

end

end Construction

/-! ### Gluing

`freeHomomorphism` (A.3) drives a worklist of dart identifications. The maps
it returns are the union-find relabellings, already proved total and
well-formed for any well-formed forest (`Unionfind.relabel_wf`) -- so the
theorem reduces to carrying `GlueInv` (sizes pinned, forests `Unionfind.WF`,
darts in bounds, queued pairs in range) through the loop. Termination: each
glue merges two dart classes (`numRoots` drops), each skip pops an obligation
(`live` drops), so `3 * numRoots + live` strictly decreases. -/

section Gluing
open Std.Do
set_option mvcgen.warning false

/-- Loop invariant of the gluing BFS. -/
structure GlueInv (pt : PseudoTriangulation) (darts : Array Dart)
    (ufV ufD : Unionfind) (q : Queue (Nat × Nat)) : Prop where
  darts_size : darts.size = pt.darts.size
  ufV_n : ufV.n = pt.n
  ufD_n : ufD.n = pt.darts.size
  ufV_wf : ufV.WF
  ufD_wf : ufD.WF
  darts_wf : ∀ i (h : i < darts.size), (darts[i]'h).InBounds pt.n darts.size
  queued : ∀ p, q.Active p → p.1 < pt.darts.size ∧ p.2 < pt.darts.size

/-- The packed-state form of the loop's mutable tuple `⟨darts, q, ufD, ufV⟩`. -/
private abbrev GlueState :=
  MProd (Array Dart) (MProd (Queue (Nat × Nat)) (MProd Unionfind Unionfind))

/-- `GlueInv` over the packed loop state, on both cursor sides (the break
side carries the same facts). Defined by `match` so it reduces on the
`Sum` constructor and exposes clean state projections. -/
private def GlueInvSum (pt : PseudoTriangulation) : GlueState ⊕ GlueState → Prop
  | .inl s => GlueInv pt s.fst s.snd.snd.snd s.snd.snd.fst s.snd.fst
  | .inr s => GlueInv pt s.fst s.snd.snd.snd s.snd.snd.fst s.snd.fst

/-- The termination measure over the packed loop state: each glue merges two
dart classes, each skip pops an obligation. -/
private def glueMeasure (s : GlueState) : Nat :=
  3 * s.snd.snd.fst.numRoots + s.snd.fst.live

/-- Popping preserves the invariant (the active set shrinks). -/
private theorem GlueInv.pop {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q q' : Queue (Nat × Nat)} {x : Nat × Nat}
    (hp : q.pop? = some (x, q')) (h : GlueInv pt darts ufV ufD q) :
    GlueInv pt darts ufV ufD q' :=
  ⟨h.darts_size, h.ufV_n, h.ufD_n, h.ufV_wf, h.ufD_wf, h.darts_wf,
   fun p hp' => h.queued p (Queue.active_pop hp hp')⟩

/-- Pushing an in-range pair preserves the invariant. -/
private theorem GlueInv.push {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {x : Nat × Nat}
    (h : GlueInv pt darts ufV ufD q)
    (hx : x.1 < pt.darts.size ∧ x.2 < pt.darts.size) :
    GlueInv pt darts ufV ufD (q.push x) :=
  ⟨h.darts_size, h.ufV_n, h.ufD_n, h.ufV_wf, h.ufD_wf, h.darts_wf,
   fun p hp' => (Queue.active_push hp').elim (h.queued p) (· ▸ hx)⟩

/-- Uniting two in-range vertices preserves the invariant. -/
private theorem GlueInv.uniteV {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {a b : Nat}
    (h : GlueInv pt darts ufV ufD q) (ha : a < pt.n) (hb : b < pt.n) :
    GlueInv pt darts (ufV.unite a b) ufD q := by
  grind [GlueInv, Unionfind.WF.unite, Unionfind.n_unite]

/-- Dart representatives stay in the fixed original dart range. -/
private theorem GlueInv.root_lt {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} (h : GlueInv pt darts ufV ufD q)
    {i : Nat} (hi : i < pt.darts.size) : ufD.root i < pt.darts.size :=
  h.ufD_n ▸ h.ufD_wf.root_lt (h.ufD_n.symm ▸ hi)

/-- Uniting the representatives of two in-range darts preserves the invariant. -/
private theorem GlueInv.uniteD {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {e f : Nat}
    (h : GlueInv pt darts ufV ufD q)
    (he : e < pt.darts.size) (hf : f < pt.darts.size) :
    GlueInv pt darts ufV (ufD.unite (ufD.root e) (ufD.root f)) q := by
  have hre := h.root_lt he
  have hrf := h.root_lt hf
  grind [GlueInv, Unionfind.WF.unite, Unionfind.n_unite]

/-- Rewriting one dart in bounds preserves the invariant. -/
private theorem GlueInv.fill {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {j : Nat} {d : Dart}
    (h : GlueInv pt darts ufV ufD q)
    (hd : j < darts.size → d.InBounds pt.n darts.size) :
    GlueInv pt (darts.set! j d) ufV ufD q := by
  grind [GlueInv, inBounds_set]

/-- In-range `!`-reads inherit the invariant's dart bounds. -/
private theorem GlueInv.read_inBounds {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} (h : GlueInv pt darts ufV ufD q)
    {i : Nat} (hi : i < pt.darts.size) : (darts[i]!).InBounds pt.n darts.size := by
  grind [GlueInv]

/-- `succ_lt`, keyed on the equation shape the loop's `match` hypotheses have,
so `grind` can instantiate it. -/
private theorem succ_some_lt {n D : Nat} {d : Dart} {j : Nat}
    (h : d.InBounds n D) (hs : d.succ = OptIdx.some j) : j < D :=
  h.succ_lt j (by simp [hs])

/-- `pred_lt` in match-equation form (see `succ_some_lt`). -/
private theorem pred_some_lt {n D : Nat} {d : Dart} {j : Nat}
    (h : d.InBounds n D) (hs : d.pred = OptIdx.some j) : j < D :=
  h.pred_lt j (by simp [hs])

/-- The glue step's shared core: popping a not-yet-merged active pair `(e, f)`
keeps the invariant through the dart-unite and the reverse push, and supplies
what the rest of the step consumes: the two head bounds (vertex unite), the
two representative bounds (`glueSucc`/`gluePred`), and the strict root-count
drop (the measure). -/
private theorem GlueInv.glue {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q q' : Queue (Nat × Nat)} {e f : Nat}
    (hpop : q.pop? = some ((e, f), q')) (hsame : ¬ ufD.same e f = true)
    (h : GlueInv pt darts ufV ufD q) :
    GlueInv pt darts ufV (ufD.unite (ufD.root e) (ufD.root f))
        (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
      ∧ ((darts[e]!).head < pt.n ∧ (darts[f]!).head < pt.n)
      ∧ (ufD.root e < pt.darts.size ∧ ufD.root f < pt.darts.size)
      ∧ (ufD.unite (ufD.root e) (ufD.root f)).numRoots < ufD.numRoots := by
  have hef := h.queued _ (Queue.active_head hpop)
  have hre := h.root_lt hef.1
  have hrf := h.root_lt hef.2
  refine ⟨((h.pop hpop).uniteD hef.1 hef.2).push
      ⟨h.darts_size ▸ (h.read_inBounds hre).rev_lt,
       h.darts_size ▸ (h.read_inBounds hrf).rev_lt⟩,
    ⟨(h.read_inBounds hef.1).head_lt, (h.read_inBounds hef.2).head_lt⟩,
    ⟨hre, hrf⟩,
    Unionfind.numRoots_unite_root_lt h.ufD_wf (by grind [GlueInv])
      (by grind [GlueInv]) ((Bool.not_eq_true _) ▸ hsame)⟩

/-- Contract for `glueSucc`: it preserves the invariant and adds at most one
queue obligation. -/
private theorem glueSucc_spec {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar : Nat}
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size) :
    GlueInv pt (glueSucc darts q eStar fStar).1 ufV ufD
        (glueSucc darts q eStar fStar).2
      ∧ (glueSucc darts q eStar fStar).2.live ≤ q.live + 1 := by
  have hbe := h.read_inBounds he
  have hbf := h.read_inBounds hf
  unfold glueSucc
  split
  · exact ⟨h.push ⟨h.darts_size ▸ succ_some_lt hbe ‹_›,
      h.darts_size ▸ succ_some_lt hbf ‹_›⟩, Nat.le_of_eq Queue.live_push⟩
  · exact ⟨h.fill fun _ => ⟨hbf.head_lt, hbf.rev_lt,
      fun j hj => Option.some.inj hj ▸ succ_some_lt hbe ‹_›, hbf.pred_lt⟩,
      Nat.le_succ _⟩
  · exact ⟨h, Nat.le_succ _⟩

/-- The corresponding contract for `gluePred`. -/
private theorem gluePred_spec {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar : Nat}
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size) :
    GlueInv pt (gluePred darts q eStar fStar).1 ufV ufD
        (gluePred darts q eStar fStar).2
      ∧ (gluePred darts q eStar fStar).2.live ≤ q.live + 1 := by
  have hbe := h.read_inBounds he
  have hbf := h.read_inBounds hf
  unfold gluePred
  split
  · exact ⟨h.push ⟨h.darts_size ▸ pred_some_lt hbe ‹_›,
      h.darts_size ▸ pred_some_lt hbf ‹_›⟩, Nat.le_of_eq Queue.live_push⟩
  · exact ⟨h.fill fun _ => ⟨hbf.head_lt, hbf.rev_lt, hbf.succ_lt,
      fun j hj => Option.some.inj hj ▸ pred_some_lt hbe ‹_›⟩,
      Nat.le_succ _⟩
  · exact ⟨h, Nat.le_succ _⟩

/-- The two adjacency-link operations preserve the invariant and together add
at most two queue obligations. -/
private theorem glueBoth_spec {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar : Nat}
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size) :
    let succ := glueSucc darts q eStar fStar
    let pred := gluePred succ.1 succ.2 eStar fStar
    GlueInv pt pred.1 ufV ufD pred.2 ∧ pred.2.live ≤ q.live + 2 := by
  grind only [gluePred_spec, glueSucc_spec]

/-- One renumber step: on the loop's exit state, the dart pushed for a
surviving representative is in bounds for the quotient -- `head` through the
total vertex relabelling, `rev` through the total dart relabelling, and open
`succ`/`pred` links through its `Bounded` half. -/
private theorem renumber_push_inBounds {pt : PseudoTriangulation}
    {darts : Array Dart} {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    (h : GlueInv pt darts ufV ufD q) {d : Nat} (hd : d < pt.darts.size) :
    let vMap := composeMap (ufV.eachRoot.map OptIdx.some) ufV.indexRoots
    let dMap := composeMap (ufD.eachRoot.map OptIdx.some) ufD.indexRoots
    let dd := darts[d]!
    Dart.InBounds ufV.numRoots ufD.numRoots
      { head := (vMap[dd.head]!).idx!
      , rev := (dMap[dd.rev]!).idx!
      , succ := match dd.succ with
          | .some s => dMap[s]!
          | .none => .none
      , pred := match dd.pred with
          | .some p => dMap[p]!
          | .none => .none } := by
  intro vMap dMap dd
  have hdd := h.read_inBounds hd
  obtain ⟨hVwf, hVtot⟩ := Unionfind.relabel_wf _ h.ufV_wf
  obtain ⟨hDwf, hDtot⟩ := Unionfind.relabel_wf _ h.ufD_wf
  have link_wf (o : OptIdx) :
      ∀ j, (match o with
        | .some i => dMap[i]!
        | .none => .none).get? = Option.some j → j < ufD.numRoots := by
    cases o with
    | none => simp
    | some i => exact fun j hj => IndexMap.get?_getElem!_lt hDwf hj
  exact ⟨IndexMap.idx!_lt_of_total hVwf hVtot (h.ufV_n.symm ▸ hdd.head_lt),
    IndexMap.idx!_lt_of_total hDwf hDtot
      (h.ufD_n.symm ▸ h.darts_size ▸ hdd.rev_lt),
    link_wf dd.succ, link_wf dd.pred⟩

/-- Invariant of the renumber loop: the output tracks the processed prefix of
`allRoots`, and every emitted dart is in bounds for the quotient. -/
private structure RenumberInv (ufV ufD : Unionfind) (k : Nat)
    (dartsStar : Array Dart) : Prop where
  size_eq : dartsStar.size = k
  dart_wf : ∀ i (h : i < dartsStar.size),
    (dartsStar[i]'h).InBounds ufV.numRoots ufD.numRoots

/-- Pushing an in-bounds dart preserves the renumber loop invariant. -/
private theorem RenumberInv.push {ufV ufD : Unionfind} {k : Nat}
    {dartsStar : Array Dart} (h : RenumberInv ufV ufD k dartsStar)
    {d : Dart} (hd : d.InBounds ufV.numRoots ufD.numRoots) :
    RenumberInv ufV ufD (k + 1) (dartsStar.push d) := by
  grind [RenumberInv]

section
-- The transparency linter flags `mvcgen`'s own `Invariant` encoding (the `⇓`
-- postconditions), not this proof's text; nothing here to rephrase.
set_option linter.tacticCheckInstances false

/-- **`freeHomomorphism` produces a well-formed quotient**: the graph is `WF`
and the maps are total, well-formed relabellings onto its index ranges. The
hypotheses are load-bearing for termination, not only bounds: on an
ill-formed graph or out-of-range pairs a glue can fail to merge classes and
the measure stalls. -/
theorem freeHomomorphism_wf {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    ptStar.WF
    ∧ maps.WF pt.n pt.darts.size ptStar.n ptStar.darts.size
    ∧ maps.vmap.Total ∧ maps.dmap.Total := by
  apply Id.of_wp_run_eq hrun fun (ptOut, mapsOut) =>
    ptOut.WF ∧ mapsOut.WF pt.n pt.darts.size ptOut.n ptOut.darts.size
    ∧ mapsOut.vmap.Total ∧ mapsOut.dmap.Total
  mvcgen
  case inv1 => exact fun s => ⟨glueMeasure s⟩
  case inv2 => exact ⇓s => ⌜GlueInvSum pt s⌝
  case inv3 =>
    rename_i r _ _ _ _
    exact ⇓⟨xs, dartsStar⟩ =>
      ⌜RenumberInv r.2.2.snd r.2.2.fst xs.prefix.length dartsStar⌝
  all_goals mleave
  -- Continue branch: the popped pair is already merged; only the queue shrinks.
  case vc1.step.h_1.isTrue =>
    obtain ⟨hm, hinv⟩ := ‹_ ∧ _›
    exact ⟨_, rfl, by grind [glueMeasure, Queue.live_pop],
      GlueInv.pop ‹_› (show GlueInv pt _ _ _ _ from hinv)⟩
  -- Glue branches (with and without the vertex unite): the shared core covers
  -- pop + dart-unite + reverse push, then the two adjacency steps compose.
  case vc2.step.h_1.isFalse.isTrue =>
    obtain ⟨hm, hinv⟩ := ‹_ ∧ _›
    obtain ⟨h1, ⟨hhe, hhf⟩, ⟨hre, hrf⟩, hdec⟩ :=
      GlueInv.glue ‹_› ‹_› (show GlueInv pt _ _ _ _ from hinv)
    obtain ⟨h4, hq⟩ := glueBoth_spec (h1.uniteV hhe hhf) hre hrf
    exact ⟨_, rfl, by grind [glueMeasure, Queue.live_pop, Queue.live_push], h4⟩
  case vc3.step.h_1.isFalse.isFalse =>
    obtain ⟨hm, hinv⟩ := ‹_ ∧ _›
    obtain ⟨h1, _, ⟨hre, hrf⟩, hdec⟩ :=
      GlueInv.glue ‹_› ‹_› (show GlueInv pt _ _ _ _ from hinv)
    obtain ⟨h4, hq⟩ := glueBoth_spec h1 hre hrf
    exact ⟨_, rfl, by grind [glueMeasure, Queue.live_pop, Queue.live_push], h4⟩
  -- Exhausted queue: the break-side invariant is the continue-side one.
  case vc4.step.h_2 => exact ‹_ ∧ _›.2
  -- Seed state: fresh forests, the input graph, the seeded queue.
  case vc5.pre =>
    exact GlueInv.mk rfl rfl rfl (Unionfind.wf_new _) (Unionfind.wf_new _) hpt
      (fun p hp => hpairs p (Queue.active_ofArray hp))
  -- Renumber loop: one push per root, so the size tracks the processed
  -- prefix; the pushed dart is in bounds for the quotient.
  case vc6.step =>
    have hri : RenumberInv _ _ _ _ := ‹_›
    have hinv' : GlueInv pt _ _ _ _ := ‹_›
    refine ⟨by grind [RenumberInv], (hri.push ?_).dart_wf⟩
    refine renumber_push_inBounds hinv'
      (hinv'.ufD_n ▸ Unionfind.mem_allRoots_lt (Array.mem_toList_iff.mp ?_))
    grind
  case vc7.post.success.pre => exact ⟨rfl, by grind⟩
  -- Exit: the maps are the union-find relabellings, total and well-formed by
  -- `relabel_wf`; the invariant pins the domain sizes and carries the quotient
  -- graph's bounds, the renumber size invariant pins the dart codomain.
  case vc8.post.success.post.success =>
    have hinv' : GlueInv pt _ _ _ _ := ‹_›
    obtain ⟨hVwf, hVtot⟩ := Unionfind.relabel_wf _ hinv'.ufV_wf
    obtain ⟨hDwf, hDtot⟩ := Unionfind.relabel_wf _ hinv'.ufD_wf
    have hri : RenumberInv _ _ _ _ := ‹_›
    exact ⟨fun i hi => by grind [RenumberInv, Unionfind.numRoots, Array.length_toList],
      ⟨by grind [GlueInv],
       by grind [RenumberInv, GlueInv, Unionfind.numRoots, Array.length_toList]⟩,
      hVtot, hDtot⟩
end

end Gluing

end PseudoTriangulation

namespace PseudoConfiguration

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

/-- `disjointUnion` on configurations preserves well-formedness (the graph
part by `PseudoTriangulation.disjointUnion_wf` -- the parent projection of
the union *is* the union of the parent projections, by structure eta; the
degree arrays concatenate as the vertex counts add). -/
theorem disjointUnion_wf {l r : PseudoConfiguration}
    (hl : l.WF) (hr : r.WF) : (l.disjointUnion r).WF := by
  refine ⟨PseudoTriangulation.disjointUnion_wf hl.1 hr.1, ?_⟩
  show (l.degrees ++ r.degrees).size = l.n + r.n
  simp [hl.2, hr.2]

end PseudoConfiguration

namespace Configuration

/-- `mirror`'s dart array, definitionally (so `simp` can rewrite under
`getElem`). -/
private theorem mirror_darts (conf : Configuration) :
    conf.mirror.darts
      = conf.darts.map fun d => { d with succ := d.pred, pred := d.succ } := rfl

/-- `mirror` keeps the vertex count, definitionally. -/
private theorem mirror_n (conf : Configuration) :
    conf.mirror.n = conf.n := rfl

/-- `mirror` keeps the degrees, definitionally. -/
private theorem mirror_degrees (conf : Configuration) :
    conf.mirror.degrees = conf.degrees := rfl

/-- `mirror` (reflecting the configuration by swapping each dart's
`succ`/`pred`) preserves well-formedness: `head`/`rev` are untouched and the
two rotation clauses swap. -/
theorem mirror_wf {conf : Configuration}
    (h : conf.toPseudoConfiguration.WF) :
    conf.mirror.toPseudoConfiguration.WF := by
  grind [PseudoConfiguration.WF, PseudoTriangulation.WF, mirror_darts,
    mirror_n, mirror_degrees, Dart.InBounds]

end Configuration

end NearLinear4ct
