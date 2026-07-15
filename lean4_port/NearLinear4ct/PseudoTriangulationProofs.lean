import NearLinear4ct.Configuration
import NearLinear4ct.MappingProofs
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
