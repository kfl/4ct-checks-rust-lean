import NearLinear4ct.Configuration
import NearLinear4ct.DartGraph
import NearLinear4ct.MappingProofs
import NearLinear4ct.UtilProofs
import Std.Tactic.Do
import Std.Internal.Do

/-!
Well-formedness of the combinatorial map, in two layers.

`Dart.InBounds` / `PseudoTriangulation.WF` / `PseudoConfiguration.WF` state
**index bounds only**: every `head` names a vertex, every `rev`/`succ`/`pred`
names a dart. Above them, `PseudoTriangulation.Valid` adds the geometric laws
the A.4 degree-resolution steps rely on and preserve: `rev` is an involution,
no edge is a graph loop, and boundary corners agree across an edge. The
rotation-system laws (the paper's M3/M4/M6) live above both as
`DartGraph.Rotational`, and the A.4 edits preserve them
(`BoundaryFanPatch.rotational`, `dartIdentification_rotational`);
intermediates of the gluing (A.3) may violate them, so like `Valid` they
hold at operation results only.

The predicates, their executable checkers (`inBoundsCheck`/`wfCheck`) and
decidability bridges (`_iff`) live beside the structure definitions
(`PseudoTriangulation.lean`/`PseudoConfiguration.lean`), where
`RotConfig.attach!` certifies loaded objects and `WFConfig.attach!`
certifies generated intermediates; this file holds the proofs.

This is the graph-side counterpart of `IndexMap.WF` (`MappingProofs.lean`),
and it is exactly the hypothesis the `homCoreGo` termination argument needs:
on a `WF` graph every worklist push (`rev`/`succ`/`pred`, Algorithm A.2)
stays in `[0, darts.size)`, so `dmap.set!` always marks.

Contents: preservation -- `fromVRotations` (unconditional), `disjointUnion`,
the free homomorphism (quotient well-formedness and coherence), and the A.4
degree-resolution steps. The configuration `mirror`'s preservation lemma
lives beside its definition (`Configuration.lean`), where it constructs the
mirrored certificate.
-/

namespace NearLinear4ct

/-! ### Local `!`-read lemmas for array edits

Lean supplies the general `set!` laws. The remaining lemmas cover `push`,
`modify`, and the field projections used by the graph-edit proofs. -/

@[simp] theorem getElem!_push_lt {α : Type _} [Inhabited α] {a : Array α} {x : α} {f : Nat}
    (hf : f < a.size) : (a.push x)[f]! = a[f]! := by grind

theorem getElem!_push_size {α : Type _} [Inhabited α] {a : Array α} {x : α} :
    (a.push x)[a.size]! = x := by grind

theorem getElem!_modify_self {α : Type _} [Inhabited α] {a : Array α} {i : Nat}
    {f : α → α} (hi : i < a.size) : (a.modify i f)[i]! = f a[i]! := by
  grind

theorem getElem!_modify_ne {α : Type _} [Inhabited α] {a : Array α} {i j : Nat}
    {f : α → α} (hne : i ≠ j) : (a.modify i f)[j]! = a[j]! := by
  grind

/-- A `pred`-write leaves `succ` untouched at every index (including its own). -/
theorem getElem!_set!_pred_succ {a : Array Dart} {i f : Nat} {p : OptIdx} :
    ((a.set! i {a[i]! with pred := p})[f]!).succ = (a[f]!).succ := by grind [Array.set!]

/-- A `succ`-write leaves `pred` untouched at every index (including its own). -/
theorem getElem!_set!_succ_pred {a : Array Dart} {i f : Nat} {s : OptIdx} :
    ((a.set! i {a[i]! with succ := s})[f]!).pred = (a[f]!).pred := by grind [Array.set!]

namespace Dart

/-- `InBounds` weakens along larger index sets. -/
theorem InBounds.mono {n D n' D' : Nat} {d : Dart}
    (h : d.InBounds n D) (hn : n ≤ n') (hD : D ≤ D') : d.InBounds n' D' := by
  grind [InBounds]

end Dart

/-- Pushing an in-bounds dart preserves an array-wide bound. -/
private theorem push_dart_wf {n D : Nat} {a : Array Dart}
    (h : ∀ i (hi : i < a.size), (a[i]'hi).InBounds n D)
    {d : Dart} (hd : d.InBounds n D) :
    ∀ i (hi : i < (a.push d).size), ((a.push d)[i]'hi).InBounds n D := by
  grind

namespace Mappings

/-- Structural homomorphism coherence for A.3's quotient map. For every
mapped dart, `head` and `rev` commute; a source-side `succ`/`pred` link is
preserved in the quotient. A boundary link may become interior when it is
glued to an interior link, hence the one-way hypotheses on `succ`/`pred`.
This property is used together with `Mappings.WF`, which puts all `!` reads
below their source and target bounds; `freeHomomorphism_wf` supplies it. -/
def Coherent (maps : Mappings) (src dst : PseudoTriangulation) : Prop :=
  ∀ f fStar, maps.dmap.idx? f = Option.some fStar →
    maps.vmap.idx? (src.darts[f]!).head =
        Option.some (dst.darts[fStar]!).head ∧
    maps.dmap.idx? (src.darts[f]!).rev =
        Option.some (dst.darts[fStar]!).rev ∧
    (∀ s, (src.darts[f]!).succ.get? = Option.some s →
      ∃ t, (dst.darts[fStar]!).succ.get? = Option.some t ∧
        maps.dmap.idx? s = Option.some t) ∧
    (∀ p, (src.darts[f]!).pred.get? = Option.some p →
      ∃ t, (dst.darts[fStar]!).pred.get? = Option.some t ∧
        maps.dmap.idx? p = Option.some t)

/-- Coherence composes: chaining a `src → mid` coherent map with a `mid → dst`
one gives a `src → dst` coherent map. No degree relation is involved; the
only additional premises say that `maps1`'s images land in `maps2`'s domain. -/
theorem Coherent.compose {maps1 maps2 : Mappings} {src mid dst : PseudoTriangulation}
    (hvb : maps1.vmap.Bounded maps2.vmap.size)
    (hdb : maps1.dmap.Bounded maps2.dmap.size)
    (h1 : maps1.Coherent src mid) (h2 : maps2.Coherent mid dst) :
    (maps1.compose maps2).Coherent src dst := by
  have hv : ∀ i, (maps1.compose maps2).vmap.idx? i
      = (maps1.vmap.idx? i).bind maps2.vmap.idx? := fun i => by
    simp only [Mappings.compose]; exact idx?_composeMap hvb i
  have hd : ∀ i, (maps1.compose maps2).dmap.idx? i
      = (maps1.dmap.idx? i).bind maps2.dmap.idx? := fun i => by
    simp only [Mappings.compose]; exact idx?_composeMap hdb i
  intro f fStar hf
  obtain ⟨g, hfg, hgStar⟩ := Option.bind_eq_some_iff.mp (hd f ▸ hf)
  -- Pin the two homomorphisms at this dart so their coherence facts are ground;
  -- grind then chains each clause through `hv`/`hd`. Applying `h1`/`h2` here (not
  -- listing `Coherent` as a grind hint) is what stops grind re-instantiating the
  -- coherence quantifiers against their own `mid.darts[…]` outputs -- the earlier
  -- e-matching blow-up.
  have := h1 f g hfg
  have := h2 g fStar hgStar
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind [Option.bind_eq_some_iff]

/-- A well-formed mapping chain supplies the bounds needed by
`Coherent.compose`. -/
theorem Coherent.compose_of_wf {maps1 maps2 : Mappings}
    {src mid dst : PseudoTriangulation}
    (hwf1 : maps1.WF src.n src.darts.size mid.n mid.darts.size)
    (hwf2 : maps2.WF mid.n mid.darts.size dst.n dst.darts.size)
    (h1 : maps1.Coherent src mid) (h2 : maps2.Coherent mid dst) :
    (maps1.compose maps2).Coherent src dst :=
  Coherent.compose
    (hwf2.vmap_wf.size_eq ▸ hwf1.vmap_wf.bounded)
    (hwf2.dmap_wf.size_eq ▸ hwf1.dmap_wf.bounded) h1 h2

/-- The identity map is coherent from a well-formed pseudo-triangulation to
itself: every dart and vertex maps to itself, including its links. -/
theorem Coherent.id {src : PseudoTriangulation} (hsrc : src.WF) :
    (Mappings.initialMappings src.n src.darts.size).Coherent src src := by
  intro f fStar hf
  obtain ⟨hfd, rfl⟩ : f < src.darts.size ∧ f = fStar := by
    have h := Mappings.idx?_initialMappings_dmap src.n src.darts.size f
    grind
  obtain ⟨hh, hr, hs, hp⟩ := hsrc.read_inBounds hfd
  grind [Mappings.idx?_initialMappings_vmap, Mappings.idx?_initialMappings_dmap]

/-- **Codomain weakening.** The identity map on `src`'s `(n, d)` indices is
coherent into any graph `dst` that agrees with `src` on those darts' `head`/`rev`
and preserves their interior `succ`/`pred` links (boundary links may newly close
-- the one-way clauses permit it). This is the identity carrier for a graph that
gains darts/vertices without disturbing the old ones. -/
theorem Coherent.id_codomain {src dst : PseudoTriangulation} {n d : Nat}
    (hhead : ∀ f, f < d → (src.darts[f]!).head < n
      ∧ (dst.darts[f]!).head = (src.darts[f]!).head)
    (hrev : ∀ f, f < d → (src.darts[f]!).rev < d
      ∧ (dst.darts[f]!).rev = (src.darts[f]!).rev)
    (hsucc : ∀ f s, f < d → (src.darts[f]!).succ.get? = Option.some s
      → s < d ∧ (dst.darts[f]!).succ.get? = Option.some s)
    (hpred : ∀ f p, f < d → (src.darts[f]!).pred.get? = Option.some p
      → p < d ∧ (dst.darts[f]!).pred.get? = Option.some p) :
    (Mappings.initialMappings n d).Coherent src dst := by
  intro f fStar hf
  obtain ⟨hfd, rfl⟩ : f < d ∧ f = fStar := by
    have h := Mappings.idx?_initialMappings_dmap n d f
    grind
  obtain ⟨hh, hheq⟩ := hhead f hfd
  obtain ⟨hr, hreq⟩ := hrev f hfd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mappings.idx?_initialMappings_vmap, if_pos hh, hheq]
  · rw [Mappings.idx?_initialMappings_dmap, if_pos hr, hreq]
  · exact fun s hs =>
      have ⟨hsd, hseq⟩ := hsucc f s hfd hs
      ⟨s, hseq, by rw [Mappings.idx?_initialMappings_dmap, if_pos hsd]⟩
  · exact fun p hp =>
      have ⟨hpd, hpeq⟩ := hpred f p hfd hp
      ⟨p, hpeq, by rw [Mappings.idx?_initialMappings_dmap, if_pos hpd]⟩

/-- **`dst` extends `src` on `[0, d)`.** The graph gained darts/vertices without
disturbing the old ones: on the first `d` darts, `head`/`rev` agree (landing in
`[0, n)`/`[0, d)`) and every interior `succ`/`pred` link is preserved (boundary
links may newly close). This is exactly what `id_codomain` needs; a graph edit
establishes it in one step from a field-by-field characterisation of the final
array against the original. -/
structure Extends (src dst : PseudoTriangulation) (n d : Nat) : Prop where
  head : ∀ f, f < d → (src.darts[f]!).head < n ∧ (dst.darts[f]!).head = (src.darts[f]!).head
  rev : ∀ f, f < d → (src.darts[f]!).rev < d ∧ (dst.darts[f]!).rev = (src.darts[f]!).rev
  succ : ∀ f s, f < d → (src.darts[f]!).succ.get? = Option.some s →
    s < d ∧ (dst.darts[f]!).succ.get? = Option.some s
  pred : ∀ f p, f < d → (src.darts[f]!).pred.get? = Option.some p →
    p < d ∧ (dst.darts[f]!).pred.get? = Option.some p

/-- The identity map on `[0, d)` is coherent into any extension. -/
theorem Coherent.id_of_extends {src dst : PseudoTriangulation} {n d : Nat}
    (h : Extends src dst n d) : (Mappings.initialMappings n d).Coherent src dst :=
  Coherent.id_codomain h.head h.rev h.succ h.pred

end Mappings

/-- A `src → dst` mapping with bounds and structural coherence (A.3).
The proof fields are erased. -/
structure CoherentMappings (src dst : PseudoTriangulation) where
  maps : Mappings
  wf : maps.WF src.n src.darts.size dst.n dst.darts.size
  coherent : maps.Coherent src dst

namespace CoherentMappings

/-- Certified mappings are determined by their underlying maps. -/
@[ext] theorem ext {src dst : PseudoTriangulation} {F G : CoherentMappings src dst}
    (h : F.maps = G.maps) : F = G := by
  cases F; cases G; cases h; rfl

/-- The identity mapping on a well-formed pseudo-triangulation. -/
def id {src : PseudoTriangulation} (hsrc : src.WF) : CoherentMappings src src where
  maps := Mappings.initialMappings src.n src.darts.size
  wf := Mappings.initialMappings_wf src.n src.darts.size
  coherent := Mappings.Coherent.id hsrc

/-- Compose certified mappings through their shared middle graph. -/
def compose {src mid dst : PseudoTriangulation}
    (F : CoherentMappings src mid) (G : CoherentMappings mid dst) :
    CoherentMappings src dst where
  maps := F.maps.compose G.maps
  wf := Mappings.compose_wf F.wf G.wf
  coherent := Mappings.Coherent.compose_of_wf F.wf G.wf F.coherent G.coherent

/-- Left identity. -/
@[simp] theorem id_comp {src dst : PseudoTriangulation} (hsrc : src.WF)
    (F : CoherentMappings src dst) : (CoherentMappings.id hsrc).compose F = F :=
  ext (Mappings.initialMappings_compose F.wf)

/-- Right identity. -/
@[simp] theorem comp_id {src dst : PseudoTriangulation} (hdst : dst.WF)
    (F : CoherentMappings src dst) : F.compose (CoherentMappings.id hdst) = F :=
  ext (Mappings.compose_initialMappings F.wf)

/-- Associativity: composition chains are correct however they are bracketed. -/
theorem compose_assoc {src a b dst : PseudoTriangulation}
    (F : CoherentMappings src a) (G : CoherentMappings a b) (H : CoherentMappings b dst) :
    (F.compose G).compose H = F.compose (G.compose H) :=
  ext (Mappings.compose_assoc F.wf G.wf H.wf)

end CoherentMappings

namespace PseudoTriangulation

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

private theorem disjointUnion_dart_left (l r : PseudoTriangulation) {i : Nat}
    (hi : i < l.darts.size) :
    ((l.disjointUnion r).darts[i]!) = l.darts[i]! := by
  grind [disjointUnion_darts]

private theorem disjointUnion_dart_right (l r : PseudoTriangulation) {i : Nat}
    (hi : i < r.darts.size) :
    ((l.disjointUnion r).darts[l.darts.size + i]!) =
      ⟨(r.darts[i]!).head + l.n, (r.darts[i]!).rev + l.darts.size,
        (r.darts[i]!).succ.map (· + l.darts.size),
        (r.darts[i]!).pred.map (· + l.darts.size)⟩ := by
  grind [disjointUnion_darts]

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
The proof models the two imperative phases as folds: phase 1 builds the
`dartOf`/`fresh` id table, and phase 2 emits one `Dart` per id. Every dart bound
flows from the table, so no hypothesis on the rotation entries is needed. -/

section Construction

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
  have : (default : Array (Option Nat)) = #[] := rfl
  grind

/-- Phase-1 loop invariant: the id table has the right shape and every id it
hands out is `< fresh` (so it indexes into the phase-2 dart array). -/
private structure DartOfWF (n : Nat) (dartOf : Array (Array (Option Nat)))
    (fresh : Nat) : Prop where
  size_eq : dartOf.size = n
  row_size : ∀ a, a < n → (dartOf[a]!).size = n
  value_lt : ∀ (a b v : Nat), (dartOf[a]!)[b]! = some v → v < fresh
  fresh_pos : 0 < fresh → 0 < n

private theorem dartOfWF_init (n : Nat) :
    DartOfWF n (Array.replicate n (Array.replicate n none)) 0 := by
  grind [DartOfWF, getElem!_replicate_replicate]

private theorem dartOfWF_set (n : Nat) (dartOf : Array (Array (Option Nat)))
    (fresh a b : Nat) (hwf : DartOfWF n dartOf fresh) (ha : a < n) :
    DartOfWF n (dartOf.setIfInBounds a ((dartOf[a]!).setIfInBounds b (some fresh)))
      (fresh + 1) := by
  grind [DartOfWF, getElem!_setIfInBounds]

private abbrev blankDart : Dart := ⟨0, 0, OptIdx.none, OptIdx.none⟩

/-- Every dart in the initial blank array is in bounds; `head = 0 < n`
follows from `fresh > 0`. -/
private theorem blankDarts_inBounds (n fresh : Nat) (hn : 0 < fresh → 0 < n)
    (i : Nat) (hi : i < (Array.replicate fresh blankDart).size) :
    ((Array.replicate fresh blankDart)[i]'hi).InBounds n
      (Array.replicate fresh blankDart).size := by
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

/-- The phase-1 step: allocate a fresh dart id for one rotation entry. -/
private def rotIdStep (a : Nat) (s : Array (Array (Option Nat)) × Nat)
    (b : Int) : Array (Array (Option Nat)) × Nat :=
  if b == -1 then s
  else (s.1.set! a ((s.1[a]!).set! b.toNat (some s.2)), s.2 + 1)

/-- Phase 1, functionally: the dart-id table and the id supply. -/
private def rotTable (n : Nat) (rotations : Array (Array Int)) :
    Array (Array (Option Nat)) × Nat :=
  (List.range' 0 n 1).foldl
    (fun s a => rotations[a]!.foldl (rotIdStep a) s)
    (Array.replicate n (Array.replicate n none), 0)

/-- **Phase 1 produces a bounded table.** -/
private theorem rotTable_wf (n : Nat) (rotations : Array (Array Int)) :
    DartOfWF n (rotTable n rotations).1 (rotTable n rotations).2 := by
  unfold rotTable
  apply List.foldlRecOn
    (motive := fun s : Array (Array (Option Nat)) × Nat => DartOfWF n s.1 s.2)
  · exact dartOfWF_init n
  · intro s hs a ha
    have ha' : a < n := by simpa [List.mem_range'_1] using ha
    apply Array.foldl_induction
      (motive := fun _ (s : Array (Array (Option Nat)) × Nat) => DartOfWF n s.1 s.2)
    · exact hs
    · intro i s hs
      grind [rotIdStep, dartOfWF_set]

/-- The phase-2 step: write the dart for one rotation entry (a no-op on the
`-1` separator). -/
private def rotWrite (dartOf : Array (Array (Option Nat))) (rot : Array Int)
    (a : Nat) (darts : Array Dart) (i : Nat) : Array Dart :=
  let b := rot[i]!
  if b == -1 then darts
  else
    let b := b.toNat
    let e := ((dartOf[a]!)[b]!).get!
    let rev := match (dartOf[b]!)[a]! with
      | some r => r
      | none => panic! s!"Discrepancy in dart structure between {a} and {b}"
    let s := if i < rot.size - 1 then rot[i + 1]! else rot[0]!
    let succ := if s != -1 then OptIdx.ofOption (dartOf[a]!)[s.toNat]! else OptIdx.none
    let p := if i > 0 then rot[i - 1]! else rot[rot.size - 1]!
    let pred := if p != -1 then OptIdx.ofOption (dartOf[a]!)[p.toNat]! else OptIdx.none
    darts.set! e ⟨a, rev, succ, pred⟩

/-- Phase 2, functionally: materialise the dart array from a table. -/
private def rotDarts (n : Nat) (rotations : Array (Array Int))
    (t : Array (Array (Option Nat)) × Nat) : Array Dart :=
  (List.range' 0 n 1).foldl
    (fun darts a =>
      (List.range' 0 rotations[a]!.size 1).foldl (rotWrite t.1 rotations[a]! a) darts)
    (Array.replicate t.2 blankDart)

/-- Phase-2 invariant: the array keeps the table's size and every dart remains
in bounds. -/
private structure DartArrayWF (n fresh : Nat) (darts : Array Dart) : Prop where
  size_eq : darts.size = fresh
  inBounds : ∀ i (hi : i < darts.size), (darts[i]'hi).InBounds n darts.size

/-- One phase-2 write keeps every dart in bounds: `head` is the row index,
`rev`/`succ`/`pred` are table reads bounded by `DartOfWF` (a panicking `rev`
read is `0 < fresh`, since the write itself lands below `fresh`). -/
private theorem DartArrayWF.write {n fresh : Nat} {darts : Array Dart}
    (hinv : DartArrayWF n fresh darts) {dartOf : Array (Array (Option Nat))}
    (hwf : DartOfWF n dartOf fresh) {rot : Array Int} {a : Nat}
    (ha : a < n) (i : Nat) :
    DartArrayWF n fresh (rotWrite dartOf rot a darts i) := by
  obtain ⟨hsz, hIH⟩ := hinv
  dsimp only [rotWrite]
  split
  · exact ⟨hsz, hIH⟩
  · refine ⟨by grind [Array.size_setIfInBounds], ?_⟩
    apply inBounds_set n _ _ _ hIH
    intro he
    refine ⟨ha, ?_, ?_, ?_⟩ <;> simp only [hsz] <;>
      grind [DartOfWF, OptIdx.get?_ofOption, OptIdx.get?_none, panicWithPosWithDecl_nat]

/-- **Phase 2 materialises in bounds** from any bounded table. -/
private theorem rotDarts_wf (n : Nat) (rotations : Array (Array Int))
    {t : Array (Array (Option Nat)) × Nat} (hwf : DartOfWF n t.1 t.2) :
    DartArrayWF n t.2 (rotDarts n rotations t) := by
  unfold rotDarts
  apply List.foldlRecOn (motive := DartArrayWF n t.2)
  · exact ⟨Array.size_replicate, fun i hi =>
      blankDarts_inBounds n t.2 hwf.fresh_pos i hi⟩
  · intro darts hinv a ha
    have ha' : a < n := by simpa [List.mem_range'_1] using ha
    apply List.foldlRecOn (motive := DartArrayWF n t.2)
    · exact hinv
    · intro darts hinv i _
      exact hinv.write hwf ha' i

/-- The executable is the two-phase composition. -/
private theorem fromVRotations_eq (n : Nat) (rotations : Array (Array Int)) :
    PseudoTriangulation.fromVRotations n rotations =
      ⟨n, rotDarts n rotations (rotTable n rotations)⟩ := by
  unfold PseudoTriangulation.fromVRotations rotTable rotDarts
  dsimp only
  rw [forIn_range_eq_foldl n _
      (fun a s => rotations[a]!.foldl (rotIdStep a) s)
      (fun a s => by
        rw [forIn_array_eq_foldl _ _ (fun b s => rotIdStep a s b)
          (fun b s => by dsimp only [rotIdStep]; split
                         · rfl
                         · split <;> rfl)]
        rfl),
    pure_bind]
  rw [forIn_range_eq_foldl n _
      (fun a darts =>
        (List.range' 0 rotations[a]!.size 1).foldl
          (rotWrite (rotTable n rotations).1 rotations[a]! a) darts)
      (fun a darts => by
        rw [forIn_range_eq_foldl rotations[a]!.size _
          (fun i darts => rotWrite (rotTable n rotations).1 rotations[a]! a darts i)
          (fun i darts => by dsimp only [rotWrite]; split <;> rfl)]
        rfl),
    pure_bind]
  rfl

/-- `fromVRotations` always produces a well-formed triangulation, *regardless*
of whether the input rotations are valid: structural `InBounds` follows
entirely from the bounded table (dart ids `< fresh = darts.size`) and row
membership (`head = a < n`), never from the rotation entries themselves. -/
theorem fromVRotations_wf (n : Nat) (rotations : Array (Array Int)) :
    (PseudoTriangulation.fromVRotations n rotations).WF := by
  rw [fromVRotations_eq]
  exact (rotDarts_wf n rotations (rotTable_wf n rotations)).inBounds

end Construction

/-! ### Dart pickers stay in range

`firstDart`/`lastDart`/`anyDart` are `findIdx?` scans, so a `some` answer is
an index; `sucKTimes` walks `succ` links, so on a `WF` graph every stop is a
dart. These bound the pairs the degree-resolution steps (A.4) feed back into
the gluing. -/

private theorem findIdx?_lt {xs : Array α} {p : α → Bool} {i : Nat}
    (h : xs.findIdx? p = some i) : i < xs.size := by
  grind [Array.findIdx?_eq_some_iff_getElem]

/-- A found first dart is an index. -/
theorem firstDart_lt {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.firstDart v = some e) : e < pt.darts.size := by
  exact findIdx?_lt (by simpa only [firstDart] using h)

/-- A found last dart is an index. -/
theorem lastDart_lt {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.lastDart v = some e) : e < pt.darts.size := by
  exact findIdx?_lt (by simpa only [lastDart] using h)

/-- A found dart is an index. -/
theorem anyDart_lt {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.anyDart v = some e) : e < pt.darts.size := by
  exact findIdx?_lt (by simpa only [anyDart] using h)

/-- The first dart of a vertex opens its rotation: `pred = nil`. -/
theorem firstDart_pred_isNone {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.firstDart v = some e) : (pt.darts[e]!).pred.isNone := by
  have he : e < pt.darts.size := firstDart_lt h
  simp only [getElem!_pos pt.darts e he]
  grind [Array.findIdx?_eq_some_iff_getElem, firstDart]

/-- The last dart of a vertex closes its rotation: `succ = nil`. -/
theorem lastDart_succ_isNone {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.lastDart v = some e) : (pt.darts[e]!).succ.isNone := by
  have he : e < pt.darts.size := lastDart_lt h
  simp only [getElem!_pos pt.darts e he]
  grind [Array.findIdx?_eq_some_iff_getElem, lastDart]

/-- Any found dart is a dart of that vertex. -/
theorem anyDart_head {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.anyDart v = some e) : (pt.darts[e]!).head = v := by
  have he : e < pt.darts.size := anyDart_lt h
  simp only [getElem!_pos pt.darts e he]
  grind [Array.findIdx?_eq_some_iff_getElem, anyDart]

/-- The first dart of a vertex is a dart of that vertex. -/
theorem firstDart_head {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.firstDart v = some e) : (pt.darts[e]!).head = v := by
  have he : e < pt.darts.size := firstDart_lt h
  simp only [getElem!_pos pt.darts e he]
  grind [Array.findIdx?_eq_some_iff_getElem, firstDart]

/-- The last dart of a vertex is a dart of that vertex. -/
theorem lastDart_head {pt : PseudoTriangulation} {v e : Nat}
    (h : pt.lastDart v = some e) : (pt.darts[e]!).head = v := by
  have he : e < pt.darts.size := lastDart_lt h
  simp only [getElem!_pos pt.darts e he]
  grind [Array.findIdx?_eq_some_iff_getElem, lastDart]

/-- **Valid pseudo-triangulation** -- the geometric layer above bounds-only `WF`:
`rev` is an involution; no edge is a graph loop (a dart and its reverse have
distinct heads, the executable `hasLoop` test -- distinct darts may still share a
head, so this is stronger than `rev e ≠ e`); and boundary corners agree across an
edge (`pred = nil` at a dart iff `succ = nil` at its reverse). `fromVRotations`
builds this from the `-1` markers; the A.4 steps must preserve it. Bounds-only
consumers keep `WF` and take on none of these obligations. -/
structure Valid (pt : PseudoTriangulation) : Prop where
  wf : pt.WF
  rev_rev : ∀ e, e < pt.darts.size → (pt.darts[(pt.darts[e]!).rev]!).rev = e
  loop_free : ∀ e, e < pt.darts.size →
    (pt.darts[e]!).head ≠ (pt.darts[(pt.darts[e]!).rev]!).head
  boundary : ∀ e, e < pt.darts.size →
    ((pt.darts[e]!).pred.isNone ↔ (pt.darts[(pt.darts[e]!).rev]!).succ.isNone)

/-- The reverse dart stays in range (from bounds). -/
theorem Valid.rev_lt {pt : PseudoTriangulation} (h : pt.Valid) {e : Nat}
    (he : e < pt.darts.size) : (pt.darts[e]!).rev < pt.darts.size :=
  (h.wf.read_inBounds he).rev_lt

/-- No dart is its own reverse (else its edge would be a self-loop). -/
theorem Valid.rev_ne {pt : PseudoTriangulation} (h : pt.Valid) {e : Nat}
    (he : e < pt.darts.size) : (pt.darts[e]!).rev ≠ e :=
  fun heq => h.loop_free e he (congrArg (fun i => (pt.darts[i]!).head) heq).symm

/-- The `succ`/`pred` mirror of `boundary`, from `boundary` at `rev e` and
`rev_rev` -- so only one boundary direction need be carried. -/
theorem Valid.boundary' {pt : PseudoTriangulation} (h : pt.Valid) {e : Nat}
    (he : e < pt.darts.size) :
    ((pt.darts[e]!).succ.isNone ↔ (pt.darts[(pt.darts[e]!).rev]!).pred.isNone) :=
  (h.rev_rev e he ▸ h.boundary _ (h.rev_lt he)).symm

/-! ### The semantic view

`dartGraph` reads a well-formed graph as a typed `DartGraph`: `WF` turns raw
indices into `Fin`s and the `OptIdx` sentinels into genuine `Option`s. Proofs
use the projection lemmas below, never the definition. -/

/-- The typed semantic view of a well-formed graph. -/
def dartGraph (pt : PseudoTriangulation) (hwf : pt.WF) :
    DartGraph (Fin pt.n) (Fin pt.darts.size) where
  head d := ⟨(pt.darts[d.val]!).head, (hwf.read_inBounds d.isLt).head_lt⟩
  rev d := ⟨(pt.darts[d.val]!).rev, (hwf.read_inBounds d.isLt).rev_lt⟩
  succ d := match hs : (pt.darts[d.val]!).succ.get? with
    | .none => none
    | .some s => some ⟨s, (hwf.read_inBounds d.isLt).succ_lt s hs⟩
  pred d := match hq : (pt.darts[d.val]!).pred.get? with
    | .none => none
    | .some p => some ⟨p, (hwf.read_inBounds d.isLt).pred_lt p hq⟩

@[simp] theorem dartGraph_head {pt : PseudoTriangulation} (hwf : pt.WF)
    (d : Fin pt.darts.size) :
    ((pt.dartGraph hwf).head d).val = (pt.darts[d.val]!).head := rfl

@[simp] theorem dartGraph_rev {pt : PseudoTriangulation} (hwf : pt.WF)
    (d : Fin pt.darts.size) :
    ((pt.dartGraph hwf).rev d).val = (pt.darts[d.val]!).rev := rfl

theorem dartGraph_succ_get? {pt : PseudoTriangulation} (hwf : pt.WF)
    (d : Fin pt.darts.size) :
    ((pt.dartGraph hwf).succ d).map Fin.val = (pt.darts[d.val]!).succ.get? := by
  simp only [dartGraph]
  split <;> rename_i hs <;> simpa using hs.symm

theorem dartGraph_pred_get? {pt : PseudoTriangulation} (hwf : pt.WF)
    (d : Fin pt.darts.size) :
    ((pt.dartGraph hwf).pred d).map Fin.val = (pt.darts[d.val]!).pred.get? := by
  simp only [dartGraph]
  split <;> rename_i hq <;> simpa using hq.symm

@[simp] theorem dartGraph_succ_isNone {pt : PseudoTriangulation} (hwf : pt.WF)
    (d : Fin pt.darts.size) :
    ((pt.dartGraph hwf).succ d).isNone = (pt.darts[d.val]!).succ.isNone := by
  rw [OptIdx.isNone_eq, ← dartGraph_succ_get? hwf d, Option.isNone_map]

@[simp] theorem dartGraph_pred_isNone {pt : PseudoTriangulation} (hwf : pt.WF)
    (d : Fin pt.darts.size) :
    ((pt.dartGraph hwf).pred d).isNone = (pt.darts[d.val]!).pred.isNone := by
  rw [OptIdx.isNone_eq, ← dartGraph_pred_get? hwf d, Option.isNone_map]

theorem dartGraph_succ_eq_none {pt : PseudoTriangulation} (hwf : pt.WF)
    {d : Fin pt.darts.size} (h : (pt.darts[d.val]!).succ.get? = .none) :
    (pt.dartGraph hwf).succ d = none :=
  Option.map_eq_none_iff.mp ((dartGraph_succ_get? hwf d).trans h)

theorem dartGraph_pred_eq_none {pt : PseudoTriangulation} (hwf : pt.WF)
    {d : Fin pt.darts.size} (h : (pt.darts[d.val]!).pred.get? = .none) :
    (pt.dartGraph hwf).pred d = none :=
  Option.map_eq_none_iff.mp ((dartGraph_pred_get? hwf d).trans h)

theorem dartGraph_succ_eq_some {pt : PseudoTriangulation} (hwf : pt.WF)
    {d : Fin pt.darts.size} {p : Nat} (h : (pt.darts[d.val]!).succ.get? = .some p) :
    (pt.dartGraph hwf).succ d = some ⟨p, (hwf.read_inBounds d.isLt).succ_lt p h⟩ := by
  obtain ⟨a, ha, hval⟩ := Option.map_eq_some_iff.mp ((dartGraph_succ_get? hwf d).trans h)
  exact ha.trans (congrArg some (Fin.ext hval))

theorem dartGraph_pred_eq_some {pt : PseudoTriangulation} (hwf : pt.WF)
    {d : Fin pt.darts.size} {p : Nat} (h : (pt.darts[d.val]!).pred.get? = .some p) :
    (pt.dartGraph hwf).pred d = some ⟨p, (hwf.read_inBounds d.isLt).pred_lt p h⟩ := by
  obtain ⟨a, ha, hval⟩ := Option.map_eq_some_iff.mp ((dartGraph_pred_get? hwf d).trans h)
  exact ha.trans (congrArg some (Fin.ext hval))

/-- Concrete validity gives the semantic laws of the view. -/
theorem Valid.toDartGraph {pt : PseudoTriangulation} (h : pt.Valid) :
    (pt.dartGraph h.wf).Valid where
  rev_rev d := Fin.ext (by simpa using h.rev_rev d.val d.isLt)
  loop_free d hEq := h.loop_free d.val d.isLt (by simpa using congrArg Fin.val hEq)
  boundary d := by simpa using h.boundary d.val d.isLt

/-- Semantic validity of the view gives back concrete validity. -/
theorem Valid.ofDartGraph {pt : PseudoTriangulation} (hwf : pt.WF)
    (h : (pt.dartGraph hwf).Valid) : pt.Valid where
  wf := hwf
  rev_rev e he := by simpa using congrArg Fin.val (h.rev_rev ⟨e, he⟩)
  loop_free e he hEq := h.loop_free ⟨e, he⟩ (Fin.ext (by simpa using hEq))
  boundary e he := by simpa using h.boundary ⟨e, he⟩


/-- **What `addBoundaryDarts` changed** (A.4.6): the implementation-level patch,
read off the `push`/`set!` chain once by `addBoundaryDarts_patch`. `dst` appends
the reverse pair for the new boundary edge at `src.darts.size`/`+ 1` and closes
the four fan corners `eF`/`eL`/`eFR`/`eLR`; every other field is untouched. The
exact targets certify that the corners are closed; the `eL`/`eF` writes are
guarded by `eFR ≠ eL`/`eLR ≠ eF`, the collisions a degenerate fan allows.
Validity and coherence are semantic consequences (`BoundaryFanPatch.valid`,
`BoundaryFanPatch.toExtends`). -/
structure BoundaryFanPatch (src dst : PseudoTriangulation) (eF eL eFR eLR : Nat) : Prop where
  wf : dst.WF
  n_eq : dst.n = src.n
  size : dst.darts.size = src.darts.size + 2
  eF_lt : eF < src.darts.size
  eL_lt : eL < src.darts.size
  eFR_def : (src.darts[eF]!).rev = eFR
  eLR_def : (src.darts[eL]!).rev = eLR
  head_eq : (src.darts[eF]!).head = (src.darts[eL]!).head
  head_ne : (src.darts[eFR]!).head ≠ (src.darts[eLR]!).head
  predF_open : (src.darts[eF]!).pred.isNone
  succL_open : (src.darts[eL]!).succ.isNone
  read_new1 : dst.darts[src.darts.size]! =
    ⟨(src.darts[eFR]!).head, src.darts.size + 1, OptIdx.none, OptIdx.some eFR⟩
  read_new2 : dst.darts[src.darts.size + 1]! =
    ⟨(src.darts[eLR]!).head, src.darts.size, OptIdx.some eLR, OptIdx.none⟩
  head_old : ∀ (j : Nat), j < src.darts.size → (dst.darts[j]!).head = (src.darts[j]!).head
  rev_old : ∀ (j : Nat), j < src.darts.size → (dst.darts[j]!).rev = (src.darts[j]!).rev
  pred_old : ∀ (j : Nat), j ≠ eF → j ≠ eLR → j < src.darts.size →
    (dst.darts[j]!).pred = (src.darts[j]!).pred
  succ_old : ∀ (j : Nat), j ≠ eL → j ≠ eFR → j < src.darts.size →
    (dst.darts[j]!).succ = (src.darts[j]!).succ
  succ_eFR : (dst.darts[eFR]!).succ = OptIdx.some src.darts.size
  pred_eLR : (dst.darts[eLR]!).pred = OptIdx.some (src.darts.size + 1)
  succ_eL : eFR ≠ eL → (dst.darts[eL]!).succ = OptIdx.some eF
  pred_eF : eLR ≠ eF → (dst.darts[eF]!).pred = OptIdx.some eL

namespace BoundaryFanPatch
variable {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}

/-- The exact targets close `eF`, including its collision with `eLR`. -/
theorem predF_closed (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    ¬ (dst.darts[eF]!).pred.isNone := by
  grind only [!OptIdx.isNone_some, hp.pred_eLR, hp.pred_eF]

/-- The exact patch target closes `eLR`. -/
theorem predLR_closed (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    ¬ (dst.darts[eLR]!).pred.isNone := by
  grind only [!OptIdx.isNone_some, hp.pred_eLR]

/-- The exact targets close `eL`, including its collision with `eFR`. -/
theorem succL_closed (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    ¬ (dst.darts[eL]!).succ.isNone := by
  grind only [!OptIdx.isNone_some, hp.succ_eFR, hp.succ_eL]

/-- The exact patch target closes `eFR`. -/
theorem succFR_closed (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    ¬ (dst.darts[eFR]!).succ.isNone := by
  grind only [!OptIdx.isNone_some, hp.succ_eFR]

end BoundaryFanPatch

/-- The dart relabelling of a boundary-fan patch: `dst`'s index space is the
old index space plus the two appended tags. -/
def BoundaryFanPatch.dartEquiv {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    TypeEquiv (Fin dst.darts.size) (Sum (Fin src.darts.size) (Fin 2)) :=
  (TypeEquiv.finCast hp.size).trans (TypeEquiv.finAddTwo src.darts.size)

/-- The relabelled semantic view of the patched graph. -/
def BoundaryFanPatch.dstView {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    DartGraph (Fin src.n) (Sum (Fin src.darts.size) (Fin 2)) :=
  (dst.dartGraph hp.wf).relabel (TypeEquiv.finCast hp.n_eq) hp.dartEquiv

@[simp] theorem BoundaryFanPatch.dartEquiv_symm_inl {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR)
    (x : Fin src.darts.size) :
    ((hp.dartEquiv.symm).toFun (Sum.inl x)).val = x.val := rfl

@[simp] theorem BoundaryFanPatch.dartEquiv_symm_inr0 {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    ((hp.dartEquiv.symm).toFun (Sum.inr 0)).val = src.darts.size := rfl

@[simp] theorem BoundaryFanPatch.dartEquiv_symm_inr1 {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR) :
    ((hp.dartEquiv.symm).toFun (Sum.inr 1)).val = src.darts.size + 1 := rfl

theorem BoundaryFanPatch.dartEquiv_inl {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR)
    (j : Fin dst.darts.size) (h : j.val < src.darts.size) :
    hp.dartEquiv.toFun j = Sum.inl ⟨j.val, h⟩ :=
  TypeEquiv.finAddTwo_inl _ h

theorem BoundaryFanPatch.dartEquiv_inr0 {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR)
    (j : Fin dst.darts.size) (h : j.val = src.darts.size) :
    hp.dartEquiv.toFun j = Sum.inr 0 :=
  TypeEquiv.finAddTwo_inr0 _ h

theorem BoundaryFanPatch.dartEquiv_inr1 {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR)
    (j : Fin dst.darts.size) (h : j.val = src.darts.size + 1) :
    hp.dartEquiv.toFun j = Sum.inr 1 :=
  TypeEquiv.finAddTwo_inr1 _ h

/-- Interior links transport through the dart bijection: `get?`-equal reads
map to `Sum.inl`-related typed links. -/
private theorem BoundaryFanPatch.link_map {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat} (hp : BoundaryFanPatch src dst eF eL eFR eLR)
    {o₁ : Option (Fin dst.darts.size)} {o₂ : Option (Fin src.darts.size)}
    (h : o₁.map Fin.val = o₂.map Fin.val) :
    o₁.map hp.dartEquiv.toFun = o₂.map (Sum.inl (β := Fin 2)) := by
  cases o₂ with
  | none =>
    have h' : o₁.map Fin.val = none := by simpa using h
    rw [Option.map_eq_none_iff.mp h']
    rfl
  | some f =>
    obtain ⟨g, hg, hval⟩ := Option.map_eq_some_iff.mp (by simpa using h)
    rw [hg, Option.map_some, Option.map_some]
    exact congrArg some
      ((hp.dartEquiv_inl g (hval.symm ▸ f.isLt)).trans (congrArg Sum.inl (Fin.ext hval)))

/-- **The concrete patch, semantically.** All `Fin`/`Sum` transport lives here:
the patch facts translate into `IsBoundaryFanPatch` on the typed
views. Fields are re-read only through the `dartGraph` projections -- the
implementation trace (`mvcgen`, the `push`/`set!` chain) is never reopened. -/
theorem BoundaryFanPatch.toDartGraph {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) (hsrc : src.WF) :
    DartGraph.IsBoundaryFanPatch (src.dartGraph hsrc) hp.dstView
      ⟨eF, hp.eF_lt⟩ ⟨eL, hp.eL_lt⟩
      ⟨eFR, hp.eFR_def ▸ (hsrc.read_inBounds hp.eF_lt).rev_lt⟩
      ⟨eLR, hp.eLR_def ▸ (hsrc.read_inBounds hp.eL_lt).rev_lt⟩ := by
  have heFRlt : eFR < src.darts.size := hp.eFR_def ▸ (hsrc.read_inBounds hp.eF_lt).rev_lt
  have heLRlt : eLR < src.darts.size := hp.eLR_def ▸ (hsrc.read_inBounds hp.eL_lt).rev_lt
  refine
    { eFR_def := Fin.ext (by simpa using hp.eFR_def)
      eLR_def := Fin.ext (by simpa using hp.eLR_def)
      head_eq := Fin.ext (by simpa using hp.head_eq)
      head_ne := fun hEq => hp.head_ne (by simpa using congrArg Fin.val hEq)
      predF_open := by simpa using hp.predF_open
      succL_open := by simpa using hp.succL_open
      rev_new1 := hp.dartEquiv_inr1 _ (by
        rw [dartGraph_rev, hp.dartEquiv_symm_inr0, congrArg Dart.rev hp.read_new1])
      rev_new2 := hp.dartEquiv_inr0 _ (by
        rw [dartGraph_rev, hp.dartEquiv_symm_inr1, congrArg Dart.rev hp.read_new2])
      head_new1 := Fin.ext (by simpa [dstView] using congrArg Dart.head hp.read_new1)
      head_new2 := Fin.ext (by simpa [dstView] using congrArg Dart.head hp.read_new2)
      succ_new1 := by
        simpa [dstView, Option.isNone_map]
          using congrArg (fun d => d.succ.isNone) hp.read_new1
      pred_new1 := by
        simp only [dstView, DartGraph.relabel_pred]
        rw [dartGraph_pred_eq_some hp.wf (d := hp.dartEquiv.symm (.inr 0)) (p := eFR)
          (by rw [hp.dartEquiv_symm_inr0]; simp [hp.read_new1]), Option.map_some]
        exact congrArg some (hp.dartEquiv_inl _ heFRlt)
      succ_new2 := by
        simp only [dstView, DartGraph.relabel_succ]
        rw [dartGraph_succ_eq_some hp.wf (d := hp.dartEquiv.symm (.inr 1)) (p := eLR)
          (by rw [hp.dartEquiv_symm_inr1]; simp [hp.read_new2]), Option.map_some]
        exact congrArg some (hp.dartEquiv_inl _ heLRlt)
      pred_new2 := by
        simpa [dstView, Option.isNone_map]
          using congrArg (fun d => d.pred.isNone) hp.read_new2
      head_old := fun x => Fin.ext (by simpa [dstView] using hp.head_old x.val x.isLt)
      rev_old := ?_
      pred_old := ?_
      succ_old := ?_
      predF_closed := fun hc => hp.predF_closed (by
        simpa [dstView, Option.isNone_map] using hc)
      predLR_closed := fun hc => hp.predLR_closed (by
        simpa [dstView, Option.isNone_map] using hc)
      succL_closed := fun hc => hp.succL_closed (by
        simpa [dstView, Option.isNone_map] using hc)
      succFR_closed := fun hc => hp.succFR_closed (by
        simpa [dstView, Option.isNone_map] using hc)
      succ_eFR := by
        simp only [dstView, DartGraph.relabel_succ]
        rw [dartGraph_succ_eq_some hp.wf (d := hp.dartEquiv.symm (.inl ⟨eFR, heFRlt⟩))
          (p := src.darts.size)
          (by rw [hp.dartEquiv_symm_inl]; simp [hp.succ_eFR]), Option.map_some]
        exact congrArg some (hp.dartEquiv_inr0 _ rfl)
      pred_eLR := by
        simp only [dstView, DartGraph.relabel_pred]
        rw [dartGraph_pred_eq_some hp.wf (d := hp.dartEquiv.symm (.inl ⟨eLR, heLRlt⟩))
          (p := src.darts.size + 1)
          (by rw [hp.dartEquiv_symm_inl]; simp [hp.pred_eLR]), Option.map_some]
        exact congrArg some (hp.dartEquiv_inr1 _ rfl)
      succ_eL := fun hc => by
        have hc' : eFR ≠ eL := fun h => hc (Fin.ext h)
        simp only [dstView, DartGraph.relabel_succ]
        rw [dartGraph_succ_eq_some hp.wf (d := hp.dartEquiv.symm (.inl ⟨eL, hp.eL_lt⟩))
          (p := eF)
          (by rw [hp.dartEquiv_symm_inl]; simp [hp.succ_eL hc']), Option.map_some]
        exact congrArg some (hp.dartEquiv_inl _ hp.eF_lt)
      pred_eF := fun hc => by
        have hc' : eLR ≠ eF := fun h => hc (Fin.ext h)
        simp only [dstView, DartGraph.relabel_pred]
        rw [dartGraph_pred_eq_some hp.wf (d := hp.dartEquiv.symm (.inl ⟨eF, hp.eF_lt⟩))
          (p := eL)
          (by rw [hp.dartEquiv_symm_inl]; simp [hp.pred_eF hc']), Option.map_some]
        exact congrArg some (hp.dartEquiv_inl _ hp.eL_lt) }
  · -- rev_old: old reverses are preserved through the relabelling
    intro x
    simp only [dstView, DartGraph.relabel_rev]
    refine (hp.dartEquiv_inl _ ?_).trans (congrArg Sum.inl (Fin.ext ?_))
    · rw [dartGraph_rev, hp.dartEquiv_symm_inl x, hp.rev_old x.val x.isLt]
      exact (hsrc.read_inBounds x.isLt).rev_lt
    · exact hp.rev_old x.val x.isLt
  · -- pred_old: interior pred links map through `Sum.inl`
    intro x hxF hxLR
    simp only [dstView, DartGraph.relabel_pred]
    refine hp.link_map ?_
    rw [dartGraph_pred_get?, dartGraph_pred_get?, hp.dartEquiv_symm_inl x]
    exact congrArg OptIdx.get?
      (hp.pred_old x.val (fun hc => hxF (Fin.ext hc)) (fun hc => hxLR (Fin.ext hc)) x.isLt)
  · -- succ_old: interior succ links map through `Sum.inl`
    intro x hxL hxFR
    simp only [dstView, DartGraph.relabel_succ]
    refine hp.link_map ?_
    rw [dartGraph_succ_get?, dartGraph_succ_get?, hp.dartEquiv_symm_inl x]
    exact congrArg OptIdx.get?
      (hp.succ_old x.val (fun hc => hxL (Fin.ext hc)) (fun hc => hxFR (Fin.ext hc)) x.isLt)

/-- A boundary-fan patch preserves validity: transport to the semantic views,
apply the semantic preservation theorem (`IsBoundaryFanPatch.valid`), and come
back. No intermediate array state is reconstructed. -/
theorem BoundaryFanPatch.valid {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid) : dst.Valid :=
  have hd := (hp.toDartGraph hv.wf).valid hv.toDartGraph
  have hd2 : (((dst.dartGraph hp.wf).relabel (TypeEquiv.finCast hp.n_eq) hp.dartEquiv).relabel
      (TypeEquiv.finCast hp.n_eq).symm hp.dartEquiv.symm).Valid :=
    hd.relabel (TypeEquiv.finCast hp.n_eq).symm hp.dartEquiv.symm
  Valid.ofDartGraph hp.wf
    (DartGraph.relabel_symm_relabel (TypeEquiv.finCast hp.n_eq) hp.dartEquiv
      (dst.dartGraph hp.wf) ▸ hd2)

/-- A boundary-fan patch preserves the rotation-system laws, by the same
round trip as `BoundaryFanPatch.valid`: transport to the semantic views,
apply `IsBoundaryFanPatch.rotational`, and come back through the
relabelling. -/
theorem BoundaryFanPatch.rotational {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid)
    (hr : (src.dartGraph hv.wf).Rotational) : (dst.dartGraph hp.wf).Rotational :=
  have hd := (hp.toDartGraph hv.wf).rotational hv.toDartGraph hr
  have hd2 : (((dst.dartGraph hp.wf).relabel (TypeEquiv.finCast hp.n_eq) hp.dartEquiv).relabel
      (TypeEquiv.finCast hp.n_eq).symm hp.dartEquiv.symm).Rotational :=
    hd.relabel (TypeEquiv.finCast hp.n_eq).symm hp.dartEquiv.symm
  DartGraph.relabel_symm_relabel (TypeEquiv.finCast hp.n_eq) hp.dartEquiv
    (dst.dartGraph hp.wf) ▸ hd2

/-- A boundary-fan patch keeps the identity coherent: interior links are never
disturbed. On a valid source the two closed fan corners were open
(`Valid.boundary` at `eF`/`eL`), so no interior `succ`/`pred` maps onto them.
(`extends` is a keyword, hence `toExtends`.) -/
theorem BoundaryFanPatch.toExtends {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid) :
    Mappings.Extends src dst src.n src.darts.size := by
  have hpO := hp.predF_open
  have hsO := hp.succL_open
  have hsuccFR : (src.darts[eFR]!).succ.isNone :=
    hp.eFR_def ▸ (hv.boundary _ hp.eF_lt).mp hpO
  have hpredLR : (src.darts[eLR]!).pred.isNone :=
    hp.eLR_def ▸ (hv.boundary' hp.eL_lt).mp hsO
  refine ⟨fun f hf => ⟨(hv.wf.read_inBounds hf).head_lt, hp.head_old f hf⟩,
      fun f hf => ⟨(hv.wf.read_inBounds hf).rev_lt, hp.rev_old f hf⟩,
      fun f s hf hs => ⟨(hv.wf.read_inBounds hf).succ_lt s hs, ?_⟩,
      fun f p hf hpr => ⟨(hv.wf.read_inBounds hf).pred_lt p hpr, ?_⟩⟩
  · rw [hp.succ_old f (by grind [OptIdx.isNone_iff_get?])
      (by grind [OptIdx.isNone_iff_get?]) hf]
    exact hs
  · rw [hp.pred_old f (by grind [OptIdx.isNone_iff_get?])
      (by grind [OptIdx.isNone_iff_get?]) hf]
    exact hpr

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

/-- Equality generated by already-merged dart classes and the still-pending
queue obligations. It is an equivalence closure because a source link may
cross several merges before the worklist reaches all of its obligations. -/
private inductive PendingEq (uf : Unionfind) (q : Queue (Nat × Nat)) :
    Nat → Nat → Prop where
  | root {a b} (ha : a < uf.n) (hb : b < uf.n)
      (h : uf.root a = uf.root b) : PendingEq uf q a b
  | queued {a b} (ha : a < uf.n) (hb : b < uf.n)
      (h : q.Active (a, b)) : PendingEq uf q a b
  | symm {a b} : PendingEq uf q a b → PendingEq uf q b a
  | trans {a b c} : PendingEq uf q a b → PendingEq uf q b c →
      PendingEq uf q a c

private theorem PendingEq.bounds {uf : Unionfind} {q : Queue (Nat × Nat)}
    {a b : Nat} (h : PendingEq uf q a b) : a < uf.n ∧ b < uf.n := by
  induction h <;> grind

private theorem PendingEq.left_lt {uf : Unionfind} {q : Queue (Nat × Nat)}
    {a b : Nat} (h : PendingEq uf q a b) : a < uf.n := h.bounds.1

private theorem PendingEq.right_lt {uf : Unionfind} {q : Queue (Nat × Nat)}
    {a b : Nat} (h : PendingEq uf q a b) : b < uf.n := h.bounds.2

private theorem PendingEq.push {uf : Unionfind} {q : Queue (Nat × Nat)}
    {a b : Nat} {x : Nat × Nat} (h : PendingEq uf q a b) :
    PendingEq uf (q.push x) a b := by
  induction h with
  | root ha hb hr => exact .root ha hb hr
  | queued ha hb hq => exact .queued ha hb (Queue.active_push_mono hq)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem PendingEq.pop_same {uf : Unionfind} {q q' : Queue (Nat × Nat)}
    {x : Nat × Nat} {a b : Nat} (hpop : q.pop? = some (x, q'))
    (hxy : uf.root x.1 = uf.root x.2) (h : PendingEq uf q a b) :
    PendingEq uf q' a b := by
  induction h with
  | root ha hb hr => exact .root ha hb hr
  | @queued c d hc hd hq =>
    rcases Queue.active_pop_cases hpop hq with hq' | rfl
    · exact .queued hc hd hq'
    · exact .root hc hd hxy
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem PendingEq.pop_unite {uf : Unionfind} (hwf : uf.WF)
    {q q' : Queue (Nat × Nat)} {x : Nat × Nat} {a b : Nat}
    (hpop : q.pop? = some (x, q')) (hx₁ : x.1 < uf.n) (hx₂ : x.2 < uf.n)
    (hne : uf.root x.1 ≠ uf.root x.2) (h : PendingEq uf q a b) :
    PendingEq (uf.unite x.1 x.2) q' a b := by
  induction h with
  | root ha hb hr =>
    exact .root (by simpa using ha) (by simpa using hb)
      (Unionfind.root_unite_of_ne_eq hwf hx₁ hx₂ ha hb hne hr)
  | @queued c d hc hd hq =>
    rcases Queue.active_pop_cases hpop hq with hq' | rfl
    · exact .queued (by simpa using hc) (by simpa using hd) hq'
    · exact .root (by simpa using hc) (by simpa using hd)
        (Unionfind.root_unite_of_ne_same hwf hc hd hne)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem PendingEq.root_eq_of_empty {uf : Unionfind}
    {q : Queue (Nat × Nat)} {a b : Nat} (hq : q.isEmpty = true)
    (h : PendingEq uf q a b) : uf.root a = uf.root b := by
  induction h with
  | root _ _ hr => exact hr
  | queued _ _ hp => exact absurd hp (Queue.not_active_of_isEmpty hq _)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The two optional dart pointers treated uniformly in Lemma 9.4's
`P ∈ {succ, pred}` argument. -/
private inductive LinkKind where
  | succ
  | pred
  deriving DecidableEq

private def LinkKind.get : LinkKind → Dart → OptIdx
  | .succ, d => d.succ
  | .pred, d => d.pred

private def LinkKind.set : LinkKind → Dart → OptIdx → Dart
  | .succ, d, o => { d with succ := o }
  | .pred, d, o => { d with pred := o }

/-- Proof-only name for one link update in the boundary-fan trace. -/
private def LinkKind.write (k : LinkKind) (a : Array Dart) (p t : Nat) : Array Dart :=
  a.set! p (k.set a[p]! (.some t))

private theorem LinkKind.read_write (k : LinkKind) (a : Array Dart) (p t j : Nat) :
    (k.write a p t)[j]! =
      if p = j ∧ p < a.size then k.set a[j]! (.some t) else a[j]! := by
  cases k <;> grind [LinkKind.write, LinkKind.set, Array.set!]

private theorem LinkKind.head_write (k : LinkKind) (a : Array Dart) (p t j : Nat) :
    (k.write a p t)[j]!.head = a[j]!.head := by
  cases k <;> grind [LinkKind.read_write, LinkKind.set]

private theorem LinkKind.rev_write (k : LinkKind) (a : Array Dart) (p t j : Nat) :
    (k.write a p t)[j]!.rev = a[j]!.rev := by
  cases k <;> grind [LinkKind.read_write, LinkKind.set]

private theorem LinkKind.get_write_self {k : LinkKind} {a : Array Dart} {p t : Nat}
    (hp : p < a.size) : k.get ((k.write a p t)[p]!) = .some t := by
  cases k <;> grind [LinkKind.read_write, LinkKind.get, LinkKind.set]

private theorem LinkKind.get_write_ne {k : LinkKind} {a : Array Dart} {p t j : Nat}
    (hjp : j ≠ p) : k.get ((k.write a p t)[j]!) = k.get a[j]! := by
  cases k <;> grind [LinkKind.read_write, LinkKind.get, LinkKind.set]

private theorem LinkKind.get_other_write {k l : LinkKind} {a : Array Dart} {p t j : Nat}
    (hkl : k ≠ l) : k.get ((l.write a p t)[j]!) = k.get a[j]! := by
  cases k <;> cases l <;> grind [LinkKind.read_write, LinkKind.get, LinkKind.set]

@[simp] private theorem LinkKind.size_write (k : LinkKind) (a : Array Dart) (p t : Nat) :
    (k.write a p t).size = a.size := by
  simp [LinkKind.write]

@[simp] private theorem LinkKind.get_set (k : LinkKind) (d : Dart) (o : OptIdx) :
    k.get (k.set d o) = o := by cases k <;> rfl

private theorem LinkKind.some_lt {k : LinkKind} {d : Dart} {n D j : Nat}
    (h : d.InBounds n D) (hj : k.get d = OptIdx.some j) : j < D := by
  cases k <;> grind [LinkKind.get, Dart.InBounds, OptIdx.get?_some]

private theorem LinkKind.get_lt {k : LinkKind} {d : Dart} {n D j : Nat}
    (h : d.InBounds n D) (hj : (k.get d).get? = Option.some j) : j < D := by
  cases k <;> grind [LinkKind.get, Dart.InBounds]

private theorem LinkKind.set_some_inBounds (k : LinkKind) {d : Dart} {n D j : Nat}
    (h : d.InBounds n D) (hj : j < D) :
    (k.set d (.some j)).InBounds n D := by
  cases k <;> grind [LinkKind.set, Dart.InBounds, OptIdx.get?_some]

/-- Proof-side common form of `glueSucc` and `gluePred`. -/
private def LinkKind.glue (k : LinkKind) (darts : Array Dart)
    (q : Queue (Nat × Nat)) (eStar fStar : Nat) : Array Dart × Queue (Nat × Nat) :=
  match k.get (darts[eStar]!), k.get (darts[fStar]!) with
  | .some e', .some f' => (darts, q.push (e', f'))
  | .some e', .none => (darts.set! fStar (k.set (darts[fStar]!) (.some e')), q)
  | _, _ => (darts, q)

@[simp] private theorem LinkKind.glue_succ (darts : Array Dart)
    (q : Queue (Nat × Nat)) (eStar fStar : Nat) :
    LinkKind.succ.glue darts q eStar fStar = glueSucc darts q eStar fStar := rfl

@[simp] private theorem LinkKind.glue_pred (darts : Array Dart)
    (q : Queue (Nat × Nat)) (eStar fStar : Nat) :
    LinkKind.pred.glue darts q eStar fStar = gluePred darts q eStar fStar := rfl

/-- Semantic invariant for A.3. Each original dart is coherent with the
current representative dart; pending adjacency identifications are interpreted
through `PendingEq`. `link_of`/`link_from` pair forward coherence with reverse
provenance: original adjacency links survive to the representative, and every
representative link descends from some original in the class -- the gluing
never invents links. The seed field records that all requested pairs remain
connected even after their queue entries are popped. -/
private structure GlueCoherent (pt : PseudoTriangulation) (dartPairs : Array (Nat × Nat))
    (darts : Array Dart) (ufV ufD : Unionfind) (q : Queue (Nat × Nat)) : Prop where
  head_eq : ∀ i, i < pt.darts.size → (darts[i]!).head = (pt.darts[i]!).head
  head : ∀ i, i < pt.darts.size →
    ufV.root (pt.darts[i]!).head = ufV.root (darts[ufD.root i]!).head
  rev : ∀ i, i < pt.darts.size →
    PendingEq ufD q (pt.darts[i]!).rev (darts[ufD.root i]!).rev
  link_of : ∀ (k : LinkKind) i, i < pt.darts.size → ∀ s,
    (k.get (pt.darts[i]!)).get? = Option.some s →
    ∃ t, (k.get (darts[ufD.root i]!)).get? = Option.some t ∧ PendingEq ufD q s t
  link_from : ∀ (k : LinkKind) i, i < pt.darts.size →
    ¬ (k.get (darts[ufD.root i]!)).isNone →
    ∃ j, j < pt.darts.size ∧ ufD.root j = ufD.root i ∧ ¬ (k.get (pt.darts[j]!)).isNone
  seeds : ∀ p ∈ dartPairs, PendingEq ufD q p.1 p.2

@[simp] private theorem root_new {n i : Nat} (hi : i < n) :
    (Unionfind.new n).root i = i :=
  Unionfind.root_eq_self (by simp [Unionfind.new, hi])

private theorem GlueCoherent.init {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size) :
    GlueCoherent pt dartPairs pt.darts (Unionfind.new pt.n)
      (Unionfind.new pt.darts.size) (Queue.ofArray dartPairs) := by
  constructor
  · grind
  · intro i hi
    have hd := hpt.read_inBounds hi
    simp only [root_new hi, root_new hd.head_lt]
  · intro i hi
    have hd := hpt.read_inBounds hi
    simpa only [root_new hi] using PendingEq.root (q := Queue.ofArray dartPairs)
      hd.rev_lt hd.rev_lt rfl
  · intro k i hi s hs
    have hslt := LinkKind.get_lt (hpt.read_inBounds hi) hs
    exact ⟨s, by simpa only [root_new hi] using hs, .root hslt hslt rfl⟩
  · intro k i hi hnn
    exact ⟨i, hi, rfl, by simpa only [root_new hi] using hnn⟩
  · intro p hp
    obtain ⟨hp₁, hp₂⟩ := hpairs p hp
    exact .queued hp₁ hp₂ (Queue.active_ofArray_of_mem hp)

private theorem GlueCoherent.pop_same {pt : PseudoTriangulation}
    {dartPairs : Array (Nat × Nat)} {darts : Array Dart} {ufV ufD : Unionfind}
    {q q' : Queue (Nat × Nat)} {e f : Nat}
    (hpop : q.pop? = some ((e, f), q')) (hsame : ufD.same e f = true)
    (h : GlueCoherent pt dartPairs darts ufV ufD q) :
    GlueCoherent pt dartPairs darts ufV ufD q' := by
  have hef : ufD.root e = ufD.root f := by
    simpa [Unionfind.same] using hsame
  exact ⟨h.head_eq, h.head,
    fun i hi => (h.rev i hi).pop_same hpop hef,
    fun k i hi s hs => (h.link_of k i hi s hs).imp fun t ht =>
      ⟨ht.1, ht.2.pop_same hpop hef⟩,
    h.link_from,
    fun p hp => (h.seeds p hp).pop_same hpop hef⟩

private theorem PendingEq.glue {uf : Unionfind} {q : Queue (Nat × Nat)}
    {a b eStar fStar : Nat} {darts : Array Dart} {k : LinkKind}
    (h : PendingEq uf q a b) : PendingEq uf (k.glue darts q eStar fStar).2 a b := by
  unfold LinkKind.glue
  split
  · exact h.push
  · exact h
  · exact h

/-- Incidence equality available to the gluing loop (the connectivity half
of Lemma 9.6): source `succ` adjacency together with merged-or-pending dart
identifications. Source links never change, so only the `PendingEq` side
moves as the loop rewrites `darts`. -/
private inductive GlueIncidenceConn (pt : PseudoTriangulation) (ufD : Unionfind)
    (q : Queue (Nat × Nat)) : Nat → Nat → Prop where
  | succ {a b} (ha : a < pt.darts.size)
      (h : (pt.darts[a]!).succ.get? = Option.some b) : GlueIncidenceConn pt ufD q a b
  | pend {a b} (h : PendingEq ufD q a b) : GlueIncidenceConn pt ufD q a b
  | symm {a b} : GlueIncidenceConn pt ufD q a b → GlueIncidenceConn pt ufD q b a
  | trans {a b c} : GlueIncidenceConn pt ufD q a b → GlueIncidenceConn pt ufD q b c →
      GlueIncidenceConn pt ufD q a c

private theorem GlueIncidenceConn.bounds {pt : PseudoTriangulation} (hpt : pt.WF)
    {ufD : Unionfind} {q : Queue (Nat × Nat)} (hn : ufD.n = pt.darts.size)
    {a b : Nat} (h : GlueIncidenceConn pt ufD q a b) :
    a < pt.darts.size ∧ b < pt.darts.size := by
  induction h with
  | succ ha hs => exact ⟨ha, (hpt.read_inBounds ha).succ_lt _ hs⟩
  | pend hp =>
    have h1 := hp.left_lt
    have h2 := hp.right_lt
    exact ⟨by omega, by omega⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-- Map the `PendingEq` generators; the source-adjacency generators are
state-independent. -/
private theorem GlueIncidenceConn.map_pend {pt : PseudoTriangulation}
    {ufD ufD' : Unionfind} {q q' : Queue (Nat × Nat)} {a b : Nat}
    (h : GlueIncidenceConn pt ufD q a b)
    (hmap : ∀ {x y : Nat}, PendingEq ufD q x y → PendingEq ufD' q' x y) :
    GlueIncidenceConn pt ufD' q' a b := by
  induction h with
  | succ ha hs => exact .succ ha hs
  | pend hp => exact .pend (hmap hp)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Typed incidence connectivity lowers to the loop's incidence equality
(reflexivity is a `PendingEq.root` fact). -/
private theorem GlueIncidenceConn.of_incidenceConn {pt : PseudoTriangulation}
    (hpt : pt.WF) {ufD : Unionfind} {q : Queue (Nat × Nat)}
    (hn : ufD.n = pt.darts.size) {d e : Fin pt.darts.size}
    (h : DartGraph.IncidenceConn (pt.dartGraph hpt) d e) :
    GlueIncidenceConn pt ufD q d.val e.val := by
  induction h with
  | refl d =>
    have hd := d.isLt
    exact .pend (.root (by omega) (by omega) rfl)
  | @succ d e hs =>
    exact .succ d.isLt
      ((dartGraph_succ_get? hpt d).symm.trans (congrArg (Option.map Fin.val) hs))
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- With an empty queue the loop's incidence equality collapses to quotient
connectivity of the source graph along the dart forest. -/
private theorem GlueIncidenceConn.to_quotientConn {pt : PseudoTriangulation}
    (hpt : pt.WF) {ufD : Unionfind} {q : Queue (Nat × Nat)}
    (hn : ufD.n = pt.darts.size) (hq : q.isEmpty = true) {a b : Nat}
    (h : GlueIncidenceConn pt ufD q a b) :
    ∀ (ha : a < pt.darts.size) (hb : b < pt.darts.size),
      DartGraph.QuotientConn (pt.dartGraph hpt)
        (fun d : Fin pt.darts.size => ufD.root d.val) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | succ ha' hs =>
    intro ha hb
    exact .succ (dartGraph_succ_eq_some hpt hs)
  | pend hp =>
    intro ha hb
    exact .collapse (hp.root_eq_of_empty hq)
  | symm h ih =>
    intro hb' ha'
    exact (ih ha' hb').symm
  | trans h₁ h₂ ih₁ ih₂ =>
    intro ha hb
    have hmid := (h₁.bounds hpt hn).2
    exact (ih₁ ha hmid).trans (ih₂ hmid hb)

/-- **The connectivity invariant (Lemma 9.6)**: the darts of one merged
vertex class lie in one incidence component -- source adjacency plus
performed and pending identifications. A vertex merge only ever happens
alongside the dart identification that connects the two components. -/
private def GlueConnected (pt : PseudoTriangulation) (ufV ufD : Unionfind)
    (q : Queue (Nat × Nat)) : Prop :=
  ∀ a b, a < pt.darts.size → b < pt.darts.size →
    ufV.root (pt.darts[a]!).head = ufV.root (pt.darts[b]!).head →
    GlueIncidenceConn pt ufD q a b

private theorem GlueConnected.init {pt : PseudoTriangulation} (hpt : pt.WF)
    (hr : (pt.dartGraph hpt).Rotational) (dartPairs : Array (Nat × Nat)) :
    GlueConnected pt (Unionfind.new pt.n) (Unionfind.new pt.darts.size)
      (Queue.ofArray dartPairs) := by
  intro a b ha hb hroot
  have hha := (hpt.read_inBounds ha).head_lt
  have hhb := (hpt.read_inBounds hb).head_lt
  have hheads : (pt.darts[a]!).head = (pt.darts[b]!).head := by
    simpa only [root_new hha, root_new hhb] using hroot
  obtain ⟨l, hl⟩ := hr.incidence ((pt.dartGraph hpt).head ⟨a, ha⟩)
  have hma : (⟨a, ha⟩ : Fin pt.darts.size) ∈ l := (hl.mem_iff _).mpr rfl
  have hmb : (⟨b, hb⟩ : Fin pt.darts.size) ∈ l :=
    (hl.mem_iff _).mpr (Fin.ext hheads.symm)
  exact GlueIncidenceConn.of_incidenceConn (ufD := Unionfind.new pt.darts.size)
    (q := Queue.ofArray dartPairs) hpt rfl (hl.connected hma hmb)

private theorem GlueConnected.pop_same {pt : PseudoTriangulation}
    {ufV ufD : Unionfind} {q q' : Queue (Nat × Nat)} {e f : Nat}
    (hpop : q.pop? = some ((e, f), q')) (hsame : ufD.same e f = true)
    (h : GlueConnected pt ufV ufD q) : GlueConnected pt ufV ufD q' := by
  have hef : ufD.root e = ufD.root f := by
    simpa [Unionfind.same] using hsame
  intro a b ha hb hroot
  exact (h a b ha hb hroot).map_pend fun hp => hp.pop_same hpop hef

private theorem GlueConnected.glue_step {pt : PseudoTriangulation} (hpt : pt.WF)
    {darts : Array Dart} {ufV ufV' ufD : Unionfind} {q q' : Queue (Nat × Nat)}
    {e f : Nat}
    (hpop : q.pop? = some ((e, f), q')) (hsame : ¬ ufD.same e f = true)
    (hinv : GlueInv pt darts ufV ufD q)
    (hheads : ∀ i, i < pt.darts.size → (darts[i]!).head = (pt.darts[i]!).head)
    (hVcases : ∀ a b, a < ufV.n → b < ufV.n → ufV'.root a = ufV'.root b →
      ufV.root a = ufV.root b ∨
      (ufV.root a = ufV.root (darts[e]!).head ∧
        ufV.root b = ufV.root (darts[f]!).head) ∨
      (ufV.root a = ufV.root (darts[f]!).head ∧
        ufV.root b = ufV.root (darts[e]!).head))
    (hconn : GlueConnected pt ufV ufD q) :
    let eStar := ufD.root e
    let fStar := ufD.root f
    let ufD' := ufD.unite eStar fStar
    let revQ := q'.push ((darts[eStar]!).rev, (darts[fStar]!).rev)
    let succ := glueSucc darts revQ eStar fStar
    let pred := gluePred succ.1 succ.2 eStar fStar
    GlueConnected pt ufV' ufD' pred.2 := by
  dsimp only []
  have hef := hinv.queued _ (Queue.active_head hpop)
  have hne : ufD.root e ≠ ufD.root f := Unionfind.root_ne_of_not_same hsame
  have he' : e < ufD.n := hinv.ufD_n.symm ▸ hef.1
  have hf' : f < ufD.n := hinv.ufD_n.symm ▸ hef.2
  -- `PendingEq` transport through pop, dart unite, and the three pushes
  have afterAll : ∀ {x y : Nat}, PendingEq ufD q x y →
      PendingEq (ufD.unite (ufD.root e) (ufD.root f))
        (gluePred (glueSucc darts
            (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
            (ufD.root e) (ufD.root f)).1
          (glueSucc darts
            (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
            (ufD.root e) (ufD.root f)).2 (ufD.root e) (ufD.root f)).2 x y := by
    intro x y hxy
    have h1 : PendingEq (ufD.unite (ufD.root e) (ufD.root f))
        (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev)) x y := by
      simpa only [Unionfind.unite_roots hinv.ufD_wf he' hf'] using
        (hxy.pop_unite hinv.ufD_wf hpop he' hf' hne).push
    simpa only [LinkKind.glue_succ, LinkKind.glue_pred] using
      (h1.glue (k := .succ) (darts := darts)
        (eStar := ufD.root e) (fStar := ufD.root f)).glue (k := .pred)
        (darts := (glueSucc darts
          (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
          (ufD.root e) (ufD.root f)).1)
        (eStar := ufD.root e) (fStar := ufD.root f)
  -- the seam: the popped obligation itself rides `afterAll` to a root fact
  have hseam := GlueIncidenceConn.pend (pt := pt)
    (afterAll (.queued he' hf' (Queue.active_head hpop)))
  intro a b ha hb hroot'
  have hha : (pt.darts[a]!).head < ufV.n := by
    simpa only [hinv.ufV_n] using (hpt.read_inBounds ha).head_lt
  have hhb : (pt.darts[b]!).head < ufV.n := by
    simpa only [hinv.ufV_n] using (hpt.read_inBounds hb).head_lt
  have hheadE : (darts[e]!).head = (pt.darts[e]!).head := hheads e hef.1
  have hheadF : (darts[f]!).head = (pt.darts[f]!).head := hheads f hef.2
  rcases hVcases _ _ hha hhb hroot' with hold | ⟨haE, hbF⟩ | ⟨haF, hbE⟩
  · exact (hconn a b ha hb hold).map_pend afterAll
  · have h1 : ufV.root (pt.darts[a]!).head = ufV.root (pt.darts[e]!).head :=
      haE.trans (congrArg ufV.root hheadE)
    have h2 : ufV.root (pt.darts[f]!).head = ufV.root (pt.darts[b]!).head :=
      (congrArg ufV.root hheadF).symm.trans hbF.symm
    exact ((hconn a e ha hef.1 h1).map_pend afterAll).trans
      (hseam.trans ((hconn f b hef.2 hb h2).map_pend afterAll))
  · have h1 : ufV.root (pt.darts[a]!).head = ufV.root (pt.darts[f]!).head :=
      haF.trans (congrArg ufV.root hheadF)
    have h2 : ufV.root (pt.darts[e]!).head = ufV.root (pt.darts[b]!).head :=
      (congrArg ufV.root hheadE).symm.trans hbE.symm
    exact ((hconn a f ha hef.2 h1).map_pend afterAll).trans
      (hseam.symm.trans ((hconn e b hef.1 hb h2).map_pend afterAll))

/-- The packed-state form of the loop's mutable tuple, in declaration order
`(darts, ufV, ufD, q)`. -/
private abbrev GlueState :=
  Array Dart × Unionfind × Unionfind × Queue (Nat × Nat)

/-- The structural and semantic loop invariants over the same packed state. -/
private def GlueSpecSum (pt : PseudoTriangulation) (hpt : pt.WF)
    (dartPairs : Array (Nat × Nat)) : GlueState ⊕ GlueState → Prop
  | .inl ⟨darts, ufV, ufD, q⟩ =>
      GlueInv pt darts ufV ufD q ∧ GlueCoherent pt dartPairs darts ufV ufD q ∧
      ((pt.dartGraph hpt).Rotational → GlueConnected pt ufV ufD q)
  | .inr ⟨darts, ufV, ufD, q⟩ =>
      GlueInv pt darts ufV ufD q ∧ GlueCoherent pt dartPairs darts ufV ufD q ∧
      ((pt.dartGraph hpt).Rotational → GlueConnected pt ufV ufD q) ∧
      q.isEmpty = true

private theorem Queue.pop?_eq_none_of_no_pair {q : Queue (Nat × Nat)}
    {o : Option ((Nat × Nat) × Queue (Nat × Nat))} (ho : q.pop? = o)
    (h : ∀ e f q', o = some ((e, f), q') → False) : q.pop? = none := by
  rw [ho]
  cases o with
  | none => rfl
  | some x =>
      obtain ⟨⟨e, f⟩, q'⟩ := x
      exact False.elim (h e f q' rfl)

/-- The termination measure over the packed loop state: each glue merges two
dart classes, each skip pops an obligation. -/
private def glueMeasure (s : GlueState) : Nat :=
  3 * s.snd.snd.fst.numRoots + s.snd.snd.snd.live

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

/-- One optional-link merge preserves the invariant and adds at most one
queue obligation. -/
private theorem LinkKind.glue_spec {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar : Nat}
    (k : LinkKind)
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size) :
    GlueInv pt (k.glue darts q eStar fStar).1 ufV ufD
        (k.glue darts q eStar fStar).2
      ∧ (k.glue darts q eStar fStar).2.live ≤ q.live + 1 := by
  have hbe := h.read_inBounds he
  have hbf := h.read_inBounds hf
  unfold LinkKind.glue
  split
  · exact ⟨h.push ⟨h.darts_size ▸ k.some_lt hbe ‹_›,
      h.darts_size ▸ k.some_lt hbf ‹_›⟩, Nat.le_of_eq Queue.live_push⟩
  · exact ⟨h.fill fun _ => k.set_some_inBounds hbf (k.some_lt hbe ‹_›),
      Nat.le_succ _⟩
  · exact ⟨h, Nat.le_succ _⟩

/-- Executable successor-link instance of `LinkKind.glue_spec`. -/
private theorem glueSucc_spec {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar : Nat}
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size) :
    GlueInv pt (glueSucc darts q eStar fStar).1 ufV ufD
        (glueSucc darts q eStar fStar).2
      ∧ (glueSucc darts q eStar fStar).2.live ≤ q.live + 1 := by
  simpa only [LinkKind.glue_succ] using LinkKind.succ.glue_spec h he hf

/-- Executable predecessor-link instance of `LinkKind.glue_spec`. -/
private theorem gluePred_spec {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar : Nat}
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size) :
    GlueInv pt (gluePred darts q eStar fStar).1 ufV ufD
        (gluePred darts q eStar fStar).2
      ∧ (gluePred darts q eStar fStar).2.live ≤ q.live + 1 := by
  simpa only [LinkKind.glue_pred] using LinkKind.pred.glue_spec h he hf

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

private theorem LinkKind.glue_head (k : LinkKind) (darts : Array Dart)
    (q : Queue (Nat × Nat)) (eStar fStar i : Nat) :
    ((k.glue darts q eStar fStar).1[i]!).head = (darts[i]!).head := by
  cases k <;> grind [LinkKind.glue, LinkKind.get, LinkKind.set]

private theorem LinkKind.glue_rev (k : LinkKind) (darts : Array Dart)
    (q : Queue (Nat × Nat)) (eStar fStar i : Nat) :
    ((k.glue darts q eStar fStar).1[i]!).rev = (darts[i]!).rev := by
  cases k <;> grind [LinkKind.glue, LinkKind.get, LinkKind.set]

private theorem LinkKind.glue_other {k l : LinkKind} (hkl : k ≠ l)
    (darts : Array Dart) (q : Queue (Nat × Nat)) (eStar fStar i : Nat) :
    l.get ((k.glue darts q eStar fStar).1[i]!) = l.get (darts[i]!) := by
  cases k <;> cases l <;> grind [LinkKind.glue, LinkKind.get, LinkKind.set]

/-- Reverse provenance of one generic link merge: a link present after the
merge was already present at the same representative, or was copied from the
removed root onto the surviving one. Holds for either observed link field. -/
private theorem LinkKind.glue_from {darts : Array Dart}
    {q : Queue (Nat × Nat)} {eStar fStar r : Nat} (k l : LinkKind)
    (_hf : fStar < darts.size)
    (h : ¬ (l.get ((k.glue darts q eStar fStar).1[r]!)).isNone) :
    ¬ (l.get (darts[r]!)).isNone ∨ (r = fStar ∧ ¬ (l.get (darts[eStar]!)).isNone) := by
  rcases heq : k.get (darts[eStar]!) with _ | e'
  · exact Or.inl (by simpa only [LinkKind.glue, heq] using h)
  · rcases hfeq : k.get (darts[fStar]!) with _ | f'
    · -- The copy case: the write lands at `fStar` and only touches field `k`.
      have h' : ¬ (l.get ((darts.set! fStar
          (k.set (darts[fStar]!) (.some e')))[r]!)).isNone := by
        simpa only [LinkKind.glue, heq, hfeq] using h
      by_cases hrf : r = fStar
      · subst hrf
        cases k <;> cases l
        · exact Or.inr ⟨rfl, by simp [heq]⟩
        · exact Or.inl (by
            simpa only [LinkKind.get, LinkKind.set, getElem!_set!_succ_pred] using h')
        · exact Or.inl (by
            simpa only [LinkKind.get, LinkKind.set, getElem!_set!_pred_succ] using h')
        · exact Or.inr ⟨rfl, by simp [heq]⟩
      · exact Or.inl (by
          simpa only [Array.getElem!_set!_ne (hij := Ne.symm hrf)] using h')
    · exact Or.inl (by simpa only [LinkKind.glue, heq, hfeq] using h)

/-- Lemma 9.4's common `P ∈ {succ, pred}` merge argument when the source
class is the one whose representative becomes a child. -/
private theorem LinkKind.glue_left {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar s u : Nat}
    (k : LinkKind) (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size)
    (hsu : (k.get (darts[eStar]!)).get? = Option.some u)
    (hr : PendingEq ufD q s u) :
    ∃ t, (k.get ((k.glue darts q eStar fStar).1[fStar]!)).get? = Option.some t ∧
      PendingEq ufD (k.glue darts q eStar fStar).2 s t := by
  have hbe := h.read_inBounds he
  have hbf := h.read_inBounds hf
  have hsu' := OptIdx.get?_eq_some_iff.mp hsu
  rcases heq : k.get (darts[eStar]!) with _ | e'
  · exact False.elim (OptIdx.none_ne_some u (heq.symm.trans hsu'))
  · have heu : e' = u := by
      have heq' := heq.symm.trans hsu'
      grind
    rcases hfeq : k.get (darts[fStar]!) with _ | f'
    · have hfd : fStar < darts.size := by grind [GlueInv]
      simp only [LinkKind.glue, heq, hfeq]
      refine ⟨u, ?_, hr⟩
      rw [Array.getElem!_set!_self (hi := hfd), LinkKind.get_set, heu, OptIdx.get?_some]
    · have he' : e' < ufD.n := by
        grind [GlueInv, LinkKind.some_lt hbe heq]
      have hf' : f' < ufD.n := by
        grind [GlueInv, LinkKind.some_lt hbf hfeq]
      simp only [LinkKind.glue, heq, hfeq]
      refine ⟨f', by simp [OptIdx.get?], ?_⟩
      exact hr.push.trans (heu ▸ PendingEq.queued he' hf' Queue.active_push_self)

/-- The same link survives unchanged for every class whose representative is
not the left root being removed. -/
private theorem LinkKind.glue_other_root {darts : Array Dart}
    {ufD : Unionfind} {q : Queue (Nat × Nat)} {eStar fStar r s u : Nat}
    (k : LinkKind)
    (hru : (k.get (darts[r]!)).get? = Option.some u)
    (hsu : PendingEq ufD q s u) :
    (k.get ((k.glue darts q eStar fStar).1[r]!)).get? = Option.some u ∧
      PendingEq ufD (k.glue darts q eStar fStar).2 s u := by
  have hru' := OptIdx.get?_eq_some_iff.mp hru
  rcases heq : k.get (darts[eStar]!) with _ | e'
  · simp only [LinkKind.glue, heq]
    exact ⟨hru, hsu⟩
  · rcases hfeq : k.get (darts[fStar]!) with _ | f'
    · by_cases hrf : r = fStar
      · subst r
        exact False.elim (OptIdx.none_ne_some u (hfeq.symm.trans hru'))
      · simp only [LinkKind.glue, heq, hfeq]
        rw [Array.getElem!_set!_ne (hij := Ne.symm hrf)]
        exact ⟨hru, hsu⟩
    · simp only [LinkKind.glue, heq, hfeq]
      exact ⟨hru, hsu.push⟩

/-- A link of the class represented by `r` after one generic link merge. If
`r` is the discarded root, its link is read from the surviving root. -/
private theorem LinkKind.glue_root {pt : PseudoTriangulation}
    {darts : Array Dart} {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    {eStar fStar r s u : Nat} (k : LinkKind)
    (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size)
    (hru : (k.get (darts[r]!)).get? = Option.some u)
    (hsu : PendingEq ufD q s u) :
    ∃ t, (k.get ((k.glue darts q eStar fStar).1[
        if r = eStar then fStar else r]!)).get? = Option.some t ∧
      PendingEq ufD (k.glue darts q eStar fStar).2 s t := by
  by_cases hre : r = eStar
  · simpa only [if_pos hre] using k.glue_left h he hf (hre ▸ hru) hsu
  · obtain ⟨ht, hst⟩ := k.glue_other_root hru hsu
    exact ⟨u, by simpa only [if_neg hre] using ht, hst⟩

/-- Semantic effect of the consecutive `succ` and `pred` merges, independent
of which of the two link fields is being observed. -/
private theorem glueBoth_link {pt : PseudoTriangulation} {darts : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    {eStar fStar r s u : Nat} (h : GlueInv pt darts ufV ufD q)
    (he : eStar < pt.darts.size) (hf : fStar < pt.darts.size)
    (k : LinkKind) (hru : (k.get (darts[r]!)).get? = Option.some u)
    (hsu : PendingEq ufD q s u) :
    let succ := LinkKind.succ.glue darts q eStar fStar
    let pred := LinkKind.pred.glue succ.1 succ.2 eStar fStar
    ∃ t, (k.get (pred.1[if r = eStar then fStar else r]!)).get? = Option.some t ∧
      PendingEq ufD pred.2 s t := by
  intro succ pred
  cases k with
  | succ =>
      obtain ⟨t, ht, hst⟩ := LinkKind.succ.glue_root h he hf hru hsu
      refine ⟨t, ?_, hst.glue⟩
      exact (congrArg OptIdx.get?
        (LinkKind.glue_other (k := .pred) (l := .succ) (by decide)
          succ.1 succ.2 eStar fStar _)).trans ht
  | pred =>
      have hlink : (LinkKind.pred.get (succ.1[r]!)).get? = Option.some u :=
        (congrArg OptIdx.get?
          (LinkKind.glue_other (k := .succ) (l := .pred) (by decide)
            darts q eStar fStar r)).trans hru
      exact LinkKind.pred.glue_root ((glueSucc_spec h he hf).1) he hf hlink hsu.glue

/-- Reverse provenance across the consecutive `succ` and `pred` merges
(parallel to `glueBoth_link`): a link present afterwards was already present,
either at the same representative or copied from the removed root onto the
surviving one. -/
private theorem glueBoth_from {darts : Array Dart} {q : Queue (Nat × Nat)}
    {eStar fStar r : Nat} (k : LinkKind) (hf : fStar < darts.size)
    (h : ¬ (k.get ((gluePred (glueSucc darts q eStar fStar).1
        (glueSucc darts q eStar fStar).2 eStar fStar).1[r]!)).isNone) :
    ¬ (k.get (darts[r]!)).isNone ∨ (r = fStar ∧ ¬ (k.get (darts[eStar]!)).isNone) := by
  have hsz : (LinkKind.succ.glue darts q eStar fStar).1.size = darts.size := by
    unfold LinkKind.glue
    split <;> simp
  have h' : ¬ (k.get ((LinkKind.pred.glue (LinkKind.succ.glue darts q eStar fStar).1
      (LinkKind.succ.glue darts q eStar fStar).2 eStar fStar).1[r]!)).isNone := by
    simpa only [LinkKind.glue_succ, LinkKind.glue_pred] using h
  rcases LinkKind.glue_from .pred k (hsz.symm ▸ hf) h' with h1 | ⟨hrf, h1⟩
  · rcases LinkKind.glue_from .succ k hf h1 with h2 | ⟨hrf, h2⟩
    · exact Or.inl h2
    · exact Or.inr ⟨hrf, h2⟩
  · rcases LinkKind.glue_from .succ k hf h1 with h2 | ⟨-, h2⟩
    · exact Or.inr ⟨hrf, h2⟩
    · exact Or.inr ⟨hrf, h2⟩

/-- One nontrivial worklist step preserves Lemma 9.4's semantic invariant.
The vertex forest may either perform the requested head union or stay put
when those heads were already identified; `hVmono`/`hVpair` cover both cases. -/
private theorem GlueCoherent.glue_step {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)} {darts : Array Dart}
    {ufV ufV' ufD : Unionfind} {q q' : Queue (Nat × Nat)} {e f : Nat}
    (hpop : q.pop? = some ((e, f), q')) (hsame : ¬ ufD.same e f = true)
    (hinv : GlueInv pt darts ufV ufD q)
    (hcoh : GlueCoherent pt dartPairs darts ufV ufD q)
    (hVn : ufV'.n = pt.n) (hVwf : ufV'.WF)
    (hVmono : ∀ {a b}, a < pt.n → b < pt.n →
      ufV.root a = ufV.root b → ufV'.root a = ufV'.root b)
    (hVpair : ufV'.root (darts[e]!).head = ufV'.root (darts[f]!).head) :
    let eStar := ufD.root e
    let fStar := ufD.root f
    let ufD' := ufD.unite eStar fStar
    let revQ := q'.push ((darts[eStar]!).rev, (darts[fStar]!).rev)
    let succ := glueSucc darts revQ eStar fStar
    let pred := gluePred succ.1 succ.2 eStar fStar
    GlueCoherent pt dartPairs pred.1 ufV' ufD' pred.2 := by
  dsimp only []
  have hef := hinv.queued _ (Queue.active_head hpop)
  have hre := hinv.root_lt hef.1
  have hrf := hinv.root_lt hef.2
  have hne : ufD.root e ≠ ufD.root f :=
    Unionfind.root_ne_of_not_same hsame
  have hcore0 := (hinv.glue hpop hsame).1
  have hcore : GlueInv pt darts ufV'
      (ufD.unite (ufD.root e) (ufD.root f))
      (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev)) :=
    ⟨hcore0.darts_size, hVn, hcore0.ufD_n, hVwf, hcore0.ufD_wf,
      hcore0.darts_wf, hcore0.queued⟩
  let succState := glueSucc darts
    (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
    (ufD.root e) (ufD.root f)
  let predState := gluePred succState.1 succState.2 (ufD.root e) (ufD.root f)
  have afterCore {a b : Nat} (hab : PendingEq ufD q a b) :
      PendingEq (ufD.unite (ufD.root e) (ufD.root f))
        (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev)) a b := by
    simpa only [Unionfind.unite_roots hinv.ufD_wf
      (hinv.ufD_n.symm ▸ hef.1) (hinv.ufD_n.symm ▸ hef.2)] using
      (hab.pop_unite hinv.ufD_wf hpop
        (hinv.ufD_n.symm ▸ hef.1) (hinv.ufD_n.symm ▸ hef.2) hne).push
  have throughAll {a b : Nat}
      (hab : PendingEq (ufD.unite (ufD.root e) (ufD.root f))
        (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev)) a b) :
      PendingEq (ufD.unite (ufD.root e) (ufD.root f)) predState.2 a b := by
    simpa only [succState, predState, LinkKind.glue_succ,
      LinkKind.glue_pred] using
      (hab.glue (k := .succ) (darts := darts)
        (eStar := ufD.root e) (fStar := ufD.root f)).glue
          (k := .pred) (darts := succState.1)
          (eStar := ufD.root e) (fStar := ufD.root f)
  have afterAll {a b : Nat} (hab : PendingEq ufD q a b) :
      PendingEq (ufD.unite (ufD.root e) (ufD.root f)) predState.2 a b :=
    throughAll (afterCore hab)
  have rootAfter (i : Nat) (hi : i < pt.darts.size) :
      (ufD.unite (ufD.root e) (ufD.root f)).root i =
        if ufD.root i = ufD.root e then ufD.root f else ufD.root i := by
    simpa only [Unionfind.unite_roots hinv.ufD_wf
      (hinv.ufD_n.symm ▸ hef.1) (hinv.ufD_n.symm ▸ hef.2)] using
      Unionfind.root_unite_of_ne hinv.ufD_wf
        (hinv.ufD_n.symm ▸ hef.1) (hinv.ufD_n.symm ▸ hef.2)
        (hinv.ufD_n.symm ▸ hi) hne
  have headFinal (i : Nat) : (predState.1[i]!).head = (darts[i]!).head := by
    calc
      (predState.1[i]!).head = (succState.1[i]!).head := by
        simpa only [predState, LinkKind.glue_pred] using
          LinkKind.glue_head .pred succState.1 succState.2
            (ufD.root e) (ufD.root f) i
      _ = (darts[i]!).head := by
        simpa only [succState, LinkKind.glue_succ] using
          LinkKind.glue_head .succ darts
            (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
            (ufD.root e) (ufD.root f) i
  have revFinal (i : Nat) : (predState.1[i]!).rev = (darts[i]!).rev := by
    calc
      (predState.1[i]!).rev = (succState.1[i]!).rev := by
        simpa only [predState, LinkKind.glue_pred] using
          LinkKind.glue_rev .pred succState.1 succState.2
            (ufD.root e) (ufD.root f) i
      _ = (darts[i]!).rev := by
        simpa only [succState, LinkKind.glue_succ] using
          LinkKind.glue_rev .succ darts
            (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
            (ufD.root e) (ufD.root f) i
  have hrevPair : PendingEq (ufD.unite (ufD.root e) (ufD.root f))
      (q'.push ((darts[ufD.root e]!).rev, (darts[ufD.root f]!).rev))
      (darts[ufD.root e]!).rev (darts[ufD.root f]!).rev := by
    exact .queued
      (by simpa only [Unionfind.n_unite, hinv.ufD_n, ← hinv.darts_size] using
        (hinv.read_inBounds hre).rev_lt)
      (by simpa only [Unionfind.n_unite, hinv.ufD_n, ← hinv.darts_size] using
        (hinv.read_inBounds hrf).rev_lt)
      Queue.active_push_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (headFinal i).trans (hcoh.head_eq i hi)
  · intro i hi
    have hsrc := hpt.read_inBounds hi
    have hri := hinv.root_lt hi
    have hdst := hinv.read_inBounds hri
    have hbase := hVmono hsrc.head_lt hdst.head_lt (hcoh.head i hi)
    by_cases hir : ufD.root i = ufD.root e
    · have heHead := hVmono (hpt.read_inBounds hef.1).head_lt
          (hinv.read_inBounds hre).head_lt (hcoh.head e hef.1)
      have hfHead := hVmono (hpt.read_inBounds hef.2).head_lt
          (hinv.read_inBounds hrf).head_lt (hcoh.head f hef.2)
      have hefHead : ufV'.root (darts[ufD.root e]!).head =
          ufV'.root (darts[ufD.root f]!).head :=
        heHead.symm.trans
          ((congrArg ufV'.root (hcoh.head_eq e hef.1).symm).trans
            (hVpair.trans
              ((congrArg ufV'.root (hcoh.head_eq f hef.2)).trans hfHead)))
      rw [rootAfter i hi, if_pos hir, headFinal]
      exact (hir ▸ hbase).trans hefHead
    · rw [rootAfter i hi, if_neg hir, headFinal]
      exact hbase
  · intro i hi
    have hbase := afterCore (hcoh.rev i hi)
    by_cases hir : ufD.root i = ufD.root e
    · have hrel := (hir ▸ hbase).trans hrevPair
      rw [rootAfter i hi, if_pos hir, revFinal]
      exact throughAll hrel
    · rw [rootAfter i hi, if_neg hir, revFinal]
      exact throughAll hbase
  · intro k i hi s hs
    obtain ⟨u, hlink, hsu⟩ := hcoh.link_of k i hi s hs
    have hsu' := afterCore hsu
    obtain ⟨t, ht, hst⟩ := glueBoth_link hcore hre hrf k hlink hsu'
    refine ⟨t, ?_, ?_⟩
    · rw [rootAfter i hi]
      simpa only [succState, predState, LinkKind.glue_succ,
        LinkKind.glue_pred] using ht
    · simpa only [succState, predState, LinkKind.glue_succ,
        LinkKind.glue_pred] using hst
  · intro k i hi hnn
    have happ : ∀ {r : Nat}, ¬ (k.get (predState.1[r]!)).isNone →
        ¬ (k.get (darts[r]!)).isNone
          ∨ (r = ufD.root f ∧ ¬ (k.get (darts[ufD.root e]!)).isNone) := fun {r} hr =>
      glueBoth_from k (hinv.darts_size.symm ▸ hrf)
        (by simpa only [succState, predState] using hr)
    have hnn' := rootAfter i hi ▸ hnn
    by_cases hir : ufD.root i = ufD.root e
    · have hnn'' : ¬ (k.get (predState.1[ufD.root f]!)).isNone := by
        simpa only [succState, predState, LinkKind.glue_succ, LinkKind.glue_pred,
          if_pos hir] using hnn'
      rcases happ hnn'' with hf' | ⟨-, he'⟩
      · obtain ⟨j, hj, hjr, hjs⟩ := hcoh.link_from k f hef.2 hf'
        refine ⟨j, hj, ?_, hjs⟩
        rw [rootAfter j hj, rootAfter i hi,
          if_neg (fun hc => hne (hc.symm.trans hjr)), if_pos hir]
        exact hjr
      · obtain ⟨j, hj, hjr, hjs⟩ := hcoh.link_from k e hef.1 he'
        refine ⟨j, hj, ?_, hjs⟩
        rw [rootAfter j hj, rootAfter i hi, if_pos hjr, if_pos hir]
    · have hnn'' : ¬ (k.get (predState.1[ufD.root i]!)).isNone := by
        simpa only [succState, predState, LinkKind.glue_succ, LinkKind.glue_pred,
          if_neg hir] using hnn'
      rcases happ hnn'' with hd' | ⟨hrf, he'⟩
      · obtain ⟨j, hj, hjr, hjs⟩ := hcoh.link_from k i hi hd'
        refine ⟨j, hj, ?_, hjs⟩
        rw [rootAfter j hj, rootAfter i hi,
          if_neg (fun hc => hir (hjr.symm.trans hc)), if_neg hir]
        exact hjr
      · obtain ⟨j, hj, hjr, hjs⟩ := hcoh.link_from k e hef.1 he'
        refine ⟨j, hj, ?_, hjs⟩
        rw [rootAfter j hj, rootAfter i hi, if_pos hjr, if_neg hir]
        exact hrf.symm
  · intro p hp
    exact afterAll (hcoh.seeds p hp)

/-- On the gluing closure's exit state, the dart emitted for a surviving
representative is in bounds for the quotient -- `head` through the total
vertex relabelling, `rev` through the total dart relabelling, and open
`succ`/`pred` links through its `Bounded` half. -/
private theorem renumberDart_inBounds {pt : PseudoTriangulation}
    {darts : Array Dart} {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    (h : GlueInv pt darts ufV ufD q) {d : Nat} (hd : d < pt.darts.size) :
    let vMap := ufV.relabel
    let dMap := ufD.relabel
    let dd := darts[d]!
    (renumberDart vMap dMap dd).InBounds ufV.numRoots ufD.numRoots := by
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

private theorem LinkKind.get_renumberDart {vMap dMap : IndexMap} {d : Dart}
    {k : LinkKind} {i : Nat} (h : (k.get d).get? = Option.some i) :
    (k.get (renumberDart vMap dMap d)).get? = (dMap[i]!).get? := by
  have hi := OptIdx.get?_eq_some_iff.mp h
  cases k <;> simp_all [LinkKind.get, renumberDart]

/-- A renumbered dart has a closed link only where the representative had
one: the rebuild maps links, it does not create them. -/
private theorem LinkKind.renumberDart_from {vMap dMap : IndexMap} {d : Dart}
    {k : LinkKind} (h : ¬ (k.get (renumberDart vMap dMap d)).isNone) :
    ¬ (k.get d).isNone := by
  cases k <;> rcases hs : d.succ with _ | s <;> rcases hp : d.pred with _ | p <;>
    simp_all [LinkKind.get, renumberDart]

/-- Specification of the completed renumbered dart array: one slot per root,
every emitted dart in bounds for the quotient, and the slot at a root's
compact index exactly the renumbered dart the root reads. -/
private structure RenumberSpec (darts : Array Dart) (ufV ufD : Unionfind)
    (dartsStar : Array Dart) : Prop where
  size_eq : dartsStar.size = ufD.numRoots
  dart_wf : ∀ i (h : i < dartsStar.size),
    (dartsStar[i]'h).InBounds ufV.numRoots ufD.numRoots
  value_eq : ∀ (r : ufD.Root) (h : (ufD.rootIndexEquiv r).val < dartsStar.size),
    dartsStar[(ufD.rootIndexEquiv r).val]'h =
      renumberDart ufV.relabel ufD.relabel (r.read darts)

/-- `materialiseQuotient`'s renumber pass meets `RenumberSpec`: `Array.map`
gives the size and slot values by library rewrites, boundedness is pointwise
from `renumberDart_inBounds`, and the root-indexed value law is
`rootIndexEquiv.left_inv` through `Root.read_allRoots`. -/
private theorem RenumberSpec.of_map {pt : PseudoTriangulation}
    {darts : Array Dart} {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    (hinv : GlueInv pt darts ufV ufD q) :
    RenumberSpec darts ufV ufD
      (ufD.allRoots.map fun d =>
        renumberDart ufV.relabel ufD.relabel darts[d]!) := by
  refine ⟨Array.size_map .., ?_, ?_⟩
  · intro i hi
    rw [Array.getElem_map]
    exact renumberDart_inBounds hinv
      (hinv.ufD_n ▸ Unionfind.mem_allRoots_lt (ufD.allRoots.getElem_mem _))
  · intro r h
    have h' : (ufD.rootIndexEquiv r).val < ufD.allRoots.size := by
      simpa using h
    rw [Array.getElem_map, ← getElem!_pos ufD.allRoots _ h',
      Unionfind.Root.read_allRoots]

/-- Slot-indexed corollary of `value_eq`: slot `c` holds the renumbered
representative stored at `allRoots[c]` -- `rootIndexEquiv.right_inv` names
the root occupying the slot. For consumers that require a source-dart index
(`link_from`'s interface). -/
private theorem RenumberSpec.value_eq_slot {darts : Array Dart}
    {ufV ufD : Unionfind} {dartsStar : Array Dart}
    (h : RenumberSpec darts ufV ufD dartsStar) {c : Nat}
    (hc : c < dartsStar.size) :
    dartsStar[c]'hc =
      renumberDart ufV.relabel ufD.relabel (darts[ufD.allRoots[c]!]!) := by
  have hcn : c < ufD.numRoots := h.size_eq ▸ hc
  let r := ufD.rootIndexEquiv.invFun ⟨c, hcn⟩
  have hrc : (ufD.rootIndexEquiv r).val = c :=
    congrArg Fin.val (ufD.rootIndexEquiv.right_inv ⟨c, hcn⟩)
  have hread : darts[ufD.allRoots[c]!]! = r.read darts := by
    simpa only [hrc] using Unionfind.Root.read_allRoots r darts
  have hv := h.value_eq r (by rw [hrc]; exact hc)
  rw [hread]
  simpa only [hrc] using hv

/-- At an empty worklist, the semantic gluing invariant and the exact
renumbering specification yield A.3's quotient-map coherence. -/
private theorem GlueCoherent.finish {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)} {darts dartsStar : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    (hinv : GlueInv pt darts ufV ufD q)
    (hcoh : GlueCoherent pt dartPairs darts ufV ufD q)
    (hri : RenumberSpec darts ufV ufD dartsStar)
    (hq : q.isEmpty = true) :
    let vMap := ufV.relabel
    let dMap := ufD.relabel
    Mappings.Coherent ⟨vMap, dMap⟩ pt ⟨ufV.numRoots, dartsStar⟩ ∧
      (∀ p ∈ dartPairs, dMap.idx? p.1 = dMap.idx? p.2) ∧
      ∀ (k : LinkKind) c, c < dartsStar.size → ¬ (k.get (dartsStar[c]!)).isNone →
        ∃ j, j < pt.darts.size ∧ dMap.idx? j = Option.some c ∧
          ¬ (k.get (pt.darts[j]!)).isNone := by
  intro vMap dMap
  refine ⟨?_, ?_, ?_⟩
  · intro f fStar hf
    obtain ⟨hfMap, -⟩ := IndexMap.idx?_eq_some_iff.mp hf
    have hfi : f < ufD.n := by
      simpa only [Unionfind.size_relabel] using
        show f < ufD.relabel.size from hfMap
    have hfpt : f < pt.darts.size := by simpa only [hinv.ufD_n] using hfi
    have hsrc := hpt.read_inBounds hfpt
    have hr := hinv.root_lt hfpt
    have hrep := hinv.read_inBounds hr
    have hfStar : fStar =
        (ufD.rootIndexEquiv (Unionfind.Root.ofNode hinv.ufD_wf ⟨f, hfi⟩)).val :=
      Option.some.inj (hf.symm.trans (ufD.relabel_idx?_root hinv.ufD_wf hfi))
    have hfStarLt : fStar < dartsStar.size := by
      have hDwf := (Unionfind.relabel_wf ufD hinv.ufD_wf).1
      have := IndexMap.idx?_lt_of_bounded hDwf.bounded hf
      simpa only [← hri.size_eq] using this
    have hout : dartsStar[fStar]! = renumberDart vMap dMap (darts[ufD.root f]!) := by
      rw [getElem!_pos dartsStar fStar hfStarLt]
      have hv := hri.value_eq (Unionfind.Root.ofNode hinv.ufD_wf ⟨f, hfi⟩)
        (hfStar ▸ hfStarLt)
      simpa only [Unionfind.Root.read_ofNode, ← hfStar] using hv
    have hsrcV : (pt.darts[f]!).head < ufV.n := by
      simpa only [hinv.ufV_n] using hsrc.head_lt
    have hrepV : (darts[ufD.root f]!).head < ufV.n := by
      simpa only [hinv.ufV_n, hinv.darts_size] using hrep.head_lt
    have houtHead := congrArg Dart.head hout
    have houtRev := congrArg Dart.rev hout
    have finishLink (k : LinkKind) (s : Nat)
        (hs : (k.get (pt.darts[f]!)).get? = Option.some s) :
        ∃ tStar, (k.get (dartsStar[fStar]!)).get? = Option.some tStar ∧
          dMap.idx? s = Option.some tStar := by
      obtain ⟨t, ht, hst⟩ := hcoh.link_of k f hfpt s hs
      refine ⟨ufD.rootRank (ufD.root t), ?_, ?_⟩
      · rw [hout, LinkKind.get_renumberDart ht,
          ufD.relabel_getElem! hinv.ufD_wf hst.right_lt]
        simp
      · calc
          dMap.idx? s = Option.some (ufD.rootRank (ufD.root s)) :=
            ufD.relabel_idx? hinv.ufD_wf hst.left_lt
          _ = Option.some (ufD.rootRank (ufD.root t)) := by
            rw [hst.root_eq_of_empty hq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        vMap.idx? (pt.darts[f]!).head =
            Option.some (ufV.rootRank (ufV.root (pt.darts[f]!).head)) :=
          ufV.relabel_idx? hinv.ufV_wf hsrcV
        _ = Option.some (ufV.rootRank (ufV.root (darts[ufD.root f]!).head)) := by
          rw [hcoh.head f hfpt]
        _ = Option.some (dartsStar[fStar]!).head := by
          rw [houtHead, renumberDart, ufV.relabel_idx! hinv.ufV_wf hrepV]
    · have hrev := (hcoh.rev f hfpt).root_eq_of_empty hq
      calc
        dMap.idx? (pt.darts[f]!).rev =
            Option.some (ufD.rootRank (ufD.root (pt.darts[f]!).rev)) :=
          ufD.relabel_idx? hinv.ufD_wf (hinv.ufD_n.symm ▸ hsrc.rev_lt)
        _ = Option.some (ufD.rootRank (ufD.root (darts[ufD.root f]!).rev)) := by
          rw [hrev]
        _ = Option.some (dartsStar[fStar]!).rev := by
          rw [houtRev, renumberDart, ufD.relabel_idx! hinv.ufD_wf
            (hinv.ufD_n.symm ▸ hinv.darts_size ▸ hrep.rev_lt)]
    · intro s hs
      simpa only [LinkKind.get] using finishLink .succ s hs
    · intro p hp
      simpa only [LinkKind.get] using finishLink .pred p hp
  · intro p hp
    have hseed := hcoh.seeds p hp
    rw [ufD.relabel_idx? hinv.ufD_wf hseed.left_lt,
      ufD.relabel_idx? hinv.ufD_wf hseed.right_lt,
      hseed.root_eq_of_empty hq]
  · -- Link provenance: slot `c` holds the renumbered root of compact index
    -- `c`; a closed link there descends, through the rebuild and then
    -- `link_from`, to some source dart of that class.
    intro k c hc hnn
    have hcn : c < ufD.numRoots := by
      simpa only [← hri.size_eq] using hc
    obtain ⟨hrlt, hroot, hrank⟩ := Unionfind.rootRank_allRoots hcn
    have hrpt : ufD.allRoots[c]! < pt.darts.size := by
      simpa only [hinv.ufD_n] using hrlt
    have hout : dartsStar[c]! = renumberDart vMap dMap (darts[ufD.allRoots[c]!]!) := by
      rw [getElem!_pos dartsStar c hc]
      exact hri.value_eq_slot hc
    have hrep : ¬ (k.get (darts[ufD.allRoots[c]!]!)).isNone :=
      LinkKind.renumberDart_from (hout ▸ hnn)
    have hself : ufD.root ufD.allRoots[c]! = ufD.allRoots[c]! :=
      Unionfind.root_eq_self hroot
    obtain ⟨j, hj, hjr, hjs⟩ := hcoh.link_from k ufD.allRoots[c]! hrpt (hself.symm ▸ hrep)
    refine ⟨j, hj, ?_, hjs⟩
    rw [ufD.relabel_idx? hinv.ufD_wf (hinv.ufD_n.symm ▸ hj), hjr, hself, hrank]

/-- At an empty worklist, the gluing connectivity invariant transports along
`rootRank`, `allRoots`, and the two relabellings to A.3's quotient
connectivity: source darts with a common quotient head are connected in the
quotient of the dart forest. -/
private theorem GlueConnected.finish {pt : PseudoTriangulation} (hwf : pt.WF)
    {darts : Array Dart} {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    (hinv : GlueInv pt darts ufV ufD q)
    (hconn : GlueConnected pt ufV ufD q)
    (hq : q.isEmpty = true) :
    let vMap := ufV.relabel
    let dMap := ufD.relabel
    ∀ a b : Fin pt.darts.size,
      vMap.idx? (pt.darts[a.val]!).head = vMap.idx? (pt.darts[b.val]!).head →
      DartGraph.QuotientConn (pt.dartGraph hwf)
        (fun d : Fin pt.darts.size => dMap.idx? d.val) a b := by
  intro vMap dMap a b hidx
  have hha : (pt.darts[a.val]!).head < ufV.n :=
    Nat.lt_of_lt_of_eq (hwf.read_inBounds a.isLt).head_lt hinv.ufV_n.symm
  have hhb : (pt.darts[b.val]!).head < ufV.n :=
    Nat.lt_of_lt_of_eq (hwf.read_inBounds b.isLt).head_lt hinv.ufV_n.symm
  have hroot := (Unionfind.relabel_idx?_eq_iff_root_eq hinv.ufV_wf hha hhb).mp hidx
  have hqc := (hconn a.val b.val a.isLt b.isLt hroot).to_quotientConn
    hwf hinv.ufD_n hq a.isLt b.isLt
  exact hqc.mono fun x y hxy =>
    (Unionfind.relabel_idx?_eq_iff_root_eq hinv.ufD_wf
      (Nat.lt_of_lt_of_eq x.isLt hinv.ufD_n.symm)
      (Nat.lt_of_lt_of_eq y.isLt hinv.ufD_n.symm)).mpr hxy

section
-- The transparency linter flags `mvcgen`'s own `Invariant` encoding (the `⇓`
-- postconditions), not this proof's text; nothing here to rephrase.
set_option linter.tacticCheckInstances false

/-- The combined A.3 contract: the quotient graph is well-formed, the maps
are total, well-formed relabellings that are also *onto* the quotient's index
ranges, they commute with every dart field (interior links map forward),
every seed pair is identified, and every closed quotient link has a source
antecedent in its dart class. Private carrier: the public tiered theorems
below expose only the facts their callers request. -/
private structure FreeHomomorphismSpec (pt : PseudoTriangulation)
    (dartPairs : Array (Nat × Nat)) (ptStar : PseudoTriangulation)
    (maps : Mappings) : Prop where
  graph_wf : ptStar.WF
  maps_wf : maps.WF pt.n pt.darts.size ptStar.n ptStar.darts.size
  vmap_total : maps.vmap.Total
  dmap_total : maps.dmap.Total
  coherent : maps.Coherent pt ptStar
  seeds : ∀ p ∈ dartPairs, maps.dmap.idx? p.1 = maps.dmap.idx? p.2
  vmap_surj : ∀ j, j < ptStar.n → ∃ i, i < pt.n ∧ maps.vmap.idx? i = Option.some j
  dmap_surj : ∀ j, j < ptStar.darts.size →
    ∃ i, i < pt.darts.size ∧ maps.dmap.idx? i = Option.some j
  link_from : ∀ (k : LinkKind) c, c < ptStar.darts.size →
    ¬ (k.get (ptStar.darts[c]!)).isNone →
    ∃ j, j < pt.darts.size ∧ maps.dmap.idx? j = Option.some c ∧
      ¬ (k.get (pt.darts[j]!)).isNone
  conn : ∀ (hwf : pt.WF), (pt.dartGraph hwf).Rotational →
    ∀ (a b : Fin pt.darts.size),
    maps.vmap.idx? (pt.darts[a.val]!).head = maps.vmap.idx? (pt.darts[b.val]!).head →
    DartGraph.QuotientConn (pt.dartGraph hwf)
      (fun d : Fin pt.darts.size => maps.dmap.idx? d.val) a b

/-- The phase-one contract: the gluing closure's exit state satisfies the
structural (`GlueInv`) and semantic (`GlueCoherent`, `GlueConnected`)
invariants at a drained queue. The queue is a proof-only ghost witness of the
exhausted worklist; it is not part of the runtime result. -/
private inductive GlueClosureSpec (pt : PseudoTriangulation) (hpt : pt.WF)
    (dartPairs : Array (Nat × Nat)) (c : HomomorphismClosure) : Prop where
  | intro (queue : Queue (Nat × Nat))
      (inv : GlueInv pt c.darts c.ufV c.ufD queue)
      (coherent : GlueCoherent pt dartPairs c.darts c.ufV c.ufD queue)
      (connected : (pt.dartGraph hpt).Rotational →
        GlueConnected pt c.ufV c.ufD queue)
      (drained : queue.isEmpty = true)

/-- Phase-one soundness: running the gluing worklist meets its contract. -/
private theorem glueClosure_spec {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {c : HomomorphismClosure} (hrun : pt.glueClosure dartPairs = c) :
    GlueClosureSpec pt hpt dartPairs c := by
  apply Std.Internal.Do.Id.of_wp_run_eq hrun (GlueClosureSpec pt hpt dartPairs)
  vcgen invariants
    | inv1 => GlueSpecSum pt hpt dartPairs
    | inv2 => glueMeasure
  -- Seed state: fresh forests, the input graph, the seeded queue.
  case vc1 =>
    exact ⟨GlueInv.mk rfl rfl rfl (Unionfind.wf_new _) (Unionfind.wf_new _) hpt
        (fun p hp => hpairs p (Queue.active_ofArray hp)),
      GlueCoherent.init hpt hpairs,
      fun hr => GlueConnected.init hpt hr dartPairs⟩
  -- Exit: the break-side invariant is the claim, at the loop's final queue.
  case vc2 =>
    obtain ⟨hinv, hcoh, hcm, hqempty⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ ∧ _ ∧ _ := ‹_›
    exact ⟨_, hinv, hcoh, hcm, hqempty⟩
  -- Continue branch: the popped pair is already merged; only the queue shrinks.
  case vc3 =>
    simp_all +zetaDelta
    grind only [GlueSpecSum, glueMeasure, !GlueInv.pop,
      !GlueCoherent.pop_same, !GlueConnected.pop_same, !Queue.live_pop]
  -- Glue branches (with and without the vertex unite): the shared core covers
  -- pop + dart-unite + reverse push, then the two adjacency steps compose.
  case vc4 =>
    simp
    obtain ⟨hinv, hcoh, hcm⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ ∧ _ := ‹_›
    obtain ⟨h1, ⟨hhe, hhf⟩, ⟨hre, hrf⟩, hdec⟩ :=
      GlueInv.glue ‹_› ‹_› hinv
    obtain ⟨h4, hq⟩ := glueBoth_spec (h1.uniteV hhe hhf) hre hrf
    have hcoh4 := GlueCoherent.glue_step hpt ‹_› ‹_› hinv hcoh
      (by simp [hinv.ufV_n])
      (hinv.ufV_wf.unite (hinv.ufV_n.symm ▸ hhe) (hinv.ufV_n.symm ▸ hhf))
      (fun ha hb hab => Unionfind.root_unite_eq hinv.ufV_wf
        (hinv.ufV_n.symm ▸ hhe) (hinv.ufV_n.symm ▸ hhf)
        (hinv.ufV_n.symm ▸ ha) (hinv.ufV_n.symm ▸ hb) hab)
      (Unionfind.root_unite_same hinv.ufV_wf
        (hinv.ufV_n.symm ▸ hhe) (hinv.ufV_n.symm ▸ hhf))
    have hcm4 := fun hr => GlueConnected.glue_step hpt ‹_› ‹_› hinv hcoh.head_eq
      (fun a b ha hb hab => Unionfind.root_unite_cases hinv.ufV_wf
        (hinv.ufV_n.symm ▸ hhe) (hinv.ufV_n.symm ▸ hhf) ha hb
        (by grind [Unionfind.same]) hab)
      (hcm hr)
    exact ⟨by grind [glueMeasure, Queue.live_pop, Queue.live_push],
      h4, hcoh4, hcm4⟩
  case vc5 =>
    simp
    obtain ⟨hinv, hcoh, hcm⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ ∧ _ := ‹_›
    obtain ⟨h1, _, ⟨hre, hrf⟩, hdec⟩ :=
      GlueInv.glue ‹_› ‹_› hinv
    obtain ⟨h4, hq⟩ := glueBoth_spec h1 hre hrf
    have hcoh4 := GlueCoherent.glue_step hpt ‹_› ‹_› hinv hcoh
      hinv.ufV_n hinv.ufV_wf (fun _ _ hab => hab) (by grind [Unionfind.same])
    have hcm4 := fun hr => GlueConnected.glue_step hpt ‹_› ‹_› hinv hcoh.head_eq
      (fun a b _ _ hab => Or.inl hab) (hcm hr)
    exact ⟨by grind [glueMeasure, Queue.live_pop, Queue.live_push],
      h4, hcoh4, hcm4⟩
  -- Exhausted queue: the break-side invariant is the continue-side one.
  case vc6 =>
    have hspec : GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ ∧ _ := ‹_›
    exact ⟨hspec.1, hspec.2.1, hspec.2.2,
      Queue.pop?_none (Queue.pop?_eq_none_of_no_pair ‹_› ‹_›)⟩

/-- Phase-two soundness: materialising the quotient from any state meeting
the phase-one contract yields the combined A.3 specification. The maps are
the union-find relabellings, total and well-formed by `relabel_wf`;
`GlueInv` pins the domain sizes and carries the quotient graph's bounds, the
renumber size specification pins the dart codomain. -/
private theorem materialiseQuotient_spec {pt : PseudoTriangulation}
    {hpt : pt.WF} {dartPairs : Array (Nat × Nat)} {c : HomomorphismClosure}
    (hspec : GlueClosureSpec pt hpt dartPairs c)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : materialiseQuotient c = (ptStar, maps)) :
    FreeHomomorphismSpec pt dartPairs ptStar maps := by
  obtain ⟨q, hinv', hcoh, hcm, hqempty⟩ := hspec
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  have hri := RenumberSpec.of_map (pt := pt) (q := q) hinv'
  obtain ⟨hVwf, hVtot⟩ := Unionfind.relabel_wf _ hinv'.ufV_wf
  obtain ⟨hDwf, hDtot⟩ := Unionfind.relabel_wf _ hinv'.ufD_wf
  obtain ⟨hcoherent, hseeds, hfrom⟩ :=
    GlueCoherent.finish hpt hinv' hcoh hri hqempty
  refine
    { graph_wf :=
        fun i hi => by grind [RenumberSpec, Unionfind.numRoots]
      maps_wf := ⟨by grind [GlueInv],
        by grind [RenumberSpec, GlueInv, Unionfind.numRoots]⟩
      vmap_total := hVtot
      dmap_total := hDtot
      coherent := hcoherent
      seeds := hseeds
      vmap_surj := ?_
      dmap_surj := ?_
      link_from := hfrom
      conn := fun hwf hr =>
        GlueConnected.finish hwf hinv' (hcm hr) hqempty }
  · intro j hj
    obtain ⟨i, hi, hidx⟩ := Unionfind.relabel_surjective _ hinv'.ufV_wf hj
    exact ⟨i, hinv'.ufV_n ▸ hi, hidx⟩
  · intro j hj
    obtain ⟨i, hi, hidx⟩ := Unionfind.relabel_surjective _ hinv'.ufD_wf (j := j)
      (by grind [RenumberSpec, Unionfind.numRoots])
    exact ⟨i, hinv'.ufD_n ▸ hi, hidx⟩

/-- The A.3 contract for `freeHomomorphism`: the two phase contracts compose. -/
private theorem freeHomomorphism_spec {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    FreeHomomorphismSpec pt dartPairs ptStar maps :=
  materialiseQuotient_spec (glueClosure_spec hpt hpairs rfl) hrun
end

/-- **`freeHomomorphism` produces a well-formed quotient**: the graph is `WF`
and the maps are total, well-formed relabellings into its index ranges.
(Surjectivity onto them is part of the semantic quotient tier,
`freeHomomorphism_isQuotientMap`.) -/
theorem freeHomomorphism_wf {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    ptStar.WF
    ∧ maps.WF pt.n pt.darts.size ptStar.n ptStar.darts.size
    ∧ maps.vmap.Total ∧ maps.dmap.Total := by
  have hspec := freeHomomorphism_spec hpt hpairs hrun
  exact ⟨hspec.graph_wf, hspec.maps_wf, hspec.vmap_total, hspec.dmap_total⟩

/-- **A.3 coherence tier.** The quotient maps commute with every dart field,
and each requested input pair has a common quotient image. -/
theorem freeHomomorphism_coherent {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    maps.Coherent pt ptStar ∧
      ∀ p ∈ dartPairs, maps.dmap.idx? p.1 = maps.dmap.idx? p.2 := by
  have hspec := freeHomomorphism_spec hpt hpairs hrun
  exact ⟨hspec.coherent, hspec.seeds⟩

/-- A.3 quotient tier: the maps are onto the quotient's index ranges, and
every closed link of the quotient has a source antecedent in its dart class --
the gluing relabels and merges links but never invents one. Private: the
public semantic API is `freeHomomorphism_isQuotientMap`. -/
private theorem freeHomomorphism_quotient {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    (∀ j, j < ptStar.n → ∃ i, i < pt.n ∧ maps.vmap.idx? i = Option.some j)
    ∧ (∀ j, j < ptStar.darts.size →
        ∃ i, i < pt.darts.size ∧ maps.dmap.idx? i = Option.some j)
    ∧ ∀ (k : LinkKind) c, c < ptStar.darts.size →
        ¬ (k.get (ptStar.darts[c]!)).isNone →
        ∃ j, j < pt.darts.size ∧ maps.dmap.idx? j = Option.some c ∧
          ¬ (k.get (pt.darts[j]!)).isNone := by
  have hspec := freeHomomorphism_spec hpt hpairs hrun
  exact ⟨hspec.vmap_surj, hspec.dmap_surj, hspec.link_from⟩

/-- The executable loop check decides dart-level loop-freedom. -/
theorem hasLoop_eq_false_iff {pt : PseudoTriangulation} :
    pt.hasLoop = false ↔ ∀ e, e < pt.darts.size →
      (pt.darts[e]!).head ≠ (pt.darts[(pt.darts[e]!).rev]!).head := by
  rw [show pt.hasLoop = pt.darts.any (fun d => d.head == (pt.darts[d.rev]!).head) from rfl,
    Array.any_eq_false]
  constructor
  · intro h e he hEq
    exact h e he (by simp only [← getElem!_pos pt.darts e he]; simp [hEq])
  · intro h i hi
    refine fun hbeq => h i hi ?_
    rw [getElem!_pos pt.darts i hi]
    exact eq_of_beq hbeq

/-- **The quotient, semantically (A.3).** The typed decodes of the returned
maps form a semantic quotient of dart graphs: `head`/`rev` commute with the
collapse and interior links map forward (the coherence tier), while the
surjectivity and provenance tiers supply the class-level converses. -/
theorem freeHomomorphism_isQuotientMap {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps))
    (hS : ptStar.WF)
    (hmw : maps.WF pt.n pt.darts.size ptStar.n ptStar.darts.size)
    (hvt : maps.vmap.Total) (hdt : maps.dmap.Total) :
    DartGraph.IsQuotientMap (pt.dartGraph hpt) (ptStar.dartGraph hS)
      (maps.vmap.toTotalFun hmw.vmap_wf hvt) (maps.dmap.toTotalFun hmw.dmap_wf hdt) := by
  obtain ⟨hcoh, -⟩ := freeHomomorphism_coherent hpt hpairs hrun
  obtain ⟨hvsurj, hdsurj, hfrom⟩ := freeHomomorphism_quotient hpt hpairs hrun
  generalize hqv : maps.vmap.toTotalFun hmw.vmap_wf hvt = qv
  generalize hqd : maps.dmap.toTotalFun hmw.dmap_wf hdt = qd
  have hidxv : ∀ i : Fin pt.n, maps.vmap.idx? i.val = Option.some (qv i).val :=
    fun i => hqv ▸ IndexMap.idx?_toTotalFun hmw.vmap_wf hvt i
  have hidxd : ∀ i : Fin pt.darts.size, maps.dmap.idx? i.val = Option.some (qd i).val :=
    fun i => hqd ▸ IndexMap.idx?_toTotalFun hmw.dmap_wf hdt i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- qv_surj
    intro c
    obtain ⟨i, hi, hidx⟩ := hvsurj c.val c.isLt
    exact ⟨⟨i, hi⟩, Fin.ext (Option.some.inj ((hidxv ⟨i, hi⟩).symm.trans hidx))⟩
  · -- qd_surj
    intro c
    obtain ⟨i, hi, hidx⟩ := hdsurj c.val c.isLt
    exact ⟨⟨i, hi⟩, Fin.ext (Option.some.inj ((hidxd ⟨i, hi⟩).symm.trans hidx))⟩
  · -- head_eq
    intro d
    obtain ⟨hhead, -, -, -⟩ := hcoh d.val (qd d).val (hidxd d)
    exact Fin.ext
      (Option.some.inj (((hidxv ((pt.dartGraph hpt).head d)).symm.trans hhead)).symm)
  · -- rev_eq
    intro d
    obtain ⟨-, hrev, -, -⟩ := hcoh d.val (qd d).val (hidxd d)
    exact Fin.ext
      (Option.some.inj (((hidxd ((pt.dartGraph hpt).rev d)).symm.trans hrev)).symm)
  · -- succ_of
    intro d s hsem
    obtain ⟨-, -, hsucc, -⟩ := hcoh d.val (qd d).val (hidxd d)
    have hs' : (pt.darts[d.val]!).succ.get? = Option.some s.val :=
      (dartGraph_succ_get? hpt d).symm.trans (congrArg (Option.map Fin.val) hsem)
    obtain ⟨t, ht, hst⟩ := hsucc s.val hs'
    have hqs : (qd s).val = t := Option.some.inj ((hidxd s).symm.trans hst)
    exact (dartGraph_succ_eq_some hS ht).trans (congrArg some (Fin.ext hqs.symm))
  · -- pred_of
    intro d p hsem
    obtain ⟨-, -, -, hpred⟩ := hcoh d.val (qd d).val (hidxd d)
    have hp' : (pt.darts[d.val]!).pred.get? = Option.some p.val :=
      (dartGraph_pred_get? hpt d).symm.trans (congrArg (Option.map Fin.val) hsem)
    obtain ⟨t, ht, hpt'⟩ := hpred p.val hp'
    have hqp : (qd p).val = t := Option.some.inj ((hidxd p).symm.trans hpt')
    exact (dartGraph_pred_eq_some hS ht).trans (congrArg some (Fin.ext hqp.symm))
  · -- succ_from
    intro d hnn
    have hnn' : ¬ (ptStar.darts[(qd d).val]!).succ.isNone := by simpa using hnn
    obtain ⟨j, hj, hjidx, hjs⟩ := hfrom .succ (qd d).val (qd d).isLt hnn'
    exact ⟨⟨j, hj⟩, Fin.ext (Option.some.inj ((hidxd ⟨j, hj⟩).symm.trans hjidx)),
      by simpa [LinkKind.get] using hjs⟩
  · -- pred_from
    intro d hnn
    have hnn' : ¬ (ptStar.darts[(qd d).val]!).pred.isNone := by simpa using hnn
    obtain ⟨j, hj, hjidx, hjs⟩ := hfrom .pred (qd d).val (qd d).isLt hnn'
    exact ⟨⟨j, hj⟩, Fin.ext (Option.some.inj ((hidxd ⟨j, hj⟩).symm.trans hjidx)),
      by simpa [LinkKind.get] using hjs⟩

/-- **`freeHomomorphism` preserves validity** when the executable loop guard
passes: the quotient relation carries `rev_rev` and `boundary`, and the false
`hasLoop` check supplies the loop-freedom a quotient cannot. -/
theorem freeHomomorphism_valid {pt : PseudoTriangulation} (hv : pt.Valid)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps))
    (hnl : ptStar.hasLoop = false) : ptStar.Valid := by
  obtain ⟨hS, hmw, hvt, hdt⟩ := freeHomomorphism_wf hv.wf hpairs hrun
  have hq := freeHomomorphism_isQuotientMap hv.wf hpairs hrun hS hmw hvt hdt
  refine Valid.ofDartGraph hS (hq.valid hv.toDartGraph ?_)
  intro c hEq
  exact hasLoop_eq_false_iff.mp hnl c.val c.isLt (by simpa using congrArg Fin.val hEq)

/-- **`freeHomomorphism` preserves the rotation laws (Lemma 9.6).** The
gluing is a quotient with connected fibers: M3/M4 transfer pointwise through
`IsQuotientMap`, and the loop-carried connectivity invariant rebuilds each
merged vertex's single incidence list via the conversion theorem. -/
theorem freeHomomorphism_rotational {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps))
    (hS : ptStar.WF) (hr : (pt.dartGraph hpt).Rotational) :
    (ptStar.dartGraph hS).Rotational := by
  obtain ⟨-, hmw, hvt, hdt⟩ := freeHomomorphism_wf hpt hpairs hrun
  have hq := freeHomomorphism_isQuotientMap hpt hpairs hrun hS hmw hvt hdt
  have hspec := freeHomomorphism_spec hpt hpairs hrun
  refine hq.rotational hr ?_ (univ := List.finRange ptStar.darts.size)
    (fun c => List.mem_finRange c)
  intro a b hab
  have h1 : maps.vmap.idx? (pt.darts[a.val]!).head =
      maps.vmap.idx? (pt.darts[b.val]!).head := by
    have ha' := IndexMap.idx?_toTotalFun hmw.vmap_wf hvt ((pt.dartGraph hpt).head a)
    have hb' := IndexMap.idx?_toTotalFun hmw.vmap_wf hvt ((pt.dartGraph hpt).head b)
    exact ha'.trans
      ((congrArg (fun z : Fin ptStar.n => Option.some z.val) hab).trans hb'.symm)
  refine (hspec.conn hpt hr a b h1).mono ?_
  intro x y hxy
  have hx := IndexMap.idx?_toTotalFun hmw.dmap_wf hdt x
  have hy := IndexMap.idx?_toTotalFun hmw.dmap_wf hdt y
  exact Fin.ext (Option.some.inj (hx.symm.trans (hxy.trans hy)))

private theorem coherent_split_fst {l r dst : PseudoTriangulation} (hl : l.WF)
    {maps : Mappings}
    (hmaps : maps.WF (l.disjointUnion r).n (l.disjointUnion r).darts.size
      dst.n dst.darts.size)
    (hcoh : maps.Coherent (l.disjointUnion r) dst) :
    Mappings.Coherent
      ⟨(splitMap maps.vmap l.n).1, (splitMap maps.dmap l.darts.size).1⟩ l dst := by
  have hlV : l.n ≤ maps.vmap.size := by
    rw [hmaps.vmap_wf.size_eq, disjointUnion_n]
    omega
  have hlD : l.darts.size ≤ maps.dmap.size := by
    rw [hmaps.dmap_wf.size_eq, disjointUnion_darts]
    simp
  have splitV (i : Nat) (hi : i < l.n) :
      (splitMap maps.vmap l.n).1.idx? i = maps.vmap.idx? i := by
    rw [idx?_splitMap_fst hlV, if_pos hi]
  have splitD (i : Nat) (hi : i < l.darts.size) :
      (splitMap maps.dmap l.darts.size).1.idx? i = maps.dmap.idx? i := by
    rw [idx?_splitMap_fst hlD, if_pos hi]
  intro f fStar hf
  obtain ⟨hfMap, -⟩ := IndexMap.idx?_eq_some_iff.mp hf
  have hfLt : f < l.darts.size := by
    simpa only [size_splitMap_fst, Nat.min_eq_left hlD] using hfMap
  have hfFull : maps.dmap.idx? f = Option.some fStar := by
    rw [← splitD f hfLt]
    exact hf
  have hfull := hcoh f fStar hfFull
  have hleft := disjointUnion_dart_left l r hfLt
  have hsrc := hl.read_inBounds hfLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [splitV _ hsrc.head_lt]
    simpa only [hleft] using hfull.1
  · rw [splitD _ hsrc.rev_lt]
    simpa only [hleft] using hfull.2.1
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hfull.2.2.1 s (by simpa only [hleft] using hs)
    exact ⟨t, ht, by simpa only [splitD s (hsrc.succ_lt s hs)] using hst⟩
  · intro p hp
    obtain ⟨t, ht, hpt⟩ := hfull.2.2.2 p (by simpa only [hleft] using hp)
    exact ⟨t, ht, by simpa only [splitD p (hsrc.pred_lt p hp)] using hpt⟩

private theorem coherent_split_snd {l r dst : PseudoTriangulation} (hr : r.WF)
    {maps : Mappings}
    (hmaps : maps.WF (l.disjointUnion r).n (l.disjointUnion r).darts.size
      dst.n dst.darts.size)
    (hcoh : maps.Coherent (l.disjointUnion r) dst) :
    Mappings.Coherent
      ⟨(splitMap maps.vmap l.n).2, (splitMap maps.dmap l.darts.size).2⟩ r dst := by
  intro f fStar hf
  have hfFull : maps.dmap.idx? (l.darts.size + f) = Option.some fStar := by
    simpa only [idx?_splitMap_snd] using hf
  have hfull := hcoh (l.darts.size + f) fStar hfFull
  have hfLt : f < r.darts.size := by
    obtain ⟨hfMap, -⟩ := IndexMap.idx?_eq_some_iff.mp hf
    have hsize : maps.dmap.size - l.darts.size = r.darts.size := by
      rw [hmaps.dmap_wf.size_eq, disjointUnion_darts]
      simp
    simpa only [size_splitMap_snd, hsize] using hfMap
  have hright := disjointUnion_dart_right l r hfLt
  have hright' : ((l.disjointUnion r).darts[f + l.darts.size]!) =
      ⟨(r.darts[f]!).head + l.n, (r.darts[f]!).rev + l.darts.size,
        (r.darts[f]!).succ.map (· + l.darts.size),
        (r.darts[f]!).pred.map (· + l.darts.size)⟩ := by
    simpa only [Nat.add_comm] using hright
  have hsrc := hr.read_inBounds hfLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [idx?_splitMap_snd]
    simpa only [hright', Nat.add_comm] using hfull.1
  · rw [idx?_splitMap_snd]
    simpa only [hright', Nat.add_comm] using hfull.2.1
  · intro s hs
    have hsUnion :
        ((l.disjointUnion r).darts[l.darts.size + f]!).succ.get? =
          Option.some (l.darts.size + s) := by
      rw [hright]
      simp [OptIdx.get?_map, hs, Nat.add_comm]
    obtain ⟨t, ht, hst⟩ := hfull.2.2.1 (l.darts.size + s) hsUnion
    refine ⟨t, ht, ?_⟩
    simpa only [idx?_splitMap_snd, Nat.add_comm] using hst
  · intro p hp
    have hpUnion :
        ((l.disjointUnion r).darts[l.darts.size + f]!).pred.get? =
          Option.some (l.darts.size + p) := by
      rw [hright]
      simp [OptIdx.get?_map, hp, Nat.add_comm]
    obtain ⟨t, ht, hpt⟩ := hfull.2.2.2 (l.darts.size + p) hpUnion
    refine ⟨t, ht, ?_⟩
    simpa only [idx?_splitMap_snd, Nat.add_comm] using hpt

private theorem freeHomomorphismPair_seed_bounds {pt0 pt1 : PseudoTriangulation}
    {dartId0 dartId1 : Nat} (hdart0 : dartId0 < pt0.darts.size)
    (hdart1 : dartId1 < pt1.darts.size) :
    ∀ p ∈ #[(dartId0, dartId1 + pt0.darts.size)],
      p.1 < (pt0.disjointUnion pt1).darts.size ∧
      p.2 < (pt0.disjointUnion pt1).darts.size := by
  grind [disjointUnion_darts]

/-- Gluing two well-formed triangulations at in-range darts produces a
well-formed quotient and total, well-formed maps from each input side. -/
theorem freeHomomorphismPair_wf {pt0 pt1 : PseudoTriangulation}
    (hpt0 : pt0.WF) (hpt1 : pt1.WF) {dartId0 dartId1 : Nat}
    (hdart0 : dartId0 < pt0.darts.size)
    (hdart1 : dartId1 < pt1.darts.size) :
    let (ptStar, maps0, maps1) :=
      pt0.freeHomomorphismPair pt1 dartId0 dartId1
    ptStar.WF
      ∧ maps0.WF pt0.n pt0.darts.size ptStar.n ptStar.darts.size
      ∧ maps1.WF pt1.n pt1.darts.size ptStar.n ptStar.darts.size
      ∧ maps0.vmap.Total ∧ maps0.dmap.Total
      ∧ maps1.vmap.Total ∧ maps1.dmap.Total := by
  generalize hrun :
    (pt0.disjointUnion pt1).freeHomomorphism
      #[(dartId0, dartId1 + pt0.darts.size)] = r
  obtain ⟨ptStar, maps⟩ := r
  obtain ⟨hptStar, hmaps, hvmap, hdmap⟩ :=
    freeHomomorphism_wf (disjointUnion_wf hpt0 hpt1)
      (freeHomomorphismPair_seed_bounds hdart0 hdart1) hrun
  simpa only [freeHomomorphismPair, hrun] using ⟨hptStar,
    ⟨splitMap_fst_wf hmaps.vmap_wf (by grind [disjointUnion_n]),
     splitMap_fst_wf hmaps.dmap_wf (by grind [disjointUnion_darts])⟩,
    ⟨by simpa [disjointUnion_n] using
        splitMap_snd_wf (l := pt0.n) hmaps.vmap_wf,
     by simpa [disjointUnion_darts] using
        splitMap_snd_wf (l := pt0.darts.size) hmaps.dmap_wf⟩,
    splitMap_fst_total hvmap, splitMap_fst_total hdmap,
    splitMap_snd_total hvmap, splitMap_snd_total hdmap⟩

/-- A.3 coherence for the pair wrapper: both restricted maps commute with the
corresponding input graph, and the selected darts have the same quotient
image. -/
theorem freeHomomorphismPair_coherent {pt0 pt1 : PseudoTriangulation}
    (hpt0 : pt0.WF) (hpt1 : pt1.WF) {dartId0 dartId1 : Nat}
    (hdart0 : dartId0 < pt0.darts.size)
    (hdart1 : dartId1 < pt1.darts.size) :
    let (ptStar, maps0, maps1) :=
      pt0.freeHomomorphismPair pt1 dartId0 dartId1
    maps0.Coherent pt0 ptStar ∧ maps1.Coherent pt1 ptStar ∧
      maps0.dmap.idx? dartId0 = maps1.dmap.idx? dartId1 := by
  generalize hrun :
    (pt0.disjointUnion pt1).freeHomomorphism
      #[(dartId0, dartId1 + pt0.darts.size)] = r
  obtain ⟨ptStar, maps⟩ := r
  have hspec := freeHomomorphism_spec (disjointUnion_wf hpt0 hpt1)
      (freeHomomorphismPair_seed_bounds hdart0 hdart1) hrun
  have hmaps := hspec.maps_wf
  have hcoh := hspec.coherent
  have hseeds := hspec.seeds
  have hcoh0 := coherent_split_fst hpt0 hmaps hcoh
  have hcoh1 := coherent_split_snd hpt1 hmaps hcoh
  have hseed := hseeds (dartId0, dartId1 + pt0.darts.size) (by simp)
  have hleft : (splitMap maps.dmap pt0.darts.size).1.idx? dartId0 =
      maps.dmap.idx? dartId0 := by
    rw [idx?_splitMap_fst]
    · simp [hdart0]
    · rw [hmaps.dmap_wf.size_eq, disjointUnion_darts]
      simp
  have hright : (splitMap maps.dmap pt0.darts.size).2.idx? dartId1 =
      maps.dmap.idx? (dartId1 + pt0.darts.size) := by
    simp only [idx?_splitMap_snd, Nat.add_comm]
  have hid : (splitMap maps.dmap pt0.darts.size).1.idx? dartId0 =
      (splitMap maps.dmap pt0.darts.size).2.idx? dartId1 := by
    rw [hleft, hright]
    exact hseed
  simpa only [freeHomomorphismPair, hrun] using ⟨hcoh0, hcoh1, hid⟩

end Gluing

section SucKTimes

/-- The executable walk is the index-blind scan of `succ.get?`. -/
private theorem sucKTimes_eq_scanGo (pt : PseudoTriangulation) (e k : Nat) :
    pt.sucKTimes e k =
      scanGo (fun _ curr => (pt.darts[curr]!).succ.get?) k 0 e := by
  unfold sucKTimes
  dsimp only
  rw [forIn_range_eq_loopGo k _
    (scanStep (fun _ curr => (pt.darts[curr]!).succ.get?))
    (fun i s => by
      dsimp only [scanStep]
      rcases (pt.darts[s.snd]!).succ with ⟨_ | nxt⟩ <;> rfl)]
  have h := loopGo_scanStep_eq (fun _ curr => (pt.darts[curr]!).succ.get?)
    (fun curr => curr) k 0 e
  rcases hL : loopGo (scanStep (fun _ curr => (pt.darts[curr]!).succ.get?))
      0 k ((none, e) : Option (Option Nat) × Nat) with ⟨o, curr⟩
  cases o <;> simpa only [hL, pure_bind, Id.run_pure, Option.map_id'] using h

/-- The scan is the semantic walk. -/
private theorem scanGo_succ_spec {pt : PseudoTriangulation} (hwf : pt.WF) :
    ∀ (k i e : Nat) (he : e < pt.darts.size),
      scanGo (fun _ curr => (pt.darts[curr]!).succ.get?) k i e =
        (DartGraph.succWalk (pt.dartGraph hwf) k ⟨e, he⟩).map Fin.val
  | 0, _, _, _ => rfl
  | k + 1, i, e, he => by
    unfold scanGo
    rcases hs : (pt.darts[e]!).succ with ⟨_ | nxt⟩
    · have hget : (pt.darts[e]!).succ.get? = Option.none := by rw [hs]; rfl
      simp only [DartGraph.succWalk,
        dartGraph_succ_eq_none hwf (d := ⟨e, he⟩) hget]
      rfl
    · have hget : (pt.darts[e]!).succ.get? = Option.some nxt := by rw [hs]; rfl
      have hnxt : nxt < pt.darts.size := (hwf.read_inBounds he).succ_lt nxt hget
      simp only [DartGraph.succWalk,
        dartGraph_succ_eq_some hwf (d := ⟨e, he⟩) hget]
      exact scanGo_succ_spec hwf k (i + 1) nxt hnxt

/-- **The executable walk is the semantic walk** (`sucKTimes` runs
`DartGraph.succWalk`), so the page-32 distinctness lemmas apply to the
identified pair. -/
private theorem sucKTimes_spec {pt : PseudoTriangulation} (hwf : pt.WF)
    {e : Nat} (he : e < pt.darts.size) {k : Nat} {r : Option Nat}
    (hrun : pt.sucKTimes e k = r) :
    r = (DartGraph.succWalk (pt.dartGraph hwf) k ⟨e, he⟩).map Fin.val := by
  rw [← hrun, sucKTimes_eq_scanGo]
  exact scanGo_succ_spec hwf k 0 e he

/-- On a `WF` graph, a successful `succ` walk ends at a dart: the semantic
walk returns a `Fin pt.darts.size`, so the bound is its codomain. -/
theorem sucKTimes_lt {pt : PseudoTriangulation} (hpt : pt.WF) {e k : Nat}
    (he : e < pt.darts.size) {c : Nat}
    (h : pt.sucKTimes e k = some c) : c < pt.darts.size := by
  have hs := (sucKTimes_spec hpt he h).symm
  grind only [Option.map_eq_some_iff]

end SucKTimes

end PseudoTriangulation

namespace PseudoConfiguration

/-- `disjointUnion` on configurations preserves well-formedness (the graph
part by `PseudoTriangulation.disjointUnion_wf` -- the parent projection of
the union *is* the union of the parent projections, by structure eta; the
degree arrays concatenate as the vertex counts add). -/
theorem disjointUnion_wf {l r : PseudoConfiguration}
    (hl : l.WF) (hr : r.WF) : (l.disjointUnion r).WF := by
  refine ⟨PseudoTriangulation.disjointUnion_wf hl.1 hr.1, ?_⟩
  show (l.degrees ++ r.degrees).size = l.n + r.n
  simp [hl.2, hr.2]

/-! ### The degree-resolution steps preserve well-formedness (A.4)

Each constructor of the `resolveDegreeIssues` BFS keeps `WF`: the graph part
comes from the gluing theorem (`freeHomomorphism_wf`) or explicit link
rewrites, the degree part from size-preserving array writes. -/

section Steps
open Std.Do
set_option mvcgen.warning false

section
set_option linter.tacticCheckInstances false
/-- `dartIdentification` (A.4.3) preserves well-formedness: the glued graph by
`freeHomomorphism_wf`, the rebuilt degrees by size-preserving writes. -/
theorem dartIdentification_wf {pc : PseudoConfiguration} (hpc : pc.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    pc'.WF := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some x => x.1.WF
  have hgraph : (⟨(pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.n,
      (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.darts⟩
        : PseudoTriangulation).WF :=
    (PseudoTriangulation.freeHomomorphism_wf hpc.1 hpairs rfl).1
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜st.snd.size = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.n
        ∧ ∀ o, st.fst = some o → o = none⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.WF, PseudoConfiguration.new]

/-- Rebuilding a configuration around a graph's own fields is that graph. -/
private theorem new_toPseudoTriangulation (X : PseudoTriangulation)
    (ds : Array Degree) :
    (PseudoConfiguration.new X.n X.darts ds).toPseudoTriangulation = X := rfl

/-- The mapping and graph `dartIdentification` returns are exactly
`freeHomomorphism`'s (the degree reconciliation writes only `degreesStar`, so
it touches neither the quotient graph nor the maps), and a returned graph has
passed the loop guard. -/
theorem dartIdentification_graph_maps {pc : PseudoConfiguration}
    {dartPairs : Array (Nat × Nat)} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    pc'.toPseudoTriangulation = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1
      ∧ m = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).2
      ∧ (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.hasLoop = false := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some (z, mp) =>
        z.toPseudoTriangulation = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1
          ∧ mp = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).2
          ∧ (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.hasLoop = false
  mvcgen
  case inv1 => exact ⇓⟨_xs, st⟩ => ⌜∀ o, st.fst = some o → o = none⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.new, new_toPseudoTriangulation]

/-- **Certified coherence for `dartIdentification` (A.4.1/A.4.3).** The quotient
map is a well-formed, structurally-coherent mapping from the input graph into the
identified one -- the gluing branch's carrier. -/
theorem dartIdentification_coherentMappings {pc : PseudoConfiguration} (hpc : pc.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    ∃ C : CoherentMappings pc.toPseudoTriangulation pc'.toPseudoTriangulation, C.maps = m := by
  obtain ⟨hgraph, hmap, -⟩ := dartIdentification_graph_maps hrun
  refine ⟨⟨m, ?_, ?_⟩, rfl⟩
  · rw [hmap, hgraph]; exact (PseudoTriangulation.freeHomomorphism_wf hpc.1 hpairs rfl).2.1
  · rw [hmap, hgraph]; exact (PseudoTriangulation.freeHomomorphism_coherent hpc.1 hpairs rfl).1
end

/-- **`dartIdentification` preserves validity (A.4.1/A.4.3).** The gluing is a
semantic quotient of the dart graph, and the executable `hasLoop` guard
supplies the loop-freedom a quotient cannot preserve by itself. -/
theorem dartIdentification_valid {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    pc'.toPseudoTriangulation.Valid := by
  obtain ⟨hgraph, -, hnl⟩ := dartIdentification_graph_maps hrun
  rw [hgraph]
  exact PseudoTriangulation.freeHomomorphism_valid hv hpairs rfl hnl

/-- Rotationality of the typed view only depends on the graph value. -/
private theorem dartGraph_rotational_congr {pt1 pt2 : PseudoTriangulation}
    (h : pt1 = pt2) (h1 : pt1.WF) (h2 : pt2.WF)
    (hr : (pt1.dartGraph h1).Rotational) : (pt2.dartGraph h2).Rotational := by
  subst h
  exact hr

/-- **`dartIdentification` preserves the rotation laws (Lemma 9.6)**, through
the `freeHomomorphism` tier. -/
theorem dartIdentification_rotational {pc : PseudoConfiguration}
    (hpt : pc.toPseudoTriangulation.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m))
    (hS : pc'.toPseudoTriangulation.WF)
    (hr : (pc.toPseudoTriangulation.dartGraph hpt).Rotational) :
    (pc'.toPseudoTriangulation.dartGraph hS).Rotational := by
  obtain ⟨hgraph, -, -⟩ := dartIdentification_graph_maps hrun
  have hS' : (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.WF := hgraph ▸ hS
  exact dartGraph_rotational_congr hgraph.symm hS' hS
    (PseudoTriangulation.freeHomomorphism_rotational hpt hpairs rfl hS' hr)

section
set_option linter.tacticCheckInstances false
/-- `singleOutLowerDegree` (A.4.9) preserves well-formedness on both sides:
the graph is untouched, the split degree writes preserve the size. -/
theorem singleOutLowerDegree_wf {pc : PseudoConfiguration} (hpc : pc.WF)
    {z1 z2 : PseudoConfiguration}
    (hrun : pc.singleOutLowerDegree = some (z1, z2)) : z1.WF ∧ z2.WF := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some x => x.1.WF ∧ x.2.WF
  have hgraph : (⟨pc.n, pc.darts⟩ : PseudoTriangulation).WF := hpc.1
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜∀ x, st.fst = some (some x) → x.1.WF ∧ x.2.WF⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.WF, PseudoConfiguration.new]

/-- **Degree splits leave the graph fixed (A.4.9).** `singleOutLowerDegree`
rewrites only degree ranges, so both children share the input's triangulation --
an existing `CoherentMappings` into `pc` transports to each child unchanged. -/
theorem singleOutLowerDegree_graph {pc : PseudoConfiguration} {z1 z2 : PseudoConfiguration}
    (hrun : pc.singleOutLowerDegree = some (z1, z2)) :
    z1.toPseudoTriangulation = pc.toPseudoTriangulation
      ∧ z2.toPseudoTriangulation = pc.toPseudoTriangulation := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some (z1, z2) => z1.toPseudoTriangulation = (⟨pc.n, pc.darts⟩ : PseudoTriangulation)
        ∧ z2.toPseudoTriangulation = ⟨pc.n, pc.darts⟩
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜∀ z1 z2, st.fst = some (some (z1, z2))
        → z1.toPseudoTriangulation = (⟨pc.n, pc.darts⟩ : PseudoTriangulation)
          ∧ z2.toPseudoTriangulation = ⟨pc.n, pc.darts⟩⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.new]

/-- Degree splits rewrite one range, so the degree array keeps its size. -/
theorem singleOutLowerDegree_degrees {pc : PseudoConfiguration} {z1 z2 : PseudoConfiguration}
    (hrun : pc.singleOutLowerDegree = some (z1, z2)) :
    z1.degrees.size = pc.degrees.size ∧ z2.degrees.size = pc.degrees.size := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some (z1, z2) => z1.degrees.size = pc.degrees.size ∧ z2.degrees.size = pc.degrees.size
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜∀ z1 z2, st.fst = some (some (z1, z2))
        → z1.degrees.size = pc.degrees.size ∧ z2.degrees.size = pc.degrees.size⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.new, Array.size_setIfInBounds]

/-- `singleOutLowerDegree` leaves the graph untouched, so both children keep
the rotation laws (A.4.9). -/
theorem singleOutLowerDegree_rotational {pc : PseudoConfiguration}
    (hwf : pc.toPseudoTriangulation.WF) {z1 z2 : PseudoConfiguration}
    (hrun : pc.singleOutLowerDegree = some (z1, z2))
    (h1 : z1.toPseudoTriangulation.WF) (h2 : z2.toPseudoTriangulation.WF)
    (hr : (pc.toPseudoTriangulation.dartGraph hwf).Rotational) :
    (z1.toPseudoTriangulation.dartGraph h1).Rotational ∧
      (z2.toPseudoTriangulation.dartGraph h2).Rotational := by
  obtain ⟨hg1, hg2⟩ := singleOutLowerDegree_graph hrun
  exact ⟨dartGraph_rotational_congr hg1.symm hwf h1 hr,
    dartGraph_rotational_congr hg2.symm hwf h2 hr⟩
end

open PseudoTriangulation

/-- Rewriting one dart's link to an in-range target preserves an array-wide
bound: the written dart inherits its other fields from the overwritten one. -/
private theorem write_link_wf (k : LinkKind) {n D : Nat}
    {a : Array Dart}
    (h : ∀ i (hi : i < a.size), (a[i]'hi).InBounds n D)
    {p t : Nat} (ht : t < D) :
    ∀ i (hi : i < (k.write a p t).size),
      ((k.write a p t)[i]'hi).InBounds n D := by
  cases k <;>
    grind [LinkKind.write, LinkKind.set, Dart.InBounds, OptIdx.get?_some, OptIdx.get?_none]

/-- The boundary-fan edit keeps every index in bounds. Per-step equations keep
each definitional comparison one write deep. -/
private theorem boundaryFan_chain_wf {n : Nat} {a a1 a2 a3 a4 a5 a6 : Array Dart}
    {eF eL eFR eLR u w : Nat}
    (h : ∀ i (hi : i < a.size), (a[i]'hi).InBounds n a.size)
    (hu : u < n) (hw : w < n) (heF : eF < a.size) (heL : eL < a.size)
    (heFR : eFR < a.size) (heLR : eLR < a.size)
    (e1 : a1 = a.push ⟨u, a.size + 1, OptIdx.none, OptIdx.some eFR⟩)
    (e2 : a2 = a1.push ⟨w, a.size, OptIdx.some eLR, OptIdx.none⟩)
    (e3 : a3 = LinkKind.pred.write a2 eF eL)
    (e4 : a4 = LinkKind.succ.write a3 eL eF)
    (e5 : a5 = LinkKind.succ.write a4 eFR a.size)
    (e6 : a6 = LinkKind.pred.write a5 eLR (a.size + 1)) :
    ∀ i (hi : i < a6.size), (a6[i]'hi).InBounds n a6.size := by
  have hsz : a6.size = a.size + 2 := by simp [e6, e5, e4, e3, e2, e1]
  have hd0 : a.size < a6.size := by omega
  have hd1 : a.size + 1 < a6.size := by omega
  have hFR' : eFR < a6.size := by omega
  have hLR' : eLR < a6.size := by omega
  have hteF : eF < a6.size := by omega
  have hteL : eL < a6.size := by omega
  have h0 : ∀ i (hi : i < a.size), (a[i]'hi).InBounds n a6.size :=
    fun i hi => (h i hi).mono (Nat.le_refl _) (by omega)
  have h1 : ∀ i (hi : i < a1.size), (a1[i]'hi).InBounds n a6.size := by
    rw [e1]
    exact push_dart_wf h0 ⟨hu, hd1, fun j hj => absurd hj (by simp),
      fun j hj => Option.some.inj hj ▸ hFR'⟩
  have h2 : ∀ i (hi : i < a2.size), (a2[i]'hi).InBounds n a6.size := by
    rw [e2]
    exact push_dart_wf h1 ⟨hw, hd0, fun j hj => Option.some.inj hj ▸ hLR',
      fun j hj => absurd hj (by simp)⟩
  have h3 : ∀ i (hi : i < a3.size), (a3[i]'hi).InBounds n a6.size := by
    rw [e3]; exact write_link_wf .pred h2 hteL
  have h4 : ∀ i (hi : i < a4.size), (a4[i]'hi).InBounds n a6.size := by
    rw [e4]; exact write_link_wf .succ h3 hteF
  have h5 : ∀ i (hi : i < a5.size), (a5[i]'hi).InBounds n a6.size := by
    rw [e5]; exact write_link_wf .succ h4 hd0
  rw [e6]
  intro i hi
  exact (write_link_wf .pred h5 hd1 i hi).mono
    (Nat.le_refl _) (Nat.le_of_eq (congrArg Array.size e6))

/-- Proof-only normal form of a successful boundary-fan edit. -/
private def boundaryFanEdit (pc : PseudoConfiguration) (eF eL : Nat) :
    PseudoConfiguration :=
  let eFR := (pc.darts[eF]!).rev
  let eLR := (pc.darts[eL]!).rev
  let u := (pc.darts[eFR]!).head
  let w := (pc.darts[eLR]!).head
  let a1 := pc.darts.push ⟨u, pc.darts.size + 1, OptIdx.none, OptIdx.some eFR⟩
  let a2 := a1.push ⟨w, pc.darts.size, OptIdx.some eLR, OptIdx.none⟩
  let a3 := a2.set! eF { a2[eF]! with pred := OptIdx.some eL }
  let a4 := a3.set! eL { a3[eL]! with succ := OptIdx.some eF }
  let a5 := a4.set! eFR { a4[eFR]! with succ := OptIdx.some pc.darts.size }
  let a6 := a5.set! eLR { a5[eLR]! with pred := OptIdx.some (pc.darts.size + 1) }
  PseudoConfiguration.new pc.n a6 pc.degrees

/-- A successful `addBoundaryDarts` run names its boundary corners and is
the normal form at them. -/
private theorem addBoundaryDarts_some {pc : PseudoConfiguration} {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    ∃ eF eL, pc.firstDart v = some eF ∧ pc.lastDart v = some eL ∧
      (pc.darts[(pc.darts[eF]!).rev]!).head ≠
        (pc.darts[(pc.darts[eL]!).rev]!).head ∧
      pc' = boundaryFanEdit pc eF eL := by
  rcases hF : pc.firstDart v with _ | eF
  · exact nomatch (show (none : Option PseudoConfiguration) = some pc' by
      simpa only [PseudoConfiguration.addBoundaryDarts, hF, Id.run_pure] using hrun)
  rcases hL : pc.lastDart v with _ | eL
  · exact nomatch (show (none : Option PseudoConfiguration) = some pc' by
      simpa only [PseudoConfiguration.addBoundaryDarts, hF, hL, Id.run_pure]
        using hrun)
  by_cases hne : (pc.darts[(pc.darts[eF]!).rev]!).head =
      (pc.darts[(pc.darts[eL]!).rev]!).head
  · exact nomatch (show (none : Option PseudoConfiguration) = some pc' by
      simpa only [PseudoConfiguration.addBoundaryDarts, hF, hL,
        show ((pc.darts[(pc.darts[eF]!).rev]!).head ==
            (pc.darts[(pc.darts[eL]!).rev]!).head) = true from by simpa using hne,
        reduceIte, Id.run_pure] using hrun)
  · refine ⟨eF, eL, rfl, rfl, hne, ?_⟩
    exact (Option.some.inj (show some (boundaryFanEdit pc eF eL) = some pc' by
      simpa only [PseudoConfiguration.addBoundaryDarts, hF, hL,
        show ((pc.darts[(pc.darts[eF]!).rev]!).head ==
            (pc.darts[(pc.darts[eL]!).rev]!).head) = false from by simpa using hne,
        Bool.false_eq_true, reduceIte, Id.run_pure, boundaryFanEdit]
        using hrun)).symm

/-- **The normal form realises the boundary-fan patch (A.4.6).** Named stages
keep each comparison one `set!` deep. Validity and coherence then follow from
`BoundaryFanPatch.valid` and `BoundaryFanPatch.toExtends`. -/
private theorem boundaryFan_chain_patch {pc : PseudoConfiguration}
    (hwf : pc.toPseudoTriangulation.WF) {v eF eL eFR eLR u w : Nat}
    {a1 a2 a3 a4 a5 a6 : Array Dart}
    (hFsome : pc.firstDart v = some eF) (hLsome : pc.lastDart v = some eL)
    (heFR : (pc.darts[eF]!).rev = eFR) (heLR : (pc.darts[eL]!).rev = eLR)
    (hu' : (pc.darts[eFR]!).head = u) (hw' : (pc.darts[eLR]!).head = w)
    (hne' : u ≠ w)
    (e1 : a1 = pc.darts.push ⟨u, pc.darts.size + 1, OptIdx.none, OptIdx.some eFR⟩)
    (e2 : a2 = a1.push ⟨w, pc.darts.size, OptIdx.some eLR, OptIdx.none⟩)
    (e3 : a3 = LinkKind.pred.write a2 eF eL)
    (e4 : a4 = LinkKind.succ.write a3 eL eF)
    (e5 : a5 = LinkKind.succ.write a4 eFR pc.darts.size)
    (e6 : a6 = LinkKind.pred.write a5 eLR (pc.darts.size + 1)) :
    PseudoTriangulation.BoundaryFanPatch pc.toPseudoTriangulation
      ⟨pc.n, a6⟩ eF eL eFR eLR := by
  have hfirst : eF < pc.darts.size := PseudoTriangulation.firstDart_lt hFsome
  have hlast : eL < pc.darts.size := PseudoTriangulation.lastDart_lt hLsome
  have hfrev : eFR < pc.darts.size := heFR ▸ (hwf.read_inBounds hfirst).rev_lt
  have hlrev : eLR < pc.darts.size := heLR ▸ (hwf.read_inBounds hlast).rev_lt
  have hu : u < pc.n := hu' ▸ (hwf.read_inBounds hfrev).head_lt
  have hw : w < pc.n := hw' ▸ (hwf.read_inBounds hlrev).head_lt
  -- Reads through the chain: the old region and the two appended darts.
  have r2 : ∀ {j : Nat}, j < pc.darts.size → a2[j]! = pc.darts[j]! := fun {j} hj => by
    rw [e2, e1, getElem!_push_lt (by simp [Array.size_push]; omega),
      getElem!_push_lt hj]
  have hsz2 : a2.size = pc.darts.size + 2 := by rw [e2, e1]; simp
  have ha3s : a3.size = a2.size := by simp [e3]
  have ha4s : a4.size = a2.size := by simp [e4, ha3s]
  have ha5s : a5.size = a2.size := by simp [e5, ha4s]
  have hsize6 : a6.size = a2.size := by simp [e6, ha5s]
  have hgUW : a2[pc.darts.size]! =
      (⟨u, pc.darts.size + 1, OptIdx.none, OptIdx.some eFR⟩ : Dart) := by
    rw [e2, e1, getElem!_push_lt (by simp [Array.size_push])]
    exact getElem!_push_size
  have hgWU : a2[pc.darts.size + 1]! =
      (⟨w, pc.darts.size, OptIdx.some eLR, OptIdx.none⟩ : Dart) := by
    rw [e2, e1]
    simpa [Array.size_push] using getElem!_push_size
      (a := pc.darts.push ⟨u, pc.darts.size + 1, OptIdx.none, OptIdx.some eFR⟩)
      (x := (⟨w, pc.darts.size, OptIdx.some eLR, OptIdx.none⟩ : Dart))
  have hn1 : a6[pc.darts.size]! =
      (⟨u, pc.darts.size + 1, OptIdx.none, OptIdx.some eFR⟩ : Dart) := by
    rw [e6, e5, e4, e3]
    grind only [LinkKind.read_write]
  have hn2 : a6[pc.darts.size + 1]! =
      (⟨w, pc.darts.size, OptIdx.some eLR, OptIdx.none⟩ : Dart) := by
    rw [e6, e5, e4, e3]
    grind only [LinkKind.read_write]
  -- The final array against `a2`: four link writes, `rev`/`head` untouched.
  have hrev6 : ∀ (j : Nat), (a6[j]!).rev = (a2[j]!).rev := fun j => by
    simp only [e6, e5, e4, e3, LinkKind.rev_write]
  have hhead6 : ∀ (j : Nat), (a6[j]!).head = (a2[j]!).head := fun j => by
    simp only [e6, e5, e4, e3, LinkKind.head_write]
  have hpred6 : ∀ (j : Nat), j ≠ eF → j ≠ eLR → (a6[j]!).pred = (a2[j]!).pred :=
    fun j hjF hjLR => by
      change LinkKind.pred.get (a6[j]!) = _
      rw [e6, LinkKind.get_write_ne hjLR,
        e5, LinkKind.get_other_write (by decide),
        e4, LinkKind.get_other_write (by decide),
        e3, LinkKind.get_write_ne hjF]
      rfl
  have hsucc6 : ∀ (j : Nat), j ≠ eL → j ≠ eFR → (a6[j]!).succ = (a2[j]!).succ :=
    fun j hjL hjFR => by
      change LinkKind.succ.get (a6[j]!) = _
      rw [e6, LinkKind.get_other_write (by decide),
        e5, LinkKind.get_write_ne hjFR,
        e4, LinkKind.get_write_ne hjL,
        e3, LinkKind.get_other_write (by decide)]
      rfl
  -- Exact corner targets: the last write to each field wins, so only the
  -- guarded corners need the distinctness hypotheses.
  have hSuccFR : (a6[eFR]!).succ = OptIdx.some pc.darts.size := by
    have hFR4 : eFR < a4.size := by omega
    change LinkKind.succ.get (a6[eFR]!) = _
    rw [e6, LinkKind.get_other_write (by decide), e5, LinkKind.get_write_self hFR4]
  have hPredLR : (a6[eLR]!).pred = OptIdx.some (pc.darts.size + 1) := by
    have hLR5 : eLR < a5.size := by omega
    change LinkKind.pred.get (a6[eLR]!) = _
    rw [e6, LinkKind.get_write_self hLR5]
  have hSuccEL : eFR ≠ eL → (a6[eL]!).succ = OptIdx.some eF := fun hc => by
    have hL3 : eL < a3.size := by omega
    change LinkKind.succ.get (a6[eL]!) = _
    rw [e6, LinkKind.get_other_write (by decide),
      e5, LinkKind.get_write_ne hc.symm, e4, LinkKind.get_write_self hL3]
  have hPredEF : eLR ≠ eF → (a6[eF]!).pred = OptIdx.some eL := fun hc => by
    have hF2 : eF < a2.size := by omega
    change LinkKind.pred.get (a6[eF]!) = _
    rw [e6, LinkKind.get_write_ne hc.symm,
      e5, LinkKind.get_other_write (by decide),
      e4, LinkKind.get_other_write (by decide), e3, LinkKind.get_write_self hF2]
  have hheadF : (pc.darts[eF]!).head = v := PseudoTriangulation.firstDart_head hFsome
  have hheadL : (pc.darts[eL]!).head = v := PseudoTriangulation.lastDart_head hLsome
  have hwf6 : ∀ i (hi : i < a6.size), (a6[i]'hi).InBounds pc.n a6.size :=
    boundaryFan_chain_wf hwf hu hw hfirst hlast hfrev hlrev e1 e2 e3 e4 e5 e6
  exact
    { wf := hwf6
      n_eq := rfl
      size := by rw [hsize6, hsz2]
      eF_lt := hfirst
      eL_lt := hlast
      eFR_def := heFR
      eLR_def := heLR
      head_eq := hheadF.trans hheadL.symm
      head_ne := by rw [hu', hw']; exact hne'
      predF_open := PseudoTriangulation.firstDart_pred_isNone hFsome
      succL_open := PseudoTriangulation.lastDart_succ_isNone hLsome
      read_new1 := by rw [hn1, hu']
      read_new2 := by rw [hn2, hw']
      head_old := fun j hj => (hhead6 j).trans (congrArg Dart.head (r2 hj))
      rev_old := fun j hj => (hrev6 j).trans (congrArg Dart.rev (r2 hj))
      pred_old := fun j hjF hjLR hj => (hpred6 j hjF hjLR).trans (congrArg Dart.pred (r2 hj))
      succ_old := fun j hjL hjFR hj => (hsucc6 j hjL hjFR).trans (congrArg Dart.succ (r2 hj))
      succ_eFR := hSuccFR
      pred_eLR := hPredLR
      succ_eL := hSuccEL
      pred_eF := hPredEF }

/-- **The implementation patch of `addBoundaryDarts` (A.4.6):** the boundary
corners witness the normal form, and the normal form realises the patch. -/
theorem addBoundaryDarts_patch {pc : PseudoConfiguration}
    (hwf : pc.toPseudoTriangulation.WF) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    ∃ eF eL eFR eLR, PseudoTriangulation.BoundaryFanPatch
      pc.toPseudoTriangulation pc'.toPseudoTriangulation eF eL eFR eLR := by
  obtain ⟨eF, eL, hF, hL, hne, rfl⟩ := addBoundaryDarts_some hrun
  refine ⟨eF, eL, (pc.darts[eF]!).rev, (pc.darts[eL]!).rev, ?_⟩
  apply boundaryFan_chain_patch hwf hF hL (hne' := hne) <;> rfl

/-- `addBoundaryDarts` keeps the degree array. -/
private theorem addBoundaryDarts_degrees {pc : PseudoConfiguration} {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.degrees = pc.degrees := by
  obtain ⟨_, _, _, _, _, rfl⟩ := addBoundaryDarts_some hrun
  rfl

/-- `addBoundaryDarts` (A.4.6) preserves well-formedness: the graph by the
patch, the degree array unchanged over an unchanged vertex count. -/
theorem addBoundaryDarts_wf {pc : PseudoConfiguration} (hpc : pc.WF) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.WF := by
  obtain ⟨_, _, _, _, hp⟩ := addBoundaryDarts_patch hpc.1 hrun
  refine ⟨hp.wf, ?_⟩
  show pc'.degrees.size = pc'.n
  rw [addBoundaryDarts_degrees hrun, hpc.2]
  exact hp.n_eq.symm

/-- **Certified step for `addBoundaryDarts` (A.4.6/A.4.8):** on a valid input
the enlarged graph is valid and reached by the identity as a certified
mapping. The carrier packages the map, its well-formedness into the two-dart
larger index ranges, and coherence at the operation boundary, so downstream
proofs never inspect the patch. -/
theorem addBoundaryDarts_spec {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.toPseudoTriangulation.Valid ∧
      ∃ C : CoherentMappings pc.toPseudoTriangulation pc'.toPseudoTriangulation,
        C.maps = Mappings.initialMappings pc.n pc.darts.size := by
  obtain ⟨_, _, _, _, hp⟩ := addBoundaryDarts_patch hv.wf hrun
  refine ⟨hp.valid hv,
    ⟨⟨Mappings.initialMappings pc.n pc.darts.size, ?_,
      Mappings.Coherent.id_of_extends (hp.toExtends hv)⟩, rfl⟩⟩
  exact (Mappings.initialMappings_wf pc.n pc.darts.size).mono
    (Nat.le_of_eq hp.n_eq.symm) (by have := hp.size; omega)

/-- `addBoundaryDarts` preserves `Valid` (A.4.6). -/
theorem addBoundaryDarts_valid {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.toPseudoTriangulation.Valid :=
  (addBoundaryDarts_spec hv hrun).1

/-- On a valid input the identity map is coherent into the enlarged graph
(A.4.8). -/
theorem addBoundaryDarts_coherent {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    (Mappings.initialMappings pc.n pc.darts.size).Coherent
      pc.toPseudoTriangulation pc'.toPseudoTriangulation := by
  obtain ⟨C, hC⟩ := (addBoundaryDarts_spec hv hrun).2
  exact hC ▸ C.coherent

/-- `addBoundaryDarts` preserves the rotation laws (A.4.6), through the
boundary-fan patch. -/
theorem addBoundaryDarts_rotational {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc')
    (hS : pc'.toPseudoTriangulation.WF)
    (hr : (pc.toPseudoTriangulation.dartGraph hv.wf).Rotational) :
    (pc'.toPseudoTriangulation.dartGraph hS).Rotational := by
  obtain ⟨eF, eL, eFR, eLR, hp⟩ := addBoundaryDarts_patch hv.wf hrun
  exact hp.rotational hv hr

/-! ### The Sections 9.3-9.4 termination potential

`resolveDegreeIssues` terminates because every arm of its loop body shrinks
a per-state potential: a boundary closure trades its two new darts for one
net open corner, an identification strictly shrinks the dart count, and a
degree split strictly shrinks the total range slack. The worklist measure
sums `3 ^ potential` over the active entries, so the split arm's two pushes
still shrink the queue total. -/

/-- Open `pred` corners of the dart array. A boundary closure removes one
net corner; gluing only ever closes corners. -/
private def openPredCorners (pt : PseudoTriangulation) : Nat :=
  (List.range pt.darts.size).countP fun i => (pt.darts[i]!).pred.isNone

/-- Total degree-range slack. A split pins one vertex's range strictly. -/
private def degreeSlack (pc : PseudoConfiguration) : Nat :=
  ((List.range pc.degrees.size).map fun v =>
    (pc.degrees[v]!).upper - (pc.degrees[v]!).lower).sum

/-- The per-state potential, additive: each arm strictly decreases it -- a
split shrinks the slack, an identification shrinks the dart count with the
other terms non-increasing, and a boundary closure trades its two new darts
against three weighted units of the closed corner. -/
private def statePotential (pc : PseudoConfiguration) : Nat :=
  degreeSlack pc + pc.darts.size + 3 * openPredCorners pc.toPseudoTriangulation

/-- The worklist weight of one entry. -/
private def resolveWeight (e : PseudoConfiguration × Mappings) : Nat :=
  3 ^ statePotential e.1

@[simp] private theorem resolveWeight_pair (z : PseudoConfiguration) (m : Mappings) :
    resolveWeight (z, m) = 3 ^ statePotential z := rfl

/-- The worklist measure over active entries. The exponential entry weight
is what lets a split replace one entry by two of smaller potential and still
shrink the total. -/
private def resolveMeasure (q : Queue (PseudoConfiguration × Mappings)) : Nat :=
  q.sumOf resolveWeight

private theorem resolveMeasure_push (q : Queue (PseudoConfiguration × Mappings))
    (x : PseudoConfiguration × Mappings) :
    resolveMeasure (q.push x) = resolveMeasure q + resolveWeight x :=
  Queue.sumOf_push resolveWeight

private theorem resolveMeasure_pop {q q' : Queue (PseudoConfiguration × Mappings)}
    {x : PseudoConfiguration × Mappings} (h : q.pop? = some (x, q')) :
    resolveMeasure q = resolveWeight x + resolveMeasure q' :=
  Queue.sumOf_pop resolveWeight h

private theorem resolveWeight_pos (e : PseudoConfiguration × Mappings) :
    0 < resolveWeight e := Nat.pow_pos (by omega)

private theorem resolveWeight_lt {z z' : PseudoConfiguration} {m m' : Mappings}
    (h : statePotential z' < statePotential z) :
    resolveWeight (z', m') < resolveWeight (z, m) :=
  Nat.pow_lt_pow_right (by omega) h

/-- Two strictly smaller powers of three sum below the original: the split
arm's two pushes still shrink the queue measure. -/
private theorem pow3_add_pow3_lt {a b c : Nat} (ha : a < c) (hb : b < c) :
    3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have h4 : 1 ≤ 3 ^ (c - 1) := Nat.pow_pos (by omega)
  omega

private theorem resolveWeight_add_lt {z1 z2 z : PseudoConfiguration}
    {m1 m2 m : Mappings} (h1 : statePotential z1 < statePotential z)
    (h2 : statePotential z2 < statePotential z) :
    resolveWeight (z1, m1) + resolveWeight (z2, m2) < resolveWeight (z, m) :=
  pow3_add_pow3_lt h1 h2

/-- Bounded choice: extract a witness family over an index range once. -/
private theorem choose_bounded {P : Nat → Nat → Prop} {n : Nat}
    (h : ∀ c, c < n → ∃ x, P c x) :
    ∃ g : Nat → Nat, ∀ c, c < n → P c (g c) :=
  ⟨fun c => if hc : c < n then (h c hc).choose else 0, fun c hc => by
    simp only [dif_pos hc]
    exact (h c hc).choose_spec⟩

/-- Choose a fiber representative for every quotient dart. -/
private theorem freeHomomorphism_fiber_choice {pt : PseudoTriangulation}
    {dartPairs : Array (Nat × Nat)} {ptStar : PseudoTriangulation} {maps : Mappings}
    (hspec : PseudoTriangulation.FreeHomomorphismSpec pt dartPairs ptStar maps) :
    ∃ g : Nat → Nat, (∀ c, c < ptStar.darts.size →
        g c < pt.darts.size ∧ maps.dmap.idx? (g c) = Option.some c) ∧
      ∀ c c', c < ptStar.darts.size → c' < ptStar.darts.size →
        g c = g c' → c = c' := by
  obtain ⟨g, hg⟩ := choose_bounded hspec.dmap_surj
  refine ⟨g, hg, ?_⟩
  intro c c' hc hc' heq
  exact Option.some.inj ((hg c hc).2.symm.trans
    ((congrArg maps.dmap.idx? heq).trans (hg c' hc').2))

/-- **Identifying a distinct pair strictly shrinks the dart count**: the
fiber choice injects the quotient darts into the source darts and misses one
of the identified pair. -/
private theorem freeHomomorphism_size_lt {pt : PseudoTriangulation}
    {dartPairs : Array (Nat × Nat)} {ptStar : PseudoTriangulation} {maps : Mappings}
    (hspec : PseudoTriangulation.FreeHomomorphismSpec pt dartPairs ptStar maps)
    {e f : Nat} (he : e < pt.darts.size) (hf : f < pt.darts.size)
    (hef : (e, f) ∈ dartPairs) (hne : e ≠ f) :
    ptStar.darts.size < pt.darts.size := by
  have hcol : maps.dmap.idx? e = maps.dmap.idx? f := hspec.seeds (e, f) hef
  obtain ⟨g, hg, hinj⟩ := freeHomomorphism_fiber_choice hspec
  by_cases hin : ∃ c, c < ptStar.darts.size ∧ g c = e
  · obtain ⟨c₀, hc₀, hgc₀⟩ := hin
    refine Counting.lt_of_inj_on_missing g (fun j hj => (hg j hj).1) hinj hf ?_
    intro j hj hgf
    have h1 : maps.dmap.idx? f = Option.some j := hgf ▸ (hg j hj).2
    have h2 : maps.dmap.idx? e = Option.some c₀ := hgc₀ ▸ (hg c₀ hc₀).2
    have hcj : c₀ = j := Option.some.inj ((h2.symm.trans hcol).trans h1)
    exact hne (hgc₀.symm.trans ((congrArg g hcj).trans hgf))
  · refine Counting.lt_of_inj_on_missing g (fun j hj => (hg j hj).1) hinj he ?_
    intro j hj hge
    exact hin ⟨j, hj, hge⟩

/-- **The quotient never opens a `pred` corner**: an open quotient dart
pulls back to an open fiber representative through coherence. -/
private theorem freeHomomorphism_openPred_le {pt : PseudoTriangulation}
    {dartPairs : Array (Nat × Nat)} {ptStar : PseudoTriangulation} {maps : Mappings}
    (hspec : PseudoTriangulation.FreeHomomorphismSpec pt dartPairs ptStar maps) :
    openPredCorners ptStar ≤ openPredCorners pt := by
  obtain ⟨g, hg, hinj⟩ := freeHomomorphism_fiber_choice hspec
  unfold openPredCorners
  rw [Counting.countP_eq_sum_map, Counting.countP_eq_sum_map]
  refine Counting.sum_le_of_inj_on g (fun j hj => (hg j hj).1) hinj ?_
  intro j hj
  by_cases hopen : (ptStar.darts[j]!).pred.isNone
  · have hsrc : (pt.darts[g j]!).pred.isNone = true := by
      cases hp : (pt.darts[g j]!).pred.get? with
      | none =>
        rw [OptIdx.isNone_eq, hp]
        rfl
      | some p =>
        obtain ⟨-, -, -, hpredc⟩ := hspec.coherent (g j) j (hg j hj).2
        obtain ⟨t, ht, -⟩ := hpredc p hp
        have hfalse : (ptStar.darts[j]!).pred.isNone = false := by
          rw [OptIdx.isNone_eq, ht]
          rfl
        exact nomatch (hfalse.symm.trans hopen)
    simp [hopen, hsrc]
  · simp [hopen]

/-- Bridge a functional `idx?` fact to the executable's `idx!` read. -/
private theorem idx!_of_idx? {mm : IndexMap} {v j : Nat} (hv : v < mm.size)
    (h : mm.idx? v = Option.some j) : (mm[v]!).idx! = j := by
  have h' : (mm[v]'hv).get? = Option.some j := (IndexMap.idx?_pos hv).symm.trans h
  rw [getElem!_pos mm v hv]
  exact OptIdx.idx!_of_get?_some h'

section
set_option linter.tacticCheckInstances false
/-- **What a reported degree issue is**: an in-range vertex with a fixed
degree, either over-incident or exactly at its boundary count. -/
theorem vertexSingleDegreeIssue_spec {pc : PseudoConfiguration} {v : Nat}
    (hrun : pc.vertexSingleDegreeIssue = some v) :
    v < pc.n ∧ (pc.degrees[v]!).fixed = true ∧
      ((pc.degrees[v]!).lower < pc.nIncidentDarts[v]! ∨
        (pc.isBoundary[v]! = true ∧
          pc.nIncidentDarts[v]! = (pc.degrees[v]!).lower)) := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some w => w < pc.n ∧ (pc.degrees[w]!).fixed = true ∧
        ((pc.degrees[w]!).lower < pc.nIncidentDarts[w]! ∨
          (pc.isBoundary[w]! = true ∧
            pc.nIncidentDarts[w]! = (pc.degrees[w]!).lower))
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜∀ w, st.fst = some (some w) → w < pc.n ∧ (pc.degrees[w]!).fixed = true ∧
        ((pc.degrees[w]!).lower < pc.nIncidentDarts[w]! ∨
          (pc.isBoundary[w]! = true ∧
            pc.nIncidentDarts[w]! = (pc.degrees[w]!).lower))⌝
  all_goals mleave
  all_goals grind

/-- The histogram fold, by induction on the dart list: each step bumps its
dart's head slot, so the result adds each head's count to the seed. -/
private theorem foldl_countHeads (n : Nat) :
    ∀ (l : List Dart) (st : Array Nat), st.size = n →
      (∀ d ∈ l, d.head < n) →
      (l.foldl (fun cnt d => cnt.modify d.head (· + 1)) st).size = n ∧
      ∀ u, u < n →
        (l.foldl (fun cnt d => cnt.modify d.head (· + 1)) st)[u]! =
          st[u]! + l.countP fun d => d.head == u
  | [], st, hsz, _ => ⟨hsz, fun u _ => by simp⟩
  | d :: l, st, hsz, hmem => by
    have hdn : d.head < n := hmem d List.mem_cons_self
    obtain ⟨hsz', hcnt⟩ := foldl_countHeads n l (st.modify d.head (· + 1))
      (by simpa using hsz) (fun x hx => hmem x (List.mem_cons_of_mem d hx))
    refine ⟨hsz', fun u hu => ?_⟩
    rw [List.foldl_cons, hcnt u hu, List.countP_cons]
    by_cases hdu : d.head = u
    · subst hdu
      rw [getElem!_modify_self (a := st) (f := (· + 1)) (by omega)]
      simp only [beq_self_eq_true, if_pos]
      omega
    · rw [getElem!_modify_ne hdu]
      simp [show (d.head == u) = false from by simpa using hdu]

/-- The incidence histogram counts the darts at each vertex. -/
private theorem nIncidentDarts_spec {pt : PseudoTriangulation} (hwf : pt.WF) :
    pt.nIncidentDarts.size = pt.n ∧ ∀ u, u < pt.n →
      pt.nIncidentDarts[u]! = pt.darts.toList.countP fun d => d.head == u := by
  have heads : ∀ d ∈ pt.darts.toList, d.head < pt.n := by
    intro d hd
    obtain ⟨i, hilt, hget⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hd)
    exact hget ▸ getElem!_pos pt.darts i hilt ▸ (hwf.read_inBounds hilt).head_lt
  have heq : pt.nIncidentDarts =
      pt.darts.toList.foldl (fun cnt d => cnt.modify d.head (· + 1))
        (Array.replicate pt.n 0) := by
    unfold PseudoTriangulation.nIncidentDarts
    dsimp only
    rw [← Array.forIn_toList, List.forIn_pure_yield_eq_foldl]
    rfl
  obtain ⟨hsz, hcnt⟩ := foldl_countHeads pt.n pt.darts.toList
    (Array.replicate pt.n 0) (Array.size_replicate ..) heads
  refine ⟨heq ▸ hsz, fun u hu => ?_⟩
  have hseed : (Array.replicate pt.n 0)[u]! = 0 := by
    rw [getElem!_pos _ u (by simpa using hu), Array.getElem_replicate]
  rw [heq, hcnt u hu, hseed, Nat.zero_add]
end

/-- The histogram entry at a vertex is its incidence list's length. -/
private theorem nIncidentDarts_eq_length {pt : PseudoTriangulation} (hwf : pt.WF)
    {vf : Fin pt.n} {l : List (Fin pt.darts.size)}
    (hl : DartGraph.IncidenceList (pt.dartGraph hwf) vf l) :
    pt.nIncidentDarts[vf.val]! = l.length := by
  obtain ⟨hsz, hcount⟩ := nIncidentDarts_spec hwf
  rw [hcount vf.val vf.isLt, Counting.list_countP_range]
  have hread : ∀ i, i < pt.darts.size → pt.darts.toList[i]! = pt.darts[i]! := by
    intro i hilt
    rw [getElem!_pos _ i (by simpa using hilt), getElem!_pos _ i hilt]
    exact Array.getElem_toList _
  have hcongr : (List.range pt.darts.toList.length).countP
      (fun i => (pt.darts.toList[i]!).head == vf.val) =
      (List.range pt.darts.size).countP
        (fun i => (pt.darts[i]!).head == vf.val) := by
    rw [show pt.darts.toList.length = pt.darts.size from Array.length_toList]
    refine List.countP_congr ?_
    intro i hi
    rw [hread i (List.mem_range.mp hi)]
  rw [hcongr, List.countP_eq_length_filter]
  have hlen : ((List.range pt.darts.size).filter
      (fun i => (pt.darts[i]!).head == vf.val)).length = (l.map Fin.val).length := by
    refine Counting.length_eq_of_nodup_iff
      (List.filter_sublist.nodup List.nodup_range)
      (Counting.nodup_map_of_inj (fun a b h => Fin.ext h) hl.nodup) ?_
    intro x
    constructor
    · intro hx
      obtain ⟨hxr, hxp⟩ := List.mem_filter.mp hx
      have hxlt : x < pt.darts.size := List.mem_range.mp hxr
      have hhead : (pt.darts[x]!).head = vf.val := by simpa using hxp
      exact List.mem_map.mpr ⟨⟨x, hxlt⟩, (hl.mem_iff _).mpr (Fin.ext hhead), rfl⟩
    · intro hx
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hx
      have hh := (hl.mem_iff d0).mp hd0
      refine List.mem_filter.mpr ⟨List.mem_range.mpr d0.isLt, ?_⟩
      simpa using congrArg Fin.val hh
  rw [hlen, List.length_map]

/-- **What the degree-reconciliation loop guarantees** (proof-only): every
quotient class's range keeps the seed clamp (`positive`), every source
vertex's range passed its non-disjointness check (`upper_pos`), and each
class range lies inside every fiber member's range (`contained`). One
concrete bridge proves this; slack bounds and the fixed-`[0,0]`
impossibility are semantic consequences. Class nonemptiness would need
source nonemptiness and waits for the degree-validity layer. -/
private structure DegreeReconciliation (src : Array Degree) (vmap : IndexMap)
    (dst : Array Degree) : Prop where
  class_lt : ∀ v, v < src.size → (vmap[v]!).idx! < dst.size
  surj : ∀ c, c < dst.size → ∃ v, v < src.size ∧ (vmap[v]!).idx! = c
  positive : ∀ c, c < dst.size → 1 ≤ (dst[c]!).lower
  upper_pos : ∀ v, v < src.size → 1 ≤ (src[v]!).upper
  contained : ∀ v, v < src.size →
    Degree.includes (src[v]!) (dst[(vmap[v]!).idx!]!) = true

/-- A fixed range that survived reconciliation is positive: its upper bound
met a clamped class, and fixedness copies that to the lower bound. -/
private theorem DegreeReconciliation.fixed_lower_pos {src : Array Degree}
    {vmap : IndexMap} {dst : Array Degree} (h : DegreeReconciliation src vmap dst)
    {v : Nat} (hv : v < src.size) (hfix : (src[v]!).fixed = true) :
    1 ≤ (src[v]!).lower := by
  have h1 := h.upper_pos v hv
  have hfx : (src[v]!).lower = (src[v]!).upper := by
    simpa [Degree.fixed] using hfix
  omega

/-- **Total slack never grows across a reconciliation**: each class range
lies inside its fiber representative's range, and distinct classes have
distinct representatives. -/
private theorem DegreeReconciliation.slack_le {src : Array Degree}
    {vmap : IndexMap} {dst : Array Degree}
    (h : DegreeReconciliation src vmap dst) :
    ((List.range dst.size).map fun c => (dst[c]!).upper - (dst[c]!).lower).sum ≤
      ((List.range src.size).map fun v => (src[v]!).upper - (src[v]!).lower).sum := by
  have hper : ∀ c, c < dst.size → ∃ w, w < src.size ∧ ((vmap[w]!).idx! = c) ∧
      (dst[c]!).upper - (dst[c]!).lower ≤ (src[w]!).upper - (src[w]!).lower := by
    intro c hc
    obtain ⟨w, hw, hcls⟩ := h.surj c hc
    have hinc : (src[w]!).lower ≤ (dst[c]!).lower ∧
        (dst[c]!).upper ≤ (src[w]!).upper := by
      simpa [Degree.includes, hcls] using h.contained w hw
    exact ⟨w, hw, hcls, by omega⟩
  obtain ⟨g, hg⟩ := choose_bounded hper
  have hinj : ∀ c c', c < dst.size → c' < dst.size → g c = g c' → c = c' := by
    intro c c' hc hc' heq
    exact (hg c hc).2.1.symm.trans
      ((congrArg (fun x => ((vmap[x]!)).idx!) heq).trans (hg c' hc').2.1)
  exact Counting.sum_le_of_inj_on g (fun c hc => (hg c hc).1) hinj
    (fun c hc => (hg c hc).2.2)

/-- The step of `dartIdentification`'s reconciliation loop: fail on a
disjoint degree pair, else intersect the vertex's degree into its quotient
slot. -/
private def reconcileStep (pc : PseudoConfiguration) (vmap : IndexMap)
    (v : Nat) (ds : Array Degree) : Option (Array Degree) :=
  if Degree.disjoint (ds[(vmap[v]!).idx!]!) pc.degrees[v]! then none
  else some (ds.set! (vmap[v]!).idx!
    (Degree.intersection (ds[(vmap[v]!).idx!]!) pc.degrees[v]!))

/-- Loop invariant of the reconciliation scan: sizes pinned to the quotient,
every slot positive, and every processed vertex's degree included in its
quotient slot (with a positive upper bound). -/
private structure ReconInv (pc : PseudoConfiguration) (vmap : IndexMap)
    (N i : Nat) (ds : Array Degree) : Prop where
  size_eq : ds.size = N
  pos : ∀ c, c < ds.size → 1 ≤ (ds[c]!).lower
  upper_pos : ∀ v', v' < i → 1 ≤ (pc.degrees[v']!).upper
  includes : ∀ v', v' < i →
    Degree.includes (pc.degrees[v']!) (ds[(vmap[v']!).idx!]!) = true

/-- One reconciliation step preserves the invariant: intersecting a
non-disjoint degree into the vertex's quotient slot keeps sizes, positivity,
and the inclusion of every processed vertex. -/
private theorem ReconInv.step {pc : PseudoConfiguration} {vmap : IndexMap}
    {N i : Nat} {ds : Array Degree}
    (hvwf : IndexMap.WF vmap pc.n N) (hvt : vmap.Total)
    (hinv : ReconInv pc vmap N i ds) (hilt : i < pc.n)
    (hdisj : ¬ Degree.disjoint (ds[(vmap[i]!).idx!]!) pc.degrees[i]! = true) :
    ReconInv pc vmap N (i + 1)
      (ds.set! (vmap[i]!).idx!
        (Degree.intersection (ds[(vmap[i]!).idx!]!) pc.degrees[i]!)) := by
  have hclslt : (vmap[i]!).idx! < N := IndexMap.idx!_lt_of_total hvwf hvt hilt
  have hsz := hinv.size_eq
  have hvsz : (vmap[i]!).idx! < ds.size := by omega
  have hnd : ¬ ((ds[(vmap[i]!).idx!]!).upper < (pc.degrees[i]!).lower ∨
      (pc.degrees[i]!).upper < (ds[(vmap[i]!).idx!]!).lower) := by
    simpa [Degree.disjoint] using hdisj
  have hposStar := hinv.pos _ hvsz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Array.size_set!]
    exact hinv.size_eq
  · intro c hc
    have hc' : c < ds.size := by
      simpa [Array.size_set!] using hc
    by_cases hcv : c = (vmap[i]!).idx!
    · subst hcv
      rw [Array.getElem!_set!_self (hi := hvsz)]
      simp only [Degree.intersection]
      omega
    · rw [Array.getElem!_set!_ne (hij := fun h => hcv h.symm)]
      exact hinv.pos c hc'
  · intro v' hv'
    by_cases hlast : v' = i
    · subst hlast
      omega
    · exact hinv.upper_pos v' (by omega)
  · intro v' hv'
    by_cases hlast : v' = i
    · subst hlast
      rw [Array.getElem!_set!_self (hi := hvsz)]
      grind [Degree.includes, Degree.intersection]
    · have hold := hinv.includes v' (by omega)
      have holdinc : (pc.degrees[v']!).lower ≤ (ds[(vmap[v']!).idx!]!).lower ∧
          (ds[(vmap[v']!).idx!]!).upper ≤ (pc.degrees[v']!).upper := by
        simpa [Degree.includes] using hold
      by_cases hcv : (vmap[v']!).idx! = (vmap[i]!).idx!
      · have holdinc' := hcv ▸ holdinc
        rw [hcv, Array.getElem!_set!_self (hi := hvsz)]
        grind [Degree.includes, Degree.intersection]
      · rw [Array.getElem!_set!_ne (hij := fun h => hcv h.symm)]
        exact hold

/-- Semantic model of the reconciliation scan: `none` on a degree mismatch,
else the reconciled degree array. -/
private def reconcileGo (pc : PseudoConfiguration) (vmap : IndexMap) :
    Nat → Nat → Array Degree → Option (Array Degree) :=
  scanGo (reconcileStep pc vmap)

/-- A successful scan carries `ReconInv` to the full vertex range. -/
private theorem reconcileGo_spec {pc : PseudoConfiguration}
    {vmap : IndexMap} {N : Nat}
    (hvwf : IndexMap.WF vmap pc.n N) (hvt : vmap.Total) :
    ∀ (n i : Nat) (ds : Array Degree) {ds' : Array Degree}, i + n = pc.n →
      ReconInv pc vmap N i ds →
      reconcileGo pc vmap n i ds = some ds' →
      ReconInv pc vmap N pc.n ds'
  | 0, i, ds, ds', hin, hinv, heq => by
    obtain rfl := Option.some.inj heq
    have hi : i = pc.n := by omega
    exact hi ▸ hinv
  | n + 1, i, ds, ds', hin, hinv, heq => by
    have hilt : i < pc.n := by omega
    by_cases hdisj : Degree.disjoint (ds[(vmap[i]!).idx!]!) pc.degrees[i]! = true
    · exact absurd heq (by simp [reconcileGo, scanGo, reconcileStep, hdisj])
    · exact reconcileGo_spec hvwf hvt n (i + 1) _ (by omega)
        (hinv.step hvwf hvt hilt hdisj)
        (by simpa [reconcileGo, scanGo, reconcileStep, if_neg hdisj] using heq)

/-- A completed invariant, with the quotient map's well-formedness, totality
and surjectivity, is exactly the reconciliation carrier. -/
private theorem ReconInv.finish {pc : PseudoConfiguration} {vmap : IndexMap}
    {N : Nat} {ds : Array Degree}
    (hinv : ReconInv pc vmap N pc.n ds)
    (hvwf : IndexMap.WF vmap pc.n N) (hvt : vmap.Total)
    (hsurj : ∀ j, j < N → ∃ i, i < pc.n ∧ vmap.idx? i = Option.some j)
    (hdsz : pc.degrees.size = pc.n) :
    DegreeReconciliation pc.degrees vmap ds := by
  have hsz := hinv.size_eq
  refine ⟨?_, ?_, fun c hc => hinv.pos c hc, fun v hv => hinv.upper_pos v (by omega),
    fun v hv => hinv.includes v (by omega)⟩
  · intro v hv
    have := IndexMap.idx!_lt_of_total hvwf hvt (show v < pc.n by omega)
    omega
  · intro c hc
    have hc' : c < N := by omega
    obtain ⟨i, hi, hidx⟩ := hsurj c hc'
    have hii : i < vmap.size := by
      rw [hvwf.size_eq]
      exact hi
    exact ⟨i, by omega, idx!_of_idx? hii hidx⟩

/-- Functional model of `dartIdentification`: fail on a loop, else run the
semantic reconciliation scan and package the quotient. -/
private def reconcileOut (pc : PseudoConfiguration)
    (zStar : PseudoTriangulation) (mappings : Mappings) :
    Option (PseudoConfiguration × Mappings) :=
  if zStar.hasLoop then none
  else
    (reconcileGo pc mappings.vmap pc.n 0
        (Array.replicate zStar.n ⟨1, INFTY⟩)).map
      fun ds => (.new zStar.n zStar.darts ds, mappings)

/-- The executable computes the functional model. -/
private theorem dartIdentification_eq_reconcileOut (pc : PseudoConfiguration)
    (dartPairs : Array (Nat × Nat)) :
    pc.dartIdentification dartPairs =
      reconcileOut pc (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1
        (pc.toPseudoTriangulation.freeHomomorphism dartPairs).2 := by
  unfold PseudoConfiguration.dartIdentification reconcileOut reconcileGo
  rcases pc.toPseudoTriangulation.freeHomomorphism dartPairs with ⟨zStar, mappings⟩
  dsimp only
  by_cases hl : zStar.hasLoop
  · simp only [if_pos hl]
    rfl
  · simp only [if_neg hl]
    rw [forIn_range_eq_loopGo pc.n _ (scanStep (reconcileStep pc mappings.vmap))
      (fun v s => by dsimp only [scanStep, reconcileStep]; split <;> rfl),
      ← loopGo_scanStep_eq (reconcileStep pc mappings.vmap)
        (fun ds => (PseudoConfiguration.new zStar.n zStar.darts ds, mappings))
        pc.n 0 (Array.replicate zStar.n ⟨1, INFTY⟩)]
    rcases hL : loopGo (scanStep (reconcileStep pc mappings.vmap)) 0 pc.n
        (none, Array.replicate zStar.n ⟨1, INFTY⟩) with ⟨o, ds⟩
    cases o <;> simp only [pure_bind, Id.run_pure]

/-- **The concrete reconciliation bridge**: a successful `dartIdentification`
run reconciles the degrees along the vertex quotient. -/
private theorem dartIdentification_reconciliation {pc : PseudoConfiguration}
    (hpc : pc.WF) {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    pc'.degrees.size = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1.n ∧
      DegreeReconciliation pc.degrees
        (pc.toPseudoTriangulation.freeHomomorphism dartPairs).2.vmap pc'.degrees := by
  rcases hfh : pc.toPseudoTriangulation.freeHomomorphism dartPairs with ⟨zStar, mappings⟩
  have hspec := PseudoTriangulation.freeHomomorphism_spec hpc.1 hpairs hfh
  have hmw := hspec.maps_wf
  have hvt := hspec.vmap_total
  have hout : reconcileOut pc zStar mappings = some (pc', m) := by
    simpa only [dartIdentification_eq_reconcileOut, hfh] using hrun
  by_cases hl : zStar.hasLoop
  · exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
      some (pc', m) by simpa only [reconcileOut, if_pos hl] using hout)
  · have hinit : ReconInv pc mappings.vmap zStar.n 0
        (Array.replicate zStar.n ⟨1, INFTY⟩) := by
      refine ⟨Array.size_replicate, ?_, fun v' hv' => absurd hv' (by simp),
        fun v' hv' => absurd hv' (by simp)⟩
      intro c hc
      have hc' : c < zStar.n := by simpa using hc
      rw [getElem!_pos _ c (by simpa using hc'), Array.getElem_replicate]
      exact Nat.le_refl 1
    have hinv' : ReconInv pc mappings.vmap zStar.n pc.n pc'.degrees := by
      have hvwf := hmw.vmap_wf
      grind only [reconcileOut, reconcileGo_spec, Option.map_eq_some_iff,
        PseudoConfiguration.new]
    refine ⟨by simpa [PseudoConfiguration.new] using hinv'.size_eq, ?_⟩
    simpa [PseudoConfiguration.new] using
      hinv'.finish hmw.vmap_wf hvt hspec.vmap_surj hpc.2

/-- The quotient never grows the total slack: construct the reconciliation
carrier and read off its numeric consequence. -/
private theorem dartIdentification_slack_le {pc : PseudoConfiguration} (hpc : pc.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    degreeSlack pc' ≤ degreeSlack pc := by
  obtain ⟨-, hrec⟩ := dartIdentification_reconciliation hpc hpairs hrun
  unfold degreeSlack
  exact hrec.slack_le

section
set_option linter.tacticCheckInstances false
/-- What a successful split did: the first slack vertex is pinned to its
lowest degree in one child and to the rest of the range in the other. -/
private theorem singleOutLowerDegree_split {pc : PseudoConfiguration}
    {z1 z2 : PseudoConfiguration}
    (hrun : pc.singleOutLowerDegree = some (z1, z2)) :
    ∃ v, v < pc.n ∧ (pc.degrees[v]!).lower < (pc.degrees[v]!).upper ∧
      z1.degrees = pc.degrees.set! v
        ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩ ∧
      z2.degrees = pc.degrees.set! v
        ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩ := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some (z1, z2) =>
        ∃ v, v < pc.n ∧ (pc.degrees[v]!).lower < (pc.degrees[v]!).upper ∧
          z1.degrees = pc.degrees.set! v
            ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩ ∧
          z2.degrees = pc.degrees.set! v
            ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜∀ p, st.fst = some (some p) →
        ∃ v, v < pc.n ∧ (pc.degrees[v]!).lower < (pc.degrees[v]!).upper ∧
          p.1.degrees = pc.degrees.set! v
            ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩ ∧
          p.2.degrees = pc.degrees.set! v
            ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.new]
end

/-- The boundary-fan patch closes two open `pred` corners (`eF` and `eLR`)
and opens one (the second new dart): one net corner disappears. -/
private theorem boundaryFanPatch_openPred {src dst : PseudoTriangulation}
    {eF eL eFR eLR : Nat}
    (hp : PseudoTriangulation.BoundaryFanPatch src dst eF eL eFR eLR)
    (hv : src.Valid) :
    openPredCorners dst + 1 = openPredCorners src := by
  have heLR : eLR < src.darts.size :=
    hp.eLR_def ▸ (hv.wf.read_inBounds hp.eL_lt).rev_lt
  have hrevLR : (src.darts[eLR]!).rev = eL := hp.eLR_def ▸ hv.rev_rev eL hp.eL_lt
  have hpLR : (src.darts[eLR]!).pred.isNone = true := by
    refine (hv.boundary eLR heLR).mpr ?_
    rw [hrevLR]
    exact hp.succL_open
  have hpF : (src.darts[eF]!).pred.isNone = true := hp.predF_open
  have hne : eF ≠ eLR := by
    intro h
    have h2 : (src.darts[eL]!).head ≠ (src.darts[eLR]!).head := by
      simpa only [hp.eLR_def] using hv.loop_free eL hp.eL_lt
    exact h2 (hp.head_eq.symm.trans (congrArg (fun j => (src.darts[j]!).head) h))
  have hdF : (dst.darts[eF]!).pred.isNone = false := by
    simpa using hp.predF_closed
  have hdLR : (dst.darts[eLR]!).pred.isNone = false := by
    rw [hp.pred_eLR]
    rfl
  have hdNew1 : (dst.darts[src.darts.size]!).pred.isNone = false := by
    rw [hp.read_new1]
    rfl
  have hdNew2 : (dst.darts[src.darts.size + 1]!).pred.isNone = true := by
    rw [hp.read_new2]
    rfl
  have hexp : openPredCorners dst = (List.range src.darts.size).countP
      (fun i => (dst.darts[i]!).pred.isNone) + 1 := by
    unfold openPredCorners
    rw [hp.size, List.range_succ, List.countP_append, List.range_succ,
      List.countP_append]
    simp [hdNew1, hdNew2]
  have hflip := Counting.countP_flip2 hne hpF hdF hpLR hdLR
    src.darts.size hp.eF_lt heLR
    (fun i hilt hiF hiLR =>
      (congrArg OptIdx.isNone (hp.pred_old i hiF hiLR hilt)).symm)
  have hsrc : openPredCorners src = (List.range src.darts.size).countP
      (fun i => (src.darts[i]!).pred.isNone) := rfl
  omega

/-- **The boundary closure strictly shrinks the potential**: two new darts
against three weighted units of the closed corner, at unchanged slack. -/
private theorem addBoundaryDarts_potential {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    statePotential pc' < statePotential pc := by
  obtain ⟨eF, eL, eFR, eLR, hp⟩ := addBoundaryDarts_patch hv.wf hrun
  have hopen := boundaryFanPatch_openPred hp hv
  have hslack : degreeSlack pc' = degreeSlack pc := by
    unfold degreeSlack
    rw [addBoundaryDarts_degrees hrun]
  have hsize : pc'.toPseudoTriangulation.darts.size =
      pc.toPseudoTriangulation.darts.size + 2 := hp.size
  unfold statePotential
  rw [hslack]
  omega

/-- **A degree split strictly shrinks both children's potentials**: the
graph is untouched and the split vertex's slack drops to `0` and `w - 1`. -/
private theorem singleOutLowerDegree_potential {pc : PseudoConfiguration}
    (hd : pc.degrees.size = pc.n) {z1 z2 : PseudoConfiguration}
    (hrun : pc.singleOutLowerDegree = some (z1, z2)) :
    statePotential z1 < statePotential pc ∧ statePotential z2 < statePotential pc := by
  obtain ⟨hg1, hg2⟩ := singleOutLowerDegree_graph hrun
  obtain ⟨v, hvn, hlt, hz1, hz2⟩ := singleOutLowerDegree_split hrun
  have hvd : v < pc.degrees.size := by omega
  have hs1 : degreeSlack z1 +
      ((pc.degrees[v]!).upper - (pc.degrees[v]!).lower) = degreeSlack pc := by
    have hflip := Counting.sum_map_range_flip
      (f := fun i => (pc.degrees[i]!).upper - (pc.degrees[i]!).lower)
      (f' := fun i => ((pc.degrees.set! v
          ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩)[i]!).upper -
        ((pc.degrees.set! v
          ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩)[i]!).lower)
      (j := v)
      (fun i hi => by rw [Array.getElem!_set!_ne (hij := fun h => hi h.symm)])
      pc.degrees.size hvd
    have hfv : ((pc.degrees.set! v
        ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩)[v]!).upper -
        ((pc.degrees.set! v
          ⟨(pc.degrees[v]!).lower, (pc.degrees[v]!).lower⟩)[v]!).lower = 0 := by
      rw [Array.getElem!_set!_self (hi := hvd)]
      simp
    unfold degreeSlack
    rw [hz1, Array.size_set!]
    omega
  have hs2 : degreeSlack z2 +
      ((pc.degrees[v]!).upper - (pc.degrees[v]!).lower) = degreeSlack pc +
      ((pc.degrees[v]!).upper - ((pc.degrees[v]!).lower + 1)) := by
    have hflip := Counting.sum_map_range_flip
      (f := fun i => (pc.degrees[i]!).upper - (pc.degrees[i]!).lower)
      (f' := fun i => ((pc.degrees.set! v
          ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩)[i]!).upper -
        ((pc.degrees.set! v
          ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩)[i]!).lower)
      (j := v)
      (fun i hi => by rw [Array.getElem!_set!_ne (hij := fun h => hi h.symm)])
      pc.degrees.size hvd
    have hfv : ((pc.degrees.set! v
        ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩)[v]!).upper -
        ((pc.degrees.set! v
          ⟨(pc.degrees[v]!).lower + 1, (pc.degrees[v]!).upper⟩)[v]!).lower =
        (pc.degrees[v]!).upper - ((pc.degrees[v]!).lower + 1) := by
      rw [Array.getElem!_set!_self (hi := hvd)]
    unfold degreeSlack
    rw [hz2, Array.size_set!]
    omega
  have hD1 : z1.toPseudoTriangulation.darts.size =
      pc.toPseudoTriangulation.darts.size := by rw [hg1]
  have hO1 : openPredCorners z1.toPseudoTriangulation =
      openPredCorners pc.toPseudoTriangulation := by rw [hg1]
  have hD2 : z2.toPseudoTriangulation.darts.size =
      pc.toPseudoTriangulation.darts.size := by rw [hg2]
  have hO2 : openPredCorners z2.toPseudoTriangulation =
      openPredCorners pc.toPseudoTriangulation := by rw [hg2]
  constructor
  · unfold statePotential
    rw [hD1, hO1]
    omega
  · unfold statePotential
    rw [hD2, hO2]
    omega

/-- **Loop invariant for `resolveDegreeIssues` (A.4.4).** Every queued or emitted
entry is a *valid, rotational* configuration reached from `origin` by a
certified mapping: `Valid` carries the geometry the A.4 steps need, the
rotation laws carry Sections 9.3-9.4's termination argument, and the
`CoherentMappings` records the homomorphism from the origin -- all of which
compose by construction. -/
structure ResolveEntry (origin : PseudoConfiguration)
    (entry : PseudoConfiguration × Mappings) : Prop where
  valid : entry.1.toPseudoTriangulation.Valid
  degrees_wf : entry.1.degrees.size = entry.1.n
  mapping : ∃ C : CoherentMappings origin.toPseudoTriangulation entry.1.toPseudoTriangulation,
    C.maps = entry.2
  rotational : (entry.1.toPseudoTriangulation.dartGraph valid.wf).Rotational

/-- The seed entry: `origin` mapped to itself by the identity (A.4.4 line 3).
Origin rotationality is a premise until the checker bridge discharges it at
load time. -/
theorem ResolveEntry.initial {origin : PseudoConfiguration}
    (hv : origin.toPseudoTriangulation.Valid) (hd : origin.degrees.size = origin.n)
    (hr : (origin.toPseudoTriangulation.dartGraph hv.wf).Rotational) :
    ResolveEntry origin (origin, Mappings.initialMappings origin.n origin.darts.size) where
  valid := hv
  degrees_wf := hd
  mapping := ⟨CoherentMappings.id hv.wf, rfl⟩
  rotational := hr

/-- **Degree-split transport (A.4.9).** `singleOutLowerDegree` only subdivides a
range, leaving the graph and mapping untouched, so both children inherit the
entry. -/
theorem ResolveEntry.singleOut {origin pc z1 z2 : PseudoConfiguration} {maps : Mappings}
    (h : ResolveEntry origin (pc, maps)) (hrun : pc.singleOutLowerDegree = some (z1, z2)) :
    ResolveEntry origin (z1, maps) ∧ ResolveEntry origin (z2, maps) := by
  obtain ⟨hg1, hg2⟩ := singleOutLowerDegree_graph hrun
  obtain ⟨hd1, hd2⟩ := singleOutLowerDegree_degrees hrun
  have hn1 : z1.n = pc.n := congrArg PseudoTriangulation.n hg1
  have hn2 : z2.n = pc.n := congrArg PseudoTriangulation.n hg2
  have hv1 : z1.toPseudoTriangulation.Valid := hg1 ▸ h.valid
  have hv2 : z2.toPseudoTriangulation.Valid := hg2 ▸ h.valid
  obtain ⟨hr1, hr2⟩ :=
    singleOutLowerDegree_rotational h.valid.wf hrun hv1.wf hv2.wf h.rotational
  exact ⟨⟨hv1, by rw [hd1, h.degrees_wf, hn1], hg1 ▸ h.mapping, hr1⟩,
    ⟨hv2, by rw [hd2, h.degrees_wf, hn2], hg2 ▸ h.mapping, hr2⟩⟩

/-- Unwrap a successful over-incidence run: the explicitly selected dart pair
exists, is in range (bounds come from the successful unwraps, not from a
nonemptiness argument), and the run is the identification of that pair. -/
private theorem fixIssue_over_run {pc : PseudoConfiguration} (hpc : pc.WF)
    {v : Nat} (h1 : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) :
    ∃ e f, e < pc.darts.size ∧ f < pc.darts.size ∧
      (if pc.isBoundary[v]! then pc.firstDart v else pc.anyDart v) = some e ∧
      pc.sucKTimes e (pc.degrees[v]!).lower = some f ∧
      pc.dartIdentification #[(e, f)] = some (pc', m) := by
  rcases hE : (if pc.isBoundary[v]! then pc.firstDart v else pc.anyDart v) with _ | e
  · exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
      some (pc', m) from by simpa only [fixSingleDegreeIssue, if_pos h1, hE] using hrun)
  · have he : e < pc.darts.size := by
      by_cases hb : pc.isBoundary[v]! = true
      · exact PseudoTriangulation.firstDart_lt (by simpa only [hb, if_pos] using hE)
      · exact PseudoTriangulation.anyDart_lt
          (by simpa only [if_neg hb] using hE)
    rcases hF : pc.sucKTimes e (pc.degrees[v]!).lower with _ | f
    · exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
        some (pc', m) from by
          simpa only [fixSingleDegreeIssue, if_pos h1, hE, hF] using hrun)
    · exact ⟨e, f, he, PseudoTriangulation.sucKTimes_lt hpc.1 he hF, rfl, hF,
        by simpa only [fixSingleDegreeIssue, if_pos h1, hE, hF] using hrun⟩

/-- `fixSingleDegreeIssue` (A.4.7) preserves well-formedness: the
over-incidence arm glues an in-range pair, the boundary arm closes the
boundary; the remaining arms cannot answer `some`. -/
theorem fixSingleDegreeIssue_wf {pc : PseudoConfiguration} (hpc : pc.WF)
    {v : Nat} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) : pc'.WF := by
  by_cases h1 : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!
  · obtain ⟨e, f, he, hf, -, -, hrun'⟩ := fixIssue_over_run hpc h1 hrun
    exact dartIdentification_wf hpc (by grind) hrun'
  · by_cases h2 : (pc.isBoundary[v]!
        && pc.nIncidentDarts[v]! == (pc.degrees[v]!).lower) = true
    · cases hA : pc.addBoundaryDarts v with
      | none =>
          exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
            some (pc', m) from by
              simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun)
      | some pcA =>
          have hr : (pcA, Mappings.initialMappings pc.n pc.darts.size) = (pc', m) :=
            Option.some.inj (by
              simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun)
          have hr' : pcA = pc' := congrArg Prod.fst hr
          exact hr' ▸ addBoundaryDarts_wf hpc hA
    · exact absurd hrun (by
        simp only [fixSingleDegreeIssue, if_neg h1, if_neg h2]
        exact fun hp => nomatch
          (show (none : Option (PseudoConfiguration × Mappings)) = some (pc', m) from hp))

/-- **Certified step for `fixSingleDegreeIssue` (A.4.7):** every successful
result is valid, has covering degrees, and is reached by a certified mapping --
soundness needs only `Valid` and degree coverage, since the option-safe arms
unwrap their darts explicitly and a successful run carries their existence.
(That every degree issue produces a result is the separate completeness claim;
the rotation laws it rests on are now in place.) -/
theorem fixSingleDegreeIssue_spec {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) (hd : pc.degrees.size = pc.n)
    {v : Nat} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) :
    pc'.toPseudoTriangulation.Valid ∧ pc'.degrees.size = pc'.n ∧
      ∃ C : CoherentMappings pc.toPseudoTriangulation pc'.toPseudoTriangulation,
        C.maps = m := by
  have hpc : pc.WF := ⟨hv.wf, hd⟩
  have hdeg : pc'.degrees.size = pc'.n := (fixSingleDegreeIssue_wf hpc hrun).2
  by_cases h1 : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!
  · -- Over-incidence: identify the selected dart pair (A.4.1).
    obtain ⟨e, f, he, hf, -, -, hrun'⟩ := fixIssue_over_run hpc h1 hrun
    exact ⟨dartIdentification_valid hv (by grind) hrun', hdeg,
      dartIdentification_coherentMappings hpc (by grind) hrun'⟩
  · by_cases h2 : (pc.isBoundary[v]!
        && pc.nIncidentDarts[v]! == (pc.degrees[v]!).lower) = true
    · -- Boundary deficit: close the fan with a new edge (A.4.6/A.4.8).
      cases hA : pc.addBoundaryDarts v with
      | none =>
          exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
            some (pc', m) from by
              simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun)
      | some pcA =>
          have hr : (pcA, Mappings.initialMappings pc.n pc.darts.size) = (pc', m) :=
            Option.some.inj (by
              simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun)
          have hr1 : pcA = pc' := congrArg Prod.fst hr
          have hr2 : Mappings.initialMappings pc.n pc.darts.size = m :=
            congrArg Prod.snd hr
          obtain ⟨hAvalid, hEx⟩ := addBoundaryDarts_spec hv hA
          obtain ⟨C, hC⟩ := hr1 ▸ hEx
          exact ⟨hr1 ▸ hAvalid, hdeg, ⟨C, hC.trans hr2⟩⟩
    · exact absurd hrun (by
        simp only [fixSingleDegreeIssue, if_neg h1, if_neg h2]
        exact fun hp => nomatch
          (show (none : Option (PseudoConfiguration × Mappings)) = some (pc', m) from hp))

/-- `fixSingleDegreeIssue` preserves validity (A.4.7). -/
theorem fixSingleDegreeIssue_valid {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) (hd : pc.degrees.size = pc.n)
    {v : Nat} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) :
    pc'.toPseudoTriangulation.Valid :=
  (fixSingleDegreeIssue_spec hv hd hrun).1

/-- `fixSingleDegreeIssue` preserves the rotation laws (A.4.7): each
producing arm is one of the two certified edits. -/
theorem fixSingleDegreeIssue_rotational {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) (hd : pc.degrees.size = pc.n)
    {v : Nat} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m))
    (hS : pc'.toPseudoTriangulation.WF)
    (hr : (pc.toPseudoTriangulation.dartGraph hv.wf).Rotational) :
    (pc'.toPseudoTriangulation.dartGraph hS).Rotational := by
  have hpc : pc.WF := ⟨hv.wf, hd⟩
  by_cases h1 : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!
  · obtain ⟨e, f, he, hf, -, -, hrun'⟩ := fixIssue_over_run hpc h1 hrun
    exact dartIdentification_rotational hv.wf (by grind) hrun' hS hr
  · by_cases h2 : (pc.isBoundary[v]!
        && pc.nIncidentDarts[v]! == (pc.degrees[v]!).lower) = true
    · cases hA : pc.addBoundaryDarts v with
      | none =>
          exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
            some (pc', m) from by
              simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun)
      | some pcA =>
          have hr1 : pcA = pc' := congrArg Prod.fst (Option.some.inj (by
            simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun))
          subst hr1
          exact addBoundaryDarts_rotational hv hA hS hr
    · exact absurd hrun (by
        simp only [fixSingleDegreeIssue, if_neg h1, if_neg h2]
        exact fun hp => nomatch
          (show (none : Option (PseudoConfiguration × Mappings)) = some (pc', m) from hp))

/-- **`fixSingleDegreeIssue` strictly shrinks the potential** at a reported
issue vertex: the over-incidence arm identifies two distinct darts of the
vertex's rotation (distinct by the page-32 walk argument, with a positive
step count from the reconciliation), and the boundary arm closes the fan. -/
private theorem fixSingleDegreeIssue_potential {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) (hd : pc.degrees.size = pc.n)
    (hr : (pc.toPseudoTriangulation.dartGraph hv.wf).Rotational)
    {v : Nat} (hvn : v < pc.n) (hfix : (pc.degrees[v]!).fixed = true)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) :
    statePotential pc' < statePotential pc := by
  have hpc : pc.WF := ⟨hv.wf, hd⟩
  by_cases h1 : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!
  · obtain ⟨e, f, he, hf, hsel, hwalk, hrun'⟩ := fixIssue_over_run hpc h1 hrun
    obtain ⟨hsz', hrec⟩ := dartIdentification_reconciliation hpc (by grind) hrun'
    have hk1 : 1 ≤ (pc.degrees[v]!).lower := hrec.fixed_lower_pos (by omega) hfix
    have hheadE : (pc.darts[e]!).head = v := by
      by_cases hb : pc.isBoundary[v]! = true
      · exact PseudoTriangulation.firstDart_head (by simpa [hb] using hsel)
      · exact PseudoTriangulation.anyDart_head (by simpa [hb] using hsel)
    obtain ⟨l, hl⟩ := hr.incidence ⟨v, hvn⟩
    have hmem : (⟨e, he⟩ : Fin pc.darts.size) ∈ l := (hl.mem_iff _).mpr (Fin.ext hheadE)
    have hinc : pc.nIncidentDarts[v]! = l.length :=
      nIncidentDarts_eq_length hv.wf (vf := ⟨v, hvn⟩) hl
    have hwalkS := PseudoTriangulation.sucKTimes_spec hv.wf he
      (k := (pc.degrees[v]!).lower) hwalk
    obtain ⟨df, hdf, hdfval⟩ := Option.map_eq_some_iff.mp hwalkS.symm
    have hne : df ≠ (⟨e, he⟩ : Fin pc.darts.size) :=
      DartGraph.IncidenceList.succWalk_ne hl hmem (by omega) (by omega) hdf
    have hnef : e ≠ f := fun h =>
      hne (Fin.ext (hdfval.trans h.symm))
    obtain ⟨hgraph, hmap, -⟩ := dartIdentification_graph_maps hrun'
    have hspecEF := PseudoTriangulation.freeHomomorphism_spec hpc.1 (by grind)
      (ptStar := (pc.toPseudoTriangulation.freeHomomorphism #[(e, f)]).1)
      (maps := (pc.toPseudoTriangulation.freeHomomorphism #[(e, f)]).2) rfl
    have hDlt := freeHomomorphism_size_lt hspecEF he hf (by simp) hnef
    have hD2 : pc'.toPseudoTriangulation.darts.size =
        (pc.toPseudoTriangulation.freeHomomorphism #[(e, f)]).1.darts.size :=
      congrArg (fun t => t.darts.size) hgraph
    have hOle := freeHomomorphism_openPred_le hspecEF
    have hO2 : openPredCorners pc'.toPseudoTriangulation =
        openPredCorners (pc.toPseudoTriangulation.freeHomomorphism #[(e, f)]).1 :=
      congrArg openPredCorners hgraph
    have hSle : degreeSlack pc' ≤ degreeSlack pc :=
      dartIdentification_slack_le hpc (by grind) hrun'
    unfold statePotential
    omega
  · by_cases h2 : (pc.isBoundary[v]!
        && pc.nIncidentDarts[v]! == (pc.degrees[v]!).lower) = true
    · cases hA : pc.addBoundaryDarts v with
      | none =>
          exact nomatch (show (none : Option (PseudoConfiguration × Mappings)) =
            some (pc', m) from by
              simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun)
      | some pcA =>
          have hr1 : pcA = pc' := congrArg Prod.fst (Option.some.inj (by
            simpa only [fixSingleDegreeIssue, if_neg h1, if_pos h2, hA] using hrun))
          subst hr1
          exact addBoundaryDarts_potential hv hA
    · exact absurd hrun (by
        simp only [fixSingleDegreeIssue, if_neg h1, if_neg h2]
        exact fun hp => nomatch
          (show (none : Option (PseudoConfiguration × Mappings)) = some (pc', m) from hp))

/-- **Degree-fix transport (A.4.7).** A fix step keeps the entry: validity and
degrees by `fixSingleDegreeIssue_spec`, the mapping by composing the entry's
certified mapping with the step's, exactly as the executable loop composes
`mappingsTilde` with `mappingsStar`. -/
theorem ResolveEntry.fixSingle {origin pc : PseudoConfiguration} {maps : Mappings}
    (h : ResolveEntry origin (pc, maps)) {v : Nat}
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) :
    ResolveEntry origin (pc', maps.compose m) := by
  obtain ⟨hvalid, hdeg, C, hC⟩ := fixSingleDegreeIssue_spec h.valid h.degrees_wf hrun
  obtain ⟨C₀, hC₀⟩ := h.mapping
  exact ⟨hvalid, hdeg, ⟨C₀.compose C, by
    show C₀.maps.compose C.maps = maps.compose m
    rw [hC₀, hC]⟩,
    fixSingleDegreeIssue_rotational h.valid h.degrees_wf hrun hvalid.wf h.rotational⟩

section
set_option linter.tacticCheckInstances false
/-- **An emitted entry is resolved**: beyond the loop invariant,
the sole emission branch fires only after all three issue tests come back
negative. Without these fields, emitting the valid origin unchanged would
satisfy the postcondition. -/
structure ResolvedEntry (origin : PseudoConfiguration)
    (entry : PseudoConfiguration × Mappings) : Prop
    extends ResolveEntry origin entry where
  noSubdegreeError : entry.1.innerSubdegreeError = false
  noSingleIssue : entry.1.vertexSingleDegreeIssue = none
  noDegreeSplit : entry.1.singleOutLowerDegree = none

/-- The BFS loop's packed state: the emitted entries and the worklist, in
declaration order. -/
private abbrev ResolveState :=
  Array (PseudoConfiguration × Mappings) × Queue (PseudoConfiguration × Mappings)

/-- Continue-side and break-side invariants over the packed state. -/
private def ResolveSpecSum (origin : PseudoConfiguration) :
    ResolveState ⊕ ResolveState → Prop
  | .inl s =>
      (∀ p, s.snd.Active p → ResolveEntry origin p) ∧ ∀ p ∈ s.fst, ResolvedEntry origin p
  | .inr s => ∀ p ∈ s.fst, ResolvedEntry origin p

grind_pattern resolveWeight_lt => resolveWeight (z', m'), resolveWeight (z, m)
grind_pattern resolveWeight_add_lt =>
  resolveWeight (z1, m1), resolveWeight (z2, m2), resolveWeight (z, m)

/-- **The A.4.4 BFS is sound and terminates**: every entry it emits is a
valid, rotational configuration with covering degrees, reached from the
origin by a certified mapping. Origin rotationality is a premise,
discharged at the load boundary by `rotationLawsCertify_rotational`. -/
theorem resolveDegreeIssues_sound {origin : PseudoConfiguration}
    (hv : origin.toPseudoTriangulation.Valid) (hd : origin.degrees.size = origin.n)
    (hr : (origin.toPseudoTriangulation.dartGraph hv.wf).Rotational)
    {out : Array (PseudoConfiguration × Mappings)}
    (hrun : origin.resolveDegreeIssues = out) :
    ∀ entry ∈ out, ResolvedEntry origin entry := by
  apply Std.Internal.Do.Id.of_wp_run_eq hrun
    fun out => ∀ entry ∈ out, ResolvedEntry origin entry
  vcgen
  case inv1 => exact ResolveSpecSum origin
  case inv2 => exact fun s => resolveMeasure s.snd
  any_goals simp_all +zetaDelta
  all_goals grind [ResolveSpecSum, ResolveEntry, ResolvedEntry,
    ResolveEntry.initial, → ResolveEntry.fixSingle, → ResolveEntry.singleOut,
    → vertexSingleDegreeIssue_spec, → fixSingleDegreeIssue_potential,
    → singleOutLowerDegree_potential, → resolveMeasure_pop, resolveMeasure_push,
    resolveWeight_pos, resolveWeight, resolveWeight_lt, resolveWeight_add_lt,
    Nat.pow_lt_pow_right, → Queue.active_pop, → Queue.active_push,
    → Queue.active_head, → Queue.active_ofArray, Array.mem_def]
end

/-- Membership form of the BFS soundness theorem: everything
`resolveDegreeIssues` emits satisfies the loop invariant. -/
theorem resolvedEntry_of_mem_resolveDegreeIssues {origin : PseudoConfiguration}
    (hv : origin.toPseudoTriangulation.Valid) (hd : origin.degrees.size = origin.n)
    (hr : (origin.toPseudoTriangulation.dartGraph hv.wf).Rotational)
    {entry : PseudoConfiguration × Mappings}
    (hmem : entry ∈ origin.resolveDegreeIssues) : ResolvedEntry origin entry :=
  resolveDegreeIssues_sound hv hd hr rfl entry hmem

/-- **The A.4.3 wrapper is certified end to end**: every entry the
configuration-level `freeHomomorphism` returns is a resolved configuration
reached from `pc` by a certified mapping -- `dartIdentification`'s carrier
composed with the BFS entry's. -/
theorem freeHomomorphism_resolvedEntries {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) (hd : pc.degrees.size = pc.n)
    (hr : (pc.toPseudoTriangulation.dartGraph hv.wf).Rotational)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {entry : PseudoConfiguration × Mappings}
    (hmem : entry ∈ pc.freeHomomorphism dartPairs) :
    ResolvedEntry pc entry := by
  cases hrun : pc.dartIdentification dartPairs with
  | none =>
    exact absurd
      (by simpa only [PseudoConfiguration.freeHomomorphism, hrun] using hmem)
      (by simp)
  | some pair =>
    obtain ⟨zStar, mappings⟩ := pair
    have hmem' := by
      simpa only [PseudoConfiguration.freeHomomorphism, hrun] using hmem
    obtain ⟨⟨zT, mT⟩, hmemR, rfl⟩ := Array.mem_map.mp hmem'
    have hpc : pc.WF := ⟨hv.wf, hd⟩
    have hSwf : zStar.WF := dartIdentification_wf hpc hpairs hrun
    have hvS : zStar.toPseudoTriangulation.Valid :=
      dartIdentification_valid hv hpairs hrun
    have hrS : (zStar.toPseudoTriangulation.dartGraph hvS.wf).Rotational :=
      dartIdentification_rotational hv.wf hpairs hrun hvS.wf hr
    have hre := resolvedEntry_of_mem_resolveDegreeIssues hvS hSwf.2 hrS hmemR
    obtain ⟨C₀, hC₀⟩ := dartIdentification_coherentMappings hpc hpairs hrun
    obtain ⟨C₁, hC₁⟩ := hre.mapping
    refine ⟨⟨hre.valid, hre.degrees_wf, ⟨C₀.compose C₁, ?_⟩, hre.rotational⟩,
      hre.noSubdegreeError, hre.noSingleIssue, hre.noDegreeSplit⟩
    show C₀.maps.compose C₁.maps = mappings.compose mT
    rw [hC₀, hC₁]

/-- **The pair wrapper is certified to its call sites**: each returned
triple is a resolved configuration with an unsplit certified mapping from
the disjoint union, and the two returned split maps are the underlying maps
of certified (well-formed, coherent) mappings from the respective sides.
Sourcing `Valid` and the rotation laws of the union from the sides awaits
the disjoint-union transport lemmas. -/
theorem freeHomomorphismPair_resolvedEntries {pc0 pc1 : PseudoConfiguration}
    (hpc0 : pc0.WF) (hpc1 : pc1.WF)
    (hvU : (pc0.disjointUnion pc1).toPseudoTriangulation.Valid)
    (hrU : ((pc0.disjointUnion pc1).toPseudoTriangulation.dartGraph
      hvU.wf).Rotational)
    {dartId0 dartId1 : Nat}
    (hdart0 : dartId0 < pc0.darts.size) (hdart1 : dartId1 < pc1.darts.size)
    {entry : PseudoConfiguration × Mappings × Mappings}
    (hmem : entry ∈ pc0.freeHomomorphismPair pc1 dartId0 dartId1) :
    ∃ (M : Mappings)
      (C0 : CoherentMappings pc0.toPseudoTriangulation entry.1.toPseudoTriangulation)
      (C1 : CoherentMappings pc1.toPseudoTriangulation entry.1.toPseudoTriangulation),
      ResolvedEntry (pc0.disjointUnion pc1) (entry.1, M) ∧
      C0.maps = entry.2.1 ∧ C1.maps = entry.2.2 := by
  obtain ⟨hUwf, hUdeg⟩ := disjointUnion_wf hpc0 hpc1
  have hmem' := by
    simpa only [PseudoConfiguration.freeHomomorphismPair] using hmem
  obtain ⟨⟨idPc, M⟩, hmemF, rfl⟩ := Array.mem_map.mp hmem'
  have hres := freeHomomorphism_resolvedEntries hvU hUdeg hrU
    (PseudoTriangulation.freeHomomorphismPair_seed_bounds hdart0 hdart1) hmemF
  obtain ⟨C, hC⟩ := hres.mapping
  have hMwf := hC ▸ C.wf
  have hMcoh := hC ▸ C.coherent
  have hUn : (pc0.disjointUnion pc1).n = pc0.n + pc1.n := rfl
  have hUd : (pc0.disjointUnion pc1).darts.size =
      pc0.darts.size + pc1.darts.size := by
    show (PseudoTriangulation.disjointUnion pc0.toPseudoTriangulation
      pc1.toPseudoTriangulation).darts.size = _
    rw [PseudoTriangulation.disjointUnion_darts]
    simp
  refine ⟨M,
    ⟨⟨(splitMap M.vmap pc0.n).1, (splitMap M.dmap pc0.darts.size).1⟩,
      ⟨splitMap_fst_wf hMwf.vmap_wf (by omega),
       splitMap_fst_wf hMwf.dmap_wf (by omega)⟩,
      PseudoTriangulation.coherent_split_fst hpc0.1 hMwf hMcoh⟩,
    ⟨⟨(splitMap M.vmap pc0.n).2, (splitMap M.dmap pc0.darts.size).2⟩,
      ⟨by rw [show pc1.n = (pc0.disjointUnion pc1).n - pc0.n from by omega]
          exact splitMap_snd_wf (l := pc0.n) hMwf.vmap_wf,
       by rw [show pc1.darts.size =
              (pc0.disjointUnion pc1).darts.size - pc0.darts.size from by omega]
          exact splitMap_snd_wf (l := pc0.darts.size) hMwf.dmap_wf⟩,
      PseudoTriangulation.coherent_split_snd hpc1.1 hMwf hMcoh⟩,
    hres, rfl, rfl⟩

end Steps

end PseudoConfiguration

namespace PseudoTriangulation

/-- A passing M3 scan gives the pointwise inverse laws. -/
private theorem linkInverseCheck_spec {pt : PseudoTriangulation}
    (h : pt.linkInverseCheck = true) {i : Nat} (hi : i < pt.darts.size) :
    (∀ e, (pt.darts[i]!).succ = OptIdx.some e →
      (pt.darts[e]!).pred = OptIdx.some i) ∧
    (∀ e, (pt.darts[i]!).pred = OptIdx.some e →
      (pt.darts[e]!).succ = OptIdx.some i) := by
  have hall := by simpa [linkInverseCheck] using h
  exact ⟨fun e he => by simpa [he, OptIdx.«some»] using (hall i hi).1,
    fun e he => by simpa [he, OptIdx.«some»] using (hall i hi).2⟩

/-- A passing M4 scan gives the pointwise head-preservation laws. -/
private theorem linkHeadCheck_spec {pt : PseudoTriangulation}
    (h : pt.linkHeadCheck = true) {i : Nat} (hi : i < pt.darts.size) :
    (∀ e, (pt.darts[i]!).succ = OptIdx.some e →
      (pt.darts[e]!).head = (pt.darts[i]!).head) ∧
    (∀ e, (pt.darts[i]!).pred = OptIdx.some e →
      (pt.darts[e]!).head = (pt.darts[i]!).head) := by
  have hall := by simpa [linkHeadCheck] using h
  exact ⟨fun e he => by simpa [he, OptIdx.«some»] using (hall i hi).1,
    fun e he => by simpa [he, OptIdx.«some»] using (hall i hi).2⟩

/-- A passing reachability scan justifies every witness index locally:
index `0` darts are their vertex's stored start, positive indices step
back through `pred`. -/
private theorem incidenceReachCheck_spec {pt : PseudoTriangulation}
    (h : pt.incidenceReachCheck = true) {d : Nat} (hd : d < pt.darts.size) :
    (pt.walkWitness.2[d]! = 0 → pt.walkWitness.1[(pt.darts[d]!).head]! = d) ∧
    (pt.walkWitness.2[d]! ≠ 0 → ∃ p, (pt.darts[d]!).pred = OptIdx.some p ∧
      pt.walkWitness.2[p]! + 1 = pt.walkWitness.2[d]!) := by
  have hall := by simpa [incidenceReachCheck] using h
  have hd' := hall d hd
  constructor
  · intro h0
    simpa [h0] using hd'
  · intro hne
    cases hp : (pt.darts[d]!).pred with
    | none => exact absurd hd' (by simp [hne, hp])
    | some p =>
      refine ⟨p, rfl, ?_⟩
      simpa [hne, hp] using hd'

/-- **The checker bridge**: a passing `rotationLawsCertify` yields the
semantic rotation laws -- `Rotational` only, not `Valid`, so it discharges
exactly the BFS wrappers' rotationality premise while validity and degree
coverage stay separately certified. The link scans give pointwise M3/M4,
reachability gives fiber connectivity, and the conversion theorem rebuilds
each vertex's incidence list. -/
theorem rotationLawsCertify_rotational {pt : PseudoTriangulation} (hwf : pt.WF)
    (h : pt.rotationLawsCertify = true) : (pt.dartGraph hwf).Rotational := by
  obtain ⟨⟨hm3, hm4⟩, hreach⟩ : (pt.linkInverseCheck = true ∧
      pt.linkHeadCheck = true) ∧ pt.incidenceReachCheck = true := by
    simpa [rotationLawsCertify, Bool.and_eq_true] using h
  have hM3a : ∀ d e, (pt.dartGraph hwf).succ d = some e →
      (pt.dartGraph hwf).pred e = some d := by
    intro d e hs
    have hget : (pt.darts[d.val]!).succ.get? = Option.some e.val :=
      (dartGraph_succ_get? hwf d).symm.trans (congrArg (Option.map Fin.val) hs)
    have hpred := (linkInverseCheck_spec hm3 d.isLt).1 e.val
      (OptIdx.get?_eq_some_iff.mp hget)
    have hpget : (pt.darts[e.val]!).pred.get? = Option.some d.val := by
      rw [hpred]
      exact OptIdx.get?_some d.val
    exact dartGraph_pred_eq_some hwf hpget
  have hM3b : ∀ d e, (pt.dartGraph hwf).pred d = some e →
      (pt.dartGraph hwf).succ e = some d := by
    intro d e hs
    have hget : (pt.darts[d.val]!).pred.get? = Option.some e.val :=
      (dartGraph_pred_get? hwf d).symm.trans (congrArg (Option.map Fin.val) hs)
    have hsucc := (linkInverseCheck_spec hm3 d.isLt).2 e.val
      (OptIdx.get?_eq_some_iff.mp hget)
    have hsget : (pt.darts[e.val]!).succ.get? = Option.some d.val := by
      rw [hsucc]
      exact OptIdx.get?_some d.val
    exact dartGraph_succ_eq_some hwf hsget
  have hM4 : ∀ d e, (pt.dartGraph hwf).succ d = some e →
      (pt.dartGraph hwf).head e = (pt.dartGraph hwf).head d := by
    intro d e hs
    have hget : (pt.darts[d.val]!).succ.get? = Option.some e.val :=
      (dartGraph_succ_get? hwf d).symm.trans (congrArg (Option.map Fin.val) hs)
    exact Fin.ext ((linkHeadCheck_spec hm4 d.isLt).1 e.val
      (OptIdx.get?_eq_some_iff.mp hget))
  refine ⟨hM3a, hM3b, hM4, ?_⟩
  intro v
  haveI := Classical.typeDecidableEq (Fin pt.n)
  refine DartGraph.exists_incidenceList_of_conn hM3a hM3b hM4
    (l₀ := (List.finRange pt.darts.size).filter
      (fun d => (pt.dartGraph hwf).head d = v)) ?_ ?_
  · intro d
    rw [List.mem_filter]
    simp [List.mem_finRange]
  · -- every dart connects to its vertex's start: induction on the witness
    have hstart : ∀ n d (hd : d < pt.darts.size), pt.walkWitness.2[d]! = n →
        ∃ s, ∃ hs : s < pt.darts.size,
          pt.walkWitness.1[(pt.darts[d]!).head]! = s ∧
          DartGraph.IncidenceConn (pt.dartGraph hwf) ⟨s, hs⟩ ⟨d, hd⟩ := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro d hd hidx
        by_cases h0 : pt.walkWitness.2[d]! = 0
        · exact ⟨d, hd, (incidenceReachCheck_spec hreach hd).1 h0, .refl _⟩
        · obtain ⟨p, hp, hpidx⟩ := (incidenceReachCheck_spec hreach hd).2 h0
          have hplt : p < pt.darts.size :=
            (hwf.read_inBounds hd).pred_lt p (by
              rw [hp]
              exact OptIdx.get?_some p)
          obtain ⟨s, hs, hstart_p, hconn_p⟩ :=
            ih pt.walkWitness.2[p]! (by omega) p hplt rfl
          have hhead : (pt.darts[p]!).head = (pt.darts[d]!).head :=
            (linkHeadCheck_spec hm4 hd).2 p hp
          have hsucc := (linkInverseCheck_spec hm3 hd).2 p hp
          have hsget : (pt.darts[p]!).succ.get? = Option.some d := by
            rw [hsucc]
            exact OptIdx.get?_some d
          refine ⟨s, hs, ?_, ?_⟩
          · rw [← hhead]
            exact hstart_p
          · exact hconn_p.trans (.succ (dartGraph_succ_eq_some hwf hsget))
    intro d₁ h1 d₂ h2
    have hh1 : (pt.dartGraph hwf).head d₁ = v := by
      simpa using (List.mem_filter.mp h1).2
    have hh2 : (pt.dartGraph hwf).head d₂ = v := by
      simpa using (List.mem_filter.mp h2).2
    obtain ⟨s₁, hs₁lt, hst₁, hc₁⟩ := hstart _ d₁.val d₁.isLt rfl
    obtain ⟨s₂, hs₂lt, hst₂, hc₂⟩ := hstart _ d₂.val d₂.isLt rfl
    have hv12 : (pt.darts[d₁.val]!).head = (pt.darts[d₂.val]!).head := by
      simpa using congrArg Fin.val (hh1.trans hh2.symm)
    have hss : s₁ = s₂ := hst₁.symm.trans (by
      rw [hv12]
      exact hst₂)
    subst hss
    exact hc₁.symm.trans hc₂

end PseudoTriangulation

/-- The load boundary's certificate, semantically: every `RotConfig`
carries the rotation laws of its dart graph (`Rotational` -- M3/M4/M6 --
not `Valid`). This is the fact the resolution wrappers take as their
rotationality premise for loaded objects. -/
theorem RotConfig.rotational (c : RotConfig) :
    (c.toPseudoTriangulation.dartGraph c.wf.1).Rotational :=
  PseudoTriangulation.rotationLawsCertify_rotational c.wf.1 c.rot_certified

end NearLinear4ct
