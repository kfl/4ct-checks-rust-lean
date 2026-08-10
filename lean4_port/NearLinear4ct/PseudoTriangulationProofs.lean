import NearLinear4ct.Configuration
import NearLinear4ct.MappingProofs
import NearLinear4ct.UtilProofs
import Std.Tactic.Do

/-!
Well-formedness of the combinatorial map, in two layers.

`Dart.InBounds` / `PseudoTriangulation.WF` / `PseudoConfiguration.WF` state
**index bounds only**: every `head` names a vertex, every `rev`/`succ`/`pred`
names a dart. Above them, `PseudoTriangulation.Valid` adds the geometric laws
the A.4 degree-resolution steps rely on and preserve: `rev` is an involution,
no edge is a graph loop, and boundary corners agree across an edge. Stronger
rotation-system laws (`succ`/`pred` inverse to each other, rotation closure)
remain unstated -- they must first be falsified empirically on the corpus,
since intermediates of the gluing (A.3) may violate them.

The predicates, their executable checkers (`inBoundsCheck`/`wfCheck`) and
decidability bridges (`_iff`) live beside the structure definitions
(`PseudoTriangulation.lean`/`PseudoConfiguration.lean`), where
`WFConfig.attach!` certifies loaded objects; this file holds the proofs.

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

/-! ### `!`-read lemmas for `Array.push`/`Array.set!`

The `?`-read lemmas are `@[grind =]`, but grinding a deep `push`/`set!` chain of
`!`-reads blows up on the intermediate `let`s. These reduce one write at a time,
so array-edit proofs (`addBoundaryDarts`, gluing, …) reason locally. -/

@[simp] theorem getElem!_push_lt {α : Type _} [Inhabited α] {a : Array α} {x : α} {f : Nat}
    (hf : f < a.size) : (a.push x)[f]! = a[f]! := by grind

theorem getElem!_push_size {α : Type _} [Inhabited α] {a : Array α} {x : α} :
    (a.push x)[a.size]! = x := by grind

theorem getElem!_set!_self {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (hi : i < a.size) : (a.set! i x)[i]! = x := by grind [Array.set!]

theorem getElem!_set!_ne {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α} {f : Nat}
    (hne : i ≠ f) : (a.set! i x)[f]! = a[f]! := by grind [Array.set!]

/-- A `pred`-write leaves `succ` untouched at every index (including its own). -/
theorem getElem!_set!_pred_succ {a : Array Dart} {i f : Nat} {p : OptIdx} :
    ((a.set! i {a[i]! with pred := p})[f]!).succ = (a[f]!).succ := by grind [Array.set!]

/-- A `succ`-write leaves `pred` untouched at every index (including its own). -/
theorem getElem!_set!_succ_pred {a : Array Dart} {i f : Nat} {s : OptIdx} :
    ((a.set! i {a[i]! with succ := s})[f]!).pred = (a[f]!).pred := by grind [Array.set!]

/-- A field-write leaves `head`/`rev` untouched at every index. -/
theorem getElem!_set!_pred_head {a : Array Dart} {i f : Nat} {p : OptIdx} :
    ((a.set! i {a[i]! with pred := p})[f]!).head = (a[f]!).head := by grind [Array.set!]
theorem getElem!_set!_pred_rev {a : Array Dart} {i f : Nat} {p : OptIdx} :
    ((a.set! i {a[i]! with pred := p})[f]!).rev = (a[f]!).rev := by grind [Array.set!]
theorem getElem!_set!_succ_head {a : Array Dart} {i f : Nat} {s : OptIdx} :
    ((a.set! i {a[i]! with succ := s})[f]!).head = (a[f]!).head := by grind [Array.set!]
theorem getElem!_set!_succ_rev {a : Array Dart} {i f : Nat} {s : OptIdx} :
    ((a.set! i {a[i]! with succ := s})[f]!).rev = (a[f]!).rev := by grind [Array.set!]

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

/-- **Append a reverse-dart pair.** The enlarged array `arr` agrees with
`pt.darts` on old indices and adds, at `D`/`D+1`, two darts that are each other's
reverse, have distinct heads, and are boundary-consistent as a pair (`pred` nil
at one iff `succ` nil at the other). Old darts' clauses come straight from `h`;
the pair's from the hypotheses. The array is given abstractly, so the caller's
`push`s need not be unfolded here. -/
theorem Valid.pushRevPair {pt : PseudoTriangulation} (h : pt.Valid) {arr : Array Dart}
    (hwf : (⟨pt.n, arr⟩ : PseudoTriangulation).WF)
    (hsize : arr.size = pt.darts.size + 2)
    (hold : ∀ (j : Nat), j < pt.darts.size → arr[j]! = pt.darts[j]!)
    (hdur : (arr[pt.darts.size]!).rev = pt.darts.size + 1)
    (hdwr : (arr[pt.darts.size + 1]!).rev = pt.darts.size)
    (hhead : (arr[pt.darts.size]!).head ≠ (arr[pt.darts.size + 1]!).head)
    (hb1 : (arr[pt.darts.size]!).pred.isNone ↔ (arr[pt.darts.size + 1]!).succ.isNone)
    (hb2 : (arr[pt.darts.size + 1]!).pred.isNone ↔ (arr[pt.darts.size]!).succ.isNone) :
    (⟨pt.n, arr⟩ : PseudoTriangulation).Valid := by
  refine ⟨hwf, ?_, ?_, ?_⟩ <;> intro e he <;> have he' : e < arr.size := he
  all_goals have htri : e < pt.darts.size ∨ e = pt.darts.size ∨ e = pt.darts.size + 1 := by omega
  all_goals grind [Valid, Valid.rev_lt]

/-- **Close a boundary fan.** The four paired writes -- `pred` at `eF`/`eLR`,
`succ` at `eL`/`eFR`, all to non-nil targets, where `eFR`/`eLR` are the reverses
of `eF`/`eL` -- take a `Valid` graph to a `Valid` graph. `rev`/`head` are
untouched, so `rev_rev`/`loop_free` transport directly. For `boundary`, only
`rev_rev` is needed: an edge whose `pred` corner was written pairs (via
`rev_rev`) with a `succ` corner that was also written, so both sides are non-nil
together; every other edge keeps its `h.boundary`. The array is given
abstractly, so no write order or distinctness reasoning leaks in. -/
theorem Valid.closeBoundaryFan {pt : PseudoTriangulation} (h : pt.Valid)
    {arr : Array Dart} {eF eL eFR eLR : Nat}
    (hwf : (⟨pt.n, arr⟩ : PseudoTriangulation).WF)
    (hsize : arr.size = pt.darts.size)
    (hrev : ∀ (j : Nat), (arr[j]!).rev = (pt.darts[j]!).rev)
    (hhead : ∀ (j : Nat), (arr[j]!).head = (pt.darts[j]!).head)
    (heF : eF < pt.darts.size) (heL : eL < pt.darts.size)
    (hFR : (pt.darts[eF]!).rev = eFR) (hLR : (pt.darts[eL]!).rev = eLR)
    (hpred : ∀ (j : Nat), j ≠ eF → j ≠ eLR → (arr[j]!).pred = (pt.darts[j]!).pred)
    (hsucc : ∀ (j : Nat), j ≠ eL → j ≠ eFR → (arr[j]!).succ = (pt.darts[j]!).succ)
    (hwpF : ¬ (arr[eF]!).pred.isNone) (hwpLR : ¬ (arr[eLR]!).pred.isNone)
    (hwsL : ¬ (arr[eL]!).succ.isNone) (hwsFR : ¬ (arr[eFR]!).succ.isNone) :
    (⟨pt.n, arr⟩ : PseudoTriangulation).Valid := by
  refine ⟨hwf, ?_, ?_, ?_⟩ <;> intro e he <;> have he' : e < arr.size := he
  all_goals have hrr := h.rev_rev e (by omega)
  all_goals grind [Valid, Valid.rev_lt]

/-- **What `addBoundaryDarts` changed** (A.4.6): the implementation-level patch,
read off the `push`/`set!` chain once by `addBoundaryDarts_patch`. `dst` appends
the reverse pair for the new boundary edge at `src.darts.size`/`+ 1` and closes
the four fan corners `eF`/`eL`/`eFR`/`eLR`; every other field is untouched. The
closed corners are recorded as non-nil rather than by target, so the fields hold
even when corners coincide and no distinctness reasoning is needed. Validity and
coherence are semantic consequences (`BoundaryFanPatch.valid`,
`BoundaryFanPatch.toExtends`). -/
structure BoundaryFanPatch (src dst : PseudoTriangulation) (eF eL eFR eLR : Nat) : Prop where
  wf : dst.WF
  n_eq : dst.n = src.n
  size : dst.darts.size = src.darts.size + 2
  eF_lt : eF < src.darts.size
  eL_lt : eL < src.darts.size
  eFR_def : (src.darts[eF]!).rev = eFR
  eLR_def : (src.darts[eL]!).rev = eLR
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
  predF_closed : ¬ (dst.darts[eF]!).pred.isNone
  predLR_closed : ¬ (dst.darts[eLR]!).pred.isNone
  succL_closed : ¬ (dst.darts[eL]!).succ.isNone
  succFR_closed : ¬ (dst.darts[eFR]!).succ.isNone

/-- A boundary-fan patch preserves validity. The patch is applied as its two
atomic steps: `Valid.pushRevPair` takes `src` to the intermediate pair-appended
graph (reconstructed from the `dst` reads), and `Valid.closeBoundaryFan` closes
the four paired corners on top of it. -/
theorem BoundaryFanPatch.valid {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid) : dst.Valid := by
  obtain ⟨hwf, hn, hsz, heF, heL, hFRd, hLRd, hhne, _hpO, _hsO, hr1, hr2, hho, hro,
    hpo, hso, hpFc, hpLRc, hsLc, hsFRc⟩ := hp
  have hd1 : (dst.darts[src.darts.size]!).InBounds src.n (src.darts.size + 2) :=
    hsz ▸ hn ▸ hwf.read_inBounds (by omega)
  have hd2 : (dst.darts[src.darts.size + 1]!).InBounds src.n (src.darts.size + 2) :=
    hsz ▸ hn ▸ hwf.read_inBounds (by omega)
  -- The intermediate graph: the source plus the appended reverse pair.
  have hread : ∀ (j : Nat),
      ((src.darts.push dst.darts[src.darts.size]!).push dst.darts[src.darts.size + 1]!)[j]!
        = if j < src.darts.size then src.darts[j]! else dst.darts[j]! := by
    intro j
    rcases Nat.lt_trichotomy j src.darts.size with hj | hj | hj
    · rw [if_pos hj, getElem!_push_lt (by simp; omega), getElem!_push_lt hj]
    · subst hj
      rw [if_neg (by omega), getElem!_push_lt (by simp), getElem!_push_size]
    · by_cases hj1 : j = src.darts.size + 1
      · subst hj1
        rw [if_neg (by omega),
          show src.darts.size + 1 = (src.darts.push dst.darts[src.darts.size]!).size by simp,
          getElem!_push_size]
      · rw [if_neg (by omega), getElem!_neg _ _ (by simp; omega),
          getElem!_neg _ _ (by omega)]
  have hmv : (⟨src.n, (src.darts.push dst.darts[src.darts.size]!).push
      dst.darts[src.darts.size + 1]!⟩ : PseudoTriangulation).Valid := by
    refine hv.pushRevPair ?_ (by simp) (fun j hj => by rw [hread j, if_pos hj]) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact (push_dart_wf (push_dart_wf
          (fun j hj => (hv.wf j hj).mono (Nat.le_refl _) (by omega)) hd1) hd2 i hi).mono
        (Nat.le_refl _) (by simp)
    · rw [hread _, if_neg (by omega), hr1]
    · rw [hread _, if_neg (by omega), hr2]
    · rw [hread (src.darts.size), hread (src.darts.size + 1), if_neg (by omega),
        if_neg (by omega), hr1, hr2]
      exact hhne
    · rw [hread (src.darts.size), hread (src.darts.size + 1), if_neg (by omega),
        if_neg (by omega), hr1, hr2]
      simp
    · rw [hread (src.darts.size), hread (src.darts.size + 1), if_neg (by omega),
        if_neg (by omega), hr1, hr2]
  have hfinal : (⟨src.n, dst.darts⟩ : PseudoTriangulation).Valid :=
    hmv.closeBoundaryFan (fun i hi => hn ▸ hwf i hi) (by simp [hsz])
      (fun j => by rw [hread j]; split <;> first | rfl | exact hro j ‹_›)
      (fun j => by rw [hread j]; split <;> first | rfl | exact hho j ‹_›)
      (by simp; omega) (by simp; omega)
      (by rw [hread eF, if_pos heF]; exact hFRd)
      (by rw [hread eL, if_pos heL]; exact hLRd)
      (fun j hjF hjLR => by rw [hread j]; split <;> first | rfl | exact hpo j hjF hjLR ‹_›)
      (fun j hjL hjFR => by rw [hread j]; split <;> first | rfl | exact hso j hjL hjFR ‹_›)
      hpFc hpLRc hsLc hsFRc
  have hEq : (⟨src.n, dst.darts⟩ : PseudoTriangulation) = dst := by rw [← hn]
  exact hEq ▸ hfinal

/-- A boundary-fan patch keeps the identity coherent: interior links are never
disturbed. On a valid source the two closed fan corners were open
(`Valid.boundary` at `eF`/`eL`), so no interior `succ`/`pred` maps onto them.
(`extends` is a keyword, hence `toExtends`.) -/
theorem BoundaryFanPatch.toExtends {src dst : PseudoTriangulation} {eF eL eFR eLR : Nat}
    (hp : BoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid) :
    Mappings.Extends src dst src.n src.darts.size := by
  obtain ⟨_hwf, _hn, _hsz, heF, heL, hFRd, hLRd, _hhne, hpO, hsO, _hr1, _hr2, hho, hro,
    hpo, hso, _hpFc, _hpLRc, _hsLc, _hsFRc⟩ := hp
  have hsuccFR : (src.darts[eFR]!).succ.isNone := hFRd ▸ (hv.boundary _ heF).mp hpO
  have hpredLR : (src.darts[eLR]!).pred.isNone := hLRd ▸ (hv.boundary' heL).mp hsO
  refine ⟨fun f hf => ⟨(hv.wf.read_inBounds hf).head_lt, hho f hf⟩,
      fun f hf => ⟨(hv.wf.read_inBounds hf).rev_lt, hro f hf⟩,
      fun f s hf hs => ⟨(hv.wf.read_inBounds hf).succ_lt s hs, ?_⟩,
      fun f p hf hpr => ⟨(hv.wf.read_inBounds hf).pred_lt p hpr, ?_⟩⟩
  · rw [hso f (by grind [OptIdx.isNone_iff_get?]) (by grind [OptIdx.isNone_iff_get?]) hf]
    exact hs
  · rw [hpo f (by grind [OptIdx.isNone_iff_get?]) (by grind [OptIdx.isNone_iff_get?]) hf]
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
through `PendingEq`. The seed field records that all requested pairs remain
connected even after their queue entries are popped. -/
private structure GlueCoherent (pt : PseudoTriangulation) (dartPairs : Array (Nat × Nat))
    (darts : Array Dart) (ufV ufD : Unionfind) (q : Queue (Nat × Nat)) : Prop where
  head_eq : ∀ i, i < pt.darts.size → (darts[i]!).head = (pt.darts[i]!).head
  head : ∀ i, i < pt.darts.size →
    ufV.root (pt.darts[i]!).head = ufV.root (darts[ufD.root i]!).head
  rev : ∀ i, i < pt.darts.size →
    PendingEq ufD q (pt.darts[i]!).rev (darts[ufD.root i]!).rev
  link : ∀ (k : LinkKind) i, i < pt.darts.size → ∀ s,
    (k.get (pt.darts[i]!)).get? = Option.some s →
    ∃ t, (k.get (darts[ufD.root i]!)).get? = Option.some t ∧ PendingEq ufD q s t
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
    fun k i hi s hs => (h.link k i hi s hs).imp fun t ht =>
      ⟨ht.1, ht.2.pop_same hpop hef⟩,
    fun p hp => (h.seeds p hp).pop_same hpop hef⟩

/-- The packed-state form of the loop's mutable tuple `⟨darts, q, ufD, ufV⟩`. -/
private abbrev GlueState :=
  MProd (Array Dart) (MProd (Queue (Nat × Nat)) (MProd Unionfind Unionfind))

/-- The structural and semantic loop invariants over the same packed state. -/
private def GlueSpecSum (pt : PseudoTriangulation)
    (dartPairs : Array (Nat × Nat)) : GlueState ⊕ GlueState → Prop
  | .inl ⟨darts, ⟨q, ⟨ufD, ufV⟩⟩⟩ =>
      GlueInv pt darts ufV ufD q ∧ GlueCoherent pt dartPairs darts ufV ufD q
  | .inr ⟨darts, ⟨q, ⟨ufD, ufV⟩⟩⟩ =>
      GlueInv pt darts ufV ufD q ∧ GlueCoherent pt dartPairs darts ufV ufD q ∧
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

private theorem PendingEq.glue {uf : Unionfind} {q : Queue (Nat × Nat)}
    {a b eStar fStar : Nat} {darts : Array Dart} {k : LinkKind}
    (h : PendingEq uf q a b) : PendingEq uf (k.glue darts q eStar fStar).2 a b := by
  unfold LinkKind.glue
  split
  · exact h.push
  · exact h
  · exact h

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
      rw [getElem!_set!_self hfd, LinkKind.get_set, heu, OptIdx.get?_some]
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
        rw [getElem!_set!_ne (Ne.symm hrf)]
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
    obtain ⟨u, hlink, hsu⟩ := hcoh.link k i hi s hs
    have hsu' := afterCore hsu
    obtain ⟨t, ht, hst⟩ := glueBoth_link hcore hre hrf k hlink hsu'
    refine ⟨t, ?_, ?_⟩
    · rw [rootAfter i hi]
      simpa only [succState, predState, LinkKind.glue_succ,
        LinkKind.glue_pred] using ht
    · simpa only [succState, predState, LinkKind.glue_succ,
        LinkKind.glue_pred] using hst
  · intro p hp
    exact afterAll (hcoh.seeds p hp)

/-- The executable dart emitted for one surviving representative. -/
private def renumberDart (vMap dMap : IndexMap) (d : Dart) : Dart :=
  { head := (vMap[d.head]!).idx!
  , rev := (dMap[d.rev]!).idx!
  , succ := match d.succ with | .some s => dMap[s]! | .none => .none
  , pred := match d.pred with | .some p => dMap[p]! | .none => .none }

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

private theorem getElem!_of_toList_eq_append_cons {xs : Array α}
    [Inhabited α] {pref : List α} {x : α} {suff : List α}
    (h : xs.toList = pref ++ x :: suff) : xs[pref.length]! = x := by
  rw [← Array.getElem!_toList, h]
  simp

/-- Invariant of the renumber loop: the output tracks the processed prefix of
`allRoots`, every emitted dart is in bounds, and slot `i` is exactly the
renumbered representative stored at `allRoots[i]`. -/
private structure RenumberInv (darts : Array Dart) (ufV ufD : Unionfind) (k : Nat)
    (dartsStar : Array Dart) : Prop where
  size_eq : dartsStar.size = k
  dart_wf : ∀ i (h : i < dartsStar.size),
    (dartsStar[i]'h).InBounds ufV.numRoots ufD.numRoots
  value_eq : ∀ i (h : i < dartsStar.size),
    dartsStar[i]'h = renumberDart
      (composeMap (ufV.eachRoot.map OptIdx.some) ufV.indexRoots)
      (composeMap (ufD.eachRoot.map OptIdx.some) ufD.indexRoots)
      (darts[ufD.allRoots[i]!]!)

/-- Pushing an in-bounds dart preserves the renumber loop invariant. -/
private theorem RenumberInv.push {darts : Array Dart} {ufV ufD : Unionfind} {k : Nat}
    {dartsStar : Array Dart} (h : RenumberInv darts ufV ufD k dartsStar)
    {d : Dart} (hd : d.InBounds ufV.numRoots ufD.numRoots)
    (hval : d = renumberDart
      (composeMap (ufV.eachRoot.map OptIdx.some) ufV.indexRoots)
      (composeMap (ufD.eachRoot.map OptIdx.some) ufD.indexRoots)
      (darts[ufD.allRoots[k]!]!)) :
    RenumberInv darts ufV ufD (k + 1) (dartsStar.push d) := by
  grind [RenumberInv]

/-- At an empty worklist, the semantic gluing invariant and the exact
renumbering invariant are precisely A.3's quotient-map coherence. -/
private theorem GlueCoherent.finish {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)} {darts dartsStar : Array Dart}
    {ufV ufD : Unionfind} {q : Queue (Nat × Nat)}
    (hinv : GlueInv pt darts ufV ufD q)
    (hcoh : GlueCoherent pt dartPairs darts ufV ufD q)
    (hri : RenumberInv darts ufV ufD ufD.allRoots.size dartsStar)
    (hq : q.isEmpty = true) :
    let vMap := composeMap (ufV.eachRoot.map OptIdx.some) ufV.indexRoots
    let dMap := composeMap (ufD.eachRoot.map OptIdx.some) ufD.indexRoots
    Mappings.Coherent ⟨vMap, dMap⟩ pt ⟨ufV.numRoots, dartsStar⟩ ∧
      ∀ p ∈ dartPairs, dMap.idx? p.1 = dMap.idx? p.2 := by
  intro vMap dMap
  constructor
  · intro f fStar hf
    obtain ⟨hfMap, -⟩ := IndexMap.idx?_eq_some_iff.mp hf
    have hfi : f < ufD.n := by
      simpa only [size_composeMap, Array.size_map, Unionfind.size_eachRoot] using
        show f < (composeMap (ufD.eachRoot.map OptIdx.some) ufD.indexRoots).size from hfMap
    have hfpt : f < pt.darts.size := by simpa only [hinv.ufD_n] using hfi
    have hsrc := hpt.read_inBounds hfpt
    have hr := hinv.root_lt hfpt
    have hrep := hinv.read_inBounds hr
    have hfRelabel := ufD.relabel_idx? hinv.ufD_wf hfi
    have hfStar : fStar = ufD.rootRank (ufD.root f) :=
      Option.some.inj (hf.symm.trans hfRelabel)
    have hfStarLt : fStar < dartsStar.size := by
      have hDwf := (Unionfind.relabel_wf ufD hinv.ufD_wf).1
      have := IndexMap.idx?_lt_of_bounded hDwf.bounded hf
      simpa only [Unionfind.numRoots, ← hri.size_eq] using this
    have hroot := hinv.ufD_wf.root_spec hfi
    have hall := Unionfind.getElem!_allRoots_rootRank hroot.2 (by simp [hroot.1])
    have hout : dartsStar[fStar]! = renumberDart vMap dMap (darts[ufD.root f]!) := by
      rw [getElem!_pos dartsStar fStar hfStarLt]
      simpa only [hfStar, hall] using hri.value_eq fStar hfStarLt
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
      obtain ⟨t, ht, hst⟩ := hcoh.link k f hfpt s hs
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

section
-- The transparency linter flags `mvcgen`'s own `Invariant` encoding (the `⇓`
-- postconditions), not this proof's text; nothing here to rephrase.
set_option linter.tacticCheckInstances false

/-- Combined A.3 contract: bounds, total quotient maps, structural coherence,
and identification of every seed pair. Kept private so the public tiered
theorems below expose only the facts their callers request. -/
private theorem freeHomomorphism_spec {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    ptStar.WF
    ∧ maps.WF pt.n pt.darts.size ptStar.n ptStar.darts.size
    ∧ maps.vmap.Total ∧ maps.dmap.Total
    ∧ maps.Coherent pt ptStar
    ∧ ∀ p ∈ dartPairs, maps.dmap.idx? p.1 = maps.dmap.idx? p.2 := by
  apply Id.of_wp_run_eq hrun fun (ptOut, mapsOut) =>
    ptOut.WF ∧ mapsOut.WF pt.n pt.darts.size ptOut.n ptOut.darts.size
    ∧ mapsOut.vmap.Total ∧ mapsOut.dmap.Total
    ∧ mapsOut.Coherent pt ptOut
    ∧ ∀ p ∈ dartPairs, mapsOut.dmap.idx? p.1 = mapsOut.dmap.idx? p.2
  mvcgen
  case inv1 => exact fun s => ⟨glueMeasure s⟩
  case inv2 => exact ⇓s => ⌜GlueSpecSum pt dartPairs s⌝
  case inv3 =>
    rename_i r _ _ _ _
    exact ⇓⟨xs, dartsStar⟩ =>
      ⌜RenumberInv r.1 r.2.2.snd r.2.2.fst xs.prefix.length dartsStar⌝
  all_goals mleave
  -- Continue branch: the popped pair is already merged; only the queue shrinks.
  case vc1.step.h_1.isTrue =>
    obtain ⟨hm, hspec⟩ := ‹_ ∧ _›
    obtain ⟨hinv, hcoh⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ := hspec
    exact ⟨_, rfl, by grind [glueMeasure, Queue.live_pop],
      GlueInv.pop ‹_› hinv, GlueCoherent.pop_same ‹_› ‹_› hcoh⟩
  -- Glue branches (with and without the vertex unite): the shared core covers
  -- pop + dart-unite + reverse push, then the two adjacency steps compose.
  case vc2.step.h_1.isFalse.isTrue =>
    obtain ⟨hm, hspec⟩ := ‹_ ∧ _›
    obtain ⟨hinv, hcoh⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ := hspec
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
    exact ⟨_, rfl, by grind [glueMeasure, Queue.live_pop, Queue.live_push], h4, hcoh4⟩
  case vc3.step.h_1.isFalse.isFalse =>
    obtain ⟨hm, hspec⟩ := ‹_ ∧ _›
    obtain ⟨hinv, hcoh⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ := hspec
    obtain ⟨h1, _, ⟨hre, hrf⟩, hdec⟩ :=
      GlueInv.glue ‹_› ‹_› hinv
    obtain ⟨h4, hq⟩ := glueBoth_spec h1 hre hrf
    have hcoh4 := GlueCoherent.glue_step hpt ‹_› ‹_› hinv hcoh
      hinv.ufV_n hinv.ufV_wf (fun _ _ hab => hab) (by grind [Unionfind.same])
    exact ⟨_, rfl, by grind [glueMeasure, Queue.live_pop, Queue.live_push], h4, hcoh4⟩
  -- Exhausted queue: the break-side invariant is the continue-side one.
  case vc4.step.h_2 =>
    have hspec : GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ := ‹_ ∧ _›.2
    exact ⟨hspec.1, hspec.2,
      Queue.pop?_none (Queue.pop?_eq_none_of_no_pair ‹_› ‹_›)⟩
  -- Seed state: fresh forests, the input graph, the seeded queue.
  case vc5.pre =>
    exact ⟨GlueInv.mk rfl rfl rfl (Unionfind.wf_new _) (Unionfind.wf_new _) hpt
        (fun p hp => hpairs p (Queue.active_ofArray hp)),
      GlueCoherent.init hpt hpairs⟩
  -- Renumber loop: one push per root, so the size tracks the processed
  -- prefix; the pushed dart is in bounds for the quotient.
  case vc6.step =>
    rename_i _ _ _ _ r _ _ _ _ pref cur suff hcursor b _ hd rv succ pred _ _
    have hri : RenumberInv _ _ _ _ _ := ‹_›
    obtain ⟨hinv', -, -⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ ∧ _ := ‹_›
    have hcur := getElem!_of_toList_eq_append_cons
      (xs := r.2.2.fst.allRoots) hcursor
    have hpush := hri.push
      (d := { head := hd, rev := rv, succ := succ, pred := pred })
      (renumber_push_inBounds hinv'
        (hinv'.ufD_n ▸ Unionfind.mem_allRoots_lt
          (Array.mem_toList_iff.mp (by grind))))
      (by unfold renumberDart; rw [hcur]; rfl)
    exact ⟨by grind [RenumberInv], hpush.dart_wf, hpush.value_eq⟩
  case vc7.post.success.pre => exact ⟨rfl, by grind, by grind⟩
  -- Exit: the maps are the union-find relabellings, total and well-formed by
  -- `relabel_wf`; the invariant pins the domain sizes and carries the quotient
  -- graph's bounds, the renumber size invariant pins the dart codomain.
  case vc8.post.success.post.success =>
    obtain ⟨hinv', hcoh, hqempty⟩ :
        GlueInv pt _ _ _ _ ∧ GlueCoherent pt dartPairs _ _ _ _ ∧ _ := ‹_›
    obtain ⟨hVwf, hVtot⟩ := Unionfind.relabel_wf _ hinv'.ufV_wf
    obtain ⟨hDwf, hDtot⟩ := Unionfind.relabel_wf _ hinv'.ufD_wf
    have hri : RenumberInv _ _ _ _ _ := ‹_›
    obtain ⟨hcoherent, hseeds⟩ :=
      GlueCoherent.finish hpt hinv' hcoh
        (by simpa only [Array.length_toList] using hri) hqempty
    exact ⟨fun i hi => by grind [RenumberInv, Unionfind.numRoots, Array.length_toList],
      ⟨by grind [GlueInv],
       by grind [RenumberInv, GlueInv, Unionfind.numRoots, Array.length_toList]⟩,
      hVtot, hDtot, hcoherent, hseeds⟩
end

/-- **`freeHomomorphism` produces a well-formed quotient**: the graph is `WF`
and the maps are total, well-formed relabellings onto its index ranges. -/
theorem freeHomomorphism_wf {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    ptStar.WF
    ∧ maps.WF pt.n pt.darts.size ptStar.n ptStar.darts.size
    ∧ maps.vmap.Total ∧ maps.dmap.Total := by
  obtain ⟨hptStar, hmaps, hvmap, hdmap, -, -⟩ :=
    freeHomomorphism_spec hpt hpairs hrun
  exact ⟨hptStar, hmaps, hvmap, hdmap⟩

/-- **A.3 coherence tier.** The quotient maps commute with every dart field,
and each requested input pair has a common quotient image. -/
theorem freeHomomorphism_coherent {pt : PseudoTriangulation} (hpt : pt.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pt.darts.size ∧ p.2 < pt.darts.size)
    {ptStar : PseudoTriangulation} {maps : Mappings}
    (hrun : pt.freeHomomorphism dartPairs = (ptStar, maps)) :
    maps.Coherent pt ptStar ∧
      ∀ p ∈ dartPairs, maps.dmap.idx? p.1 = maps.dmap.idx? p.2 := by
  obtain ⟨-, -, -, -, hcoherent, hseeds⟩ :=
    freeHomomorphism_spec hpt hpairs hrun
  exact ⟨hcoherent, hseeds⟩

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
  obtain ⟨-, hmaps, -, -, hcoh, hseeds⟩ :=
    freeHomomorphism_spec (disjointUnion_wf hpt0 hpt1)
      (freeHomomorphismPair_seed_bounds hdart0 hdart1) hrun
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
open Std.Do
set_option mvcgen.warning false
set_option linter.tacticCheckInstances false

/-- On a `WF` graph, a successful `succ` walk ends at a dart. -/
theorem sucKTimes_lt {pt : PseudoTriangulation} (hpt : pt.WF) {e k : Nat}
    (he : e < pt.darts.size) {c : Nat}
    (h : pt.sucKTimes e k = some c) : c < pt.darts.size := by
  apply Id.of_wp_run_eq h fun
    | none => True
    | some x => x < pt.darts.size
  mvcgen
  case inv1 =>
    exact ⇓⟨_xs, st⟩ =>
      ⌜st.snd < pt.darts.size ∧ ∀ o, st.fst = some o → o = none⌝
  all_goals mleave
  all_goals try grind
  all_goals exact ⟨LinkKind.succ.some_lt (hpt.read_inBounds (‹_ ∧ _›).1) ‹_›,
    by grind⟩

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

/-- A picked optional dart index reads (`get!`) in range: `some` answers are
bounded by hypothesis, `none`'s default `0` needs a nonempty range. -/
private theorem get!_lt_of_some_lt {o : Option Nat} {D : Nat}
    (hsome : ∀ e, o = some e → e < D) (hD : 0 < D) : o.get! < D := by
  cases o with
  | some e => exact hsome e rfl
  | none => simpa using hD

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

/-- The mapping and graph `dartIdentification` returns are exactly
`freeHomomorphism`'s: the degree reconciliation writes only `degreesStar`, so it
touches neither the quotient graph nor the maps. -/
theorem dartIdentification_graph_maps {pc : PseudoConfiguration}
    {dartPairs : Array (Nat × Nat)} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    pc'.toPseudoTriangulation = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1
      ∧ m = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).2 := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some (z, mp) =>
        z.toPseudoTriangulation = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).1
          ∧ mp = (pc.toPseudoTriangulation.freeHomomorphism dartPairs).2
  mvcgen
  case inv1 => exact ⇓⟨_xs, st⟩ => ⌜∀ o, st.fst = some o → o = none⌝
  all_goals mleave
  all_goals grind [PseudoConfiguration.new]

/-- **Certified coherence for `dartIdentification` (A.4.1/A.4.3).** The quotient
map is a well-formed, structurally-coherent mapping from the input graph into the
identified one -- the gluing branch's carrier. -/
theorem dartIdentification_coherentMappings {pc : PseudoConfiguration} (hpc : pc.WF)
    {dartPairs : Array (Nat × Nat)}
    (hpairs : ∀ p ∈ dartPairs, p.1 < pc.darts.size ∧ p.2 < pc.darts.size)
    {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.dartIdentification dartPairs = some (pc', m)) :
    ∃ C : CoherentMappings pc.toPseudoTriangulation pc'.toPseudoTriangulation, C.maps = m := by
  obtain ⟨hgraph, hmap⟩ := dartIdentification_graph_maps hrun
  refine ⟨⟨m, ?_, ?_⟩, rfl⟩
  · rw [hmap, hgraph]; exact (PseudoTriangulation.freeHomomorphism_wf hpc.1 hpairs rfl).2.1
  · rw [hmap, hgraph]; exact (PseudoTriangulation.freeHomomorphism_coherent hpc.1 hpairs rfl).1
end

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
end

/-- Rewriting one dart's link to an in-range target preserves an array-wide
bound: the written dart inherits its other fields from the overwritten one. -/
private theorem set_link_wf (k : PseudoTriangulation.LinkKind) {n D : Nat}
    {a : Array Dart}
    (h : ∀ i (hi : i < a.size), (a[i]'hi).InBounds n D)
    {p t : Nat} (ht : t < D) :
    ∀ i (hi : i < (a.set! p (k.set (a[p]!) (OptIdx.some t))).size),
      ((a.set! p (k.set (a[p]!) (OptIdx.some t)))[i]'hi).InBounds n D := by
  cases k <;>
    grind [PseudoTriangulation.LinkKind.set, Dart.InBounds,
      OptIdx.get?_some, OptIdx.get?_none]

/-- The whole boundary-fan chain keeps every index in bounds: the appended pair
points at existing vertices and at each other, and the four link rewrites target
existing darts. The one bounds proof over the `push`/`set!` chain, shared by
`addBoundaryDarts_wf` and `addBoundaryDarts_patch`. The chain is given as
per-step equations (discharged by `rfl` at the use sites), which keeps every
definitional comparison one write deep. -/
private theorem boundaryFan_chain_wf {n : Nat} {a a1 a2 a3 a4 a5 a6 : Array Dart}
    {eF eL eFR eLR u w : Nat}
    (h : ∀ i (hi : i < a.size), (a[i]'hi).InBounds n a.size)
    (hu : u < n) (hw : w < n) (heF : eF < a.size) (heL : eL < a.size)
    (heFR : eFR < a.size) (heLR : eLR < a.size)
    (e1 : a1 = a.push ⟨u, a.size + 1, OptIdx.none, OptIdx.some eFR⟩)
    (e2 : a2 = a1.push ⟨w, a.size, OptIdx.some eLR, OptIdx.none⟩)
    (e3 : a3 = a2.set! eF { a2[eF]! with pred := OptIdx.some eL })
    (e4 : a4 = a3.set! eL { a3[eL]! with succ := OptIdx.some eF })
    (e5 : a5 = a4.set! eFR { a4[eFR]! with succ := OptIdx.some a.size })
    (e6 : a6 = a5.set! eLR { a5[eLR]! with pred := OptIdx.some (a.size + 1) }) :
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
    rw [e3]; exact set_link_wf .pred h2 (p := eF) (t := eL) hteL
  have h4 : ∀ i (hi : i < a4.size), (a4[i]'hi).InBounds n a6.size := by
    rw [e4]; exact set_link_wf .succ h3 (p := eL) (t := eF) hteF
  have h5 : ∀ i (hi : i < a5.size), (a5[i]'hi).InBounds n a6.size := by
    rw [e5]; exact set_link_wf .succ h4 (p := eFR) (t := a.size) hd0
  rw [e6]
  intro i hi
  exact (set_link_wf .pred h5 (p := eLR) (t := a.size + 1) hd1 i hi).mono
    (Nat.le_refl _) (Nat.le_of_eq (congrArg Array.size e6))

section
set_option linter.tacticCheckInstances false
/-- `addBoundaryDarts` (A.4.6) preserves well-formedness: the two boundary
darts point at existing vertices and each other, and the four link rewrites
stay inside the grown array. -/
theorem addBoundaryDarts_wf {pc : PseudoConfiguration} (hpc : pc.WF) {v : Nat}
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.WF := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some x => x.WF
  mvcgen -trivial
  all_goals mleave
  case vc2.isFalse =>
    rename_i eF eL eFR eLR u w _jp hne dUW dWU a0 a1 a2 a3 a4 a5 a6
    -- Here `u ≠ w`, so the graph is nonempty and every read lands.
    have hsz : pc.darts.size ≠ 0 := by
      intro hzero
      have hdd : (default : Dart) = ⟨0, 0, OptIdx.none, OptIdx.none⟩ := rfl
      grind
    have hfirst : eF < pc.darts.size :=
      get!_lt_of_some_lt (fun e he => PseudoTriangulation.firstDart_lt he)
        (Nat.pos_of_ne_zero hsz)
    have hlast : eL < pc.darts.size :=
      get!_lt_of_some_lt (fun e he => PseudoTriangulation.lastDart_lt he)
        (Nat.pos_of_ne_zero hsz)
    have hfrev : eFR < pc.darts.size := (hpc.1.read_inBounds hfirst).rev_lt
    have hlrev : eLR < pc.darts.size := (hpc.1.read_inBounds hlast).rev_lt
    have hu : u < pc.n := (hpc.1.read_inBounds hfrev).head_lt
    have hw : w < pc.n := (hpc.1.read_inBounds hlrev).head_lt
    have e1 : a1 = a0.push ⟨u, a0.size + 1, OptIdx.none, OptIdx.some eFR⟩ := rfl
    have e2 : a2 = a1.push ⟨w, a0.size, OptIdx.some eLR, OptIdx.none⟩ := rfl
    have e3 : a3 = a2.set! eF { a2[eF]! with pred := OptIdx.some eL } := rfl
    have e4 : a4 = a3.set! eL { a3[eL]! with succ := OptIdx.some eF } := rfl
    have e5 : a5 = a4.set! eFR { a4[eFR]! with succ := OptIdx.some a0.size } := rfl
    have e6 : a6 = a5.set! eLR { a5[eLR]! with pred := OptIdx.some (a0.size + 1) } := rfl
    clear_value a1 a2 a3 a4 a5 a6
    have h6 : ∀ i (hi : i < a6.size), (a6[i]'hi).InBounds pc.n a6.size :=
      boundaryFan_chain_wf hpc.1 hu hw hfirst hlast hfrev hlrev e1 e2 e3 e4 e5 e6
    exact ⟨h6, hpc.2⟩

/-- **The implementation patch of `addBoundaryDarts` (A.4.6):** the one theorem
that follows the `push`/`set!` chain. It reads the chain off into
`BoundaryFanPatch` facts; validity and coherence follow purely
(`BoundaryFanPatch.valid`, `BoundaryFanPatch.toExtends`). -/
theorem addBoundaryDarts_patch {pc : PseudoConfiguration}
    (hwf : pc.toPseudoTriangulation.WF) {v : Nat}
    (hfd : (pc.firstDart v).isSome) (hld : (pc.lastDart v).isSome)
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    ∃ eF eL eFR eLR, PseudoTriangulation.BoundaryFanPatch
      pc.toPseudoTriangulation pc'.toPseudoTriangulation eF eL eFR eLR := by
  apply Id.of_wp_run_eq hrun fun
    | none => True
    | some x => ∃ eF eL eFR eLR, PseudoTriangulation.BoundaryFanPatch
        pc.toPseudoTriangulation x.toPseudoTriangulation eF eL eFR eLR
  mvcgen -trivial
  all_goals mleave
  case vc2.isFalse =>
    have hFsome : pc.firstDart v = some (pc.firstDart v).get! := by
      cases h : pc.firstDart v with | none => exact absurd hfd (by simp [h]) | some e => rfl
    have hLsome : pc.lastDart v = some (pc.lastDart v).get! := by
      cases h : pc.lastDart v with | none => exact absurd hld (by simp [h]) | some e => rfl
    rename_i eF eL eFR eLR u w _jp hne dUW dWU a0 a1 a2 a3 a4 a5 a6
    have hfirst : eF < pc.darts.size := PseudoTriangulation.firstDart_lt hFsome
    have hlast : eL < pc.darts.size := PseudoTriangulation.lastDart_lt hLsome
    have hfrev : eFR < pc.darts.size := (hwf.read_inBounds hfirst).rev_lt
    have hlrev : eLR < pc.darts.size := (hwf.read_inBounds hlast).rev_lt
    have hu : u < pc.n := (hwf.read_inBounds hfrev).head_lt
    have hw : w < pc.n := (hwf.read_inBounds hlrev).head_lt
    have hne' : u ≠ w := fun h => absurd (by simp [h]) hne
    -- Reads through the chain: the old region and the two appended darts.
    have r2 : ∀ {j : Nat}, j < pc.darts.size → a2[j]! = pc.darts[j]! := fun {j} hj => by
      unfold a2 a1 a0
      rw [getElem!_push_lt (by simp [Array.size_push]; omega), getElem!_push_lt hj]
    have hsz2 : a2.size = pc.darts.size + 2 := by unfold a2 a1 a0; simp
    have ha3s : a3.size = a2.size := by unfold a3; simp
    have ha4s : a4.size = a2.size := by unfold a4 a3; simp
    have ha5s : a5.size = a2.size := by unfold a5 a4 a3; simp
    have hsize6 : a6.size = a2.size := by unfold a6 a5 a4 a3; simp
    have hgUW : a2[pc.darts.size]! = (⟨u, dWU, OptIdx.none, OptIdx.some eFR⟩ : Dart) := by
      unfold a2 a1 a0
      rw [getElem!_push_lt (by simp [Array.size_push])]
      exact getElem!_push_size
    have hgWU : a2[pc.darts.size + 1]! = (⟨w, dUW, OptIdx.some eLR, OptIdx.none⟩ : Dart) := by
      unfold a2 a1 a0
      rw [show pc.darts.size + 1
            = (pc.darts.push (⟨u, dWU, OptIdx.none, OptIdx.some eFR⟩ : Dart)).size by
          simp [Array.size_push]]
      exact getElem!_push_size
    have hn1 : a6[pc.darts.size]! = (⟨u, dWU, OptIdx.none, OptIdx.some eFR⟩ : Dart) := by
      unfold a6; rw [getElem!_set!_ne (Nat.ne_of_lt hlrev)]
      unfold a5; rw [getElem!_set!_ne (Nat.ne_of_lt hfrev)]
      unfold a4; rw [getElem!_set!_ne (Nat.ne_of_lt hlast)]
      unfold a3; rw [getElem!_set!_ne (Nat.ne_of_lt hfirst)]
      exact hgUW
    have hn2 : a6[pc.darts.size + 1]! = (⟨w, dUW, OptIdx.some eLR, OptIdx.none⟩ : Dart) := by
      unfold a6; rw [getElem!_set!_ne (Nat.ne_of_lt (by omega))]
      unfold a5; rw [getElem!_set!_ne (Nat.ne_of_lt (by omega))]
      unfold a4; rw [getElem!_set!_ne (Nat.ne_of_lt (by omega))]
      unfold a3; rw [getElem!_set!_ne (Nat.ne_of_lt (by omega))]
      exact hgWU
    -- The final array against `a2`: four link writes, `rev`/`head` untouched.
    have hrev6 : ∀ (j : Nat), (a6[j]!).rev = (a2[j]!).rev := fun j => by
      unfold a6; rw [getElem!_set!_pred_rev]; unfold a5; rw [getElem!_set!_succ_rev]
      unfold a4; rw [getElem!_set!_succ_rev]; unfold a3; rw [getElem!_set!_pred_rev]
    have hhead6 : ∀ (j : Nat), (a6[j]!).head = (a2[j]!).head := fun j => by
      unfold a6; rw [getElem!_set!_pred_head]; unfold a5; rw [getElem!_set!_succ_head]
      unfold a4; rw [getElem!_set!_succ_head]; unfold a3; rw [getElem!_set!_pred_head]
    have hpred6 : ∀ (j : Nat), j ≠ eF → j ≠ eLR → (a6[j]!).pred = (a2[j]!).pred :=
      fun j hjF hjLR => by
        unfold a6; rw [getElem!_set!_ne (Ne.symm hjLR)]; unfold a5; rw [getElem!_set!_succ_pred]
        unfold a4; rw [getElem!_set!_succ_pred]; unfold a3; rw [getElem!_set!_ne (Ne.symm hjF)]
    have hsucc6 : ∀ (j : Nat), j ≠ eL → j ≠ eFR → (a6[j]!).succ = (a2[j]!).succ :=
      fun j hjL hjFR => by
        unfold a6; rw [getElem!_set!_pred_succ]; unfold a5; rw [getElem!_set!_ne (Ne.symm hjFR)]
        unfold a4; rw [getElem!_set!_ne (Ne.symm hjL)]; unfold a3; rw [getElem!_set!_pred_succ]
    -- The four fan corners are closed, however the edited darts overlap.
    have hwpF : ¬ (a6[eF]!).pred.isNone := by
      by_cases hc : eLR = eF
      · unfold a6; rw [hc, getElem!_set!_self (by rw [ha5s, hsz2]; omega)]; simp
      · unfold a6; rw [getElem!_set!_ne hc]
        unfold a5; rw [getElem!_set!_succ_pred]
        unfold a4; rw [getElem!_set!_succ_pred]
        unfold a3; rw [getElem!_set!_self (by rw [hsz2]; omega)]
        simp
    have hwsL : ¬ (a6[eL]!).succ.isNone := by
      unfold a6; rw [getElem!_set!_pred_succ]
      by_cases hc : eFR = eL
      · unfold a5; rw [hc, getElem!_set!_self (by rw [ha4s, hsz2]; omega)]; simp
      · unfold a5; rw [getElem!_set!_ne hc]
        unfold a4; rw [getElem!_set!_self (by rw [ha3s, hsz2]; omega)]
        simp
    have hwpLR : ¬ (a6[eLR]!).pred.isNone := by
      unfold a6; rw [getElem!_set!_self (by rw [ha5s, hsz2]; omega)]; simp
    have hwsFR : ¬ (a6[eFR]!).succ.isNone := by
      unfold a6; rw [getElem!_set!_pred_succ]
      unfold a5; rw [getElem!_set!_self (by rw [ha4s, hsz2]; omega)]; simp
    have e1 : a1 = a0.push ⟨u, a0.size + 1, OptIdx.none, OptIdx.some eFR⟩ := rfl
    have e2 : a2 = a1.push ⟨w, a0.size, OptIdx.some eLR, OptIdx.none⟩ := rfl
    have e3 : a3 = a2.set! eF { a2[eF]! with pred := OptIdx.some eL } := rfl
    have e4 : a4 = a3.set! eL { a3[eL]! with succ := OptIdx.some eF } := rfl
    have e5 : a5 = a4.set! eFR { a4[eFR]! with succ := OptIdx.some a0.size } := rfl
    have e6 : a6 = a5.set! eLR { a5[eLR]! with pred := OptIdx.some (a0.size + 1) } := rfl
    clear_value a1 a2 a3 a4 a5 a6
    have hwf6 : ∀ i (hi : i < a6.size), (a6[i]'hi).InBounds pc.n a6.size :=
      boundaryFan_chain_wf hwf hu hw hfirst hlast hfrev hlrev e1 e2 e3 e4 e5 e6
    refine ⟨eF, eL, eFR, eLR, ?_⟩
    show PseudoTriangulation.BoundaryFanPatch pc.toPseudoTriangulation ⟨pc.n, a6⟩ eF eL eFR eLR
    exact
      { wf := hwf6
        n_eq := rfl
        size := by rw [hsize6, hsz2]
        eF_lt := hfirst
        eL_lt := hlast
        eFR_def := rfl
        eLR_def := rfl
        head_ne := hne'
        predF_open := PseudoTriangulation.firstDart_pred_isNone hFsome
        succL_open := PseudoTriangulation.lastDart_succ_isNone hLsome
        read_new1 := hn1
        read_new2 := hn2
        head_old := fun j hj => (hhead6 j).trans (congrArg Dart.head (r2 hj))
        rev_old := fun j hj => (hrev6 j).trans (congrArg Dart.rev (r2 hj))
        pred_old := fun j hjF hjLR hj => (hpred6 j hjF hjLR).trans (congrArg Dart.pred (r2 hj))
        succ_old := fun j hjL hjFR hj => (hsucc6 j hjL hjFR).trans (congrArg Dart.succ (r2 hj))
        predF_closed := hwpF
        predLR_closed := hwpLR
        succL_closed := hwsL
        succFR_closed := hwsFR }
end

/-- **Certified step for `addBoundaryDarts` (A.4.6/A.4.8):** on a valid input the
enlarged graph is valid and the identity map is coherent into it. The
implementation patch supplies the facts; the semantic layer does the rest. -/
theorem addBoundaryDarts_spec {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    (hfd : (pc.firstDart v).isSome) (hld : (pc.lastDart v).isSome)
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.toPseudoTriangulation.Valid ∧
      (Mappings.initialMappings pc.n pc.darts.size).Coherent
        pc.toPseudoTriangulation pc'.toPseudoTriangulation := by
  obtain ⟨eF, eL, eFR, eLR, hp⟩ := addBoundaryDarts_patch hv.wf hfd hld hrun
  exact ⟨hp.valid hv, Mappings.Coherent.id_of_extends (hp.toExtends hv)⟩

/-- `addBoundaryDarts` preserves `Valid` (A.4.6). -/
theorem addBoundaryDarts_valid {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    (hfd : (pc.firstDart v).isSome) (hld : (pc.lastDart v).isSome)
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    pc'.toPseudoTriangulation.Valid :=
  (addBoundaryDarts_spec hv hfd hld hrun).1

/-- On a valid input the identity map is coherent into the enlarged graph
(A.4.8). -/
theorem addBoundaryDarts_coherent {pc : PseudoConfiguration}
    (hv : pc.toPseudoTriangulation.Valid) {v : Nat}
    (hfd : (pc.firstDart v).isSome) (hld : (pc.lastDart v).isSome)
    {pc' : PseudoConfiguration} (hrun : pc.addBoundaryDarts v = some pc') :
    (Mappings.initialMappings pc.n pc.darts.size).Coherent
      pc.toPseudoTriangulation pc'.toPseudoTriangulation :=
  (addBoundaryDarts_spec hv hfd hld hrun).2

/-- **Loop invariant for `resolveDegreeIssues` (A.4.4).** Every queued or emitted
entry is a *valid* configuration reached from `origin` by a certified mapping:
`Valid` carries the geometry the A.4 steps need, and the `CoherentMappings`
records the homomorphism from the origin -- the two compose by construction. -/
structure ResolveEntry (origin : PseudoConfiguration)
    (entry : PseudoConfiguration × Mappings) : Prop where
  valid : entry.1.toPseudoTriangulation.Valid
  degrees_wf : entry.1.degrees.size = entry.1.n
  mapping : ∃ C : CoherentMappings origin.toPseudoTriangulation entry.1.toPseudoTriangulation,
    C.maps = entry.2

/-- The seed entry: `origin` mapped to itself by the identity (A.4.4 line 3). -/
theorem ResolveEntry.initial {origin : PseudoConfiguration}
    (hv : origin.toPseudoTriangulation.Valid) (hd : origin.degrees.size = origin.n) :
    ResolveEntry origin (origin, Mappings.initialMappings origin.n origin.darts.size) where
  valid := hv
  degrees_wf := hd
  mapping := ⟨CoherentMappings.id hv.wf, rfl⟩

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
  exact ⟨⟨hg1 ▸ h.valid, by rw [hd1, h.degrees_wf, hn1], hg1 ▸ h.mapping⟩,
    ⟨hg2 ▸ h.valid, by rw [hd2, h.degrees_wf, hn2], hg2 ▸ h.mapping⟩⟩

/-- An empty graph has no incident darts (so an over-incident vertex forces a
nonempty graph). -/
private theorem nIncidentDarts_getElem!_empty {pc : PseudoConfiguration}
    (h : pc.darts.size = 0) {v : Nat} : pc.nIncidentDarts[v]! = 0 := by
  have he : pc.darts = #[] := by grind
  have hz : pc.nIncidentDarts = Array.replicate pc.n 0 := by
    simp [PseudoTriangulation.nIncidentDarts, he]
  rcases Nat.lt_or_ge v pc.n with hv | hv <;> simp [hz, hv]

/-- In the over-incidence arm, the selected dart and its `lower`-th successor
are both in range; over-incidence itself forces the graph to be nonempty. -/
private theorem fixIssue_pair_bounds {pc : PseudoConfiguration} (hpc : pc.WF)
    {v : Nat} (hinc : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!) :
    let e := (if pc.isBoundary[v]! then pc.firstDart v else pc.anyDart v).get!
    let f := (pc.sucKTimes e (pc.degrees[v]!).lower).get!
    e < pc.darts.size ∧ f < pc.darts.size := by
  dsimp only []
  have hne : pc.darts.size ≠ 0 := fun h0 => by
    have h := nIncidentDarts_getElem!_empty (pc := pc) h0 (v := v)
    omega
  have he : (if pc.isBoundary[v]! then pc.firstDart v else pc.anyDart v).get!
      < pc.darts.size := by
    split
    · exact get!_lt_of_some_lt (fun e he => PseudoTriangulation.firstDart_lt he)
        (Nat.pos_of_ne_zero hne)
    · exact get!_lt_of_some_lt (fun e he => PseudoTriangulation.anyDart_lt he)
        (Nat.pos_of_ne_zero hne)
  have hf : (pc.sucKTimes ((if pc.isBoundary[v]! then pc.firstDart v
      else pc.anyDart v).get!) (pc.degrees[v]!).lower).get! < pc.darts.size :=
    get!_lt_of_some_lt (fun f hs => PseudoTriangulation.sucKTimes_lt hpc.1 he hs)
      (Nat.pos_of_ne_zero hne)
  exact ⟨he, hf⟩

/-- `fixSingleDegreeIssue` (A.4.7) preserves well-formedness: the
over-incidence arm glues an in-range pair, the boundary arm closes the
boundary; the remaining arms cannot answer `some`. -/
theorem fixSingleDegreeIssue_wf {pc : PseudoConfiguration} (hpc : pc.WF)
    {v : Nat} {pc' : PseudoConfiguration} {m : Mappings}
    (hrun : pc.fixSingleDegreeIssue v = some (pc', m)) : pc'.WF := by
  by_cases h1 : (pc.degrees[v]!).lower < pc.nIncidentDarts[v]!
  · obtain ⟨he, hf⟩ := fixIssue_pair_bounds hpc h1
    have hrun' : pc.dartIdentification
        #[((if pc.isBoundary[v]! then pc.firstDart v else pc.anyDart v).get!,
          (pc.sucKTimes ((if pc.isBoundary[v]! then pc.firstDart v
            else pc.anyDart v).get!) (pc.degrees[v]!).lower).get!)] =
        some (pc', m) := by
      simpa only [fixSingleDegreeIssue, if_pos h1] using hrun
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

end Steps

end PseudoConfiguration

end NearLinear4ct
