/-!
Semantic dart-graph model.

`DartGraph V D` is a semantic dart graph: typed `head`/`rev`/`succ`/`pred`
maps with no arrays, no index bounds and no sentinels. It is not yet a
rotation system -- the rotation laws (`succ`/`pred` inverses, rotation
closure) are deliberately deferred. `DartGraph.Valid` mirrors
`PseudoTriangulation.Valid` exactly.
Graph edits are modelled as relations between semantic views -- the
boundary-fan extension `IsBoundaryFanPatch` (A.4.6) over a sum type, and the
gluing quotient `IsQuotientMap` (A.3/A.4.1) along non-injective collapse
maps -- and invariant preservation is proved here once, on the typed dart
space.

Proof-only: imported by the proof layer, never by executable code. The
array representation stays authoritative; `PseudoTriangulationProofs.lean`
defines the concrete view (`PseudoTriangulation.dartGraph`) and the bridges.
-/

namespace NearLinear4ct

/-- A bijection with explicit inverse (core has no `TypeEquiv` type). -/
structure TypeEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace TypeEquiv

instance {α β : Type} : CoeFun (TypeEquiv α β) (fun _ => α → β) := ⟨toFun⟩

/-- The inverse bijection. -/
def symm {α β : Type} (e : TypeEquiv α β) : TypeEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[simp] theorem symm_apply_apply {α β : Type} (e : TypeEquiv α β) (a : α) :
    e.symm (e a) = a := e.left_inv a

@[simp] theorem apply_symm_apply {α β : Type} (e : TypeEquiv α β) (b : β) :
    e (e.symm b) = b := e.right_inv b

theorem injective {α β : Type} (e : TypeEquiv α β) {a a' : α} (h : e a = e a') :
    a = a' :=
  (e.left_inv a).symm.trans ((congrArg e.invFun h).trans (e.left_inv a'))

@[simp] theorem symm_symm {α β : Type} (e : TypeEquiv α β) : e.symm.symm = e := rfl

/-- Compose two bijections. -/
def trans {α β γ : Type} (e₁ : TypeEquiv α β) (e₂ : TypeEquiv β γ) : TypeEquiv α γ where
  toFun a := e₂ (e₁ a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv a := (congrArg e₁.invFun (e₂.left_inv (e₁ a))).trans (e₁.left_inv a)
  right_inv c := (congrArg e₂.toFun (e₁.right_inv (e₂.invFun c))).trans (e₂.right_inv c)

/-- Cast between equal-length index types. -/
def finCast {n m : Nat} (h : n = m) : TypeEquiv (Fin n) (Fin m) where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun i := ⟨i.val, h ▸ i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem finCast_val {n m : Nat} (h : n = m) (i : Fin n) :
    ((finCast h).toFun i).val = i.val := rfl

/-- Split off the two appended indices: `Fin (n + 2)` is the old index space
plus a two-element tag. -/
def finAddTwo (n : Nat) : TypeEquiv (Fin (n + 2)) (Sum (Fin n) (Fin 2)) where
  toFun i :=
    if h : i.val < n then .inl ⟨i.val, h⟩ else .inr ⟨i.val - n, by omega⟩
  invFun := fun
    | .inl j => ⟨j.val, by omega⟩
    | .inr k => ⟨n + k.val, by omega⟩
  left_inv i := by
    by_cases h : i.val < n <;> simp [h, Fin.ext_iff]; omega
  right_inv x := by
    rcases x with j | k
    · simp [j.isLt]
    · have hk : ¬ n + k.val < n := by omega
      simp [hk]

@[simp] theorem finAddTwo_symm_inl (n : Nat) (x : Fin n) :
    (((finAddTwo n).symm).toFun (Sum.inl x)).val = x.val := rfl

@[simp] theorem finAddTwo_symm_inr0 (n : Nat) :
    (((finAddTwo n).symm).toFun (Sum.inr 0)).val = n := rfl

@[simp] theorem finAddTwo_symm_inr1 (n : Nat) :
    (((finAddTwo n).symm).toFun (Sum.inr 1)).val = n + 1 := rfl

theorem finAddTwo_inl {n : Nat} (i : Fin (n + 2)) (h : i.val < n) :
    (finAddTwo n).toFun i = Sum.inl ⟨i.val, h⟩ := by simp [finAddTwo, h]

theorem finAddTwo_inr0 {n : Nat} (i : Fin (n + 2)) (h : i.val = n) :
    (finAddTwo n).toFun i = Sum.inr 0 := by simp [finAddTwo, h]

theorem finAddTwo_inr1 {n : Nat} (i : Fin (n + 2)) (h : i.val = n + 1) :
    (finAddTwo n).toFun i = Sum.inr 1 := by simp [finAddTwo, h]

end TypeEquiv

/-- A semantic dart graph: typed link maps, no representation. `Option` is
genuine absence -- boundary corners -- not a sentinel encoding. -/
structure DartGraph (V D : Type) where
  head : D → V
  rev : D → D
  succ : D → Option D
  pred : D → Option D

namespace DartGraph

/-- The geometric laws of `PseudoTriangulation.Valid`, stated semantically:
`rev` is an involution, no edge is a graph loop, and boundary corners agree
across an edge. -/
structure Valid {V D : Type} (G : DartGraph V D) : Prop where
  rev_rev : ∀ d, G.rev (G.rev d) = d
  loop_free : ∀ d, G.head d ≠ G.head (G.rev d)
  boundary : ∀ d, (G.pred d).isNone ↔ (G.succ (G.rev d)).isNone

/-- Presence form of `boundary`: a closed `pred` corner pairs with a closed
`succ` corner across the edge. -/
theorem Valid.pred_present_iff_succ_rev {V D : Type} {G : DartGraph V D}
    (h : G.Valid) (d : D) :
    ¬ (G.pred d).isNone ↔ ¬ (G.succ (G.rev d)).isNone :=
  not_congr (h.boundary d)

/-- Transport a graph along vertex and dart bijections. -/
def relabel {V V' D D' : Type} (ev : TypeEquiv V V') (ed : TypeEquiv D D')
    (G : DartGraph V D) : DartGraph V' D' where
  head d := ev (G.head (ed.symm d))
  rev d := ed (G.rev (ed.symm d))
  succ d := (G.succ (ed.symm d)).map ed
  pred d := (G.pred (ed.symm d)).map ed

@[simp] theorem relabel_head {V V' D D' : Type} (ev : TypeEquiv V V') (ed : TypeEquiv D D')
    (G : DartGraph V D) (d : D') :
    (G.relabel ev ed).head d = ev (G.head (ed.symm d)) := rfl

@[simp] theorem relabel_rev {V V' D D' : Type} (ev : TypeEquiv V V') (ed : TypeEquiv D D')
    (G : DartGraph V D) (d : D') :
    (G.relabel ev ed).rev d = ed (G.rev (ed.symm d)) := rfl

@[simp] theorem relabel_succ {V V' D D' : Type} (ev : TypeEquiv V V') (ed : TypeEquiv D D')
    (G : DartGraph V D) (d : D') :
    (G.relabel ev ed).succ d = (G.succ (ed.symm d)).map ed := rfl

@[simp] theorem relabel_pred {V V' D D' : Type} (ev : TypeEquiv V V') (ed : TypeEquiv D D')
    (G : DartGraph V D) (d : D') :
    (G.relabel ev ed).pred d = (G.pred (ed.symm d)).map ed := rfl

/-- Validity is representation-independent: it survives relabelling. -/
theorem Valid.relabel {V V' D D' : Type} {G : DartGraph V D}
    (h : G.Valid) (ev : TypeEquiv V V') (ed : TypeEquiv D D') :
    (G.relabel ev ed).Valid where
  rev_rev d := by simp [DartGraph.relabel, h.rev_rev]
  loop_free d hEq := h.loop_free (ed.symm d) (ev.injective (by simpa [DartGraph.relabel] using hEq))
  boundary d := by simpa [DartGraph.relabel] using h.boundary (ed.symm d)

/-- Relabelling there and back is the identity, pointwise in every field. -/
theorem relabel_symm_relabel {V V' D D' : Type} (ev : TypeEquiv V V') (ed : TypeEquiv D D')
    (G : DartGraph V D) : (G.relabel ev ed).relabel ev.symm ed.symm = G := by
  obtain ⟨head, rev, succ, pred⟩ := G
  simp only [relabel, mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext d <;>
    simp [Option.map_map, Function.comp_def]

/-- **The boundary-fan edit, semantically (A.4.6).** `dst` is `src` with two
new darts (the `Fin 2` tags) forming the reverse pair of the new boundary
edge, and the four fan corners `eF`/`eL`/`eFR`/`eLR` closed. Old links map
through `Sum.inl`; the closed corners are only required non-nil, exactly as
the concrete patch promises, so corner collisions need no special case. -/
structure IsBoundaryFanPatch {V D : Type} (src : DartGraph V D)
    (dst : DartGraph V (Sum D (Fin 2))) (eF eL eFR eLR : D) : Prop where
  eFR_def : src.rev eF = eFR
  eLR_def : src.rev eL = eLR
  head_ne : src.head eFR ≠ src.head eLR
  predF_open : (src.pred eF).isNone
  succL_open : (src.succ eL).isNone
  rev_new1 : dst.rev (.inr 0) = .inr 1
  rev_new2 : dst.rev (.inr 1) = .inr 0
  head_new1 : dst.head (.inr 0) = src.head eFR
  head_new2 : dst.head (.inr 1) = src.head eLR
  succ_new1 : (dst.succ (.inr 0)).isNone
  pred_new1 : ¬ (dst.pred (.inr 0)).isNone
  succ_new2 : ¬ (dst.succ (.inr 1)).isNone
  pred_new2 : (dst.pred (.inr 1)).isNone
  head_old : ∀ d, dst.head (.inl d) = src.head d
  rev_old : ∀ d, dst.rev (.inl d) = .inl (src.rev d)
  pred_old : ∀ d, d ≠ eF → d ≠ eLR → dst.pred (.inl d) = (src.pred d).map .inl
  succ_old : ∀ d, d ≠ eL → d ≠ eFR → dst.succ (.inl d) = (src.succ d).map .inl
  predF_closed : ¬ (dst.pred (.inl eF)).isNone
  predLR_closed : ¬ (dst.pred (.inl eLR)).isNone
  succL_closed : ¬ (dst.succ (.inl eL)).isNone
  succFR_closed : ¬ (dst.succ (.inl eFR)).isNone

/-- **The boundary-fan edit preserves validity** -- the semantic core of the
A.4.6 step. Old darts split into the four closed corners (paired by
`rev_rev`) and the untouched rest; the new pair is boundary-consistent by
construction. No arrays, indices or write order appear. -/
theorem IsBoundaryFanPatch.valid {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid) :
    dst.Valid := by
  have hi2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine ⟨?_, ?_, ?_⟩ <;> intro d <;> rcases d with x | i
  · grind [IsBoundaryFanPatch, Valid]
  · rcases hi2 i with rfl | rfl <;> grind [IsBoundaryFanPatch, Valid]
  · grind [IsBoundaryFanPatch, Valid]
  · rcases hi2 i with rfl | rfl <;> grind [IsBoundaryFanPatch, Valid]
  · by_cases hxF : x = eF
    · subst hxF; grind [IsBoundaryFanPatch, Valid]
    by_cases hxLR : x = eLR
    · subst hxLR; have h3 := hv.rev_rev eL; grind [IsBoundaryFanPatch, Valid]
    · have h1 := hv.rev_rev x
      have hrL : src.rev x ≠ eL :=
        fun hc => hxLR (h1.symm.trans ((congrArg src.rev hc).trans hp.eLR_def))
      have hrFR : src.rev x ≠ eFR :=
        fun hc => hxF (h1.symm.trans
          ((congrArg src.rev (hc.trans hp.eFR_def.symm)).trans (hv.rev_rev eF)))
      have h4 := hp.pred_old x hxF hxLR
      have h5 := hp.succ_old (src.rev x) hrL hrFR
      grind [IsBoundaryFanPatch, Valid, Option.isNone_map]
  · rcases hi2 i with rfl | rfl <;> grind [IsBoundaryFanPatch, Valid]

/-- **A quotient of dart graphs (A.3/A.4.1).** `qv`/`qd` collapse vertices and
darts onto `dst`: `head`/`rev` commute with the collapse, interior links map
onto interior links (boundary corners may close), and every `dst` link has a
source preimage within the same dart class -- the gluing never invents links.
Unlike `IsBoundaryFanPatch` this relates graphs over arbitrary index types by
non-injective maps, not bijections. -/
structure IsQuotientMap {V D V' D' : Type} (src : DartGraph V D)
    (dst : DartGraph V' D') (qv : V → V') (qd : D → D') : Prop where
  qv_surj : ∀ c, ∃ v, qv v = c
  qd_surj : ∀ c, ∃ d, qd d = c
  head_eq : ∀ d, dst.head (qd d) = qv (src.head d)
  rev_eq : ∀ d, dst.rev (qd d) = qd (src.rev d)
  succ_of : ∀ d s, src.succ d = some s → dst.succ (qd d) = some (qd s)
  pred_of : ∀ d p, src.pred d = some p → dst.pred (qd d) = some (qd p)
  succ_from : ∀ d, ¬ (dst.succ (qd d)).isNone → ∃ d', qd d' = qd d ∧ ¬ (src.succ d').isNone
  pred_from : ∀ d, ¬ (dst.pred (qd d)).isNone → ∃ d', qd d' = qd d ∧ ¬ (src.pred d').isNone

/-- Some dart in the quotient class `c` has the given link closed. The
class-level currency of quotient reasoning: the `_present_iff` lemmas trade
destination corners for it, and `mirror_present` reverses it, so validity
transport never manages existential witnesses by hand. -/
def Present {D D' : Type} (link : D → Option D) (qd : D → D') (c : D') : Prop :=
  ∃ w, qd w = c ∧ ¬ (link w).isNone

/-- `qd`-equal darts have `qd`-equal reverses (through `rev_eq`). -/
theorem IsQuotientMap.rev_class {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) {a b : D} (h : qd a = qd b) :
    qd (src.rev a) = qd (src.rev b) :=
  (hq.rev_eq a).symm.trans ((congrArg dst.rev h).trans (hq.rev_eq b))

/-- The destination `pred` corner of a class is closed iff some source dart
of the class has a closed `pred` (`pred_of` forward, `pred_from` back). -/
theorem IsQuotientMap.pred_present_iff {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (d : D) :
    ¬ (dst.pred (qd d)).isNone ↔ Present src.pred qd (qd d) := by
  constructor
  · exact fun h => hq.pred_from d h
  · rintro ⟨w, hw, hwp⟩
    cases hcp : src.pred w with
    | none => exact absurd (by simp [hcp]) hwp
    | some p => exact fun hnil => by simp [hw ▸ hq.pred_of w p hcp] at hnil

/-- As `pred_present_iff`, for the `succ` corner. -/
theorem IsQuotientMap.succ_present_iff {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (d : D) :
    ¬ (dst.succ (qd d)).isNone ↔ Present src.succ qd (qd d) := by
  constructor
  · exact fun h => hq.succ_from d h
  · rintro ⟨w, hw, hws⟩
    cases hcs : src.succ w with
    | none => exact absurd (by simp [hcs]) hws
    | some s => exact fun hnil => by simp [hw ▸ hq.succ_of w s hcs] at hnil

/-- Reversing a class turns source `pred` presence into source `succ`
presence: the witness moves to its reverse dart, and `src.Valid.boundary`
closes the mirrored corner. -/
theorem IsQuotientMap.mirror_present {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (hv : src.Valid) (d : D) :
    Present src.pred qd (qd d) ↔ Present src.succ qd (qd (src.rev d)) := by
  constructor
  · rintro ⟨w, hw, hwp⟩
    exact ⟨src.rev w, hq.rev_class hw, (hv.pred_present_iff_succ_rev w).mp hwp⟩
  · rintro ⟨w, hw, hws⟩
    refine ⟨src.rev w, (hq.rev_class hw).trans (congrArg qd (hv.rev_rev d)), ?_⟩
    exact (hv.pred_present_iff_succ_rev (src.rev w)).mpr ((hv.rev_rev w).symm ▸ hws)

/-- **A quotient preserves validity**, given loop-freedom of the result (the
executable `hasLoop` guard, which the quotient does not preserve by itself):
`rev_rev` transports along the collapse, and `boundary` is classwise -- both
corners of a class trade for source-class presence, and `mirror_present`
carries presence across the edge. -/
theorem IsQuotientMap.valid {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (hv : src.Valid)
    (hloop : ∀ c, dst.head c ≠ dst.head (dst.rev c)) : dst.Valid := by
  refine ⟨?_, hloop, ?_⟩
  · intro c
    obtain ⟨d, rfl⟩ := hq.qd_surj c
    rw [hq.rev_eq d, hq.rev_eq (src.rev d), hv.rev_rev d]
  · intro c
    obtain ⟨d, rfl⟩ := hq.qd_surj c
    rw [hq.rev_eq d]
    have hp := hq.pred_present_iff d
    have hm := hq.mirror_present hv d
    have hs := hq.succ_present_iff (src.rev d)
    grind only [Present]

end DartGraph
end NearLinear4ct
