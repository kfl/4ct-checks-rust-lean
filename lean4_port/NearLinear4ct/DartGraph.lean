import NearLinear4ct.TypeEquiv

/-!
Semantic dart-graph model.

`DartGraph V D` is a semantic dart graph: typed `head`/`rev`/`succ`/`pred`
maps with no arrays, no index bounds and no sentinels. `DartGraph.Valid`
mirrors `PseudoTriangulation.Valid` exactly; `DartGraph.Rotational` adds the
rotation-system laws (the paper's M3/M4/M6) on top, with each vertex's
incidence list carried explicitly so counting arguments are list-index
arithmetic.
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

namespace TypeEquiv

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

/-- Walking `succ` for `k` successful steps -- the semantic `sucKTimes`. -/
def succWalk {V D : Type} (G : DartGraph V D) : Nat → D → Option D
  | 0, d => some d
  | k + 1, d =>
    match G.succ d with
    | some e => succWalk G k e
    | none => none

/-- **One incidence list (the paper's M6).** `l` enumerates the darts of `v`
exactly once, consecutive entries are `succ`-linked, and the ends either join
up (an inner vertex's cyclic rotation) or are open on both sides (a boundary
vertex's unique corners). Finiteness of each vertex's dart set is implied by
the enumeration itself, so no global finiteness assumption is needed. -/
structure IncidenceList {V D : Type} (G : DartGraph V D) (v : V)
    (l : List D) : Prop where
  mem_iff : ∀ d, d ∈ l ↔ G.head d = v
  nodup : l.Nodup
  chain : ∀ (i : Nat) (d₁ d₂ : D), l[i]? = some d₁ → l[i + 1]? = some d₂ →
    G.succ d₁ = some d₂
  ends : ∀ dl dh, l.getLast? = some dl → l.head? = some dh →
    G.succ dl = some dh ∨ (G.succ dl = none ∧ G.pred dh = none)

/-- **The rotation-system laws (the paper's M3/M4/M6)**, layered above
`Valid`: `succ`/`pred` are mutually inverse partial maps that stay within
their vertex, and every vertex carries exactly one incidence list. Like
`Valid`, the laws hold at operation results, not at gluing intermediates (a
copied link briefly lacks its inverse); they survived falsification attempts
on enumerated wheels, their gluing quotients with every
`resolveDegreeIssues` intermediate, and boundary-fan edits before being
formalised. -/
structure Rotational {V D : Type} (G : DartGraph V D) : Prop where
  succ_pred : ∀ d e, G.succ d = some e → G.pred e = some d
  pred_succ : ∀ d e, G.pred d = some e → G.succ e = some d
  succ_head : ∀ d e, G.succ d = some e → G.head e = G.head d
  incidence : ∀ v, ∃ l, IncidenceList G v l

/-- `succ` is injective where present (from M3: both preimages are the
target's `pred`). -/
theorem Rotational.succ_inj {V D : Type} {G : DartGraph V D}
    (hr : G.Rotational) {d d' e : D}
    (h : G.succ d = some e) (h' : G.succ d' = some e) : d = d' :=
  Option.some.inj ((hr.succ_pred d e h).symm.trans (hr.succ_pred d' e h'))

/-- `pred` preserves the vertex (from M3 and M4). -/
theorem Rotational.pred_head {V D : Type} {G : DartGraph V D}
    (hr : G.Rotational) {d e : D} (h : G.pred d = some e) :
    G.head e = G.head d :=
  (hr.succ_head e d (hr.pred_succ d e h)).symm

namespace IncidenceList

/-- A `succ`-open dart sits at the end of its list: everywhere else the
chain provides a successor. -/
theorem succ_none_last {V D : Type} {G : DartGraph V D} {v : V} {l : List D}
    (hl : IncidenceList G v l) {i : Nat} (hi : i < l.length)
    (hn : G.succ (l[i]'hi) = none) : i = l.length - 1 := by
  refine Classical.byContradiction fun hne => ?_
  have hi1 : i + 1 < l.length := by omega
  have hstep := hl.chain i (l[i]'hi) (l[i + 1]'hi1)
    (by simp [List.getElem?_eq_getElem hi]) (by simp [List.getElem?_eq_getElem hi1])
  exact nomatch (hn.symm.trans hstep)

/-- **The unique open `succ` corner (half of the paper's page-32 flip
argument):** two `succ`-open darts of one vertex coincide. -/
theorem succ_none_unique {V D : Type} {G : DartGraph V D} {v : V} {l : List D}
    (hl : IncidenceList G v l) {d₁ d₂ : D}
    (h1 : d₁ ∈ l) (h2 : d₂ ∈ l)
    (hn1 : G.succ d₁ = none) (hn2 : G.succ d₂ = none) : d₁ = d₂ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
  have hilast := hl.succ_none_last hi hn1
  have hjlast := hl.succ_none_last hj hn2
  exact (List.getElem_inj hl.nodup).mpr (by omega)

/-- Walking a cyclic list moves the index modulo the length. -/
theorem succWalk_cyclic {V D : Type} {G : DartGraph V D} {v : V} {l : List D}
    (hl : IncidenceList G v l)
    (hcyc : ∀ dl dh, l.getLast? = some dl → l.head? = some dh →
      G.succ dl = some dh)
    (k : Nat) {i : Nat} (hi : i < l.length) :
    succWalk G k (l[i]'hi) =
      some (l[(i + k) % l.length]'(Nat.mod_lt _ (by omega))) := by
  induction k generalizing i with
  | zero => simp [succWalk, Nat.mod_eq_of_lt hi]
  | succ k ih =>
    by_cases hlast : i + 1 < l.length
    · have hstep := hl.chain i (l[i]'hi) (l[i + 1]'hlast)
        (by simp [List.getElem?_eq_getElem hi]) (by simp [List.getElem?_eq_getElem hlast])
      simp only [succWalk, hstep]
      rw [ih hlast]
      congr 1
      exact (List.getElem_inj hl.nodup).mpr (by congr 1; omega)
    · have hi0 : 0 < l.length := by omega
      have hstep := hcyc (l[i]'hi) (l[0]'hi0)
        (by have hieq : i = l.length - 1 := by omega
            subst hieq
            rw [List.getLast?_eq_getElem?]
            exact List.getElem?_eq_getElem hi)
        (by rw [List.head?_eq_getElem?]
            exact List.getElem?_eq_getElem hi0)
      simp only [succWalk, hstep]
      rw [ih hi0]
      congr 1
      refine (List.getElem_inj hl.nodup).mpr ?_
      have h1 : i + (k + 1) = l.length + k := by omega
      rw [Nat.zero_add, h1, Nat.add_mod_left]

/-- Walking an open list moves the index linearly, falling off the end. -/
theorem succWalk_open {V D : Type} {G : DartGraph V D} {v : V} {l : List D}
    (hl : IncidenceList G v l)
    (hopen : ∀ dl, l.getLast? = some dl → G.succ dl = none)
    (k : Nat) {i : Nat} (hi : i < l.length) :
    succWalk G k (l[i]'hi) =
      if h : i + k < l.length then some (l[i + k]'h) else none := by
  induction k generalizing i with
  | zero => simp [succWalk, hi]
  | succ k ih =>
    by_cases hlast : i + 1 < l.length
    · have hstep := hl.chain i (l[i]'hi) (l[i + 1]'hlast)
        (by simp [List.getElem?_eq_getElem hi]) (by simp [List.getElem?_eq_getElem hlast])
      simp only [succWalk, hstep]
      rw [ih hlast]
      by_cases hin : i + (k + 1) < l.length
      · rw [dif_pos (by omega : i + 1 + k < l.length), dif_pos hin]
        congr 1
        exact (List.getElem_inj hl.nodup).mpr (by omega)
      · rw [dif_neg (by omega), dif_neg hin]
    · have hstep := hopen (l[i]'hi)
        (by have hieq : i = l.length - 1 := by omega
            subst hieq
            rw [List.getLast?_eq_getElem?]
            exact List.getElem?_eq_getElem hi)
      simp only [succWalk, hstep]
      rw [dif_neg (by omega)]

/-- **The paper's page-32 walk argument (M6 core):** a successful walk of
`0 < k < ` list length steps leaves its start dart. In the cyclic case the
index shift is nonzero modulo the length; in the open case the indices
differ. -/
theorem succWalk_ne {V D : Type} {G : DartGraph V D} {v : V} {l : List D}
    (hl : IncidenceList G v l) {d e : D} {k : Nat}
    (hd : d ∈ l) (h0 : 0 < k) (hk : k < l.length)
    (hwalk : succWalk G k d = some e) : e ≠ d := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  have hlast : l.getLast? = some (l[l.length - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?]
    exact List.getElem?_eq_getElem (by omega)
  have hhead : l.head? = some (l[0]'(by omega)) := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem (by omega)
  rcases hl.ends _ _ hlast hhead with hcyc | ⟨hnil, -⟩
  · -- Cyclic list: the walk shifts the index by `k ≢ 0` modulo the length.
    have hchar := hl.succWalk_cyclic
      (fun dl dh h1 h2 =>
        Option.some.inj (hlast.symm.trans h1) ▸
          Option.some.inj (hhead.symm.trans h2) ▸ hcyc) k hi
    have he : e = l[(i + k) % l.length]'(Nat.mod_lt _ (by omega)) :=
      Option.some.inj (hwalk.symm.trans hchar)
    intro heq
    have hidx : (i + k) % l.length = i :=
      (List.getElem_inj hl.nodup).mp (he.symm.trans heq)
    by_cases hlt : i + k < l.length
    · have := (Nat.mod_eq_of_lt hlt).symm.trans hidx
      omega
    · have hsub : (i + k) % l.length = i + k - l.length := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have := hsub.symm.trans hidx
      omega
  · -- Open list: the walk succeeded, so the shifted index is in range.
    have hchar := hl.succWalk_open
      (fun dl h1 => Option.some.inj (hlast.symm.trans h1) ▸ hnil) k hi
    have h2 := hwalk.symm.trans hchar
    by_cases hin : i + k < l.length
    · have he : e = l[i + k]'hin := Option.some.inj (h2.trans (dif_pos hin))
      intro heq
      have := (List.getElem_inj hl.nodup).mp (he.symm.trans heq)
      omega
    · exact nomatch (h2.trans (dif_neg hin))

/-- A vertex with a `succ`-open dart also has a `pred`-open one: the single
incidence list cannot be cyclic, so both ends are open. The semantic core of
`fixSingleDegreeIssue`'s completeness claim (a boundary vertex has first and
last darts). -/
theorem exists_pred_none {V D : Type} {G : DartGraph V D} {v : V} {l : List D}
    (hl : IncidenceList G v l) {d : D} (hd : d ∈ l) (hn : G.succ d = none) :
    ∃ d', d' ∈ l ∧ G.pred d' = none := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  have hilast := hl.succ_none_last hi hn
  have hlen : 0 < l.length := by omega
  have hlast : l.getLast? = some (l[l.length - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?]
    exact List.getElem?_eq_getElem (by omega)
  have hhead : l.head? = some (l[0]'hlen) := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem hlen
  rcases hl.ends _ _ hlast hhead with hcyc | ⟨-, hopen⟩
  · subst hilast
    exact nomatch (hn.symm.trans hcyc)
  · exact ⟨l[0]'hlen, List.getElem_mem hlen, hopen⟩

end IncidenceList

/-- A `pred`-open dart sits at the head of its list: elsewhere the chain's
predecessor supplies a `pred` through M3. -/
theorem Rotational.pred_none_first {V D : Type} {G : DartGraph V D}
    (hr : G.Rotational) {v : V} {l : List D} (hl : IncidenceList G v l)
    {i : Nat} (hi : i < l.length) (hn : G.pred (l[i]'hi) = none) : i = 0 := by
  refine Classical.byContradiction fun hne => ?_
  have hprev : i - 1 < l.length := by omega
  have hstep := hl.chain (i - 1) (l[i - 1]'hprev) (l[i]'hi)
    (by simp [List.getElem?_eq_getElem hprev])
    (by rw [show i - 1 + 1 = i from by omega]
        simp [List.getElem?_eq_getElem hi])
  exact nomatch (hn.symm.trans (hr.succ_pred _ _ hstep))

/-- **The unique open `pred` corner** (with `IncidenceList.succ_none_unique`,
the page-32 flip argument's uniqueness half): two `pred`-open darts of one
vertex coincide. -/
theorem Rotational.pred_none_unique {V D : Type} {G : DartGraph V D}
    (hr : G.Rotational) {v : V} {l : List D} (hl : IncidenceList G v l)
    {d₁ d₂ : D} (h1 : d₁ ∈ l) (h2 : d₂ ∈ l)
    (hn1 : G.pred d₁ = none) (hn2 : G.pred d₂ = none) : d₁ = d₂ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
  have hifirst := hr.pred_none_first hl hi hn1
  have hjfirst := hr.pred_none_first hl hj hn2
  exact (List.getElem_inj hl.nodup).mpr (by omega)

/-- **Incidence connectivity**: the equivalence closure of `succ` adjacency.
The unordered counterpart of sharing an incidence list -- the gluing quotient
maintains it per merged class, and `exists_incidenceList_of_conn` converts it
back into the ordered M6 witness once, at the whole-quotient boundary. -/
inductive IncidenceConn {V D : Type} (G : DartGraph V D) : D → D → Prop
  | refl (d : D) : IncidenceConn G d d
  | succ {d e : D} : G.succ d = some e → IncidenceConn G d e
  | symm {d e : D} : IncidenceConn G d e → IncidenceConn G e d
  | trans {d e f : D} : IncidenceConn G d e → IncidenceConn G e f → IncidenceConn G d f

/-- Walking forward along an incidence list connects any earlier entry to
any later one. -/
theorem IncidenceList.conn_of_le {V D : Type} {G : DartGraph V D} {v : V}
    {l : List D} (hl : IncidenceList G v l) :
    ∀ {i j : Nat} (hi : i < l.length) (hj : j < l.length), i ≤ j →
      IncidenceConn G (l[i]'hi) (l[j]'hj) := by
  intro i j
  induction j with
  | zero =>
    intro hi hj hij
    have h0 : i = 0 := Nat.le_zero.mp hij
    subst h0
    exact .refl _
  | succ k ih =>
    intro hi hj hij
    by_cases hik : i = k + 1
    · subst hik
      exact .refl _
    · have hk : k < l.length := by omega
      exact .trans (ih hi hk (by omega))
        (.succ (hl.chain k _ _ (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hj)))

/-- Two members of one incidence list are incidence-connected. -/
theorem IncidenceList.connected {V D : Type} {G : DartGraph V D} {v : V}
    {l : List D} (hl : IncidenceList G v l) {d₁ d₂ : D}
    (h1 : d₁ ∈ l) (h2 : d₂ ∈ l) : IncidenceConn G d₁ d₂ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
  rcases Nat.le_total i j with h | h
  · exact hl.conn_of_le hi hj h
  · exact .symm (hl.conn_of_le hj hi h)

/-- A property holding somewhere on `Nat` holds at a least witness (core has
no `Nat.find`). -/
private theorem exists_minimal {p : Nat → Prop} :
    ∀ n, p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hlow : ∃ k, k < n ∧ p k
    · obtain ⟨k, hk, hpk⟩ := hlow
      exact ih k hk hpk
    · exact ⟨n, hn, fun k hk hpk => hlow ⟨k, hk, hpk⟩⟩

/-- A duplicate-free list injects into any list containing its members. -/
private theorem length_le_of_nodup_subset {α : Type} :
    ∀ {l l' : List α}, l.Nodup → (∀ a ∈ l, a ∈ l') → l.length ≤ l'.length := by
  intro l
  induction l with
  | nil => intro l' _ _; simp
  | cons a t ih =>
    intro l' hn hsub
    haveI := Classical.typeDecidableEq α
    have hat := List.nodup_cons.mp hn
    have ha : a ∈ l' := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x ∈ t, x ∈ l'.erase a := by
      intro x hx
      exact (List.mem_erase_of_ne fun (hxa : x = a) => hat.1 (hxa ▸ hx)).mpr
        (hsub x (List.mem_cons_of_mem a hx))
    have hlen := List.length_erase_of_mem ha
    have hpos := List.length_pos_of_mem ha
    have := ih hat.2 hsub'
    simp only [List.length_cons]
    omega

/-- Extract an index-level duplicate from a repetitive list. -/
private theorem exists_dup_of_not_nodup {α : Type} {c : List α} (h : ¬ c.Nodup) :
    ∃ (i j : Nat) (hi : i < c.length) (hj : j < c.length),
      i < j ∧ c[i]'hi = c[j]'hj := by
  refine Classical.byContradiction fun hno => ?_
  refine h (List.pairwise_iff_getElem.mpr ?_)
  intro i j hi hj hij heq
  exact hno ⟨i, j, hi, hj, hij, heq⟩

/-- The link-reversed graph: `succ` and `pred` swapped. Every forward walk
lemma then serves the backward direction. -/
def op {V D : Type} (G : DartGraph V D) : DartGraph V D :=
  ⟨G.head, G.rev, G.pred, G.succ⟩

@[simp] theorem op_head {V D : Type} (G : DartGraph V D) : G.op.head = G.head := rfl

@[simp] theorem op_succ {V D : Type} (G : DartGraph V D) : G.op.succ = G.pred := rfl

@[simp] theorem op_pred {V D : Type} (G : DartGraph V D) : G.op.pred = G.succ := rfl

/-- Follow `succ` greedily for at most `fuel` steps, collecting the visited
darts -- the constructive side of the connectivity-to-M6 conversion. -/
def succChain {V D : Type} (G : DartGraph V D) : Nat → D → List D
  | 0, d => [d]
  | fuel + 1, d =>
    match G.succ d with
    | some e => d :: succChain G fuel e
    | none => [d]

theorem succChain_head? {V D : Type} (G : DartGraph V D) (fuel : Nat) (d : D) :
    (succChain G fuel d).head? = some d := by
  cases fuel with
  | zero => rfl
  | succ k =>
    cases hs : G.succ d with
    | some e => simp [succChain, hs]
    | none => simp [succChain, hs]

theorem succChain_ne_nil {V D : Type} (G : DartGraph V D) (fuel : Nat) (d : D) :
    succChain G fuel d ≠ [] :=
  fun hnil => nomatch ((succChain_head? G fuel d).symm.trans (congrArg List.head? hnil))

theorem succChain_length_le {V D : Type} (G : DartGraph V D) :
    ∀ (fuel : Nat) (d : D), (succChain G fuel d).length ≤ fuel + 1 := by
  intro fuel
  induction fuel with
  | zero => intro d; simp [succChain]
  | succ k ih =>
    intro d
    cases hs : G.succ d with
    | none => simp [succChain, hs]
    | some e =>
      have := ih e
      simp only [succChain, hs, List.length_cons]
      omega

/-- Walk members all sit at the walk's starting vertex, given M4. -/
theorem succChain_head_eq {V D : Type} {G : DartGraph V D}
    (hM4 : ∀ d e, G.succ d = some e → G.head e = G.head d) :
    ∀ (fuel : Nat) (d : D), ∀ x ∈ succChain G fuel d, G.head x = G.head d := by
  intro fuel
  induction fuel with
  | zero =>
    intro d x hx
    have hxd : x = d := by simpa [succChain] using hx
    exact congrArg G.head hxd
  | succ k ih =>
    intro d x hx
    cases hs : G.succ d with
    | none =>
      have hxd : x = d := by simpa [succChain, hs] using hx
      exact congrArg G.head hxd
    | some e =>
      have hx' : x = d ∨ x ∈ succChain G k e := by simpa [succChain, hs] using hx
      rcases hx' with rfl | hx'
      · rfl
      · exact (ih e x hx').trans (hM4 d e hs)

/-- Consecutive walk entries are `succ`-linked. -/
theorem succChain_chain {V D : Type} (G : DartGraph V D) :
    ∀ (fuel : Nat) (d : D) (i : Nat) (d₁ d₂ : D),
      (succChain G fuel d)[i]? = some d₁ → (succChain G fuel d)[i + 1]? = some d₂ →
      G.succ d₁ = some d₂ := by
  intro fuel
  induction fuel with
  | zero =>
    intro d i d₁ d₂ _h1 h2
    exact nomatch ((show (succChain G 0 d)[i + 1]? = none by
      simp [succChain]).symm.trans h2)
  | succ k ih =>
    intro d i d₁ d₂ h1 h2
    cases hs : G.succ d with
    | none =>
      exact nomatch ((show (succChain G (k + 1) d)[i + 1]? = none by
        simp [succChain, hs]).symm.trans h2)
    | some e =>
      cases i with
      | zero =>
        have hd1 : d = d₁ := by simpa [succChain, hs] using h1
        have h2' : (succChain G k e)[0]? = some d₂ := by simpa [succChain, hs] using h2
        have hh : (succChain G k e)[0]? = some e := by
          rw [← List.head?_eq_getElem?]
          exact succChain_head? G k e
        have hd2 : e = d₂ := Option.some.inj (hh.symm.trans h2')
        exact hd1 ▸ hd2 ▸ hs
      | succ j =>
        have h1' : (succChain G k e)[j]? = some d₁ := by simpa [succChain, hs] using h1
        have h2' : (succChain G k e)[j + 1]? = some d₂ := by simpa [succChain, hs] using h2
        exact ih e j d₁ d₂ h1' h2'

/-- A walk shorter than its fuel allows was stopped by an open corner. -/
theorem succChain_terminal {V D : Type} (G : DartGraph V D) :
    ∀ (fuel : Nat) (d : D), (succChain G fuel d).length < fuel + 1 →
      ∃ dl, (succChain G fuel d).getLast? = some dl ∧ G.succ dl = none := by
  intro fuel
  induction fuel with
  | zero =>
    intro d h
    exact absurd h (by simp [succChain])
  | succ k ih =>
    intro d h
    cases hs : G.succ d with
    | none => exact ⟨d, by simp [succChain, hs], hs⟩
    | some e =>
      have hcons : (succChain G (k + 1) d).length = (succChain G k e).length + 1 := by
        simp [succChain, hs]
      obtain ⟨dl, hdl, hnone⟩ := ih e (by omega)
      refine ⟨dl, ?_, hnone⟩
      calc (succChain G (k + 1) d).getLast?
          = (d :: succChain G k e).getLast? := by simp [succChain, hs]
        _ = (succChain G k e).getLast? :=
            List.getLast?_cons_of_ne_nil (succChain_ne_nil G k e)
        _ = some dl := hdl

section ChainLists

variable {V D : Type} {G : DartGraph V D}

/-- Backward links of a `succ`-chained list, via M3. -/
private theorem chain_pred {c : List D}
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hchain : ∀ (i : Nat) (d₁ d₂ : D), c[i]? = some d₁ → c[i + 1]? = some d₂ →
      G.succ d₁ = some d₂) :
    ∀ (j : Nat) (hj : j < c.length), 0 < j →
      G.pred (c[j]'hj) = some (c[j - 1]'(by omega)) := by
  intro j hj hj0
  have h1 : c[j - 1]? = some (c[j - 1]'(by omega)) := List.getElem?_eq_getElem (by omega)
  have h2 : c[j - 1 + 1]? = some (c[j]'hj) := by
    have hjj : j - 1 + 1 = j := by omega
    rw [hjj]
    exact List.getElem?_eq_getElem hj
  exact hM3a _ _ (hchain (j - 1) _ _ h1 h2)

/-- **A chain from a `pred`-open start never repeats**: a repeat would
backtrack step by step to a predecessor of the open start. -/
private theorem nodup_of_chain_open {c : List D}
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hchain : ∀ (i : Nat) (d₁ d₂ : D), c[i]? = some d₁ → c[i + 1]? = some d₂ →
      G.succ d₁ = some d₂)
    {d₀ : D} (hhead : c.head? = some d₀) (hopen : G.pred d₀ = none) : c.Nodup := by
  have hpred := chain_pred hM3a hchain
  have hne : ∀ (i j : Nat) (hi : i < c.length) (hj : j < c.length), i < j →
      c[i]'hi ≠ c[j]'hj := by
    intro i
    induction i with
    | zero =>
      intro j hi hj hij heq
      have h0 : c[0]'hi = d₀ := by
        have hh : c[0]? = some d₀ := (List.head?_eq_getElem? (l := c)).symm.trans hhead
        exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hh)
      have hpj := hpred j hj (by omega)
      have hnone : G.pred (c[j]'hj) = none := by
        rw [← heq, h0]
        exact hopen
      exact nomatch (hnone.symm.trans hpj)
    | succ k ih =>
      intro j hi hj hij heq
      have hpk := hpred (k + 1) hi (by omega)
      have hpj := hpred j hj (by omega)
      have heqp : c[k]'(by omega) = c[j - 1]'(by omega) :=
        Option.some.inj (hpk.symm.trans ((congrArg G.pred heq).trans hpj))
      exact ih (j - 1) (by omega) (by omega) (by omega) heqp
  exact List.pairwise_iff_getElem.mpr hne

/-- **Backtracking a repeat to the start**: if a `succ`-chained list repeats
a value `i` positions apart, its start value returns after `j - i` steps. -/
private theorem chain_return {c : List D}
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hchain : ∀ (i : Nat) (d₁ d₂ : D), c[i]? = some d₁ → c[i + 1]? = some d₂ →
      G.succ d₁ = some d₂) :
    ∀ (i j : Nat), i ≤ j → ∀ x, c[i]? = some x → c[j]? = some x →
      ∀ s, c[0]? = some s → c[j - i]? = some s := by
  intro i
  induction i with
  | zero =>
    intro j _hij x h0 hj s hs
    have hsx : s = x := Option.some.inj (hs.symm.trans h0)
    subst hsx
    exact hj
  | succ k ih =>
    intro j hij x hk1 hj s hs
    have hklen : k + 1 < c.length := (List.getElem?_eq_some_iff.mp hk1).1
    have hjlen : j < c.length := (List.getElem?_eq_some_iff.mp hj).1
    have hkr : c[k]? = some (c[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hj1r : c[j - 1]? = some (c[j - 1]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hj2 : c[j - 1 + 1]? = some x := by
      have hjj : j - 1 + 1 = j := by omega
      rw [hjj]
      exact hj
    have hpx1 : G.pred x = some (c[k]'(by omega)) := hM3a _ _ (hchain k _ _ hkr hk1)
    have hpx2 : G.pred x = some (c[j - 1]'(by omega)) := hM3a _ _ (hchain (j - 1) _ _ hj1r hj2)
    have heq : c[k]'(by omega) = c[j - 1]'(by omega) :=
      Option.some.inj (hpx1.symm.trans hpx2)
    have hres := ih (j - 1) (by omega) _ hkr (heq ▸ hj1r) s hs
    have hidx : j - 1 - k = j - (k + 1) := by omega
    exact hidx ▸ hres

/-- A list closed under `succ` and `pred` adjacency captures whole incidence
components: connected darts are members together. -/
private theorem conn_mem_iff {l : List D}
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hsucc_closed : ∀ x ∈ l, ∀ y, G.succ x = some y → y ∈ l)
    (hpred_closed : ∀ x ∈ l, ∀ y, G.pred x = some y → y ∈ l)
    {a b : D} (hc : IncidenceConn G a b) : a ∈ l ↔ b ∈ l := by
  induction hc with
  | refl d => exact Iff.rfl
  | succ h =>
    rename_i d e
    exact ⟨fun hd => hsucc_closed d hd e h, fun he => hpred_closed e he d (hM3a d e h)⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end ChainLists

section ConnToM6

variable {V D : Type} {G : DartGraph V D} {v : V}

/-- The open-corner construction: walking `succ` from a `pred`-open fiber
member visits each connected dart exactly once and stops at the `succ`-open
corner. -/
private theorem exists_incidenceList_open
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hM4 : ∀ d e, G.succ d = some e → G.head e = G.head d)
    {l₀ : List D} (hmem : ∀ d, d ∈ l₀ ↔ G.head d = v)
    (hconn : ∀ d₁ ∈ l₀, ∀ d₂ ∈ l₀, IncidenceConn G d₁ d₂)
    {dO : D} (hdO : dO ∈ l₀) (hpO : G.pred dO = none) :
    ∃ l, IncidenceList G v l := by
  have hchain := succChain_chain G l₀.length dO
  have hnodup : (succChain G l₀.length dO).Nodup :=
    nodup_of_chain_open hM3a hchain (succChain_head? G l₀.length dO) hpO
  have hsub : ∀ x ∈ succChain G l₀.length dO, x ∈ l₀ := fun x hx =>
    (hmem x).mpr ((succChain_head_eq hM4 l₀.length dO x hx).trans ((hmem dO).mp hdO))
  have hlen : (succChain G l₀.length dO).length < l₀.length + 1 := by
    have := length_le_of_nodup_subset hnodup hsub
    have hpos : 0 < l₀.length := List.length_pos_of_mem hdO
    omega
  obtain ⟨dl, hdl, hdlnone⟩ := succChain_terminal G l₀.length dO hlen
  have hs0read : (succChain G l₀.length dO)[0]? = some dO :=
    (List.head?_eq_getElem?).symm.trans (succChain_head? G l₀.length dO)
  have hlpos : 0 < (succChain G l₀.length dO).length :=
    (List.getElem?_eq_some_iff.mp hs0read).1
  have hlastread : (succChain G l₀.length dO)[(succChain G l₀.length dO).length - 1]? =
      some dl := (List.getLast?_eq_getElem?).symm.trans hdl
  have hsucc_closed : ∀ x ∈ succChain G l₀.length dO, ∀ y, G.succ x = some y →
      y ∈ succChain G l₀.length dO := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    by_cases hilast : i + 1 < (succChain G l₀.length dO).length
    · have hnext := hchain i _ _ (List.getElem?_eq_getElem hi)
        (List.getElem?_eq_getElem hilast)
      have hy' : y = (succChain G l₀.length dO)[i + 1]'hilast :=
        Option.some.inj (hy.symm.trans hnext)
      rw [hy']
      exact List.getElem_mem hilast
    · have hxdl : (succChain G l₀.length dO)[i]'hi = dl := by
        have hieq : i = (succChain G l₀.length dO).length - 1 := by omega
        subst hieq
        exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hlastread)
      exact nomatch (((congrArg G.succ hxdl).trans hdlnone).symm.trans hy)
  have hpred_closed : ∀ x ∈ succChain G l₀.length dO, ∀ y, G.pred x = some y →
      y ∈ succChain G l₀.length dO := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    by_cases hi0 : 0 < i
    · have hp := chain_pred hM3a hchain i hi hi0
      have hy' : y = (succChain G l₀.length dO)[i - 1]'(by omega) :=
        Option.some.inj (hy.symm.trans hp)
      rw [hy']
      exact List.getElem_mem (by omega)
    · have hieq : i = 0 := by omega
      subst hieq
      have h0 : (succChain G l₀.length dO)[0]'hi = dO :=
        Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hs0read)
      exact nomatch (((congrArg G.pred h0).trans hpO).symm.trans hy)
  refine ⟨succChain G l₀.length dO, ?_, hnodup, hchain, ?_⟩
  · intro d
    constructor
    · intro hd
      exact (hmem d).mp (hsub d hd)
    · intro hd
      have hdOmem : dO ∈ succChain G l₀.length dO := List.mem_of_getElem? hs0read
      exact (conn_mem_iff hM3a hsucc_closed hpred_closed
        (hconn d ((hmem d).mpr hd) dO hdO)).mpr hdOmem
  · intro dl' dh' hdl' hdh'
    have hdleq : dl' = dl := Option.some.inj (hdl'.symm.trans hdl)
    have hdheq : dh' = dO :=
      Option.some.inj (hdh'.symm.trans (succChain_head? G l₀.length dO))
    right
    rw [hdleq, hdheq]
    exact ⟨hdlnone, hpO⟩

/-- The cyclic construction: with no open corner in the fiber, the walk from
any member runs to full fuel, pigeonholes into a repeat, and the least return
of the start cuts out a single cycle. -/
private theorem exists_incidenceList_cyclic
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hM4 : ∀ d e, G.succ d = some e → G.head e = G.head d)
    {l₀ : List D} (hmem : ∀ d, d ∈ l₀ ↔ G.head d = v)
    (hconn : ∀ d₁ ∈ l₀, ∀ d₂ ∈ l₀, IncidenceConn G d₁ d₂)
    {s₀ : D} (hs₀ : s₀ ∈ l₀)
    (hBs : ∀ d ∈ l₀, G.succ d ≠ none) :
    ∃ l, IncidenceList G v l := by
  have hchain := succChain_chain G l₀.length s₀
  have hsub : ∀ x ∈ succChain G l₀.length s₀, x ∈ l₀ := fun x hx =>
    (hmem x).mpr ((succChain_head_eq hM4 l₀.length s₀ x hx).trans ((hmem s₀).mp hs₀))
  have hs0read : (succChain G l₀.length s₀)[0]? = some s₀ :=
    (List.head?_eq_getElem?).symm.trans (succChain_head? G l₀.length s₀)
  -- the walk runs to full fuel: a terminal corner would be `succ`-open in the fiber
  have hfull : (succChain G l₀.length s₀).length = l₀.length + 1 := by
    by_cases hlt : (succChain G l₀.length s₀).length < l₀.length + 1
    · obtain ⟨dl, hdl, hdlnone⟩ := succChain_terminal G l₀.length s₀ hlt
      have hdlmem : dl ∈ succChain G l₀.length s₀ :=
        List.mem_of_getElem? ((List.getLast?_eq_getElem?).symm.trans hdl)
      exact absurd hdlnone (hBs dl (hsub dl hdlmem))
    · have := succChain_length_le G l₀.length s₀
      omega
  -- pigeonhole: the walk repeats, and the start returns
  have hnotnodup : ¬ (succChain G l₀.length s₀).Nodup := by
    intro hnd'
    have := length_le_of_nodup_subset hnd' hsub
    omega
  obtain ⟨i, j, hi, hj, hij, heq⟩ := exists_dup_of_not_nodup hnotnodup
  have hreturn : (succChain G l₀.length s₀)[j - i]? = some s₀ :=
    chain_return hM3a hchain i j (by omega) _ (List.getElem?_eq_getElem hi)
      (heq.symm ▸ List.getElem?_eq_getElem hj) s₀ hs0read
  -- the least return cuts the cycle
  obtain ⟨m, ⟨hm1, hmret⟩, hmin⟩ := exists_minimal
    (p := fun m => 1 ≤ m ∧ (succChain G l₀.length s₀)[m]? = some s₀)
    (j - i) ⟨by omega, hreturn⟩
  have hmlen : m < (succChain G l₀.length s₀).length :=
    (List.getElem?_eq_some_iff.mp hmret).1
  have htlen : (List.take m (succChain G l₀.length s₀)).length = m := by
    rw [List.length_take]
    omega
  -- the seam: the cycle's last entry links back to the start
  have hseam : G.succ ((succChain G l₀.length s₀)[m - 1]'(by omega)) = some s₀ := by
    have hr2 : (succChain G l₀.length s₀)[m - 1 + 1]? = some s₀ := by
      have hmm : m - 1 + 1 = m := by omega
      rw [hmm]
      exact hmret
    exact hchain (m - 1) _ _ (List.getElem?_eq_getElem (by omega)) hr2
  have hmem_take : ∀ (p : Nat), p < m →
      ∀ (hple : p < (succChain G l₀.length s₀).length),
      (succChain G l₀.length s₀)[p]'hple ∈
        List.take m (succChain G l₀.length s₀) := by
    intro p hp hple
    exact List.mem_of_getElem? ((List.getElem?_take).trans
      ((if_pos hp).trans (List.getElem?_eq_getElem hple)))
  have hs0take : s₀ ∈ List.take m (succChain G l₀.length s₀) :=
    List.mem_of_getElem? ((List.getElem?_take).trans ((if_pos (by omega)).trans hs0read))
  -- chain of the prefix
  have htchain : ∀ (p : Nat) (d₁ d₂ : D),
      (List.take m (succChain G l₀.length s₀))[p]? = some d₁ →
      (List.take m (succChain G l₀.length s₀))[p + 1]? = some d₂ →
      G.succ d₁ = some d₂ := by
    intro p d₁ d₂ h1 h2
    have hp1 : p + 1 < m := by
      refine Classical.byContradiction fun hnp => ?_
      have hnone : (List.take m (succChain G l₀.length s₀))[p + 1]? = none :=
        (List.getElem?_take).trans (if_neg hnp)
      exact nomatch (hnone.symm.trans h2)
    have h1' : (succChain G l₀.length s₀)[p]? = some d₁ :=
      ((if_pos (by omega)).symm.trans ((List.getElem?_take).symm.trans h1))
    have h2' : (succChain G l₀.length s₀)[p + 1]? = some d₂ :=
      ((if_pos hp1).symm.trans ((List.getElem?_take).symm.trans h2))
    exact hchain p d₁ d₂ h1' h2'
  -- no repeats inside the cycle: an inner repeat would return the start too soon
  have htnodup : (List.take m (succChain G l₀.length s₀)).Nodup := by
    refine List.pairwise_iff_getElem.mpr ?_
    intro p q hp hq hpq heqt
    have hpm : p < m := by omega
    have hqm : q < m := by omega
    have heqc : (succChain G l₀.length s₀)[p]'(by omega) =
        (succChain G l₀.length s₀)[q]'(by omega) := by
      rw [← List.getElem_take (h := hp), ← List.getElem_take (h := hq)]
      exact heqt
    have hret := chain_return hM3a hchain p q (by omega) _
      (List.getElem?_eq_getElem (by omega))
      (heqc.symm ▸ List.getElem?_eq_getElem (by omega)) s₀ hs0read
    exact hmin (q - p) (by omega) ⟨by omega, hret⟩
  -- adjacency closure of the cycle
  have hsucc_closed : ∀ x ∈ List.take m (succChain G l₀.length s₀), ∀ y,
      G.succ x = some y → y ∈ List.take m (succChain G l₀.length s₀) := by
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hx
    have hpm : p < m := by omega
    have hxe : (List.take m (succChain G l₀.length s₀))[p]'hp =
        (succChain G l₀.length s₀)[p]'(by omega) := List.getElem_take
    have hyc : G.succ ((succChain G l₀.length s₀)[p]'(by omega)) = some y :=
      (congrArg G.succ hxe).symm.trans hy
    by_cases hpm1 : p + 1 < m
    · have hnext := hchain p _ _ (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by omega))
      have hy' : y = (succChain G l₀.length s₀)[p + 1]'(by omega) :=
        Option.some.inj (hyc.symm.trans hnext)
      rw [hy']
      exact hmem_take (p + 1) hpm1 (by omega)
    · have hpe : p = m - 1 := by omega
      subst hpe
      have hy' : y = s₀ := Option.some.inj (hyc.symm.trans hseam)
      rw [hy']
      exact hs0take
  have hpred_closed : ∀ x ∈ List.take m (succChain G l₀.length s₀), ∀ y,
      G.pred x = some y → y ∈ List.take m (succChain G l₀.length s₀) := by
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hx
    have hpm : p < m := by omega
    have hxe : (List.take m (succChain G l₀.length s₀))[p]'hp =
        (succChain G l₀.length s₀)[p]'(by omega) := List.getElem_take
    have hyc : G.pred ((succChain G l₀.length s₀)[p]'(by omega)) = some y :=
      (congrArg G.pred hxe).symm.trans hy
    by_cases hp0 : 0 < p
    · have hpp := chain_pred hM3a hchain p (by omega) hp0
      have hy' : y = (succChain G l₀.length s₀)[p - 1]'(by omega) :=
        Option.some.inj (hyc.symm.trans hpp)
      rw [hy']
      exact hmem_take (p - 1) (by omega) (by omega)
    · have hpe : p = 0 := by omega
      subst hpe
      have h0 : (succChain G l₀.length s₀)[0]'(by omega) = s₀ :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hs0read)
      have hps : G.pred s₀ = some ((succChain G l₀.length s₀)[m - 1]'(by omega)) :=
        hM3a _ _ hseam
      have hy' : y = (succChain G l₀.length s₀)[m - 1]'(by omega) :=
        Option.some.inj ((((congrArg G.pred h0).symm.trans hyc).symm.trans hps))
      rw [hy']
      exact hmem_take (m - 1) (by omega) (by omega)
  -- ends read off the prefix
  have htlast : (List.take m (succChain G l₀.length s₀)).getLast? =
      some ((succChain G l₀.length s₀)[m - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, htlen, List.getElem?_take, if_pos (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  have hthead : (List.take m (succChain G l₀.length s₀)).head? = some s₀ := by
    rw [List.head?_eq_getElem?, List.getElem?_take, if_pos (by omega)]
    exact hs0read
  refine ⟨List.take m (succChain G l₀.length s₀), ?_, htnodup, htchain, ?_⟩
  · intro d
    constructor
    · intro hd
      exact (hmem d).mp (hsub d (List.mem_of_mem_take hd))
    · intro hd
      exact (conn_mem_iff hM3a hsucc_closed hpred_closed
        (hconn d ((hmem d).mpr hd) s₀ hs₀)).mpr hs0take
  · intro dl' dh' hdl' hdh'
    have hdleq : dl' = (succChain G l₀.length s₀)[m - 1]'(by omega) :=
      Option.some.inj (hdl'.symm.trans htlast)
    have hdheq : dh' = s₀ := Option.some.inj (hdh'.symm.trans hthead)
    left
    rw [hdleq, hdheq]
    exact hseam

/-- **Unordered connectivity is all of M6** (the conversion theorem): on a
graph satisfying the pointwise M3/M4 laws, a vertex whose fiber is finitely
enumerated (duplicates allowed -- only the walk itself must not repeat) and
incidence-connected has an incidence list. The list is built by walking `succ` from the unique open corner when
one exists, else around the cycle; with no `pred`-open corner the fiber has
no `succ`-open corner either, by a backward walk on the link-reversed
graph. -/
theorem exists_incidenceList_of_conn
    (hM3a : ∀ d e, G.succ d = some e → G.pred e = some d)
    (hM3b : ∀ d e, G.pred d = some e → G.succ e = some d)
    (hM4 : ∀ d e, G.succ d = some e → G.head e = G.head d)
    {l₀ : List D} (hmem : ∀ d, d ∈ l₀ ↔ G.head d = v)
    (hconn : ∀ d₁ ∈ l₀, ∀ d₂ ∈ l₀, IncidenceConn G d₁ d₂) :
    ∃ l, IncidenceList G v l := by
  by_cases hemp : l₀ = []
  · subst hemp
    refine ⟨[], ?_, List.nodup_nil, ?_, ?_⟩
    · intro d
      constructor
      · intro h
        exact absurd h (by simp)
      · intro h
        exact absurd ((hmem d).mpr h) (by simp)
    · intro i d₁ d₂ h1 _h2
      exact absurd h1 (by simp)
    · intro dl dh hdl _hdh
      exact absurd hdl (by simp)
  · obtain ⟨s₀, hs₀⟩ : ∃ s, s ∈ l₀ := by
      cases l₀ with
      | nil => exact absurd rfl hemp
      | cons a t => exact ⟨a, by simp⟩
    by_cases hopenex : ∃ dO, dO ∈ l₀ ∧ G.pred dO = none
    · obtain ⟨dO, hdO, hpO⟩ := hopenex
      exact exists_incidenceList_open hM3a hM4 hmem hconn hdO hpO
    · -- no `pred`-open corner: the fiber has no `succ`-open corner either
      have hBs : ∀ d ∈ l₀, G.succ d ≠ none := by
        intro d hd hnone
        have hop3a : ∀ a b, G.op.succ a = some b → G.op.pred b = some a :=
          fun a b h => hM3b a b h
        have hop4 : ∀ a b, G.op.succ a = some b → G.op.head b = G.op.head a :=
          fun a b h => (hM4 b a (hM3b a b h)).symm
        have hopchain := succChain_chain G.op l₀.length d
        have hopnodup : (succChain G.op l₀.length d).Nodup :=
          nodup_of_chain_open hop3a hopchain (succChain_head? G.op l₀.length d) hnone
        have hopsub : ∀ x ∈ succChain G.op l₀.length d, x ∈ l₀ := fun x hx =>
          (hmem x).mpr ((succChain_head_eq hop4 l₀.length d x hx).trans ((hmem d).mp hd))
        by_cases hfull : (succChain G.op l₀.length d).length < l₀.length + 1
        · obtain ⟨dl, hdl, hdlnone⟩ := succChain_terminal G.op l₀.length d hfull
          have hdlmem : dl ∈ succChain G.op l₀.length d :=
            List.mem_of_getElem? ((List.getLast?_eq_getElem?).symm.trans hdl)
          exact hopenex ⟨dl, hopsub dl hdlmem, hdlnone⟩
        · have hle := length_le_of_nodup_subset hopnodup hopsub
          omega
      exact exists_incidenceList_cyclic hM3a hM4 hmem hconn hs₀ hBs

end ConnToM6

/-- `Nodup` survives an injective map (core has no `Nodup.map`). -/
private theorem nodup_map_of_injective {α β : Type} {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) {l : List α} (h : l.Nodup) :
    (l.map f).Nodup :=
  List.pairwise_map.mpr (h.imp fun hab hfeq => hab (hf _ _ hfeq))

/-- An incidence list survives relabelling, mapped through the dart
bijection. -/
theorem IncidenceList.relabel {V V' D D' : Type} {G : DartGraph V D} {v : V}
    {l : List D} (hl : IncidenceList G v l)
    (ev : TypeEquiv V V') (ed : TypeEquiv D D') :
    IncidenceList (G.relabel ev ed) (ev v) (l.map ed) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d'
    constructor
    · intro hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      rw [relabel_head, TypeEquiv.symm_apply_apply]
      exact congrArg ev ((hl.mem_iff x).mp hx)
    · intro hh
      refine List.mem_map.mpr ⟨ed.symm d', ?_, ed.right_inv d'⟩
      refine (hl.mem_iff _).mpr (ev.injective ?_)
      simpa using hh
  · exact nodup_map_of_injective (fun _ _ => ed.injective) hl.nodup
  · intro i d₁ d₂ h1 h2
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h1)
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h2)
    rw [relabel_succ, TypeEquiv.symm_apply_apply, hl.chain i x y hx hy]
    rfl
  · intro dl dh hdl hdh
    obtain ⟨xl, hxl, rfl⟩ :=
      Option.map_eq_some_iff.mp ((List.getLast?_map).symm.trans hdl)
    obtain ⟨xh, hxh, rfl⟩ :=
      Option.map_eq_some_iff.mp ((List.head?_map).symm.trans hdh)
    rcases hl.ends xl xh hxl hxh with hcyc | ⟨hsn, hpn⟩
    · exact Or.inl (by rw [relabel_succ, TypeEquiv.symm_apply_apply, hcyc]; rfl)
    · refine Or.inr ⟨?_, ?_⟩
      · rw [relabel_succ, TypeEquiv.symm_apply_apply, hsn]
        rfl
      · rw [relabel_pred, TypeEquiv.symm_apply_apply, hpn]
        rfl

/-- The rotation-system laws are representation-independent: they survive
relabelling, like `Valid.relabel`. -/
theorem Rotational.relabel {V V' D D' : Type} {G : DartGraph V D}
    (hr : G.Rotational) (ev : TypeEquiv V V') (ed : TypeEquiv D D') :
    (G.relabel ev ed).Rotational := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d e hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp
      ((relabel_succ ev ed G d).symm.trans hs)
    rw [relabel_pred, TypeEquiv.symm_apply_apply, hr.succ_pred (ed.symm d) y hy]
    simp
  · intro d e hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp
      ((relabel_pred ev ed G d).symm.trans hs)
    rw [relabel_succ, TypeEquiv.symm_apply_apply, hr.pred_succ (ed.symm d) y hy]
    simp
  · intro d e hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp
      ((relabel_succ ev ed G d).symm.trans hs)
    rw [relabel_head, relabel_head, TypeEquiv.symm_apply_apply]
    exact congrArg ev (hr.succ_head (ed.symm d) y hy)
  · intro c
    obtain ⟨l, hl⟩ := hr.incidence (ev.symm c)
    exact ⟨l.map ed, by simpa using hl.relabel ev ed⟩


/-- **The boundary-fan edit, semantically (A.4.6).** `dst` is `src` with two
new darts (the `Fin 2` tags) forming the reverse pair of the new boundary
edge, and the four fan corners `eF`/`eL`/`eFR`/`eLR` closed. Old links map
through `Sum.inl`; each closed corner records its exact target, the `eL`/`eF`
seams guarded by `eFR ≠ eL`/`eLR ≠ eF` -- the collisions a degenerate fan
allows -- alongside plain closedness facts for consumers that need no
targets. -/
structure IsBoundaryFanPatch {V D : Type} (src : DartGraph V D)
    (dst : DartGraph V (Sum D (Fin 2))) (eF eL eFR eLR : D) : Prop where
  eFR_def : src.rev eF = eFR
  eLR_def : src.rev eL = eLR
  head_eq : src.head eF = src.head eL
  head_ne : src.head eFR ≠ src.head eLR
  predF_open : (src.pred eF).isNone
  succL_open : (src.succ eL).isNone
  rev_new1 : dst.rev (.inr 0) = .inr 1
  rev_new2 : dst.rev (.inr 1) = .inr 0
  head_new1 : dst.head (.inr 0) = src.head eFR
  head_new2 : dst.head (.inr 1) = src.head eLR
  succ_new1 : (dst.succ (.inr 0)).isNone
  pred_new1 : dst.pred (.inr 0) = some (.inl eFR)
  succ_new2 : dst.succ (.inr 1) = some (.inl eLR)
  pred_new2 : (dst.pred (.inr 1)).isNone
  succ_eFR : dst.succ (.inl eFR) = some (.inr 0)
  pred_eLR : dst.pred (.inl eLR) = some (.inr 1)
  succ_eL : eFR ≠ eL → dst.succ (.inl eL) = some (.inl eF)
  pred_eF : eLR ≠ eF → dst.pred (.inl eF) = some (.inl eL)
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

namespace IsBoundaryFanPatch

/-- Shared distinctness facts of a fan patch on a valid source: the three
touched vertices are pairwise distinct and the four corners never collide
across roles. -/
theorem corner_facts {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid) :
    src.head eF ≠ src.head eFR ∧ src.head eF ≠ src.head eLR ∧
      eFR ≠ eL ∧ eLR ≠ eF ∧
      (src.succ eFR).isNone ∧ (src.pred eLR).isNone := by
  have hu : src.head eF ≠ src.head eFR := hp.eFR_def ▸ hv.loop_free eF
  have hw : src.head eF ≠ src.head eLR :=
    hp.head_eq.symm ▸ (hp.eLR_def ▸ hv.loop_free eL)
  refine ⟨hu, hw, ?_, ?_, ?_, ?_⟩
  · exact fun h => hu (hp.head_eq.trans (congrArg src.head h).symm)
  · exact fun h => hw (congrArg src.head h).symm
  · exact hp.eFR_def ▸ (hv.boundary eF).mp hp.predF_open
  · have := (hv.boundary (src.rev eL)).mpr
      (by rw [hv.rev_rev eL]; exact hp.succL_open)
    exact hp.eLR_def ▸ this

/-- An untouched vertex keeps its incidence list, mapped through `Sum.inl`:
none of its darts is a fan corner (their heads differ), so every link is
preserved verbatim. -/
theorem fan_untouched {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR) (_hv : src.Valid)
    {c : V} {lc : List D} (hlc : IncidenceList src c lc)
    (hcv : c ≠ src.head eF) (hcu : c ≠ src.head eFR) (hcw : c ≠ src.head eLR) :
    IncidenceList dst c (lc.map .inl) := by
  have hmem : ∀ d ∈ lc, d ≠ eF ∧ d ≠ eL ∧ d ≠ eFR ∧ d ≠ eLR := by
    intro d hd
    have hhd := (hlc.mem_iff d).mp hd
    exact ⟨fun h => hcv (hhd.symm.trans (congrArg src.head h)),
      fun h => hcv (hhd.symm.trans ((congrArg src.head h).trans hp.head_eq.symm)),
      fun h => hcu (hhd.symm.trans (congrArg src.head h)),
      fun h => hcw (hhd.symm.trans (congrArg src.head h))⟩
  have hsucc : ∀ d ∈ lc, dst.succ (.inl d) = (src.succ d).map .inl := fun d hd =>
    hp.succ_old d (hmem d hd).2.1 (hmem d hd).2.2.1
  have hpred : ∀ d ∈ lc, dst.pred (.inl d) = (src.pred d).map .inl := fun d hd =>
    hp.pred_old d (hmem d hd).1 (hmem d hd).2.2.2
  refine ⟨?_, nodup_map_of_injective (fun _ _ => Sum.inl.inj) hlc.nodup, ?_, ?_⟩
  · intro d'
    rcases d' with x | i
    · simpa [List.mem_map, hp.head_old] using hlc.mem_iff x
    · have hi2 : i = 0 ∨ i = 1 := by omega
      constructor
      · intro hmem'
        exact absurd hmem' (by simp [List.mem_map])
      · intro hhead
        rcases hi2 with rfl | rfl
        · exact absurd hhead.symm (hp.head_new1 ▸ hcu)
        · exact absurd hhead.symm (hp.head_new2 ▸ hcw)
  · intro i d₁ d₂ h1 h2
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h1)
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h2)
    rw [hsucc x (List.mem_of_getElem? hx), hlc.chain i x y hx hy]
    rfl
  · intro dl dh hdl hdh
    obtain ⟨xl, hxl, rfl⟩ := Option.map_eq_some_iff.mp ((List.getLast?_map).symm.trans hdl)
    obtain ⟨xh, hxh, rfl⟩ := Option.map_eq_some_iff.mp ((List.head?_map).symm.trans hdh)
    have hxl_mem := List.mem_of_getElem?
      ((List.getLast?_eq_getElem? (l := lc)).symm.trans hxl)
    have hxh_mem := List.mem_of_getElem?
      ((List.head?_eq_getElem? (l := lc)).symm.trans hxh)
    rcases hlc.ends xl xh hxl hxh with hcyc | ⟨hnone, hpnone⟩
    · left
      rw [hsucc xl hxl_mem, hcyc]
      rfl
    · right
      refine ⟨?_, ?_⟩
      · rw [hsucc xl hxl_mem, hnone]
        rfl
      · rw [hpred xh hxh_mem, hpnone]
        rfl

/-- The selected vertex's list closes into a cycle: `eF` sits at its head
(`pred`-open), `eL` at its end (`succ`-open), interior links are preserved,
and the new seam `succ eL = eF` joins the ends -- the vertex becomes inner.
This is the paper's page-32 flip argument, list-form. -/
theorem fan_v {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR)
    (hv : src.Valid) (hr : src.Rotational)
    {lv : List D} (hlv : IncidenceList src (src.head eF) lv) :
    IncidenceList dst (src.head eF) (lv.map .inl) := by
  obtain ⟨hu, hw, hFRneL, hLRneF, -, -⟩ := hp.corner_facts hv
  have heF_mem : eF ∈ lv := (hlv.mem_iff eF).mpr rfl
  have heL_mem : eL ∈ lv := (hlv.mem_iff eL).mpr hp.head_eq.symm
  obtain ⟨iF, hiF, hiFeq⟩ := List.mem_iff_getElem.mp heF_mem
  obtain ⟨iL, hiL, hiLeq⟩ := List.mem_iff_getElem.mp heL_mem
  have hiF0 : iF = 0 := hr.pred_none_first hlv hiF
    (hiFeq.symm ▸ Option.isNone_iff_eq_none.mp hp.predF_open)
  have hiLlast : iL = lv.length - 1 := hlv.succ_none_last hiL
    (hiLeq.symm ▸ Option.isNone_iff_eq_none.mp hp.succL_open)
  subst hiF0 hiLlast
  have hne_fr : ∀ d ∈ lv, d ≠ eFR := fun d hd h =>
    hu (((hlv.mem_iff d).mp hd).symm.trans (congrArg src.head h))
  refine ⟨?_, nodup_map_of_injective (fun _ _ => Sum.inl.inj) hlv.nodup, ?_, ?_⟩
  · intro d'
    rcases d' with x | i
    · simpa [List.mem_map, hp.head_old] using hlv.mem_iff x
    · have hi2 : i = 0 ∨ i = 1 := by omega
      constructor
      · intro hmem'
        exact absurd hmem' (by simp [List.mem_map])
      · intro hhead
        rcases hi2 with rfl | rfl
        · exact absurd (hhead.symm.trans hp.head_new1) hu
        · exact absurd (hhead.symm.trans hp.head_new2) hw
  · intro i d₁ d₂ h1 h2
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h1)
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h2)
    obtain ⟨hlt1, hxeq⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hlt2, -⟩ := List.getElem?_eq_some_iff.mp hy
    have hxne : x ≠ eL := by
      intro h
      have hidx : i = lv.length - 1 :=
        (List.getElem_inj hlv.nodup).mp (hxeq.trans (h.trans hiLeq.symm))
      omega
    rw [hp.succ_old x hxne (hne_fr x (List.mem_of_getElem? hx)), hlv.chain i x y hx hy]
    rfl
  · intro dl dh hdl hdh
    obtain ⟨xl, hxl, rfl⟩ := Option.map_eq_some_iff.mp ((List.getLast?_map).symm.trans hdl)
    obtain ⟨xh, hxh, rfl⟩ := Option.map_eq_some_iff.mp ((List.head?_map).symm.trans hdh)
    have hxl_eq : xl = eL := by
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp
        ((List.getLast?_eq_getElem? (l := lv)).symm.trans hxl)
      exact hget.symm.trans hiLeq
    have hxh_eq : xh = eF := by
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp
        ((List.head?_eq_getElem? (l := lv)).symm.trans hxh)
      exact hget.symm.trans hiFeq
    subst hxl_eq hxh_eq
    exact Or.inl (hp.succ_eL hFRneL)

/-- The far vertex `u` of the new edge gains the first new dart at the end
of its list: its old last corner `eFR` closes onto the new dart, which is
the new open corner. -/
theorem fan_u {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid)
    {lu : List D} (hlu : IncidenceList src (src.head eFR) lu) :
    IncidenceList dst (src.head eFR) (lu.map .inl ++ [.inr 0]) := by
  obtain ⟨hu, hw, hFRneL, hLRneF, hsFRnone, hpLRnone⟩ := hp.corner_facts hv
  have heFR_mem : eFR ∈ lu := (hlu.mem_iff eFR).mpr rfl
  obtain ⟨iR, hiR, hiReq⟩ := List.mem_iff_getElem.mp heFR_mem
  have hiRlast : iR = lu.length - 1 := hlu.succ_none_last hiR
    (hiReq.symm ▸ Option.isNone_iff_eq_none.mp hsFRnone)
  subst hiRlast
  have hmemg : ∀ d ∈ lu, d ≠ eF ∧ d ≠ eL ∧ d ≠ eLR := by
    intro d hd
    have hhd := (hlu.mem_iff d).mp hd
    exact ⟨fun h => hu ((congrArg src.head h).symm.trans hhd),
      fun h => hu (hp.head_eq.trans ((congrArg src.head h).symm.trans hhd)),
      fun h => hp.head_ne (hhd.symm.trans (congrArg src.head h))⟩
  have hlen : 0 < lu.length := List.length_pos_of_mem heFR_mem
  -- The source list is open: its last corner is `succ`-open.
  have hopen : src.pred (lu[0]'hlen) = none := by
    have hlast : lu.getLast? = some (lu[lu.length - 1]'hiR) := by
      rw [List.getLast?_eq_getElem?]
      exact List.getElem?_eq_getElem hiR
    have hhead : lu.head? = some (lu[0]'hlen) := by
      rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem hlen
    rcases hlu.ends _ _ hlast hhead with hcyc | ⟨-, hpn⟩
    · exact nomatch
        ((hiReq ▸ Option.isNone_iff_eq_none.mp hsFRnone).symm.trans hcyc)
    · exact hpn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d'
    rcases d' with x | i
    · constructor
      · intro hm
        have hm' : x ∈ lu := by
          rcases List.mem_append.mp hm with h | h
          · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h
            exact (Sum.inl.inj hyx) ▸ hy
          · exact absurd h (by simp)
        exact (hp.head_old x).trans ((hlu.mem_iff x).mp hm')
      · intro hh
        refine List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x, ?_, rfl⟩))
        exact (hlu.mem_iff x).mpr ((hp.head_old x).symm.trans hh)
    · have hi2 : i = 0 ∨ i = 1 := by omega
      constructor
      · intro hm
        rcases hi2 with rfl | rfl
        · exact hp.head_new1
        · rcases List.mem_append.mp hm with h | h
          · exact absurd h (by simp [List.mem_map])
          · exact absurd h (by simp)
      · intro hh
        rcases hi2 with rfl | rfl
        · simp
        · exact absurd (hh.symm.trans hp.head_new2) hp.head_ne
  · rw [List.nodup_append]
    refine ⟨nodup_map_of_injective (fun _ _ => Sum.inl.inj) hlu.nodup, by simp, ?_⟩
    intro d' hm e' hm'
    rcases List.mem_map.mp hm with ⟨x, -, rfl⟩
    cases List.mem_singleton.mp hm'
    exact fun h => nomatch h
  · intro i d₁ d₂ h1 h2
    by_cases hin : i + 1 < lu.length
    · have h1' : (lu.map .inl)[i]? = some d₁ :=
        (List.getElem?_append_left (by simp only [List.length_map]; omega)).symm.trans h1
      have h2' : (lu.map .inl)[i + 1]? = some d₂ :=
        (List.getElem?_append_left (by simp only [List.length_map]; omega)).symm.trans h2
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h1')
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h2')
      have hxne : x ≠ eFR := by
        intro h
        obtain ⟨hlt1, hxeq⟩ := List.getElem?_eq_some_iff.mp hx
        have : i = lu.length - 1 :=
          (List.getElem_inj hlu.nodup).mp (hxeq.trans (h.trans hiReq.symm))
        omega
      rw [hp.succ_old x (hmemg x (List.mem_of_getElem? hx)).2.1 hxne,
        hlu.chain i x y hx hy]
      rfl
    · by_cases hi : i < lu.length
      · -- the seam: the mapped last element links to the appended new dart
        have hieq : i = lu.length - 1 := by omega
        subst hieq
        have h1' : (lu.map .inl)[lu.length - 1]? = some d₁ :=
          (List.getElem?_append_left (by simp only [List.length_map]; omega)).symm.trans h1
        obtain ⟨x, hx, rfl⟩ :=
          Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h1')
        obtain ⟨hlt1, hxeq⟩ := List.getElem?_eq_some_iff.mp hx
        have hxeFR : x = eFR := hxeq.symm.trans hiReq
        subst hxeFR
        have hsome : (lu.map (Sum.inl : D → Sum D (Fin 2)) ++ [.inr 0])[lu.length - 1 + 1]? =
            some (Sum.inr 0) := by
          have hix : lu.length - 1 + 1 = (lu.map (Sum.inl : D → Sum D (Fin 2))).length := by
            simp only [List.length_map]; omega
          rw [hix, List.getElem?_append_right (Nat.le_refl _)]
          simp
        have hd2 : d₂ = Sum.inr 0 := Option.some.inj (h2.symm.trans hsome)
        subst hd2
        exact hp.succ_eFR
      · -- reads past the appended element cannot both succeed
        have hnone : (lu.map (Sum.inl : D → Sum D (Fin 2)) ++ [.inr 0])[i + 1]? = none :=
          List.getElem?_eq_none (by
            simp only [List.length_append, List.length_map, List.length_cons,
              List.length_nil]
            omega)
        exact nomatch (hnone.symm.trans h2)
  · intro dl dh hdl hdh
    have hdl' : dl = Sum.inr 0 :=
      (Option.some.inj ((List.getLast?_concat).symm.trans hdl)).symm
    have hh0 : (lu.map (Sum.inl : D → Sum D (Fin 2)) ++ [Sum.inr 0]).head? =
        some (Sum.inl (lu[0]'hlen)) := by
      rw [List.head?_eq_getElem?,
        List.getElem?_append_left (by simp only [List.length_map]; omega),
        List.getElem?_map, List.getElem?_eq_getElem hlen]
      rfl
    have hdh' : dh = Sum.inl (lu[0]'hlen) := Option.some.inj (hdh.symm.trans hh0)
    subst hdl' hdh'
    right
    refine ⟨Option.isNone_iff_eq_none.mp hp.succ_new1, ?_⟩
    rw [hp.pred_old _ (hmemg _ (List.getElem_mem hlen)).1
      (hmemg _ (List.getElem_mem hlen)).2.2, hopen]
    rfl

/-- The near vertex `w` of the new edge gains the second new dart at the
front of its list: the new dart is the new open corner and closes onto the
old first corner `eLR`. -/
theorem fan_w {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid)
    (hr : src.Rotational) {lw : List D}
    (hlw : IncidenceList src (src.head eLR) lw) :
    IncidenceList dst (src.head eLR) (.inr 1 :: lw.map .inl) := by
  obtain ⟨hu, hw, hFRneL, hLRneF, hsFRnone, hpLRnone⟩ := hp.corner_facts hv
  have heLR_mem : eLR ∈ lw := (hlw.mem_iff eLR).mpr rfl
  obtain ⟨i0, hi0lt, hi0eq⟩ := List.mem_iff_getElem.mp heLR_mem
  have hi00 : i0 = 0 := hr.pred_none_first hlw hi0lt
    (hi0eq.symm ▸ Option.isNone_iff_eq_none.mp hpLRnone)
  subst hi00
  have hmemg : ∀ d ∈ lw, d ≠ eF ∧ d ≠ eL ∧ d ≠ eFR := by
    intro d hd
    have hhd := (hlw.mem_iff d).mp hd
    exact ⟨fun h => hw ((congrArg src.head h).symm.trans hhd),
      fun h => hw (hp.head_eq.trans ((congrArg src.head h).symm.trans hhd)),
      fun h => hp.head_ne ((congrArg src.head h).symm.trans hhd)⟩
  have hlt : lw.length - 1 < lw.length := by omega
  -- The source list is open: were it cyclic, `eLR` would have a predecessor.
  have hwopen : src.succ (lw[lw.length - 1]'hlt) = none := by
    have hlast : lw.getLast? = some (lw[lw.length - 1]'hlt) := by
      rw [List.getLast?_eq_getElem?]
      exact List.getElem?_eq_getElem hlt
    have hhead : lw.head? = some (lw[0]'hi0lt) := by
      rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem hi0lt
    rcases hlw.ends _ _ hlast hhead with hcyc | ⟨hsn, -⟩
    · have hpred : src.pred eLR = some (lw[lw.length - 1]'hlt) :=
        hi0eq ▸ hr.succ_pred _ _ hcyc
      exact nomatch ((Option.isNone_iff_eq_none.mp hpLRnone).symm.trans hpred)
    · exact hsn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d'
    rcases d' with x | i
    · constructor
      · intro hm
        have hm' : x ∈ lw := by
          rcases List.mem_cons.mp hm with h | h
          · exact nomatch h
          · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h
            exact (Sum.inl.inj hyx) ▸ hy
        exact (hp.head_old x).trans ((hlw.mem_iff x).mp hm')
      · intro hh
        exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
          ⟨x, (hlw.mem_iff x).mpr ((hp.head_old x).symm.trans hh), rfl⟩))
    · have hi2 : i = 0 ∨ i = 1 := by omega
      constructor
      · intro hm
        rcases hi2 with rfl | rfl
        · rcases List.mem_cons.mp hm with h | h
          · exact absurd (Sum.inr.inj h) (by decide)
          · exact absurd h (by simp [List.mem_map])
        · exact hp.head_new2
      · intro hh
        rcases hi2 with rfl | rfl
        · exact absurd (hp.head_new1.symm.trans hh) hp.head_ne
        · exact List.mem_cons.mpr (Or.inl rfl)
  · rw [List.nodup_cons]
    refine ⟨?_, nodup_map_of_injective (fun _ _ => Sum.inl.inj) hlw.nodup⟩
    intro hm
    obtain ⟨y, -, hyx⟩ := List.mem_map.mp hm
    exact nomatch hyx
  · intro i d₁ d₂ h1 h2
    by_cases hi0 : i = 0
    · subst hi0
      have hd1 : d₁ = Sum.inr 1 :=
        (Option.some.inj ((List.getElem?_cons_zero).symm.trans h1)).symm
      have h2' : (lw.map (Sum.inl : D → Sum D (Fin 2)))[0]? = some d₂ :=
        (List.getElem?_cons_succ).symm.trans h2
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h2')
      obtain ⟨hlt', hyeq⟩ := List.getElem?_eq_some_iff.mp hy
      have hyeLR : y = eLR := hyeq.symm.trans hi0eq
      subst hd1 hyeLR
      exact hp.succ_new2
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have h1' : (lw.map (Sum.inl : D → Sum D (Fin 2)))[j]? = some d₁ :=
        (List.getElem?_cons_succ).symm.trans h1
      have h2' : (lw.map (Sum.inl : D → Sum D (Fin 2)))[j + 1]? = some d₂ :=
        (List.getElem?_cons_succ).symm.trans h2
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h1')
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp ((List.getElem?_map).symm.trans h2')
      rw [hp.succ_old x (hmemg x (List.mem_of_getElem? hx)).2.1
        (hmemg x (List.mem_of_getElem? hx)).2.2, hlw.chain j x y hx hy]
      rfl
  · intro dl dh hdl hdh
    have hmapne : lw.map (Sum.inl : D → Sum D (Fin 2)) ≠ [] := by
      cases lw with
      | nil => exact absurd hi0lt (by simp)
      | cons a l => simp
    have hmaplast : (lw.map (Sum.inl : D → Sum D (Fin 2))).getLast? =
        some (Sum.inl (lw[lw.length - 1]'hlt)) := by
      rw [List.getLast?_eq_getElem?, List.length_map, List.getElem?_map,
        List.getElem?_eq_getElem hlt]
      rfl
    have hdl' : dl = Sum.inl (lw[lw.length - 1]'hlt) :=
      Option.some.inj (((List.getLast?_cons_of_ne_nil hmapne).symm.trans hdl).symm.trans hmaplast)
    have hdh' : dh = Sum.inr 1 :=
      (Option.some.inj ((List.head?_cons).symm.trans hdh)).symm
    subst hdl' hdh'
    right
    refine ⟨?_, Option.isNone_iff_eq_none.mp hp.pred_new2⟩
    rw [hp.succ_old _ (hmemg _ (List.getElem_mem hlt)).2.1
      (hmemg _ (List.getElem_mem hlt)).2.2, hwopen]
    rfl

/-- **The boundary-fan edit preserves the rotation-system laws.** The two
new darts splice into the fans of `u` and `w` exactly once each -- `succ` and
`pred` stay mutually inverse and `head`-preserving pointwise, and every
vertex keeps a single incidence list via the four fan lemmas. -/
theorem rotational {V D : Type} {src : DartGraph V D}
    {dst : DartGraph V (Sum D (Fin 2))} {eF eL eFR eLR : D}
    (hp : IsBoundaryFanPatch src dst eF eL eFR eLR) (hv : src.Valid)
    (hr : src.Rotational) : dst.Rotational := by
  obtain ⟨hu, hw, hFRneL, hLRneF, hsFRnone, hpLRnone⟩ := hp.corner_facts hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d e hs
    rcases d with x | i
    · by_cases hxFR : x = eFR
      · subst hxFR
        have he : e = Sum.inr 0 := Option.some.inj (hs.symm.trans hp.succ_eFR)
        subst he
        exact hp.pred_new1
      · by_cases hxL : x = eL
        · subst hxL
          have he : e = Sum.inl eF := Option.some.inj (hs.symm.trans (hp.succ_eL hFRneL))
          subst he
          exact hp.pred_eF hLRneF
        · have hs' := (hp.succ_old x hxL hxFR).symm.trans hs
          obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs'
          have hpy := hr.succ_pred x y hy
          have hyF : y ≠ eF := fun h => nomatch (hpy.symm.trans
            ((congrArg src.pred h).trans (Option.isNone_iff_eq_none.mp hp.predF_open)))
          have hyLR : y ≠ eLR := fun h => nomatch (hpy.symm.trans
            ((congrArg src.pred h).trans (Option.isNone_iff_eq_none.mp hpLRnone)))
          rw [hp.pred_old y hyF hyLR, hpy]
          rfl
    · have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · exact nomatch ((Option.isNone_iff_eq_none.mp hp.succ_new1).symm.trans hs)
      · have he : e = Sum.inl eLR := Option.some.inj (hs.symm.trans hp.succ_new2)
        subst he
        exact hp.pred_eLR
  · intro d e hs
    rcases d with x | i
    · by_cases hxF : x = eF
      · subst hxF
        have he : e = Sum.inl eL := Option.some.inj (hs.symm.trans (hp.pred_eF hLRneF))
        subst he
        exact hp.succ_eL hFRneL
      · by_cases hxLR : x = eLR
        · subst hxLR
          have he : e = Sum.inr 1 := Option.some.inj (hs.symm.trans hp.pred_eLR)
          subst he
          exact hp.succ_new2
        · have hs' := (hp.pred_old x hxF hxLR).symm.trans hs
          obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs'
          have hsy := hr.pred_succ x y hy
          have hyL : y ≠ eL := fun h => nomatch (hsy.symm.trans
            ((congrArg src.succ h).trans (Option.isNone_iff_eq_none.mp hp.succL_open)))
          have hyFR : y ≠ eFR := fun h => nomatch (hsy.symm.trans
            ((congrArg src.succ h).trans (Option.isNone_iff_eq_none.mp hsFRnone)))
          rw [hp.succ_old y hyL hyFR, hsy]
          rfl
    · have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · have he : e = Sum.inl eFR := Option.some.inj (hs.symm.trans hp.pred_new1)
        subst he
        exact hp.succ_eFR
      · exact nomatch ((Option.isNone_iff_eq_none.mp hp.pred_new2).symm.trans hs)
  · intro d e hs
    rcases d with x | i
    · by_cases hxFR : x = eFR
      · subst hxFR
        have he : e = Sum.inr 0 := Option.some.inj (hs.symm.trans hp.succ_eFR)
        subst he
        exact hp.head_new1.trans (hp.head_old _).symm
      · by_cases hxL : x = eL
        · subst hxL
          have he : e = Sum.inl eF := Option.some.inj (hs.symm.trans (hp.succ_eL hFRneL))
          subst he
          exact (hp.head_old eF).trans (hp.head_eq.trans (hp.head_old _).symm)
        · have hs' := (hp.succ_old x hxL hxFR).symm.trans hs
          obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs'
          exact (hp.head_old y).trans ((hr.succ_head x y hy).trans (hp.head_old x).symm)
    · have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · exact nomatch ((Option.isNone_iff_eq_none.mp hp.succ_new1).symm.trans hs)
      · have he : e = Sum.inl eLR := Option.some.inj (hs.symm.trans hp.succ_new2)
        subst he
        exact (hp.head_old eLR).trans hp.head_new2.symm
  · intro v
    by_cases hvF : v = src.head eF
    · subst hvF
      obtain ⟨lv, hlv⟩ := hr.incidence (src.head eF)
      exact ⟨_, hp.fan_v hv hr hlv⟩
    · by_cases hvU : v = src.head eFR
      · subst hvU
        obtain ⟨lu, hlu⟩ := hr.incidence (src.head eFR)
        exact ⟨_, hp.fan_u hv hlu⟩
      · by_cases hvW : v = src.head eLR
        · subst hvW
          obtain ⟨lw, hlw⟩ := hr.incidence (src.head eLR)
          exact ⟨_, hp.fan_w hv hr hlw⟩
        · obtain ⟨lc, hlc⟩ := hr.incidence v
          exact ⟨_, hp.fan_untouched hv hlc hvF hvU hvW⟩

end IsBoundaryFanPatch

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

/-- **M3 transfers through a quotient, `succ` side**: a closed destination
corner comes from some closed source corner of the class (`succ_from`), and
the source inverse collapses back onto the class. `IsQuotientMap` describes
finished quotients only, so the intermediate gluing states that break M3
never appear here. -/
theorem IsQuotientMap.succ_pred {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (hr : src.Rotational) :
    ∀ c e, dst.succ c = some e → dst.pred e = some c := by
  intro c e hs
  obtain ⟨d, rfl⟩ := hq.qd_surj c
  obtain ⟨d', hd', hns⟩ := hq.succ_from d (by simp [hs])
  cases hcs : src.succ d' with
  | none => exact absurd (by simp [hcs]) hns
  | some s =>
    have h2 : dst.succ (qd d) = some (qd s) :=
      (congrArg dst.succ hd').symm.trans (hq.succ_of d' s hcs)
    have he : e = qd s := Option.some.inj (hs.symm.trans h2)
    subst he
    exact (hq.pred_of s d' (hr.succ_pred d' s hcs)).trans (congrArg some hd')

/-- As `IsQuotientMap.succ_pred`, for the `pred` side of M3. -/
theorem IsQuotientMap.pred_succ {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (hr : src.Rotational) :
    ∀ c e, dst.pred c = some e → dst.succ e = some c := by
  intro c e hs
  obtain ⟨d, rfl⟩ := hq.qd_surj c
  obtain ⟨d', hd', hns⟩ := hq.pred_from d (by simp [hs])
  cases hcs : src.pred d' with
  | none => exact absurd (by simp [hcs]) hns
  | some p =>
    have h2 : dst.pred (qd d) = some (qd p) :=
      (congrArg dst.pred hd').symm.trans (hq.pred_of d' p hcs)
    have he : e = qd p := Option.some.inj (hs.symm.trans h2)
    subst he
    exact (hq.succ_of p d' (hr.pred_succ d' p hcs)).trans (congrArg some hd')

/-- **M4 transfers through a quotient**: the destination `succ` link stays
within the class's head vertex, because the source link does and `head_eq`
collapses both heads the same way. -/
theorem IsQuotientMap.succ_head {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (hr : src.Rotational) :
    ∀ c e, dst.succ c = some e → dst.head e = dst.head c := by
  intro c e hs
  obtain ⟨d, rfl⟩ := hq.qd_surj c
  obtain ⟨d', hd', hns⟩ := hq.succ_from d (by simp [hs])
  cases hcs : src.succ d' with
  | none => exact absurd (by simp [hcs]) hns
  | some s =>
    have h2 : dst.succ (qd d) = some (qd s) :=
      (congrArg dst.succ hd').symm.trans (hq.succ_of d' s hcs)
    have he : e = qd s := Option.some.inj (hs.symm.trans h2)
    subst he
    calc dst.head (qd s) = qv (src.head s) := hq.head_eq s
      _ = qv (src.head d') := congrArg qv (hr.succ_head d' s hcs)
      _ = dst.head (qd d') := (hq.head_eq d').symm
      _ = dst.head (qd d) := congrArg dst.head hd'

/-- Connectivity available to a quotient: the equivalence closure of source
`succ` adjacency together with collapse-map equality. The gluing loop
maintains this per merged vertex class; it is exactly what a finished
quotient needs to recover destination incidence connectivity. -/
inductive QuotientConn {V D D' : Type} (src : DartGraph V D) (qd : D → D') :
    D → D → Prop
  | refl (d : D) : QuotientConn src qd d d
  | succ {d e : D} : src.succ d = some e → QuotientConn src qd d e
  | collapse {d e : D} : qd d = qd e → QuotientConn src qd d e
  | symm {d e : D} : QuotientConn src qd d e → QuotientConn src qd e d
  | trans {d e f : D} : QuotientConn src qd d e → QuotientConn src qd e f →
      QuotientConn src qd d f

/-- Quotient connectivity collapses onto destination incidence connectivity:
`succ` steps push through `succ_of`, and collapse steps become reflexive. -/
theorem QuotientConn.map {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) {a b : D}
    (h : QuotientConn src qd a b) : IncidenceConn dst (qd a) (qd b) := by
  induction h with
  | refl d => exact .refl _
  | succ hs => exact .succ (hq.succ_of _ _ hs)
  | collapse hc => exact hc ▸ .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Quotient connectivity transports to any collapse map with a coarser
kernel: only the `collapse` generator mentions the map. -/
theorem QuotientConn.mono {V D D' D'' : Type} {src : DartGraph V D}
    {qd : D → D'} {qd' : D → D''}
    (hker : ∀ x y, qd x = qd y → qd' x = qd' y) {a b : D}
    (h : QuotientConn src qd a b) : QuotientConn src qd' a b := by
  induction h with
  | refl d => exact .refl d
  | succ hs => exact .succ hs
  | collapse hc => exact .collapse (hker _ _ hc)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A quotient with connected fibers preserves the rotation laws.** M3/M4
transfer pointwise; each destination fiber, enumerated from a finite dart
universe, is incidence-connected by `fiber_conn`, and the conversion theorem
rebuilds its single incidence list. -/
theorem IsQuotientMap.rotational {V D V' D' : Type} {src : DartGraph V D}
    {dst : DartGraph V' D'} {qv : V → V'} {qd : D → D'}
    (hq : IsQuotientMap src dst qv qd) (hr : src.Rotational)
    (hfib : ∀ a b, qv (src.head a) = qv (src.head b) → QuotientConn src qd a b)
    {univ : List D'} (huniv : ∀ c : D', c ∈ univ) :
    dst.Rotational := by
  refine ⟨hq.succ_pred hr, hq.pred_succ hr, hq.succ_head hr, ?_⟩
  intro v'
  haveI := Classical.typeDecidableEq V'
  refine exists_incidenceList_of_conn (hq.succ_pred hr) (hq.pred_succ hr)
    (hq.succ_head hr) (l₀ := univ.filter (fun c => dst.head c = v')) ?_ ?_
  · intro d
    rw [List.mem_filter]
    simp [huniv d]
  · intro c₁ h1 c₂ h2
    have hh1 : dst.head c₁ = v' := by
      have := (List.mem_filter.mp h1).2
      simpa using this
    have hh2 : dst.head c₂ = v' := by
      have := (List.mem_filter.mp h2).2
      simpa using this
    obtain ⟨a, rfl⟩ := hq.qd_surj c₁
    obtain ⟨b, rfl⟩ := hq.qd_surj c₂
    have hab : qv (src.head a) = qv (src.head b) :=
      (hq.head_eq a).symm.trans ((hh1.trans hh2.symm).trans (hq.head_eq b))
    exact (hfib a b hab).map hq

end DartGraph
end NearLinear4ct
