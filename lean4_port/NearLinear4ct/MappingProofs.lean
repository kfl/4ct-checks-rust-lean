import NearLinear4ct.Mapping

/-!
The `IndexMap` specification and its laws.

A **well-formed** `IndexMap` represents a total function
`Fin dom → Option (Fin codom)` -- the paper's `ϕ★ : X → Y ∪ {⊥}` for finite
index sets (Algorithm A.2.1, line 1). This module makes that a theorem: `WF`
is the well-formedness predicate, `toFun` the machine-checked decode, and the
laws below pin the meaning of the three map combinators --
`Mappings.initialMappings` is the paper's `id_X` (A.4.4), `composeMap` is
Kleisli composition (the paper's `φ̃ ∘ φ★`, A.4.3), and `splitMap` is
restriction along a domain decomposition. Proofs live here so `Mapping.lean`
keeps reading like the paper (the `UtilProofs` precedent).

Specification vocabulary is `Nat`-with-bounds (`idx?`, `Bounded`); `Fin`
appears only in the decode. `Bounded` is factored out of `WF` because the hot
discharge (`composeMap`'s internal `map2[j.idx!]!`) needs only
`map1.Bounded map2.size` -- `idx?_composeMap` proves that read's panic branch
dead. Note `idx?_composeMap` is *stated* under `Bounded` deliberately: the
equation would hold vacuously without it (an out-of-range `!` read yields the
default `OptIdx.none`, which `bind` absorbs), but the `Bounded` form is the
one that carries the panic-branch-dead content -- do not "generalise" it away.
-/

namespace NearLinear4ct
namespace IndexMap

/-- Functional model: the partial function an `IndexMap` denotes.
`none` when unmapped or out of range. No `!`. -/
def idx? (m : IndexMap) (i : Nat) : Option Nat :=
  if h : i < m.size then (m[i]'h).get? else Option.none

/-- Every mapped entry lands below `codom`. -/
def Bounded (m : IndexMap) (codom : Nat) : Prop :=
  ∀ i (h : i < m.size) j, (m[i]'h).get? = Option.some j → j < codom

/-- Well-formed map from an index set of size `dom` into one of size `codom` --
the paper's `ϕ : X → Y ∪ {⊥}` for finite index sets (Algorithm A.2.1 line 1). -/
structure WF (m : IndexMap) (dom codom : Nat) : Prop where
  size_eq : m.size = dom
  bounded : m.Bounded codom

/-- No `⊥` entries (Algorithm A.3.1 line 40: the free-homomorphism map is
total). Stated separately from `WF`: the paper separates the A.2.1-partial
maps from the A.3.1-total ones. -/
def Total (m : IndexMap) : Prop := ∀ i (h : i < m.size), (m[i]'h).isSome

/-- Executable well-formedness check (`Test.lean` tripwires; boundary
`proofAssert` if an `IndexMap` ever crosses the I/O boundary). -/
def wfCheck (m : IndexMap) (dom codom : Nat) : Bool :=
  m.size == dom && m.all (fun o => decide (o.raw ≤ codom))

/-! ### Plumbing -/

/-- The in-range `idx?` read, folded. -/
theorem idx?_pos {m : IndexMap} {i : Nat} (h : i < m.size) :
    m.idx? i = (m[i]'h).get? := dif_pos h

/-- The out-of-range `idx?` read, folded. -/
theorem idx?_neg {m : IndexMap} {i : Nat} (h : ¬ i < m.size) :
    m.idx? i = Option.none := dif_neg h

theorem wf_iff {m : IndexMap} {dom codom : Nat} :
    m.WF dom codom ↔ m.size = dom ∧ m.Bounded codom :=
  ⟨fun h => ⟨h.size_eq, h.bounded⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `Bounded` in terms of the raw encoding (`raw 0 = none`;
`raw (j+1) ≤ codom ↔ j < codom`). -/
theorem bounded_iff_raw_le {m : IndexMap} {codom : Nat} :
    m.Bounded codom ↔ ∀ i (h : i < m.size), (m[i]'h).raw ≤ codom := by
  simp [Bounded, OptIdx.raw_le_iff_get?_lt]

/-- The executable check decides `WF`. -/
theorem wfCheck_iff {m : IndexMap} {dom codom : Nat} :
    m.wfCheck dom codom = true ↔ m.WF dom codom := by
  rw [wf_iff, bounded_iff_raw_le, wfCheck, Bool.and_eq_true]
  simp

theorem idx?_eq_some_iff {m : IndexMap} {i j : Nat} :
    m.idx? i = Option.some j ↔ ∃ h : i < m.size, (m[i]'h).get? = Option.some j := by
  grind [idx?]

theorem idx?_lt_of_bounded {m : IndexMap} {codom i j : Nat}
    (hb : m.Bounded codom) (hj : m.idx? i = Option.some j) : j < codom := by
  grind [Bounded, idx?_eq_some_iff]

theorem bounded_iff_idx?_lt {m : IndexMap} {codom : Nat} :
    m.Bounded codom ↔ ∀ i j, m.idx? i = Option.some j → j < codom := by
  constructor
  · intro hb i j hj
    exact idx?_lt_of_bounded hb hj
  · intro h i hi j hj
    apply h i j
    rw [idx?_eq_some_iff]
    exact ⟨hi, hj⟩

/-! ### The decode: a WF `IndexMap` *is* a function between finite index sets -/

/-- The partial function `Fin dom → Option (Fin codom)` a well-formed
`IndexMap` denotes -- the fidelity payoff: "represents the paper's `ϕ★`" is a
theorem, not a comment. -/
def toFun (m : IndexMap) (h : m.WF dom codom) (i : Fin dom) : Option (Fin codom) :=
  (m[i.val]'(h.size_eq.symm ▸ i.isLt)).toFin? (h.bounded i.val _)

/-- Coherence: `toFun` is `idx?` under `Fin.val` -- every `toFun` theorem is a
transport of an `idx?` theorem (all real proving happens once, at the `idx?`
level). -/
theorem toFun_val {m : IndexMap} (h : m.WF dom codom) (i : Fin dom) :
    (m.toFun h i).map Fin.val = m.idx? i.val := by
  have hi : i.val < m.size := h.size_eq.symm ▸ i.isLt
  unfold toFun idx?
  rw [dif_pos hi]
  simp

theorem isSome_toFun {m : IndexMap} (h : m.WF dom codom) (ht : m.Total) (i : Fin dom) :
    (m.toFun h i).isSome := by
  have hi : i.val < m.size := h.size_eq.symm ▸ i.isLt
  have hs := ht i.val hi
  rw [OptIdx.isSome_eq] at hs
  unfold toFun
  simpa using hs

/-- The total decode, for maps with no `⊥` entries (A.3.1). -/
def toTotalFun (m : IndexMap) (h : m.WF dom codom) (ht : m.Total) (i : Fin dom) :
    Fin codom := (m.toFun h i).get (isSome_toFun h ht i)

/-- `Option (Fin _)` values are determined by their `val` images (the transport
tool for the decode theorems). -/
private theorem option_fin_val_inj {k : Nat} {a b : Option (Fin k)}
    (h : a.map Fin.val = b.map Fin.val) : a = b := by
  cases a <;> cases b <;> simp_all [Fin.ext_iff]

end IndexMap

/-! ### `Mappings` well-formedness (four `Nat`s: must not mention graphs) -/

/-- Both maps well-formed: `vmap : n → n'` and `dmap : d → d'`. -/
structure Mappings.WF (ms : Mappings) (n d n' d' : Nat) : Prop where
  vmap_wf : ms.vmap.WF n n'
  dmap_wf : ms.dmap.WF d d'

section

open IndexMap

/-! ### L1 -- `initialMappings` is the paper's `id_X` (A.4.4) -/

@[simp] theorem getElem_range_map_some {n i : Nat} (h : i < ((Array.range n).map OptIdx.some).size) :
    ((Array.range n).map OptIdx.some)[i]'h = OptIdx.some i := by
  simp_all

theorem range_map_some_wf {n codom : Nat} {f : Nat → Nat}
    (hf : ∀ i, i < n → f i < codom) :
    WF ((Array.range n).map fun i => OptIdx.some (f i)) n codom := by
  constructor
  · simp
  · intro i h j hj
    simp at hj
    subst hj
    exact hf i (by simpa using h)

theorem range_map_some_total {n : Nat} {f : Nat → Nat} :
    Total ((Array.range n).map fun i => OptIdx.some (f i)) := by
  intro i h
  simp

theorem Mappings.initialMappings_vmap_wf (n d : Nat) : (Mappings.initialMappings n d).vmap.WF n n := by
  simpa [Mappings.initialMappings] using
    (range_map_some_wf (n := n) (codom := n) (f := fun i => i) (fun _ hi => hi))

theorem Mappings.initialMappings_dmap_wf (n d : Nat) : (Mappings.initialMappings n d).dmap.WF d d := by
  simpa [Mappings.initialMappings] using
    (range_map_some_wf (n := d) (codom := d) (f := fun i => i) (fun _ hi => hi))

theorem Mappings.initialMappings_wf (n d : Nat) :
    (Mappings.initialMappings n d).WF n d n d :=
  ⟨initialMappings_vmap_wf n d, initialMappings_dmap_wf n d⟩

theorem Mappings.initialMappings_vmap_total (n d : Nat) : (Mappings.initialMappings n d).vmap.Total := by
  simpa [Mappings.initialMappings] using
    (range_map_some_total (n := n) (f := fun i => i))

theorem Mappings.initialMappings_dmap_total (n d : Nat) : (Mappings.initialMappings n d).dmap.Total := by
  simpa [Mappings.initialMappings] using
    (range_map_some_total (n := d) (f := fun i => i))

theorem Mappings.idx?_initialMappings_vmap (n d i : Nat) :
    (Mappings.initialMappings n d).vmap.idx? i = if i < n then Option.some i else Option.none := by
  unfold idx?
  simp [Mappings.initialMappings]

/-! ### L2 -- `composeMap` is Kleisli composition (the paper's `φ̃ ∘ φ★`, A.4.3) -/

@[simp] theorem size_composeMap (m1 m2 : IndexMap) :
    (composeMap m1 m2).size = m1.size := by
  simp [composeMap]

/-- The `composeMap` entry read, folded (its `Array.getElem_map` equation). -/
theorem getElem_composeMap {m1 m2 : IndexMap} {i : Nat} (hi : i < m1.size) :
    (composeMap m1 m2)[i]'(by simpa using hi) =
      if (m1[i]'hi).isNone then OptIdx.none else m2[(m1[i]'hi).idx!]! := by
  simp [composeMap]

/-- **The workhorse.** Under `Bounded`, composing maps is Kleisli composition
of the functions they denote -- and the proof shows `composeMap`'s internal
`map2[j.idx!]!` read (Mapping.lean) is in range, i.e. its panic branch is
dead. (True even without `Bounded` -- an out-of-range `!` read defaults to
`OptIdx.none`, which `bind` absorbs -- but the `Bounded` form carries the
panic-branch-dead content; see the module header.) -/
theorem idx?_composeMap {m1 m2 : IndexMap} (hb : m1.Bounded m2.size) (i : Nat) :
    (composeMap m1 m2).idx? i = (m1.idx? i).bind m2.idx? := by
  by_cases hi : i < m1.size
  · rw [idx?_pos (by simpa using hi), getElem_composeMap hi, idx?_pos hi]
    rcases hm : (m1[i]'hi).get? with _ | k
    · simp [OptIdx.isNone_eq, hm]
    · have hk : k < m2.size := hb i hi k hm
      simp [OptIdx.isNone_eq, hm, OptIdx.idx!_of_get?_some hm,
        getElem!_pos m2 k hk, idx?_pos hk]
  · rw [idx?_neg (by simpa using hi), idx?_neg hi]
    rfl

theorem composeMap_wf {m1 m2 : IndexMap} {a b c : Nat}
    (h1 : m1.WF a b) (h2 : m2.WF b c) : (composeMap m1 m2).WF a c := by
  constructor
  · simp [h1.size_eq]
  · rw [bounded_iff_idx?_lt]
    intro i j hj
    rw [idx?_composeMap (h2.size_eq ▸ h1.bounded)] at hj
    obtain ⟨k, hk1, hk2⟩ := Option.bind_eq_some_iff.mp hj
    exact idx?_lt_of_bounded h2.bounded hk2

theorem composeMap_total {m1 m2 : IndexMap}
    (t1 : m1.Total) (hb : m1.Bounded m2.size) (t2 : m2.Total) :
    (composeMap m1 m2).Total := by
  grind [Total, composeMap, Bounded, OptIdx.isNone, OptIdx.isSome, OptIdx.idx!, OptIdx.get?]

/-- Lifted to `Mappings.compose` (`self` first, then `other` -- note the paper
writes `φ̃ ∘ φ★`, applying `φ★` first; same composite, opposite notation). -/
theorem Mappings.compose_wf {ms1 ms2 : Mappings} {n d n' d' n'' d'' : Nat}
    (h1 : ms1.WF n d n' d') (h2 : ms2.WF n' d' n'' d'') :
    (ms1.compose ms2).WF n d n'' d'' :=
  ⟨composeMap_wf h1.vmap_wf h2.vmap_wf, composeMap_wf h1.dmap_wf h2.dmap_wf⟩

/-! ### L3 -- `splitMap` is restriction along a domain decomposition (the
codomain is unchanged: both halves map into the same target; the second
half's domain embeds by `i ↦ l + i`) -/

@[simp] theorem size_splitMap_fst (m : IndexMap) (l : Nat) :
    (splitMap m l).1.size = min l m.size := by
  simp [splitMap]

@[simp] theorem size_splitMap_snd (m : IndexMap) (l : Nat) :
    (splitMap m l).2.size = m.size - l := by
  simp [splitMap]

theorem idx?_splitMap_fst {m : IndexMap} {l : Nat} (hl : l ≤ m.size) (i : Nat) :
    (splitMap m l).1.idx? i = if i < l then m.idx? i else Option.none := by
  grind [idx?, splitMap]

theorem idx?_splitMap_snd (m : IndexMap) (l i : Nat) :
    (splitMap m l).2.idx? i = m.idx? (l + i) := by
  grind [idx?, splitMap]

theorem splitMap_fst_wf {m : IndexMap} {dom codom l : Nat}
    (h : m.WF dom codom) (hl : l ≤ dom) : (splitMap m l).1.WF l codom := by
  constructor
  · simp [h.size_eq]; omega
  · rw [bounded_iff_idx?_lt]
    intro i j hj
    rw [idx?_splitMap_fst (h.size_eq ▸ hl)] at hj
    split at hj
    · exact idx?_lt_of_bounded h.bounded hj
    · contradiction

theorem splitMap_snd_wf {m : IndexMap} {dom codom l : Nat}
    (h : m.WF dom codom) : (splitMap m l).2.WF (dom - l) codom := by
  constructor
  · simp [h.size_eq]
  · rw [bounded_iff_idx?_lt]
    intro i j hj
    rw [idx?_splitMap_snd] at hj
    exact idx?_lt_of_bounded h.bounded hj

theorem splitMap_fst_total {m : IndexMap} {l : Nat} (ht : m.Total) :
    (splitMap m l).1.Total := by
  grind [Total, splitMap]

theorem splitMap_snd_total {m : IndexMap} {l : Nat} (ht : m.Total) :
    (splitMap m l).2.Total := by
  grind [Total, splitMap]

/-- Reassembly: the two restrictions *are* the map -- pins
`freeHomomorphismPair`'s meaning. -/
theorem splitMap_fst_append_snd {m : IndexMap} {l : Nat} (hl : l ≤ m.size) :
    (splitMap m l).1 ++ (splitMap m l).2 = m := by
  grind [splitMap]

/-! ### Decode payoffs: the combinators under `toFun` (each a transport of its
`idx?` twin via `toFun_val` + `option_fin_val_inj`) -/

/-- `initialMappings` denotes the identity (the paper's `id_X`, A.4.4). -/
theorem Mappings.toFun_initialMappings_vmap {n d : Nat} (i : Fin n) :
    (Mappings.initialMappings n d).vmap.toFun (initialMappings_vmap_wf n d) i
      = Option.some i := by
  apply option_fin_val_inj
  rw [toFun_val, idx?_initialMappings_vmap]
  simp [i.isLt]

/-- `composeMap` denotes Kleisli composition of the denoted functions. -/
theorem toFun_composeMap {m1 m2 : IndexMap} {a b c : Nat}
    (h1 : m1.WF a b) (h2 : m2.WF b c) (i : Fin a) :
    (composeMap m1 m2).toFun (composeMap_wf h1 h2) i
      = (m1.toFun h1 i).bind (m2.toFun h2) := by
  apply option_fin_val_inj
  rw [toFun_val, idx?_composeMap (h2.size_eq ▸ h1.bounded)]
  rw [← toFun_val h1 i]
  cases hm : m1.toFun h1 i with
  | none => simp
  | some k => simp [toFun_val h2 k]

/-- The first half of a split denotes the restriction to `[0, l)`. -/
theorem toFun_splitMap_fst {m : IndexMap} {dom codom l : Nat}
    (h : m.WF dom codom) (hl : l ≤ dom) (i : Fin l) :
    (splitMap m l).1.toFun (splitMap_fst_wf h hl) i
      = m.toFun h (i.castLE hl) := by
  apply option_fin_val_inj
  rw [toFun_val, toFun_val, idx?_splitMap_fst (h.size_eq ▸ hl)]
  simp [i.isLt, Fin.castLE]

/-- The second half denotes the restriction along `i ↦ l + i`. -/
theorem toFun_splitMap_snd {m : IndexMap} {dom codom l : Nat}
    (h : m.WF dom codom) (i : Fin (dom - l)) :
    (splitMap m l).2.toFun (splitMap_snd_wf h) i
      = m.toFun h ⟨l + i.val, by omega⟩ := by
  apply option_fin_val_inj
  rw [toFun_val, toFun_val, idx?_splitMap_snd]

end
end NearLinear4ct
