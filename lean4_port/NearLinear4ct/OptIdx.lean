/-!
A compact, **verified** optional index.

`OptIdx` encodes an `Option Nat`: `0 = none`, `i+1 = some i`. It is a single-field
structure over `Nat`, so at runtime it is represented **as a `Nat`** (an unboxed
tagged immediate) -- `Array OptIdx` is a dense scalar array, whereas
`Array (Option Nat)` heap-allocates and reference-counts a `some` cell per mapped
entry, because **Lean has no niche optimisation** (the optimisation that lets a
Rust `Option<NonZeroU32>` be stored unboxed). So `OptIdx` recovers that unboxed
representation by hand.

The `Option Nat` semantics are recovered by `get?`, and the encoding is
**proved sound** below (`get?_some`, `get?_none`, the round-trips): the compact
representation is not merely encapsulated and tested but machine-checked to carry
exactly the same information as `Option Nat` -- so using it, even in public types,
does not weaken the sentinel-soundness guarantee.
-/

namespace NearLinear4ct

/-- A compact optional index: `0` encodes `none`, `i+1` encodes `some i`.
Construct with `OptIdx.none` / `OptIdx.some` / `OptIdx.ofOption`; read with the
`Bool` predicates (hot path, no allocation) or `get?` (boundary, `Option Nat`). -/
structure OptIdx where
  /-- Raw encoding: `0 = none`, `i+1 = some i`. Prefer the smart constructors. -/
  raw : Nat
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- The derived `BEq` is lawful (it is `Nat` equality on `raw`). Not provided by
`deriving BEq` upstream, but needed to reason about the `!=` consistency test in
the homomorphism BFS loop. -/
instance : LawfulBEq OptIdx where
  eq_of_beq {a b} h := by
    have hr : a.raw = b.raw := eq_of_beq (show (a.raw == b.raw) = true from h)
    cases a; cases b; simp_all
  rfl {a} := by show (a.raw == a.raw) = true; simp

namespace OptIdx

/-- `none` (unmapped).

`@[match_pattern]`: usable in patterns, so call sites match an `OptIdx` like
an `Option` without decoding through `get?`. -/
@[match_pattern] protected def none : OptIdx := ⟨0⟩

/-- `some i` (mapped to index `i`).

`@[match_pattern]`: the pattern `.some i` unfolds to `⟨i + 1⟩`, so
`.none`/`.some i` matches are exhaustive. -/
@[inline, match_pattern] protected def «some» (i : Nat) : OptIdx := ⟨i + 1⟩

/-- Whether this is `some _` (no allocation -- for the hot loop). -/
@[inline] def isSome (o : OptIdx) : Bool := o.raw != 0

/-- Whether this is `none` (no allocation). -/
@[inline] def isNone (o : OptIdx) : Bool := o.raw == 0

/-- The decoded `Option Nat` view (boundary accessor; builds an `Option`). -/
def get? (o : OptIdx) : Option Nat := if o.raw == 0 then Option.none else Option.some (o.raw - 1)

/-- The index, assuming `some` (panics on `none`). For callers that already know
the entry is mapped (e.g. after the BFS made it total). -/
def idx! (o : OptIdx) : Nat :=
  if o.raw == 0 then panic! "OptIdx.idx! on none" else o.raw - 1

/-- Encode an `Option Nat`. -/
def ofOption : Option Nat → OptIdx
  | Option.none => .none
  | Option.some i => .some i

/-- Map the index if present, staying unboxed (mirrors `Option.map`; `map f ∘ get? =
get? ∘ Option.map f`). -/
@[inline] def map (f : Nat → Nat) (o : OptIdx) : OptIdx :=
  if o.raw == 0 then .none else .some (f (o.raw - 1))

/-- Decode an optional index into an optional finite index, given a bound proof. -/
def toFin? (o : OptIdx) (h : ∀ j, o.get? = Option.some j → j < n) :
    Option (Fin n) :=
  match hj : o.get? with
  | Option.none => Option.none
  | Option.some j => Option.some ⟨j, h j hj⟩

/-! ### Soundness: `OptIdx` carries exactly the data of `Option Nat`.

These discharge the sentinel-soundness obligation by proof -- the compact encoding
is verified equivalent to `Option Nat`, so exposing `OptIdx` in public types is as
trustworthy as `Option`. -/

@[simp, grind .] theorem some_ne_none (i : Nat) : OptIdx.some i ≠ OptIdx.none := by
  simp [OptIdx.some, OptIdx.none]

@[simp, grind .] theorem none_ne_some (i : Nat) : OptIdx.none ≠ OptIdx.some i := by
  simp [OptIdx.some, OptIdx.none]

@[simp, grind =] theorem some_inj {i j : Nat} : OptIdx.some i = OptIdx.some j ↔ i = j := by
  simp [OptIdx.some]

@[simp] theorem isNone_none : OptIdx.none.isNone = true := rfl

@[simp, grind =] theorem default_eq_none : (default : OptIdx) = OptIdx.none := rfl

/-- Canonicalise raw literals (as exposed by a `match`) to the smart
constructors, so the `grind`-tagged lemmas above and below apply to them. -/
@[grind =] theorem mk_zero : (⟨0⟩ : OptIdx) = OptIdx.none := rfl

@[grind =] theorem mk_succ (i : Nat) : (⟨i + 1⟩ : OptIdx) = OptIdx.some i := rfl

/-- `Option`-shaped case analysis: `cases o with | none => .. | some i => ..`,
as if `some`/`none` were constructors (they are defs, so the structural
eliminator would expose `⟨raw⟩`). Tactic-level only; `grind` gets its
`OptIdx` reasoning from the tagged lemmas above instead. -/
@[cases_eliminator] protected def casesIdx {motive : OptIdx → Sort u} (o : OptIdx)
    (none : motive .none) (some : (i : Nat) → motive (.some i)) : motive o :=
  match o with
  | .none => none
  | .some i => some i

@[simp] theorem get?_none : OptIdx.none.get? = Option.none := rfl

@[simp] theorem get?_some (i : Nat) : (OptIdx.«some» i).get? = Option.some i := by
  simp [OptIdx.«some», get?]

@[simp] theorem idx!_some (i : Nat) : (OptIdx.«some» i).idx! = i := by
  simp [OptIdx.«some», idx!]

@[simp] theorem idx!_raw_succ (i : Nat) : ({ raw := i + 1 } : OptIdx).idx! = i := by
  simp [idx!]

@[simp] theorem isNone_some (i : Nat) : (OptIdx.«some» i).isNone = false := by
  simp [OptIdx.«some», isNone]

@[simp] theorem isNone_raw_succ (i : Nat) : ({ raw := i + 1 } : OptIdx).isNone = false := by
  simp [isNone]

@[simp] theorem isSome_some (i : Nat) : (OptIdx.«some» i).isSome := by
  simp [OptIdx.«some», isSome]

@[simp] theorem isSome_raw_succ (i : Nat) : ({ raw := i + 1 } : OptIdx).isSome := by
  simp [isSome]

@[simp] theorem isSome_eq (o : OptIdx) : o.isSome = o.get?.isSome := by
  simp [isSome, get?]; split <;> simp_all

@[simp] theorem ofOption_get? (o : Option Nat) : (ofOption o).get? = o := by
  cases o <;> simp [ofOption]

/-- `map` mirrors `Option.map` under the `Option Nat` view. -/
@[simp] theorem get?_map (f : Nat → Nat) (o : OptIdx) : (map f o).get? = o.get?.map f := by
  obtain ⟨raw⟩ := o
  cases raw with
  | zero => rfl
  | succ n => simp [map, get?, OptIdx.some]

/-- Round-trip the other way: `ofOption ∘ get? = id`. Together with `get?_ofOption`
this is the bijection `OptIdx ≃ Option Nat`. -/
theorem get?_ofOption (o : OptIdx) : ofOption o.get? = o := by
  obtain ⟨raw⟩ := o
  cases raw with
  | zero => rfl
  | succ n => simp [get?, ofOption, OptIdx.«some»]

/-- A mapped `get?` pins down the value: `some` is the only preimage. -/
theorem get?_eq_some_iff {o : OptIdx} {j : Nat} :
    o.get? = Option.some j ↔ o = OptIdx.«some» j := by
  grind [OptIdx, get?, OptIdx.«some»]

/-- Raw bounds are exactly bounds on the decoded value, when present. -/
theorem raw_le_iff_get?_lt {o : OptIdx} {bound : Nat} :
    o.raw ≤ bound ↔ ∀ j, o.get? = Option.some j → j < bound := by
  obtain ⟨raw⟩ := o
  cases raw with
  | zero => simp [get?]
  | succ k => simp [get?]; omega

/-- `toFin?` is the decoded optional index under `Fin.val`. -/
@[simp] theorem toFin?_val {o : OptIdx} (h : ∀ j, o.get? = Option.some j → j < n) :
    (o.toFin? h).map Fin.val = o.get? := by
  unfold toFin?
  split <;> simp_all

@[simp] theorem toFin?_isSome {o : OptIdx} (h : ∀ j, o.get? = Option.some j → j < n) :
    (o.toFin? h).isSome = o.get?.isSome := by
  unfold toFin?
  split <;> simp_all

/-- `isNone` under the `Option Nat` view. -/
theorem isNone_iff_get? {o : OptIdx} : o.isNone ↔ o.get? = Option.none := by
  obtain ⟨raw⟩ := o
  cases raw <;> simp [isNone, get?]

/-- `isNone` under the `Option Nat` view, as a `Bool` rewrite. -/
theorem isNone_eq (o : OptIdx) : o.isNone = o.get?.isNone := by
  grind [isNone, get?]

/-- The `!`-discharge converter: a `get?` fact justifies the panicking read. -/
theorem idx!_of_get?_some {o : OptIdx} {j : Nat} (h : o.get? = Option.some j) :
    o.idx! = j := by
  obtain ⟨raw⟩ := o
  cases raw with
  | zero => simp [get?] at h
  | succ n => simp [get?] at h; simp [idx!, h]

end OptIdx
end NearLinear4ct
