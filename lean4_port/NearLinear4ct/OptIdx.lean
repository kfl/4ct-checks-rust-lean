/-!
A compact optional index — the Lean analogue of the Rust port's `OptIdx`, but a
**verified** abstraction.

`OptIdx` encodes an `Option Nat`: `0 = none`, `i+1 = some i`. It is a single-field
structure over `Nat`, so at runtime it is represented **as a `Nat`** (an unboxed
tagged immediate) — `Array OptIdx` is a dense scalar array, whereas
`Array (Option Nat)` heap-allocates and reference-counts a `some` cell per mapped
entry, because **Lean has no niche optimisation** (unlike Rust's
`Option<NonZeroU32>`). So `OptIdx` recovers, by hand, the unboxed representation
Rust gets for free from a niche.

Crucially, the `Option Nat` semantics are recovered by `get?`, and the encoding is
**proved sound** below (`get?_some`, `get?_none`, the round-trips). This is the
Lean-specific payoff: the compact representation is not merely encapsulated and
tested (as in C++/Rust) but machine-checked to carry exactly the same information
as `Option Nat` — so using it, even in public types, does not weaken R1.
-/

namespace NearLinear4ct

/-- A compact optional index: `0` encodes `none`, `i+1` encodes `some i`.
Construct with `OptIdx.none` / `OptIdx.some` / `OptIdx.ofOption`; read with the
`Bool` predicates (hot path, no allocation) or `get?` (boundary, `Option Nat`). -/
structure OptIdx where
  /-- Raw encoding: `0 = none`, `i+1 = some i`. Prefer the smart constructors. -/
  raw : Nat
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace OptIdx

/-- `none` (unmapped). -/
def none : OptIdx := ⟨0⟩

/-- `some i` (mapped to index `i`). -/
def «some» (i : Nat) : OptIdx := ⟨i + 1⟩

/-- Whether this is `some _` (no allocation — for the hot loop). -/
def isSome (o : OptIdx) : Bool := o.raw != 0

/-- Whether this is `none` (no allocation). -/
def isNone (o : OptIdx) : Bool := o.raw == 0

/-- The decoded `Option Nat` view (boundary accessor; builds an `Option`). -/
def get? (o : OptIdx) : Option Nat := if o.raw == 0 then Option.none else Option.some (o.raw - 1)

/-- The index, assuming `some` (panics on `none`). For callers that already know
the entry is mapped (the C++ `map[i]` after the BFS made it total). -/
def idx! (o : OptIdx) : Nat :=
  if o.raw == 0 then panic! "OptIdx.idx! on none" else o.raw - 1

/-- Encode an `Option Nat`. -/
def ofOption : Option Nat → OptIdx
  | Option.none => none
  | Option.some i => «some» i

/-! ### Soundness: `OptIdx` carries exactly the data of `Option Nat`.

These discharge R1 by proof — the compact encoding is verified equivalent to
`Option Nat`, so exposing `OptIdx` in public types is as trustworthy as `Option`. -/

@[simp] theorem get?_none : OptIdx.none.get? = Option.none := rfl

@[simp] theorem get?_some (i : Nat) : (OptIdx.«some» i).get? = Option.some i := by
  simp [OptIdx.«some», get?]

@[simp] theorem isSome_eq (o : OptIdx) : o.isSome = o.get?.isSome := by
  simp [isSome, get?]; split <;> simp_all

@[simp] theorem ofOption_get? (o : Option Nat) : (ofOption o).get? = o := by
  cases o <;> simp [ofOption]

/-- Round-trip the other way: `ofOption ∘ get? = id`. Together with `get?_ofOption`
this is the bijection `OptIdx ≃ Option Nat`. -/
theorem get?_ofOption (o : OptIdx) : ofOption o.get? = o := by
  obtain ⟨raw⟩ := o
  cases raw with
  | zero => rfl
  | succ n => simp [get?, ofOption, OptIdx.«some»]

end OptIdx
end NearLinear4ct
