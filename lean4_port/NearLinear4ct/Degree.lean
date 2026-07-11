/-!
Inclusive degree ranges.

`Degree { lower, upper }` is an inclusive degree range with intersection /
containment / disjointness predicates. In the on-disk format the degree `∞` is
written as `0` (see `../FORMAT.md`); that mapping is handled at the I/O boundary,
not here.

The fields are `Nat`. A degree is a vertex degree bound, always `≥ 1` -- a
negative value is an *error*, not a valid state, so `Nat` encodes the invariant
rather than weakening it (and `intersection` can still return an empty range
with `lower > upper`, both `Nat`). The *derived* signed quantities (curvature
`6 - d`, charges) coerce to `Int` at their computation sites. This removes the
boxed-`Int` handling and `Int.toNat` conversions from the hot `containConf`
degree-bucket indexing (`dbd[dY][dX]`). The `degree - 1` refinement site
(`CartWheel.refineNever`) assumes `lower ≥ 1`; that is `proofAssert`-checked at
load (`assertDegreesValid`), and the gate is proved sufficient for the site in
`CartwheelProofs.lean`.
-/

namespace NearLinear4ct

/-- Number of concrete cartwheel degrees (`CARTWHEEL_DEGREES`). -/
def CARTWHEEL_DEGREES_SIZE : Nat := 5
/-- The concrete degrees a cartwheel neighbour may take. -/
def CARTWHEEL_DEGREES : Array Nat := #[5, 6, 7, 8, 9]
def CARTWHEEL_DEG_MIN : Nat := 5
def CARTWHEEL_DEG_MAX : Nat := 9
/-- Sentinel standing in for an unbounded (∞) degree. -/
def INFTY : Nat := 1000000000
def CONF_DEG_MAX : Nat := 12

/-- An inclusive degree range `[lower, upper]`, both `Nat` (a degree is `≥ 1`).

Ordering is lexicographic by `lower` then `upper` (the field declaration order),
which the derived `Ord` reproduces exactly. -/
structure Degree where
  lower : Nat
  upper : Nat
deriving DecidableEq, Repr, Inhabited, Ord, BEq, Hashable

namespace Degree

/-- A fixed (point) degree `[x, x]`. -/
def exact (x : Nat) : Degree := ⟨x, x⟩

/-- Whether the range is a single fixed value. -/
def fixed (d : Degree) : Bool := d.lower == d.upper

/-- Whether two ranges have no common value. -/
def disjoint (a b : Degree) : Bool :=
  decide (a.upper < b.lower) || decide (b.upper < a.lower)

/-- Whether two ranges share at least one value. -/
def hasIntersection (a b : Degree) : Bool := !disjoint a b

/-- The intersection range. May be empty (`lower > upper`)
if the inputs are disjoint. -/
def intersection (a b : Degree) : Degree :=
  ⟨max a.lower b.lower, min a.upper b.upper⟩

/-- Whether `outer` contains `inner`. -/
def includes (outer inner : Degree) : Bool :=
  decide (outer.lower ≤ inner.lower) && decide (inner.upper ≤ outer.upper)

/-- Lexicographic `<` / `≤` from the derived `Ord`. -/
instance : LT Degree := ⟨fun a b => compare a b = Ordering.lt⟩
instance : LE Degree := ⟨fun a b => compare a b ≠ Ordering.gt⟩
instance (a b : Degree) : Decidable (a < b) := inferInstanceAs (Decidable (_ = _))
instance (a b : Degree) : Decidable (a ≤ b) := inferInstanceAs (Decidable (_ ≠ _))

/-! ### Algebra laws

Universal correctness facts for the range predicates -- proved for *all* ranges
(the finite grid these replaced only exercised `1..7`). The intersection
non-emptiness law needs the ranges to be non-empty (`lower ≤ upper`); an empty
range like `⟨5, 3⟩` can report `hasIntersection` yet have an empty intersection,
which is exactly the precondition the proof makes explicit. -/

/-- `hasIntersection` is by definition the negation of `disjoint`. -/
theorem hasIntersection_eq_not_disjoint (a b : Degree) :
    hasIntersection a b = !disjoint a b := rfl

/-- `disjoint` is symmetric. -/
theorem disjoint_comm (a b : Degree) : disjoint a b = disjoint b a := by
  grind [disjoint]

/-- `hasIntersection` is symmetric. -/
theorem hasIntersection_comm (a b : Degree) :
    hasIntersection a b = hasIntersection b a := by
  grind [hasIntersection, disjoint_comm]

/-- `includes` is reflexive. -/
theorem includes_refl (a : Degree) : includes a a = true := by
  simp [includes]

/-- `intersection` is contained in its left operand. -/
theorem intersection_includes_left (a b : Degree) :
    includes a (intersection a b) = true := by
  grind [includes, intersection]

/-- `intersection` is contained in its right operand. -/
theorem intersection_includes_right (a b : Degree) :
    includes b (intersection a b) = true := by
  grind [includes, intersection]

/-- When two *non-empty* ranges intersect, their `intersection` is non-empty. -/
theorem intersection_nonempty (a b : Degree)
    (ha : a.lower ≤ a.upper) (hb : b.lower ≤ b.upper)
    (h : hasIntersection a b = true) :
    (intersection a b).lower ≤ (intersection a b).upper := by
  grind [hasIntersection, intersection, disjoint]


end Degree
end NearLinear4ct
