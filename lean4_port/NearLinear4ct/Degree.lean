/-!
Phase 1 — leaf type. Port of `../src/degree.{hpp,cpp}`.

`Degree { lower, upper }` is an inclusive degree range with intersection /
containment / disjointness predicates. In the on-disk format the degree `∞` is
written as `0` (see `../FORMAT.md`); that mapping is handled at the I/O boundary
(P4), not here.

L2 decision (record, revised P14): the fields are `Nat`. A degree is a vertex
degree bound, always `≥ 1` — a negative value is an *error*, not a valid state, so
`Nat` encodes the invariant rather than weakening it (and `intersection` can still
return an empty range with `lower > upper`, both `Nat`). The *derived* signed
quantities (curvature `6 − d`, charges) coerce to `Int` at their computation sites.
This removes the boxed-`Int` handling and `Int.toNat` conversions from the hot
`containConf` degree-bucket indexing (`dbd[dY][dX]`, ~7% of `combine_rules`). Two
`degree − 1` refinement sites assume `lower ≥ 1`; that is `proofAssert`-checked
(static proof recorded in `PROOFS.md`).
-/

namespace NearLinear4ct

/-- Number of concrete cartwheel degrees (`CARTWHEEL_DEGREES`). -/
def CARTWHEEL_DEGREES_SIZE : Nat := 5
/-- The concrete degrees a cartwheel neighbour may take. -/
def CARTWHEEL_DEGREES : Array Nat := #[5, 6, 7, 8, 9]
def CARTWHEEL_DEG_MIN : Nat := 5
def CARTWHEEL_DEG_MAX : Nat := 9
/-- Sentinel standing in for an unbounded (∞) degree. Matches the C++ `1e9`. -/
def INFTY : Nat := 1000000000
def CONF_DEG_MAX : Nat := 12

/-- An inclusive degree range `[lower, upper]`, both `Nat` (a degree is `≥ 1`).

Ordering is the C++ default `operator<=>`: lexicographic by `lower` then `upper`
(the field declaration order). The derived `Ord` reproduces this exactly. -/
structure Degree where
  lower : Nat
  upper : Nat
deriving DecidableEq, Repr, Inhabited, Ord, BEq, Hashable

namespace Degree

/-- A fixed (point) degree `[x, x]` (the C++ `Degree(int x)` converting ctor). -/
def exact (x : Nat) : Degree := ⟨x, x⟩

/-- Whether the range is a single fixed value (C++ `fixed()`). -/
def fixed (d : Degree) : Bool := d.lower == d.upper

/-- Whether two ranges have no common value (C++ `disjoint`). -/
def disjoint (a b : Degree) : Bool :=
  decide (a.upper < b.lower) || decide (b.upper < a.lower)

/-- Whether two ranges share at least one value (C++ `has_intersection`). -/
def hasIntersection (a b : Degree) : Bool := !disjoint a b

/-- The intersection range (C++ `intersection`). May be empty (`lower > upper`)
if the inputs are disjoint, exactly as in C++. -/
def intersection (a b : Degree) : Degree :=
  ⟨max a.lower b.lower, min a.upper b.upper⟩

/-- Whether `outer` contains `inner` (C++ `include(degree0, degree1)`). -/
def includes (outer inner : Degree) : Bool :=
  decide (outer.lower ≤ inner.lower) && decide (inner.upper ≤ outer.upper)

/-- Lexicographic `<` / `≤` from the derived `Ord` (matches C++ `operator<=>`). -/
instance : LT Degree := ⟨fun a b => compare a b = Ordering.lt⟩
instance : LE Degree := ⟨fun a b => compare a b ≠ Ordering.gt⟩
instance (a b : Degree) : Decidable (a < b) := inferInstanceAs (Decidable (_ = _))
instance (a b : Degree) : Decidable (a ≤ b) := inferInstanceAs (Decidable (_ ≠ _))

end Degree
end NearLinear4ct
