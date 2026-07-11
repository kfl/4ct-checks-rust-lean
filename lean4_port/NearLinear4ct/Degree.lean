/-!
Phase 1 — leaf type. Port of `../src/degree.{hpp,cpp}`.

`Degree { lower, upper }` is an inclusive degree range with intersection /
containment / disjointness predicates. In the on-disk format the degree `∞` is
written as `0` (see `../FORMAT.md`); that mapping is handled at the I/O boundary
(P4), not here.

L2 decision (record): the fields are `Int` (faithful to the C++ `int`). Degrees
are non-negative in practice, but `intersection` can legitimately return an empty
range with `lower > upper`, and later code computes signed quantities derived from
degrees (curvature `6 − d`, charges). Indices elsewhere stay `Nat`; degrees are
the first `Int` site.
-/

namespace NearLinear4ct

/-- Number of concrete cartwheel degrees (`CARTWHEEL_DEGREES`). -/
def CARTWHEEL_DEGREES_SIZE : Nat := 5
/-- The concrete degrees a cartwheel neighbour may take. -/
def CARTWHEEL_DEGREES : Array Int := #[5, 6, 7, 8, 9]
def CARTWHEEL_DEG_MIN : Int := 5
def CARTWHEEL_DEG_MAX : Int := 9
/-- Sentinel standing in for an unbounded (∞) degree. Matches the C++ `1e9`. -/
def INFTY : Int := 1000000000
def CONF_DEG_MAX : Int := 12

/-- An inclusive degree range `[lower, upper]`.

Ordering is the C++ default `operator<=>`: lexicographic by `lower` then `upper`
(the field declaration order). The derived `Ord` reproduces this exactly. -/
structure Degree where
  lower : Int
  upper : Int
deriving DecidableEq, Repr, Inhabited, Ord, BEq, Hashable

namespace Degree

/-- A fixed (point) degree `[x, x]` (the C++ `Degree(int x)` converting ctor). -/
def exact (x : Int) : Degree := ⟨x, x⟩

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
