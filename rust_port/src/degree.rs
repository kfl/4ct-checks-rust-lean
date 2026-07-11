//! Phase 1 — leaf type. Port of `../src/degree.{hpp,cpp}`.
//!
//! `Degree { lower, upper }` is an inclusive degree range with intersection /
//! containment / disjointness predicates. In the on-disk format the degree
//! `∞` is written as `0` (see `../FORMAT.md`); that mapping is handled at the
//! I/O boundary (P4), not here.

/// Number of concrete cartwheel degrees (`CARTWHEEL_DEGREES`).
pub const CARTWHEEL_DEGREES_SIZE: usize = 5;
/// The concrete degrees a cartwheel neighbour may take.
pub const CARTWHEEL_DEGREES: [i32; CARTWHEEL_DEGREES_SIZE] = [5, 6, 7, 8, 9];
pub const CARTWHEEL_DEG_MIN: i32 = 5;
pub const CARTWHEEL_DEG_MAX: i32 = 9;
/// Sentinel value standing in for an unbounded (∞) degree. Matches the C++ `1e9`.
pub const INFTY: i32 = 1_000_000_000;
pub const CONF_DEG_MAX: i32 = 12;

/// An inclusive degree range `[lower, upper]`.
///
/// Ordering is the C++ default `operator<=>`: lexicographic by `lower` then
/// `upper` (the field declaration order). `derive(PartialOrd, Ord)` reproduces
/// this exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Degree {
    pub lower: i32,
    pub upper: i32,
}

impl Degree {
    /// A range `[lower, upper]` (C++ `Degree(lower, upper)`).
    pub const fn new(lower: i32, upper: i32) -> Self {
        Degree { lower, upper }
    }

    /// A fixed (point) degree `[x, x]` (C++ `Degree(x)`).
    pub const fn exact(x: i32) -> Self {
        Degree { lower: x, upper: x }
    }

    /// Whether the range is a single fixed value (C++ `fixed()`).
    pub const fn is_fixed(&self) -> bool {
        self.lower == self.upper
    }

    /// Whether two ranges have no common value (C++ `disjoint`).
    pub const fn is_disjoint(a: &Degree, b: &Degree) -> bool {
        a.upper < b.lower || b.upper < a.lower
    }

    /// Whether two ranges share at least one value (C++ `has_intersection`).
    pub const fn has_intersection(a: &Degree, b: &Degree) -> bool {
        !Degree::is_disjoint(a, b)
    }

    /// The intersection range (C++ `intersection`). May be empty
    /// (`lower > upper`) if the inputs are disjoint, exactly as in C++.
    pub fn intersection(a: &Degree, b: &Degree) -> Degree {
        Degree::new(a.lower.max(b.lower), a.upper.min(b.upper))
    }

    /// Whether `outer` contains `inner` (C++ `include(degree0, degree1)`).
    pub const fn includes(outer: &Degree, inner: &Degree) -> bool {
        outer.lower <= inner.lower && inner.upper <= outer.upper
    }
}

impl From<i32> for Degree {
    /// Mirrors the C++ implicit `Degree(int)` converting constructor.
    fn from(x: i32) -> Self {
        Degree::exact(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    // Degrees order lexicographically by (lower, upper).
    #[test]
    fn compare() {
        let d1 = Degree::new(5, 6);
        let d2 = Degree::new(5, 6);
        let d3 = Degree::new(5, 7);
        let d4 = Degree::new(6, 7);
        assert_eq!(d1, d2);
        assert!(d1 < d3);
        assert!(d1 < d4);
        assert!(d3 > d1);
        assert!(d4 > d1);
    }

    #[test]
    fn fixed_and_conversion() {
        assert!(Degree::exact(7).is_fixed());
        assert!(!Degree::new(5, 6).is_fixed());
        assert_eq!(Degree::from(7), Degree::new(7, 7));
    }

    #[test]
    fn intersection_disjoint_include() {
        let a = Degree::new(5, 8);
        let b = Degree::new(7, 9);
        let c = Degree::new(10, 11);
        assert!(Degree::has_intersection(&a, &b));
        assert!(!Degree::is_disjoint(&a, &b));
        assert_eq!(Degree::intersection(&a, &b), Degree::new(7, 8));
        assert!(Degree::is_disjoint(&a, &c));

        // Empty intersection keeps the C++ behaviour (lower > upper).
        let empty = Degree::intersection(&a, &c);
        assert!(empty.lower > empty.upper);

        assert!(Degree::includes(&Degree::new(5, 9), &Degree::new(6, 8)));
        assert!(!Degree::includes(&Degree::new(6, 8), &Degree::new(5, 9)));
    }

    /// Property (self-contained oracle): the algebraic laws of `Degree` ranges,
    /// checked against independently-computed expectations (no transcribed
    /// constants). `mk` builds a valid non-empty range from any `i8` pair.
    #[quickcheck]
    fn prop_degree_algebra(a: i8, b: i8, c: i8, e: i8) -> bool {
        let mk = |x: i8, y: i8| Degree::new(x.min(y) as i32, x.max(y) as i32);
        let da = mk(a, b);
        let db = mk(c, e);
        // has_intersection is symmetric and is exactly the negation of is_disjoint.
        let sym = Degree::has_intersection(&da, &db) == Degree::has_intersection(&db, &da);
        let disj = Degree::has_intersection(&da, &db) != Degree::is_disjoint(&da, &db);
        // includes is reflexive.
        let refl = Degree::includes(&da, &da) && Degree::includes(&db, &db);
        // when they intersect, the intersection is [max(lowers), min(uppers)],
        // non-empty, and contained in both operands.
        let inter_ok = if Degree::has_intersection(&da, &db) {
            let i = Degree::intersection(&da, &db);
            i.lower <= i.upper
                && i == Degree::new(da.lower.max(db.lower), da.upper.min(db.upper))
                && Degree::includes(&da, &i)
                && Degree::includes(&db, &i)
        } else {
            true
        };
        sym && disj && refl && inter_ok
    }
}
