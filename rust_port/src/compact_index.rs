//! Shared compact optional index.
//!
//! A 4-byte stand-in for `Option<usize>` used in hot data structures (the
//! `Dart` half-edge links and the `homomorphism` scratch maps), so they keep
//! real `Option` ergonomics without paying for a 16-byte `Option<usize>`.

use std::num::NonZeroU32;

/// An optional index that fits in 4 bytes. `None` is the niche (all-zero
/// bytes), and index `0` is a valid `Some`.
///
/// Internally an index `i` is stored as `NonZeroU32(i + 1)`, so
/// `size_of::<OptIdx>() == 4` while `None` keeps the all-zero representation --
/// `vec![OptIdx::NONE; n]` therefore lowers to a zeroing allocation. The
/// `i + 1` encoding is checked once, here, instead of being open-coded at each
/// call site.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Hash)]
pub struct OptIdx(Option<NonZeroU32>);

impl OptIdx {
    /// The boundary / unmapped sentinel.
    pub const NONE: Self = OptIdx(None);

    /// Wrap a present index. Panics if it cannot be encoded in the compact
    /// range (`i + 1` must fit in a non-zero `u32`).
    #[inline]
    pub fn some(idx: usize) -> Self {
        let encoded = idx
            .checked_add(1)
            .and_then(|e| u32::try_from(e).ok())
            .and_then(NonZeroU32::new)
            .unwrap_or_else(|| panic!("index {idx} exceeds compact optional index range"));
        OptIdx(Some(encoded))
    }

    /// Encode an `Option<usize>`.
    #[inline]
    pub fn from_option(idx: Option<usize>) -> Self {
        match idx {
            Some(i) => Self::some(i),
            None => Self::NONE,
        }
    }

    /// Decode to `Option<usize>`.
    #[inline]
    pub fn get(self) -> Option<usize> {
        self.0.map(|i| (i.get() - 1) as usize)
    }

    #[inline]
    pub fn is_none(self) -> bool {
        self.0.is_none()
    }

    #[inline]
    pub fn is_some(self) -> bool {
        self.0.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[test]
    fn round_trips() {
        assert_eq!(OptIdx::NONE.get(), None);
        assert_eq!(OptIdx::from_option(None).get(), None);
        for i in [0usize, 1, 2, 42, u32::MAX as usize - 1] {
            assert_eq!(OptIdx::some(i).get(), Some(i));
            assert_eq!(OptIdx::from_option(Some(i)).get(), Some(i));
        }
        assert!(OptIdx::NONE.is_none());
        assert!(OptIdx::some(0).is_some());
    }

    #[test]
    fn is_four_bytes() {
        assert_eq!(std::mem::size_of::<OptIdx>(), 4);
    }

    #[test]
    #[should_panic(expected = "exceeds compact optional index range")]
    fn rejects_out_of_range() {
        OptIdx::some(u32::MAX as usize);
    }

    /// Property (R1): `OptIdx` round-trips `Option<usize>` for every encodable
    /// value across the whole `u32` range -- `from_option(o).get() == o`. This
    /// fuzzes the `i + 1` / `NonZeroU32` encoding far beyond the handful of
    /// fixed values in `round_trips`.
    #[quickcheck]
    fn prop_round_trips(x: Option<u32>) -> TestResult {
        if x == Some(u32::MAX) {
            // one value past the encodable range; the panic is covered by
            // `rejects_out_of_range`.
            return TestResult::discard();
        }
        let o = x.map(|v| v as usize);
        TestResult::from_bool(OptIdx::from_option(o).get() == o)
    }

    /// Property (R1 niche soundness): the `None` sentinel -- the compact
    /// stand-in for the C++ `-1` -- is distinct from *every* present index,
    /// including `some(0)`, which a naive all-zero sentinel would swallow; and
    /// `is_some`/`is_none` agree with `get`.
    #[quickcheck]
    fn prop_none_distinct_from_every_some(x: u32) -> TestResult {
        if x == u32::MAX {
            return TestResult::discard();
        }
        let s = OptIdx::some(x as usize);
        TestResult::from_bool(
            s != OptIdx::NONE
                && s.is_some()
                && !s.is_none()
                && s.get().is_some()
                && OptIdx::NONE.is_none()
                && OptIdx::NONE.get().is_none(),
        )
    }
}
