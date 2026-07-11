//! Phase 1 — shared compact optional index.
//!
//! A 4-byte stand-in for `Option<usize>` used in hot data structures (the
//! `Dart` half-edge links and the `homomorphism` scratch maps), so they keep
//! real `Option` ergonomics without paying for a 16-byte `Option<usize>`.

use std::num::NonZeroU32;

/// An optional index that fits in 4 bytes. `None` is the niche (all-zero
/// bytes), and index `0` is a valid `Some`.
///
/// Internally an index `i` is stored as `NonZeroU32(i + 1)`, so
/// `size_of::<OptIdx>() == 4` while `None` keeps the all-zero representation —
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
}
