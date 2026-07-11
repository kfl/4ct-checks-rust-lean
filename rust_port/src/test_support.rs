//! Shared test fixtures and helpers (compiled only under `cfg(test)`).
//!
//! Centralises what several test modules previously each redefined: the `Dart`
//! builder, the degree/index-map helpers, one RAII temp-file helper, and the
//! on-disk fixture strings (in the `FORMAT.md` text encoding).

use crate::degree::Degree;
use crate::pseudo_triangulation::Dart;
use std::io::Write;
use tempfile::{Builder, NamedTempFile};

/// Build a `Dart` from an `int` quad, mapping `-1` to `None` (the boundary
/// sentinel) -- the inverse of how a dart's `succ`/`pred` are printed.
pub(crate) fn d(head: i32, rev: i32, succ: i32, pred: i32) -> Dart {
    let opt = |x: i32| if x == -1 { None } else { Some(x as usize) };
    Dart::new(head as usize, rev as usize, opt(succ), opt(pred))
}

/// A vector of fixed (point) degrees.
pub(crate) fn exact(xs: &[i32]) -> Vec<Degree> {
    xs.iter().map(|&x| Degree::exact(x)).collect()
}

/// Wrap indices as a total `Option` index map.
pub(crate) fn imap(xs: &[usize]) -> Vec<Option<usize>> {
    xs.iter().map(|&x| Some(x)).collect()
}

/// Write `content` to a fresh temp file with the given `suffix` (e.g. `".rule"`).
/// The returned guard deletes the file when it drops -- no manual cleanup, and
/// safe even if the test panics. Read it via `f.path()`.
pub(crate) fn temp_with(content: &str, suffix: &str) -> NamedTempFile {
    let mut f = Builder::new()
        .suffix(suffix)
        .tempfile()
        .expect("create temp file");
    f.write_all(content.as_bytes()).expect("write temp file");
    f
}

// On-disk fixtures in the FORMAT.md text encoding, shared across test modules.
pub(crate) const RULE1: &str = "\n2 1 2 2\n1 5 5 2 -1\n2 5 0 1 -1\n";
pub(crate) const RULE2: &str = "\n6 1 2 1\n1 7 7 5 4 3 2 6 -1\n2 7 0 1 3 -1 6\n3 5 5 2 1 4 -1\n4 5 6 3 1 5 -1\n5 5 5 4 1 -1\n6 5 5 1 2 -1\n";
pub(crate) const RULE3: &str = "\n6 1 2 1\n1 7 7 4 6 2 3 -1\n2 7 0 3 1 6 -1\n3 5 5 1 2 -1\n4 6 6 5 6 1 -1\n5 5 5 6 4 -1\n6 5 5 2 1 4 5 -1\n";
pub(crate) const RULE4: &str = "\n8 1 2 1\n1 7 7 3 4 2 6 -1\n2 7 7 7 6 1 4 5 -1\n3 5 5 4 1 -1\n4 7 7 5 2 1 3 -1\n5 6 0 2 4 -1\n6 5 5 1 2 7 8 -1\n7 6 6 8 6 2 -1\n8 7 0 6 7 -1\n";

pub(crate) const CW1: &str = "8 1\n1 7 7 2 3 4 5 6 7 8\n2 5 5 3 1 8 -1\n3 5 5 4 1 2 -1\n4 6 6 5 1 3 -1\n5 5 5 6 1 4 -1\n6 5 5 7 1 5 -1\n7 5 5 8 1 6 -1\n8 9 9 2 1 7 -1\n";
pub(crate) const CW2: &str = "18 1\n1 7 7 2 3 4 5 6 7 8\n2 5 5 1 8 9 10 3\n3 7 7 1 2 10 11 12 13 4\n4 5 5 1 3 13 14 5\n5 5 5 1 4 14 15 6\n6 9 9 16 7 1 5 15 -1\n7 5 5 1 6 16 17 8\n8 6 6 2 1 7 17 18 9\n9 5 9 10 2 8 18 -1\n10 5 9 11 3 2 9 -1\n11 5 9 12 3 10 -1\n12 5 9 13 3 11 -1\n13 5 9 14 4 3 12 -1\n14 5 9 15 5 4 13 -1\n15 5 9 6 5 14 -1\n16 5 9 17 7 6 -1\n17 5 9 18 8 7 16 -1\n18 5 9 9 8 17 -1\n";

pub(crate) const CONF1: &str = "\n17 10\n11 5 1 12 17 9 10\n12 5 1 2 13 17 11\n13 6 2 14 16 7 17 12\n14 5 2 3 15 16 13\n15 5 3 4 5 16 14\n16 6 5 6 7 13 14 15\n17 6 7 8 9 11 12 13\n";
pub(crate) const CONF2: &str =
    "\n11 7\n8 5 1 2 9 11 7\n9 6 2 3 4 10 11 8\n10 5 4 5 6 11 9\n11 5 6 7 8 9 10\n";
