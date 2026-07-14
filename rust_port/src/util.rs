//! Shared helpers.
//!
//! Contains `Unionfind`, `lex_min` (lexicographically-minimal rotation test),
//! the `FromFile` trait, and the `get_objects` directory loader.

use std::cmp::Ordering;
use std::path::{Path, PathBuf};

/// Disjoint-set forest (union-find) without path compression or union-by-rank,
/// matching the C++ `Unionfind`.
///
/// The C++ stores `parents[x] < 0` to mark a root (with the value `-1`); here a
/// root is `None` and an interior node is `Some(parent)`.
pub struct Unionfind {
    pub n: usize,
    parents: Vec<Option<usize>>,
}

impl Unionfind {
    pub fn new(n: usize) -> Self {
        Unionfind {
            n,
            parents: vec![None; n],
        }
    }

    /// Representative of `x`.
    pub fn root(&self, mut x: usize) -> usize {
        while let Some(p) = self.parents[x] {
            x = p;
        }
        x
    }

    /// Attach `x`'s tree under `y`'s root: `parents[root(x)] = root(y)`.
    pub fn unite(&mut self, x: usize, y: usize) {
        let x = self.root(x);
        let y = self.root(y);
        if x == y {
            return;
        }
        self.parents[x] = Some(y);
    }

    pub fn same(&self, x: usize, y: usize) -> bool {
        self.root(x) == self.root(y)
    }

    /// `root(i)` for every `i`. Always total.
    pub fn each_root(&self) -> Vec<usize> {
        (0..self.n).map(|i| self.root(i)).collect()
    }

    /// The indices that are roots.
    pub fn all_roots(&self) -> Vec<usize> {
        (0..self.n).filter(|&i| self.parents[i].is_none()).collect()
    }

    /// A relabelling map: each root gets a fresh sequential index; non-roots map
    /// to `None` (the C++ `-1`). Composes with [`each_root`](Self::each_root) via
    /// [`crate::mapping::compose_map`] to renumber a quotient (see
    /// `PseudoTriangulation::disjoint_union`).
    pub fn index_roots(&self) -> Vec<Option<usize>> {
        let mut index = 0;
        self.parents
            .iter()
            .map(|parent| {
                if parent.is_some() {
                    return None;
                }
                let id = Some(index);
                index += 1;
                id
            })
            .collect()
    }

    pub fn num_roots(&self) -> usize {
        (0..self.n).filter(|&i| self.parents[i].is_none()).count()
    }
}

/// Whether `a` is lexicographically minimal among all its rotations.
///
/// Rotation `r` never materialises: against `a` it compares as `a[r..]` vs
/// `a[..n-r]`, with `a[..r]` vs `a[n-r..]` as the tiebreak -- two borrowed
/// slice comparisons, no allocation or shifting.
pub fn lex_min<T: Ord>(a: &[T]) -> bool {
    let n = a.len();
    (1..n).all(|r| match a[r..].cmp(&a[..n - r]) {
        Ordering::Less => false,
        Ordering::Greater => true,
        Ordering::Equal => a[..r] >= a[n - r..],
    })
}

/// A type that can be loaded from a single file. Implementations may panic on
/// malformed input.
pub trait FromFile: Sized {
    fn from_file(path: &Path) -> Self;
}

/// Load every regular file in `dir` whose extension matches `extension`
/// (e.g. `".rule"`), as `T`, **sorted by path**.
///
/// Ordering is observable (it defines the `combined_flag` rule order, see
/// `../FORMAT.md`), so we sort explicitly rather than rely on filesystem order.
pub fn get_objects<T: FromFile>(dir: &Path, extension: &str) -> Vec<T> {
    // `Path::extension` yields the suffix without the leading dot. Normalise so
    // callers can pass ".rule".
    let want = extension.trim_start_matches('.');

    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read directory {}: {e}", dir.display()))
        .map(|entry| entry.expect("directory entry").path())
        .filter(|p| p.is_file() && p.extension().and_then(|e| e.to_str()) == Some(want))
        .collect();
    paths.sort();

    paths
        .iter()
        .map(|p| {
            tracing::debug!("Loading from file: {}", p.display());
            T::from_file(p)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    #[test]
    fn unionfind_basic() {
        let mut uf = Unionfind::new(5);
        assert_eq!(uf.num_roots(), 5);
        uf.unite(0, 1);
        uf.unite(3, 4);
        assert!(uf.same(0, 1));
        assert!(!uf.same(0, 2));
        assert!(uf.same(3, 4));
        assert_eq!(uf.num_roots(), 3);

        // Roots are 1, 2, 4 (unite attaches root(x) under root(y)).
        assert_eq!(uf.all_roots(), vec![1, 2, 4]);
        assert_eq!(uf.each_root(), vec![1, 1, 2, 4, 4]);
        // index_roots numbers the roots in order; non-roots are None.
        assert_eq!(
            uf.index_roots(),
            vec![None, Some(0), Some(1), None, Some(2)]
        );
    }

    #[test]
    fn unionfind_relabel_composes() {
        // The disjoint_union pattern: compose_map(each_root, index_roots) yields
        // a total map onto the compacted root indices.
        let mut uf = Unionfind::new(4);
        uf.unite(0, 2);
        let each: Vec<Option<usize>> = uf.each_root().into_iter().map(Some).collect();
        let relabel = crate::mapping::compose_map(&each, &uf.index_roots());
        // No None survives: each_root always points at a root.
        assert!(relabel.iter().all(|x| x.is_some()));
        assert_eq!(relabel.len(), 4);
    }

    #[test]
    fn lex_min_detects_minimal_rotation() {
        assert!(lex_min(&[1, 2, 3]));
        assert!(!lex_min(&[2, 3, 1])); // rotation [1,2,3] is smaller
        assert!(!lex_min(&[3, 1, 2]));
        assert!(lex_min(&[1, 1, 2]));
        assert!(lex_min::<i32>(&[])); // vacuously minimal
        assert!(lex_min(&[5])); // single element
    }

    /// Property (self-contained oracle): `lex_min(v)` agrees with the brute-force
    /// definition -- `v` is minimal iff no rotation of `v` is strictly smaller.
    /// The right-hand side is computed independently (generate every rotation and
    /// compare), so nothing here is transcribed from the C++.
    #[quickcheck]
    fn prop_lex_min_matches_bruteforce(v: Vec<i8>) -> bool {
        let n = v.len();
        let is_min = (0..n).all(|k| {
            let rot: Vec<i8> = (0..n).map(|j| v[(j + k) % n]).collect();
            v.as_slice() <= rot.as_slice()
        });
        lex_min(&v) == is_min
    }

    struct Line(String);
    impl FromFile for Line {
        fn from_file(path: &Path) -> Self {
            Line(std::fs::read_to_string(path).unwrap().trim().to_string())
        }
    }

    #[test]
    fn get_objects_filters_and_sorts() {
        let dir = tempfile::tempdir().unwrap();
        // Create out of order, with a non-matching extension mixed in.
        std::fs::write(dir.path().join("b.rule"), "B").unwrap();
        std::fs::write(dir.path().join("a.rule"), "A").unwrap();
        std::fs::write(dir.path().join("c.other"), "C").unwrap();

        let objs: Vec<Line> = get_objects(dir.path(), ".rule");
        let got: Vec<&str> = objs.iter().map(|l| l.0.as_str()).collect();
        assert_eq!(got, vec!["A", "B"]); // sorted by path, ".other" excluded
        // `dir` auto-removes on drop.
    }
}
