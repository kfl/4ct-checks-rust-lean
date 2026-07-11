//! Phase 1 — leaf type. Port of `../src/mapping.{hpp,cpp}`.
//!
//! `Mappings { vmap, dmap }` carries vertex- and dart-index maps and supports
//! composition. Free functions `compose_map` / `split_map` go here too.
//!
//! R1 (index / sentinel representation — the crate-wide decision):
//! An index map entry is `Option<usize>`, where `None` is the C++ `-1`
//! ("unmapped"). `homomorphism` (P3) returns *partial* maps (unreached
//! vertices/darts are `-1`), so the type must admit "no image". Using `Option`
//! instead of an `i32` sentinel turns the C++ `== -1` checks into `is_none()`
//! and — crucially for trust — turns the latent UB of indexing with `-1`
//! (`map2[map1[i]]` when `map1[i] == -1`) into a defined `None`. On the domain
//! actually exercised (total maps), the two are identical; see the open item in
//! `PORTING_PLAN.md` to confirm composition is only ever used on total maps.

/// A vertex- or dart-index map. `None` == the C++ `-1` (unmapped).
pub type IndexMap = Vec<Option<usize>>;

/// Vertex map + dart map produced by (free) homomorphisms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mappings {
    pub vmap: IndexMap,
    pub dmap: IndexMap,
}

impl Mappings {
    pub fn new(vmap: IndexMap, dmap: IndexMap) -> Self {
        Mappings { vmap, dmap }
    }

    /// Identity maps on `n` vertices and `dart_size` darts (C++ `initial_mappings`).
    pub fn initial_mappings(n: usize, dart_size: usize) -> Self {
        let vmap = (0..n).map(Some).collect();
        let dmap = (0..dart_size).map(Some).collect();
        Mappings { vmap, dmap }
    }

    /// `self` followed by `other` (C++ `compose`: `result[i] = other[self[i]]`).
    pub fn compose(&self, other: &Mappings) -> Mappings {
        Mappings {
            vmap: compose_map(&self.vmap, &other.vmap),
            dmap: compose_map(&self.dmap, &other.dmap),
        }
    }
}

/// Compose two index maps: `result[i] = map2[map1[i]]` (C++ `compose_map`).
///
/// `None` propagates: if `map1[i]` is unmapped, so is the result. This matches
/// C++ on every total input and is strictly safer on partial input (no UB).
pub fn compose_map(map1: &[Option<usize>], map2: &[Option<usize>]) -> IndexMap {
    map1.iter().map(|&j| j.and_then(|j| map2[j])).collect()
}

/// Split an index map at `l` into `(map[..l], map[l..])` (C++ `split_map`).
pub fn split_map(map: &[Option<usize>], l: usize) -> (IndexMap, IndexMap) {
    assert!(l <= map.len());
    (map[..l].to_vec(), map[l..].to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(xs: &[usize]) -> IndexMap {
        xs.iter().map(|&x| Some(x)).collect()
    }

    #[test]
    fn initial_is_identity() {
        let id = Mappings::initial_mappings(3, 4);
        assert_eq!(id.vmap, m(&[0, 1, 2]));
        assert_eq!(id.dmap, m(&[0, 1, 2, 3]));
    }

    #[test]
    fn compose_matches_cpp_semantics() {
        // result[i] = map2[map1[i]]
        let map1 = m(&[2, 0, 1]);
        let map2 = m(&[10, 11, 12]);
        assert_eq!(compose_map(&map1, &map2), m(&[12, 10, 11]));
    }

    #[test]
    fn compose_with_identity_is_noop() {
        let id = Mappings::initial_mappings(3, 3);
        let a = Mappings::new(m(&[1, 2, 0]), m(&[2, 1, 0]));
        assert_eq!(a.compose(&id), a);
        assert_eq!(id.compose(&a), a);
    }

    #[test]
    fn compose_propagates_none() {
        let map1: IndexMap = vec![Some(0), None, Some(1)];
        let map2 = m(&[7, 8]);
        assert_eq!(compose_map(&map1, &map2), vec![Some(7), None, Some(8)]);
    }

    #[test]
    fn split_partitions() {
        let map = m(&[0, 1, 2, 3, 4]);
        let (l, r) = split_map(&map, 2);
        assert_eq!(l, m(&[0, 1]));
        assert_eq!(r, m(&[2, 3, 4]));
        let (l, r) = split_map(&map, 0);
        assert!(l.is_empty());
        assert_eq!(r, map);
    }
}
