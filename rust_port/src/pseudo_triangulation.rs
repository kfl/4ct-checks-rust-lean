//! Phase 2 — combinatorial map. Port of `../src/pseudo_triangulation.{hpp,cpp}`.
//!
//! A `PseudoTriangulation` is a rotation system on `n` vertices built from darts
//! (half-edges). `Dart { head, rev, succ, pred }`:
//! - `head` — the vertex this dart points at (always present);
//! - `rev`  — the reverse dart (always present);
//! - `succ` / `pred` — next / previous dart in the rotation around `head`,
//!   or `None` at a boundary (R1: the C++ `nil = -1`).

use crate::compact_index::OptIdx;
use crate::mapping::{Mappings, compose_map, split_map};
use crate::util::Unionfind;
use std::collections::VecDeque;

/// A half-edge. `head`/`rev` are total; `succ`/`pred` are `None` at a boundary.
/// All four are stored compactly (`head`/`rev` as `u32`, `succ`/`pred` as
/// [`OptIdx`]); the accessors below present the domain-facing `usize` /
/// `Option<usize>` view.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dart {
    head: u32,
    rev: u32,
    succ: OptIdx,
    pred: OptIdx,
}

impl Dart {
    pub fn new(head: usize, rev: usize, succ: Option<usize>, pred: Option<usize>) -> Self {
        Dart {
            head: index_to_u32(head, "head vertex"),
            rev: index_to_u32(rev, "reverse dart"),
            succ: OptIdx::from_option(succ),
            pred: OptIdx::from_option(pred),
        }
    }

    pub fn head(self) -> usize {
        self.head as usize
    }

    pub fn rev(self) -> usize {
        self.rev as usize
    }

    pub fn succ(self) -> Option<usize> {
        self.succ.get()
    }

    pub fn pred(self) -> Option<usize> {
        self.pred.get()
    }

    pub fn set_succ(&mut self, succ: Option<usize>) {
        self.succ = OptIdx::from_option(succ);
    }

    pub fn set_pred(&mut self, pred: Option<usize>) {
        self.pred = OptIdx::from_option(pred);
    }

    pub fn swap_succ_pred(&mut self) {
        std::mem::swap(&mut self.succ, &mut self.pred);
    }
}

fn index_to_u32(idx: usize, name: &str) -> u32 {
    u32::try_from(idx).unwrap_or_else(|_| panic!("{name} index {idx} exceeds u32::MAX"))
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PseudoTriangulation {
    pub n: usize,
    pub darts: Vec<Dart>,
}

impl PseudoTriangulation {
    pub fn new(n: usize, darts: Vec<Dart>) -> Self {
        PseudoTriangulation { n, darts }
    }

    /// Multi-line dump of every dart (C++ `debug`).
    pub fn debug(&self) -> String {
        let mut res = format!("N: {}\n", self.n);
        for d in &self.darts {
            res += &format!(
                "Dart({}, {}, {}, {}),\n",
                d.head(),
                fmt_idx(Some(d.rev())),
                fmt_idx(d.succ()),
                fmt_idx(d.pred())
            );
        }
        res
    }

    /// Human-readable rotation view (C++ `to_string`).
    pub fn show(&self) -> String {
        let mut res = format!("N: {}\n", self.n);
        let edges: Vec<(usize, usize)> = self
            .darts
            .iter()
            .map(|d| (d.head(), self.darts[d.rev()].head()))
            .collect();
        let e_rotations = self.get_e_rotations();
        for (v, rotation) in e_rotations.iter().enumerate() {
            res += &format!("{v}: ");
            for &dart_id in rotation {
                match dart_id {
                    None => res += "nil, ",
                    Some(e) => res += &format!("e{e}({}-{}), ", edges[e].0, edges[e].1),
                }
            }
            res += "\n";
        }
        res
    }

    /// Build from clockwise vertex rotations (C++ `from_v_rotations`).
    ///
    /// `rotations[a]` lists the neighbours of `a` clockwise; `-1` marks a
    /// boundary gap (kept as `i32` so the input matches the C++/file form).
    pub fn from_v_rotations(n: usize, rotations: &[Vec<i32>]) -> PseudoTriangulation {
        // dart_of[a][b] = id of the dart a -> b, if any.
        let mut dart_of = vec![vec![None::<usize>; n]; n];
        let mut fresh = 0usize;
        for a in 0..n {
            for &b in &rotations[a] {
                if b == -1 {
                    continue;
                }
                let b = b as usize;
                assert!(
                    dart_of[a][b].is_none(),
                    "Multiple darts between {a} and {b}"
                );
                dart_of[a][b] = Some(fresh);
                fresh += 1;
            }
        }

        let mut darts = vec![Dart::new(0, 0, None, None); fresh];
        for a in 0..n {
            let size = rotations[a].len();
            for i in 0..size {
                let b = rotations[a][i];
                if b == -1 {
                    continue;
                }
                let b = b as usize;
                let e = dart_of[a][b].expect("dart just assigned");
                let rev = dart_of[b][a]
                    .unwrap_or_else(|| panic!("Discrepancy in dart structure between {a} and {b}"));
                // Neighbour clockwise-after / clockwise-before `b` in a's rotation
                // (cyclic), mapping `-1` boundary markers to `None`.
                let s = if i < size - 1 {
                    rotations[a][i + 1]
                } else {
                    rotations[a][0]
                };
                let succ = if s != -1 {
                    dart_of[a][s as usize]
                } else {
                    None
                };
                let p = if i > 0 {
                    rotations[a][i - 1]
                } else {
                    rotations[a][size - 1]
                };
                let pred = if p != -1 {
                    dart_of[a][p as usize]
                } else {
                    None
                };
                darts[e] = Dart::new(a, rev, succ, pred);
            }
        }
        PseudoTriangulation::new(n, darts)
    }

    /// Side-by-side union, shifting `r`'s vertex/dart indices (C++ `disjoint_union`).
    pub fn disjoint_union(l: &PseudoTriangulation, r: &PseudoTriangulation) -> PseudoTriangulation {
        let n = l.n + r.n;
        let offset = l.darts.len();
        let mut darts = l.darts.clone();
        for d in &r.darts {
            darts.push(Dart::new(
                d.head() + l.n,
                d.rev() + offset,
                d.succ().map(|s| s + offset),
                d.pred().map(|p| p + offset),
            ));
        }
        PseudoTriangulation::new(n, darts)
    }

    /// Whether any dart is a self-loop (`head == rev's head`) (C++ `has_loop`).
    pub fn has_loop(&self) -> bool {
        self.darts
            .iter()
            .any(|d| d.head() == self.darts[d.rev()].head())
    }

    /// Number of darts pointing at each vertex (C++ `n_incident_darts`).
    pub fn n_incident_darts(&self) -> Vec<usize> {
        let mut n_incident = vec![0; self.n];
        for d in &self.darts {
            n_incident[d.head()] += 1;
        }
        n_incident
    }

    /// Which vertices lie on a boundary, i.e. have a dart with no `succ`
    /// (C++ `is_boundary`).
    pub fn is_boundary(&self) -> Vec<bool> {
        let mut is_boundary = vec![false; self.n];
        for d in &self.darts {
            if d.succ().is_none() {
                is_boundary[d.head()] = true;
            }
        }
        is_boundary
    }

    /// First dart of `v` in rotation order (the one with no `pred`); `None` if
    /// `v` has no boundary-start dart (C++ `first_dart`, where `nil` -> `None`).
    pub fn first_dart(&self, v: usize) -> Option<usize> {
        self.darts
            .iter()
            .position(|d| d.head() == v && d.pred().is_none())
    }

    /// Last dart of `v` (no `succ`) (C++ `last_dart`).
    pub fn last_dart(&self, v: usize) -> Option<usize> {
        self.darts
            .iter()
            .position(|d| d.head() == v && d.succ().is_none())
    }

    /// Any dart of `v` (C++ `any_dart`).
    pub fn any_dart(&self, v: usize) -> Option<usize> {
        self.darts.iter().position(|d| d.head() == v)
    }

    /// Follow `succ` `k` times from `e`; `None` if a boundary is hit
    /// (C++ `suc_k_times`).
    pub fn suc_k_times(&self, e: usize, k: i32) -> Option<usize> {
        let mut curr = e;
        for _ in 0..k {
            curr = self.darts[curr].succ()?;
        }
        Some(curr)
    }

    /// For each vertex, the cyclic rotation of its darts. A boundary rotation is
    /// terminated by a trailing `None` (C++ `get_e_rotations`, where the trailing
    /// `nil` plays the same role).
    pub fn get_e_rotations(&self) -> Vec<Vec<Option<usize>>> {
        let is_boundary = self.is_boundary();
        (0..self.n)
            .map(|v| {
                let e_start = if is_boundary[v] {
                    self.first_dart(v)
                } else {
                    self.any_dart(v)
                }
                .expect("vertex has at least one incident dart");
                let mut rotation = Vec::new();
                let mut e_cur = e_start;
                loop {
                    rotation.push(Some(e_cur));
                    match self.darts[e_cur].succ() {
                        None => {
                            rotation.push(None);
                            break;
                        }
                        Some(next) => {
                            e_cur = next;
                            if e_cur == e_start {
                                break;
                            }
                        }
                    }
                }
                rotation
            })
            .collect()
    }

    /// All darts from `head` to `tail` (C++ `get_darts`).
    pub fn get_darts(&self, head: usize, tail: usize) -> Vec<usize> {
        self.darts
            .iter()
            .enumerate()
            .filter(|(_, d)| d.head() == head && self.darts[d.rev()].head() == tail)
            .map(|(i, _)| i)
            .collect()
    }

    /// Free homomorphism gluing the given dart pairs, returning the quotient map
    /// and the index `Mappings` onto it (C++ member `free_homomorphism`).
    pub fn free_homomorphism(
        &self,
        dart_pairs: &[(usize, usize)],
    ) -> (PseudoTriangulation, Mappings) {
        let mut darts = self.darts.clone(); // copy: succ/pred get rewritten as we glue
        let mut uf_v = Unionfind::new(self.n);
        let mut uf_d = Unionfind::new(darts.len());
        let mut q: VecDeque<(usize, usize)> = dart_pairs.iter().copied().collect();

        while let Some((e, f)) = q.pop_front() {
            if uf_d.same(e, f) {
                continue;
            }
            let h_e = darts[e].head();
            let h_f = darts[f].head();
            if !uf_v.same(h_e, h_f) {
                uf_v.unite(h_e, h_f);
            }
            let e_star = uf_d.root(e);
            let f_star = uf_d.root(f);
            uf_d.unite(e_star, f_star); // f_star becomes the representative

            let e_rev = darts[e_star].rev();
            let f_rev = darts[f_star].rev();
            q.push_back((e_rev, f_rev));

            let e_succ = darts[e_star].succ();
            let f_succ = darts[f_star].succ();
            if let (Some(es), Some(fs)) = (e_succ, f_succ) {
                q.push_back((es, fs));
            }
            let e_pred = darts[e_star].pred();
            let f_pred = darts[f_star].pred();
            if let (Some(ep), Some(fp)) = (e_pred, f_pred) {
                q.push_back((ep, fp));
            }
            // Fill in the representative's open sides from the other dart.
            if e_succ.is_some() && f_succ.is_none() {
                darts[f_star].set_succ(e_succ);
            }
            if e_pred.is_some() && f_pred.is_none() {
                darts[f_star].set_pred(e_pred);
            }
        }

        // Renumber survivors: each_root (total) composed with index_roots
        // (compacted ids). `each_root` is lifted to `Some(..)` here so it joins
        // the partial-map algebra; the result is total (each_root hits roots).
        let v_map = compose_map(&lift(uf_v.each_root()), &uf_v.index_roots());
        let d_map = compose_map(&lift(uf_d.each_root()), &uf_d.index_roots());

        let darts_star = uf_d
            .all_roots()
            .into_iter()
            .map(|d| {
                let head = v_map[darts[d].head()].expect("vertex has a compacted id");
                let rev = d_map[darts[d].rev()].expect("rev dart survives");
                let succ = darts[d]
                    .succ()
                    .map(|s| d_map[s].expect("succ dart survives"));
                let pred = darts[d]
                    .pred()
                    .map(|p| d_map[p].expect("pred dart survives"));
                Dart::new(head, rev, succ, pred)
            })
            .collect();

        let pt = PseudoTriangulation::new(uf_v.num_roots(), darts_star);
        (pt, Mappings::new(v_map, d_map))
    }

    /// Free homomorphism over the disjoint union of `pt0`, `pt1`, identifying
    /// `dart_id0` (in `pt0`) with `dart_id1` (in `pt1`); returns the quotient and
    /// the two index maps restricted to each side (C++ static `free_homomorphism`).
    pub fn free_homomorphism_pair(
        pt0: &PseudoTriangulation,
        pt1: &PseudoTriangulation,
        dart_id0: usize,
        dart_id1: usize,
    ) -> (PseudoTriangulation, Mappings, Mappings) {
        let pt = PseudoTriangulation::disjoint_union(pt0, pt1);
        let dart_id1 = dart_id1 + pt0.darts.len();
        let (identified_pt, mappings) = pt.free_homomorphism(&[(dart_id0, dart_id1)]);
        let (vmap0, vmap1) = split_map(&mappings.vmap, pt0.n);
        let (dmap0, dmap1) = split_map(&mappings.dmap, pt0.darts.len());
        (
            identified_pt,
            Mappings::new(vmap0, dmap0),
            Mappings::new(vmap1, dmap1),
        )
    }
}

/// Lift a total index list into the partial-map algebra (`Some` everywhere).
fn lift(xs: Vec<usize>) -> Vec<Option<usize>> {
    xs.into_iter().map(Some).collect()
}

/// Format an optional index the way the C++ printed `int` darts (`-1` for nil).
fn fmt_idx(x: Option<usize>) -> String {
    match x {
        Some(v) => v.to_string(),
        None => "-1".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{d, imap};

    // from_v_rotations builds the dart structure from clockwise vertex rotations
    // (-1 marks a boundary gap).
    #[test]
    fn from_v_rotation() {
        let rotation = vec![vec![1, 2, -1], vec![2, 0, -1], vec![0, 1, -1]];
        let pt = PseudoTriangulation::from_v_rotations(3, &rotation);
        let expected = PseudoTriangulation::new(
            3,
            vec![
                d(0, 3, 1, -1),
                d(0, 4, -1, 0),
                d(1, 5, 3, -1),
                d(1, 0, -1, 2),
                d(2, 1, 5, -1),
                d(2, 2, -1, 4),
            ],
        );
        assert_eq!(pt, expected);
    }

    // free_homomorphism_pair glues two identical triangles along a matched dart
    // pair into their quotient, returning the index maps of each input onto it.
    #[test]
    fn identify() {
        let rotation0 = vec![vec![1, 2, -1], vec![2, 0, -1], vec![0, 1, -1]];
        let pt0 = PseudoTriangulation::from_v_rotations(3, &rotation0);
        let pt1 = PseudoTriangulation::from_v_rotations(3, &rotation0);
        let (pt, mappings0, mappings1) =
            PseudoTriangulation::free_homomorphism_pair(&pt0, &pt1, 0, 5);
        let expected = PseudoTriangulation::new(
            4,
            vec![
                d(3, 2, -1, 9),
                d(2, 3, 6, -1),
                d(0, 0, 3, -1),
                d(0, 1, -1, 2),
                d(1, 7, 5, -1),
                d(1, 8, -1, 4),
                d(2, 9, 7, 1),
                d(2, 4, -1, 6),
                d(3, 5, 9, -1),
                d(3, 6, 0, 8),
            ],
        );
        assert_eq!(mappings0.vmap, imap(&[3, 2, 0]));
        assert_eq!(mappings1.vmap, imap(&[1, 2, 3]));
        assert_eq!(mappings0.dmap, imap(&[9, 0, 1, 6, 2, 3]));
        assert_eq!(mappings1.dmap, imap(&[4, 5, 6, 7, 8, 9]));
        assert_eq!(pt, expected);
    }

    // free_homomorphism_pair on a larger asymmetric pair: the glued quotient
    // collapses to 3 vertices.
    #[test]
    fn identify2() {
        let pt0 = PseudoTriangulation::from_v_rotations(
            7,
            &[
                vec![1, 2, 3, 4, 5],
                vec![2, 0, 5, -1],
                vec![3, 0, 1, -1],
                vec![4, 0, 2, -1],
                vec![6, 5, 0, 3, -1],
                vec![1, 0, 4, 6, -1],
                vec![5, 4, -1],
            ],
        );
        let pt1 = PseudoTriangulation::from_v_rotations(
            9,
            &[
                vec![1, 2, 3, 4, 5, 6, 7],
                vec![8, 2, 0, 7, -1],
                vec![3, 0, 1, 8, -1],
                vec![4, 0, 2, -1],
                vec![5, 0, 3, -1],
                vec![6, 0, 4, -1],
                vec![7, 0, 5, -1],
                vec![1, 0, 6, -1],
                vec![2, 1, -1],
            ],
        );
        let (pt, _m0, _m1) = PseudoTriangulation::free_homomorphism_pair(&pt0, &pt1, 7, 10);
        let expected = PseudoTriangulation::new(
            3,
            vec![
                d(1, 1, 4, -1),
                d(2, 0, -1, 7),
                d(0, 5, 2, 2),
                d(1, 7, -1, 6),
                d(1, 6, 5, 0),
                d(1, 2, 6, 4),
                d(1, 4, 3, 5),
                d(2, 3, 1, -1),
            ],
        );
        assert_eq!(pt, expected);
    }
}
