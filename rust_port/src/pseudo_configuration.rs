//! Configuration with degrees.
//!
//! This embeds a `PseudoTriangulation` (`tri`) and accesses it directly
//! (`self.tri.darts`, `self.tri.first_dart(v)`, …) rather than inheriting from
//! it -- no `Deref`. A shared trait is deferred until `Configuration`, `Rule`,
//! and `CartWheel` need to share these methods.
//!
//! The BFS `homomorphism` is the trickiest method -- it initialises the
//! vertex/dart maps to "unmapped" (`None`, the C++ `-1`) and branches on the
//! sentinel.
//!
//! Scope note: methods that consume derived types are split into separate `impl`
//! blocks (modules in one crate may reference each other freely), so they live
//! here as their dependencies land:
//! - the reducible-configuration cluster -- `contain_conf`,
//!   `darts_by_degree`, `rooted_contain_conf`, `blocked_by_reducible_configuration`,
//!   `representative_degree` -- needed so `rule::combine_rules` compiles.
//! - the charge methods (`always_apply`, `never_apply`, `amount_of_*`,
//!   `dominantly_apply`) and the cartwheel-combination methods
//!   (`combine_each_cartwheel`, `combine_each_cartwheel_twice`), whose tests need
//!   `CartWheel`.

use crate::cartwheel::CartWheel;
use crate::compact_index::OptIdx;
use crate::configuration::Configuration;
use crate::degree::{CARTWHEEL_DEG_MAX, CONF_DEG_MAX, Degree, INFTY};
use crate::mapping::Mappings;
use crate::pseudo_triangulation::{Dart, PseudoTriangulation};
use crate::rule::{CombinedRule, Rule};
use crate::work_queue::WorkQueue;
use rayon::prelude::*;
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PseudoConfiguration {
    pub tri: PseudoTriangulation,
    pub degrees: Vec<Degree>,
}

impl PseudoConfiguration {
    /// Construct from `(N, darts, degrees)`.
    pub fn new(n: usize, darts: Vec<Dart>, degrees: Vec<Degree>) -> Self {
        PseudoConfiguration {
            tri: PseudoTriangulation::new(n, darts),
            degrees,
        }
    }

    /// Multi-line dump.
    pub fn debug(&self) -> String {
        let mut res = self.tri.debug();
        for deg in &self.degrees {
            res += &format!("Degree({}, {}),\n", deg.lower, deg.upper);
        }
        res
    }

    /// Human-readable rotation view with degrees.
    pub fn show(&self) -> String {
        let mut res = format!("N: {}\n", self.tri.n);
        let edges: Vec<(usize, usize)> = self
            .tri
            .darts
            .iter()
            .map(|d| (d.head(), self.tri.darts[d.rev()].head()))
            .collect();
        let e_rotations = self.tri.get_e_rotations();
        for (v, rotation) in e_rotations.iter().enumerate() {
            res += &format!(
                "{v}, deg=({}, {}): ",
                self.degrees[v].lower, self.degrees[v].upper
            );
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

    /// Build from vertex rotations + degrees.
    pub fn from_v_rotations(n: usize, v_rotations: &[Vec<i32>], degrees: Vec<Degree>) -> Self {
        assert_eq!(degrees.len(), n);
        let tri = PseudoTriangulation::from_v_rotations(n, v_rotations);
        PseudoConfiguration { tri, degrees }
    }

    /// Side-by-side union.
    pub fn disjoint_union(l: &PseudoConfiguration, r: &PseudoConfiguration) -> PseudoConfiguration {
        let tri = PseudoTriangulation::disjoint_union(&l.tri, &r.tri);
        let mut degrees = l.degrees.clone();
        degrees.extend_from_slice(&r.degrees);
        PseudoConfiguration { tri, degrees }
    }

    /// BFS graph homomorphism rooted at a dart pair, accepting a vertex degree
    /// compatibility test. Returns the index maps if a homomorphism exists.
    ///
    /// `vmap`/`dmap` start all-`None` ("unmapped", the C++ `-1`) and the boundary
    /// branches turn on `succ` being present while `succ_star` is `None`.
    /// The returned `Mappings` may be *partial*. The scratch maps use the compact
    /// 4-byte [`OptIdx`] (same `None`-is-unmapped semantics as the C++ `-1`), and
    /// are decoded to the public `Option<usize>` representation at the return.
    pub fn homomorphism<F>(
        from: &PseudoConfiguration,
        dart_from: usize,
        to: &PseudoConfiguration,
        dart_to: usize,
        degree_test: F,
    ) -> Option<Mappings>
    where
        F: Fn(Degree, Degree) -> bool,
    {
        let mut vmap = vec![OptIdx::NONE; from.tri.n];
        let mut dmap = vec![OptIdx::NONE; from.tri.darts.len()];
        let mut q =
            WorkQueue::with_capacity(from.tri.darts.len().saturating_mul(3).saturating_add(1));
        q.push((dart_from, dart_to));

        while let Some((f, f_star)) = q.pop() {
            if let Some(existing) = dmap[f].get() {
                if existing != f_star {
                    return None;
                }
                continue;
            }
            dmap[f] = OptIdx::some(f_star);

            let h = from.tri.darts[f].head();
            let h_star = to.tri.darts[f_star].head();
            if let Some(vh) = vmap[h].get()
                && vh != h_star
            {
                return None;
            }
            vmap[h] = OptIdx::some(h_star);
            if !degree_test(from.degrees[h], to.degrees[h_star]) {
                return None;
            }

            q.push((from.tri.darts[f].rev(), to.tri.darts[f_star].rev()));

            match (from.tri.darts[f].succ(), to.tri.darts[f_star].succ()) {
                (Some(_), None) => return None,
                (Some(s), Some(ss)) => q.push((s, ss)),
                _ => {}
            }
            match (from.tri.darts[f].pred(), to.tri.darts[f_star].pred()) {
                (Some(_), None) => return None,
                (Some(p), Some(pp)) => q.push((p, pp)),
                _ => {}
            }
        }

        Some(Mappings::new(
            vmap.iter().map(|x| x.get()).collect(),
            dmap.iter().map(|x| x.get()).collect(),
        ))
    }

    /// Glue the dart pairs as a combinatorial map and reconcile degrees, if the
    /// result is loop-free and degree-consistent.
    pub fn dart_identification(
        &self,
        dart_pairs: &[(usize, usize)],
    ) -> Option<(PseudoConfiguration, Mappings)> {
        let (z_star, mappings) = self.tri.free_homomorphism(dart_pairs);
        if z_star.has_loop() {
            return None; // a loop error
        }

        let mut degrees_star = vec![Degree::new(1, INFTY); z_star.n];
        for v in 0..self.tri.n {
            let v_star = mappings.vmap[v].expect("identification map is total");
            if Degree::is_disjoint(&degrees_star[v_star], &self.degrees[v]) {
                return None; // a degree-mismatch error
            }
            degrees_star[v_star] = Degree::intersection(&degrees_star[v_star], &self.degrees[v]);
        }

        let pc = PseudoConfiguration {
            tri: z_star,
            degrees: degrees_star,
        };
        Some((pc, mappings))
    }

    /// Identify the dart pairs and resolve any resulting degree issues.
    pub fn free_homomorphism(
        &self,
        dart_pairs: &[(usize, usize)],
    ) -> Vec<(PseudoConfiguration, Mappings)> {
        let Some((z_star, mappings)) = self.dart_identification(dart_pairs) else {
            return Vec::new();
        };
        z_star
            .resolve_degree_issues()
            .into_iter()
            .map(|(z_tilde, mappings_tilde)| {
                let composed = mappings.compose(&mappings_tilde);
                (z_tilde, composed)
            })
            .collect()
    }

    /// Free homomorphism over the disjoint union of `pc0`, `pc1`, identifying
    /// `dart_id0` (in `pc0`) with `dart_id1` (in `pc1`); returns each result with
    /// the two index maps restricted to each side.
    pub fn free_homomorphism_pair(
        pc0: &PseudoConfiguration,
        pc1: &PseudoConfiguration,
        dart_id0: usize,
        dart_id1: usize,
    ) -> Vec<(PseudoConfiguration, Mappings, Mappings)> {
        let pc = PseudoConfiguration::disjoint_union(pc0, pc1);
        let dart_id1 = dart_id1 + pc0.tri.darts.len();
        pc.free_homomorphism(&[(dart_id0, dart_id1)])
            .into_iter()
            .map(|(identified_pc, mappings)| {
                let (vmap0, vmap1) = crate::mapping::split_map(&mappings.vmap, pc0.tri.n);
                let (dmap0, dmap1) = crate::mapping::split_map(&mappings.dmap, pc0.tri.darts.len());
                (
                    identified_pc,
                    Mappings::new(vmap0, dmap0),
                    Mappings::new(vmap1, dmap1),
                )
            })
            .collect()
    }

    /// Enumerate the configurations obtained by resolving every degree issue
    /// (over-incident fixed vertices, boundary closures, degree splits) via BFS.
    /// Results come back in FIFO (queue) order.
    pub fn resolve_degree_issues(&self) -> Vec<(PseudoConfiguration, Mappings)> {
        let mut z = Vec::new();
        let mut q: VecDeque<(PseudoConfiguration, Mappings)> = VecDeque::new();
        let initial = Mappings::initial_mappings(self.tri.n, self.tri.darts.len());
        q.push_back((self.clone(), initial));

        while let Some((z_tilde, mappings_tilde)) = q.pop_front() {
            if z_tilde.inner_subdegree_error() {
                continue;
            }
            if let Some(v) = z_tilde.vertex_single_degree_issue() {
                if let Some((z_star, mappings_star)) = z_tilde.fix_single_degree_issue(v) {
                    let composed = mappings_tilde.compose(&mappings_star);
                    q.push_back((z_star, composed));
                }
                continue;
            }
            if let Some((z1, z2)) = z_tilde.single_out_lower_degree() {
                q.push_back((z1, mappings_tilde.clone()));
                q.push_back((z2, mappings_tilde));
                continue;
            }
            z.push((z_tilde, mappings_tilde));
        }
        z
    }

    /// Whether an interior vertex has fewer incident darts than its lower degree
    /// bound.
    pub fn inner_subdegree_error(&self) -> bool {
        let n_incident = self.tri.n_incident_darts();
        let is_boundary = self.tri.is_boundary();
        (0..self.tri.n).any(|v| !is_boundary[v] && (n_incident[v] as i32) < self.degrees[v].lower)
    }

    /// Find a fixed-degree vertex whose incidences need adjusting.
    pub fn vertex_single_degree_issue(&self) -> Option<usize> {
        let n_incident = self.tri.n_incident_darts();
        let is_boundary = self.tri.is_boundary();
        (0..self.tri.n).find(|&v| {
            if !self.degrees[v].is_fixed() {
                return false;
            }
            let inc = n_incident[v] as i32;
            self.degrees[v].lower < inc || (is_boundary[v] && inc == self.degrees[v].lower)
        })
    }

    /// Resolve the single degree issue at `v`.
    pub fn fix_single_degree_issue(&self, v: usize) -> Option<(PseudoConfiguration, Mappings)> {
        assert!(self.degrees[v].is_fixed());
        let n_incident = self.tri.n_incident_darts();
        let is_boundary = self.tri.is_boundary();
        let inc = n_incident[v] as i32;

        if self.degrees[v].lower < inc {
            let e = if is_boundary[v] {
                self.tri.first_dart(v)
            } else {
                self.tri.any_dart(v)
            }
            .expect("vertex with excess incidences has a dart");
            let f = self
                .tri
                .suc_k_times(e, self.degrees[v].lower)
                .expect("step stays within the rotation");
            self.dart_identification(&[(e, f)])
        } else if is_boundary[v] && inc == self.degrees[v].lower {
            self.add_boundary_darts(v).map(|pc| {
                (
                    pc,
                    Mappings::initial_mappings(self.tri.n, self.tri.darts.len()),
                )
            })
        } else {
            unreachable!("fix_single_degree_issue called without a degree issue")
        }
    }

    /// Close a boundary fan at `v` by adding the two darts of a new edge
    ///. `None` on a boundary error (`u == w`).
    pub fn add_boundary_darts(&self, v: usize) -> Option<PseudoConfiguration> {
        let mut z = self.clone();
        let e_first = z
            .tri
            .first_dart(v)
            .expect("boundary vertex has a first dart");
        let e_last = z.tri.last_dart(v).expect("boundary vertex has a last dart");
        let e_first_rev = z.tri.darts[e_first].rev();
        let e_last_rev = z.tri.darts[e_last].rev();
        let u = z.tri.darts[e_first_rev].head();
        let w = z.tri.darts[e_last_rev].head();
        if u == w {
            return None; // a boundary error
        }
        let d_uw = z.tri.darts.len();
        let d_wu = d_uw + 1;
        z.tri
            .darts
            .push(Dart::new(u, d_wu, None, Some(e_first_rev)));
        z.tri.darts.push(Dart::new(w, d_uw, Some(e_last_rev), None));
        z.tri.darts[e_first].set_pred(Some(e_last));
        z.tri.darts[e_last].set_succ(Some(e_first));
        z.tri.darts[e_first_rev].set_succ(Some(d_uw));
        z.tri.darts[e_last_rev].set_pred(Some(d_wu));
        Some(z)
    }

    /// Split the first range-valued vertex into its lowest degree vs. the rest.
    pub fn single_out_lower_degree(&self) -> Option<(PseudoConfiguration, PseudoConfiguration)> {
        let n_incident = self.tri.n_incident_darts();
        let v = (0..self.tri.n).find(|&v| {
            let deg = self.degrees[v];
            deg.lower < deg.upper && deg.lower <= n_incident[v] as i32
        })?;
        let deg = self.degrees[v];
        let mut z1 = self.clone();
        let mut z2 = self.clone();
        z1.degrees[v].upper = deg.lower;
        z2.degrees[v].lower = deg.lower + 1;
        Some((z1, z2))
    }
}

// --- reducible-configuration cluster (consumes `Configuration`) --------------
impl PseudoConfiguration {
    /// Whether this configuration contains any reducible configuration in `confs`.
    pub fn contain_conf(&self, center: usize, confs: &[Configuration]) -> bool {
        let darts_by_degree = self.darts_by_degree();
        for conf in confs {
            // Root degrees are cached (derived and validated by
            // `Configuration::new`), so the sweep reads two fields per
            // configuration instead of re-deriving them.
            let d_y = conf.root_head_deg;
            let d_x = conf.root_tail_deg;
            for &f_star in &darts_by_degree[d_y as usize][d_x as usize] {
                if d_y > 8 && self.tri.darts[f_star].head() != center {
                    continue;
                }
                if self.rooted_contain_conf(f_star, conf) {
                    return true;
                }
            }
        }
        false
    }

    /// Bucket darts by the fixed (head-degree, tail-degree) of their endpoints,
    /// dropping endpoints above `CONF_DEG_MAX`.
    pub fn darts_by_degree(&self) -> Vec<Vec<Vec<usize>>> {
        let size = CONF_DEG_MAX as usize + 1;
        let mut buckets = vec![vec![Vec::new(); size]; size];
        for (i, e) in self.tri.darts.iter().enumerate() {
            let y = e.head();
            let x = self.tri.darts[e.rev()].head();
            assert!(self.degrees[y].is_fixed());
            assert!(self.degrees[x].is_fixed());
            let d_y = self.degrees[y].lower;
            let d_x = self.degrees[x].lower;
            if d_y > CONF_DEG_MAX || d_x > CONF_DEG_MAX {
                continue;
            }
            buckets[d_y as usize][d_x as usize].push(i);
        }
        buckets
    }

    /// Whether `conf` embeds into `self` rooted at `dart_id`, with the
    /// configuration's degrees included in `self`'s.
    pub fn rooted_contain_conf(&self, dart_id: usize, conf: &Configuration) -> bool {
        PseudoConfiguration::homomorphism(&conf.pc, conf.dart_id, self, dart_id, |a, b| {
            Degree::includes(&a, &b)
        })
        .is_some()
    }

    /// Whether every fixed-degree representative contains a reducible
    /// configuration.
    pub fn blocked_by_reducible_configuration(
        &self,
        center: usize,
        confs: &[Configuration],
    ) -> bool {
        self.representative_degree(center)
            .iter()
            .all(|z| z.contain_conf(center, confs))
    }

    /// Enumerate the fixed-degree representatives.
    /// High degrees collapse to a single `exact(upper)` instead of expanding.
    pub fn representative_degree(&self, center: usize) -> Vec<PseudoConfiguration> {
        let n = self.tri.n;
        let mut t: Vec<Vec<Degree>> = vec![vec![Degree::new(1, INFTY); n]];
        for (v, deg_v) in self.degrees.iter().enumerate() {
            // A high-degree vertex collapses to a single `exact(upper)`; the
            // threshold is CONF_DEG_MAX for the center and 8 for the others.
            let high_threshold = if v == center { CONF_DEG_MAX } else { 8 };
            let choices: Vec<Degree> = if deg_v.upper > high_threshold {
                vec![Degree::exact(deg_v.upper)]
            } else {
                (deg_v.lower..=deg_v.upper).map(Degree::exact).collect()
            };
            let mut new_t = Vec::new();
            for degs in &t {
                for &d in &choices {
                    let mut nd = degs.clone();
                    nd[v] = d;
                    new_t.push(nd);
                }
            }
            t = new_t;
        }
        t.into_iter()
            .map(|deg| PseudoConfiguration::new(n, self.tri.darts.clone(), deg))
            .collect()
    }
}

// --- charge methods + cartwheel combination (consume `Rule`/`CartWheel`) -----
impl PseudoConfiguration {
    /// Whether `rule` always applies at `dart_id` -- its degrees include this
    /// configuration's.
    pub fn always_apply(&self, dart_id: usize, rule: &Rule) -> bool {
        PseudoConfiguration::homomorphism(&rule.pc, rule.st_id, self, dart_id, |a, b| {
            Degree::includes(&a, &b)
        })
        .is_some()
    }

    /// Whether `rule` can never apply at `dart_id` -- no degree-overlapping
    /// homomorphism exists.
    pub fn never_apply(&self, dart_id: usize, rule: &Rule) -> bool {
        PseudoConfiguration::homomorphism(&rule.pc, rule.st_id, self, dart_id, |a, b| {
            Degree::has_intersection(&a, &b)
        })
        .is_none()
    }

    /// Total charge guaranteed to be sent along `dart_id`.
    pub fn amount_of_charge_send(&self, dart_id: usize, rules: &[Rule]) -> i32 {
        rules
            .iter()
            .filter(|r| self.always_apply(dart_id, r))
            .map(|r| r.amount)
            .sum()
    }

    /// Maximum charge that could possibly be sent along `dart_id` over the
    /// applicable combined rules.
    pub fn amount_of_possible_charge_send(
        &self,
        dart_id: usize,
        combined_rules: &[CombinedRule],
    ) -> i32 {
        let mut amount = 0;
        for cr in combined_rules {
            if self.never_apply(dart_id, &cr.rule) {
                continue;
            }
            amount = amount.max(cr.rule.amount);
        }
        amount
    }

    /// Whether `rule` dominantly applies at `dart_id`.
    pub fn dominantly_apply(&self, dart_id: usize, rule: &Rule) -> bool {
        let g_dominant = |deg_r: Degree, deg_c: Degree| {
            Degree::has_intersection(&deg_r, &deg_c)
                && (deg_r.upper == INFTY || deg_c.upper < CARTWHEEL_DEG_MAX)
        };
        PseudoConfiguration::homomorphism(&rule.pc, rule.st_id, self, dart_id, g_dominant).is_some()
    }

    /// Glue each cartwheel onto `dart`, keeping results not blocked by a
    /// reducible configuration. The sweep is a `par_iter` over the candidates;
    /// `collect` preserves the sequential order, so results are
    /// thread-count independent.
    pub fn combine_each_cartwheel(
        &self,
        dart: usize,
        cartwheels: &[CartWheel],
        confs: &[Configuration],
    ) -> Vec<(PseudoConfiguration, Mappings)> {
        cartwheels
            .par_iter()
            .flat_map_iter(|cartwheel| {
                let mut zs = Vec::new();
                for &center_dart in &cartwheel.center_darts {
                    let fhs = PseudoConfiguration::free_homomorphism_pair(
                        self,
                        &cartwheel.pc,
                        dart,
                        center_dart,
                    );
                    for (z_star, mappings_pc, _) in fhs {
                        if z_star.blocked_by_reducible_configuration(0, confs) {
                            continue;
                        }
                        zs.push((z_star, mappings_pc));
                    }
                }
                zs.into_iter()
            })
            .collect()
    }

    /// Glue cartwheels onto two darts in sequence.
    pub fn combine_each_cartwheel_twice(
        &self,
        dart1: usize,
        dart2: usize,
        cartwheels: &[CartWheel],
        confs: &[Configuration],
    ) -> Vec<(PseudoConfiguration, Mappings)> {
        let mut z_star_stars = Vec::new();
        for (z_star, cw2z_star) in self.combine_each_cartwheel(dart1, cartwheels, confs) {
            let mapped_dart2 = cw2z_star.dmap[dart2].expect("combination map is total");
            for (z, z_star2z) in z_star.combine_each_cartwheel(mapped_dart2, cartwheels, confs) {
                z_star_stars.push((z, cw2z_star.compose(&z_star2z)));
            }
        }
        z_star_stars
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{d, imap};

    // free_homomorphism_pair glues two copies along a dart pair; the quotient
    // carries both index maps (vmap/dmap) onto it.
    #[test]
    fn identify1() {
        let rotation = vec![vec![1, 2, -1], vec![2, 0, -1], vec![0, 1, -1]];
        let degrees = vec![Degree::new(5, 6), Degree::new(6, 7), Degree::exact(7)];
        let pc0 = PseudoConfiguration::from_v_rotations(3, &rotation, degrees.clone());
        let pc1 = PseudoConfiguration::from_v_rotations(3, &rotation, degrees);
        let pcs = PseudoConfiguration::free_homomorphism_pair(&pc0, &pc1, 5, 4);
        assert_eq!(pcs.len(), 1);
        let expected = PseudoConfiguration::new(
            4,
            vec![
                d(0, 2, 1, -1),
                d(0, 3, -1, 0),
                d(1, 0, -1, 5),
                d(3, 1, 8, -1),
                d(1, 7, 5, -1),
                d(1, 8, 2, 4),
                d(2, 9, 7, -1),
                d(2, 4, -1, 6),
                d(3, 5, 9, 3),
                d(3, 6, -1, 8),
            ],
            vec![
                Degree::new(5, 6),
                Degree::exact(6),
                Degree::new(6, 7),
                Degree::exact(7),
            ],
        );
        let (pc, m0, m1) = &pcs[0];
        assert_eq!(*pc, expected);
        assert_eq!(m0.vmap, imap(&[0, 1, 3]));
        assert_eq!(m0.dmap, imap(&[0, 1, 5, 2, 3, 8]));
        assert_eq!(m1.vmap, imap(&[1, 2, 3]));
        assert_eq!(m1.dmap, imap(&[4, 5, 6, 7, 8, 9]));
    }

    // homomorphism finds a degree-compatible embedding of pc0 into pc1 from a
    // start dart (Some), or None when the target dart's neighbourhood is
    // degree-incompatible.
    #[test]
    fn find_homomorphism() {
        let pc0 = PseudoConfiguration::from_v_rotations(
            5,
            &[
                vec![1, 2, 3, 4, -1],
                vec![2, 0, -1],
                vec![3, 0, 1, -1],
                vec![4, 0, 2, -1],
                vec![0, 3, -1],
            ],
            vec![
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(5),
            ],
        );
        let pc1 = PseudoConfiguration::from_v_rotations(
            7,
            &[
                vec![1, 2, 3, 4, 5, 6],
                vec![2, 0, 6, -1],
                vec![3, 0, 1, -1],
                vec![4, 0, 2, -1],
                vec![5, 0, 3, -1],
                vec![6, 0, 4, -1],
                vec![1, 0, 5, -1],
            ],
            vec![
                Degree::exact(6),
                Degree::new(5, INFTY),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(6),
            ],
        );
        let has_intersection = |a: Degree, b: Degree| Degree::has_intersection(&a, &b);
        // (0,1) -> (0,1)
        assert!(PseudoConfiguration::homomorphism(&pc0, 0, &pc1, 0, has_intersection).is_some());
        // (0,1) -> (6,1)
        assert!(PseudoConfiguration::homomorphism(&pc0, 0, &pc1, 8, has_intersection).is_none());
    }

    // resolve_degree_issues splits a centre whose degree range is not yet fixed
    // into its concrete completions -- here [5,8] yields 3 results.
    #[test]
    fn resolve_degree_issues1() {
        let rotation = vec![
            vec![1, 2, 3, 4, 5, 6, -1],
            vec![2, 0, -1],
            vec![3, 0, 1, -1],
            vec![4, 0, 2, -1],
            vec![5, 0, 3, -1],
            vec![6, 0, 4, -1],
            vec![0, 5, -1],
        ];
        let degrees = vec![
            Degree::new(5, 8),
            Degree::exact(6),
            Degree::exact(6),
            Degree::exact(6),
            Degree::exact(6),
            Degree::exact(6),
            Degree::exact(6),
        ];
        let pc = PseudoConfiguration::from_v_rotations(7, &rotation, degrees);
        let pcs = pc.resolve_degree_issues();
        assert_eq!(pcs.len(), 3);

        let expected0 = PseudoConfiguration::new(
            6,
            vec![
                d(0, 7, 1, 4),
                d(0, 10, 2, 0),
                d(0, 13, 3, 1),
                d(0, 16, 4, 2),
                d(0, 18, 0, 3),
                d(5, 8, 18, -1),
                d(1, 11, 7, -1),
                d(1, 0, 8, 6),
                d(1, 5, -1, 7),
                d(2, 14, 10, -1),
                d(2, 1, 11, 9),
                d(2, 6, -1, 10),
                d(3, 17, 13, -1),
                d(3, 2, 14, 12),
                d(3, 9, -1, 13),
                d(4, 19, 16, -1),
                d(4, 3, 17, 15),
                d(4, 12, -1, 16),
                d(5, 4, 19, 5),
                d(5, 15, -1, 18),
            ],
            vec![
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
            ],
        );
        let expected1 = PseudoConfiguration::new(
            7,
            vec![
                d(0, 7, 1, -1),
                d(0, 9, 2, 0),
                d(0, 12, 3, 1),
                d(0, 15, 4, 2),
                d(0, 18, 5, 3),
                d(0, 20, -1, 4),
                d(1, 10, 7, -1),
                d(1, 0, -1, 6),
                d(2, 13, 9, -1),
                d(2, 1, 10, 8),
                d(2, 6, -1, 9),
                d(3, 16, 12, -1),
                d(3, 2, 13, 11),
                d(3, 8, -1, 12),
                d(4, 19, 15, -1),
                d(4, 3, 16, 14),
                d(4, 11, -1, 15),
                d(5, 21, 18, -1),
                d(5, 4, 19, 17),
                d(5, 14, -1, 18),
                d(6, 5, 21, -1),
                d(6, 17, -1, 20),
            ],
            vec![
                Degree::new(7, 8),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
            ],
        );
        let expected2 = PseudoConfiguration::new(
            7,
            vec![
                d(0, 7, 1, 5),
                d(0, 9, 2, 0),
                d(0, 12, 3, 1),
                d(0, 15, 4, 2),
                d(0, 18, 5, 3),
                d(0, 20, 0, 4),
                d(1, 10, 7, -1),
                d(1, 0, 22, 6),
                d(2, 13, 9, -1),
                d(2, 1, 10, 8),
                d(2, 6, -1, 9),
                d(3, 16, 12, -1),
                d(3, 2, 13, 11),
                d(3, 8, -1, 12),
                d(4, 19, 15, -1),
                d(4, 3, 16, 14),
                d(4, 11, -1, 15),
                d(5, 21, 18, -1),
                d(5, 4, 19, 17),
                d(5, 14, -1, 18),
                d(6, 5, 21, 23),
                d(6, 17, -1, 20),
                d(1, 23, -1, 7),
                d(6, 22, 20, -1),
            ],
            vec![
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
            ],
        );
        assert_eq!(pcs[0].0, expected0);
        assert_eq!(pcs[1].0, expected1);
        assert_eq!(pcs[2].0, expected2);

        assert_eq!(pcs[0].1.vmap, imap(&[0, 5, 1, 2, 3, 4, 5]));
        assert_eq!(
            pcs[0].1.dmap,
            imap(&[
                4, 0, 1, 2, 3, 4, 5, 18, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19
            ])
        );
        assert_eq!(pcs[1].1.vmap, imap(&[0, 1, 2, 3, 4, 5, 6]));
        assert_eq!(
            pcs[1].1.dmap,
            imap(&[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21
            ])
        );
        assert_eq!(pcs[2].1.vmap, imap(&[0, 1, 2, 3, 4, 5, 6]));
        assert_eq!(
            pcs[2].1.dmap,
            imap(&[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21
            ])
        );
    }

    // resolve_degree_issues on a range that admits a single completion (one result).
    #[test]
    fn resolve_degree_issues2() {
        let rotation = vec![
            vec![1, 2, 3, 4, 5, 6],
            vec![2, 0, 6, -1],
            vec![3, 0, 1, -1],
            vec![4, 0, 2, -1],
            vec![5, 0, 3, -1],
            vec![6, 0, 4, -1],
            vec![1, 0, 5, -1],
        ];
        let degrees = vec![
            Degree::new(5, 8),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(5),
        ];
        let pc = PseudoConfiguration::from_v_rotations(7, &rotation, degrees);
        let pcs = pc.resolve_degree_issues();
        assert_eq!(pcs.len(), 1);
        let expected = PseudoConfiguration::new(
            7,
            vec![
                d(0, 7, 1, 5),
                d(0, 10, 2, 0),
                d(0, 13, 3, 1),
                d(0, 16, 4, 2),
                d(0, 19, 5, 3),
                d(0, 22, 0, 4),
                d(1, 11, 7, -1),
                d(1, 0, 8, 6),
                d(1, 21, -1, 7),
                d(2, 14, 10, -1),
                d(2, 1, 11, 9),
                d(2, 6, -1, 10),
                d(3, 17, 13, -1),
                d(3, 2, 14, 12),
                d(3, 9, -1, 13),
                d(4, 20, 16, -1),
                d(4, 3, 17, 15),
                d(4, 12, -1, 16),
                d(5, 23, 19, -1),
                d(5, 4, 20, 18),
                d(5, 15, -1, 19),
                d(6, 8, 22, -1),
                d(6, 5, 23, 21),
                d(6, 18, -1, 22),
            ],
            vec![
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
            ],
        );
        assert_eq!(pcs[0].0, expected);
        assert_eq!(pcs[0].1.vmap, imap(&[0, 1, 2, 3, 4, 5, 6]));
        assert_eq!(pcs[0].1.dmap, imap(&(0..24).collect::<Vec<_>>()));
    }

    // resolve_degree_issues on the icosahedron (all degrees already fixed at 5):
    // no split is needed, so the input is returned as the single result.
    #[test]
    fn resolve_degree_issues3() {
        let rotations = vec![
            vec![1, 3, 8, 7, 2, -1],
            vec![2, 5, 4, 3, 0, -1],
            vec![0, 7, 6, 5, 1, -1],
            vec![0, 1, 4, 9, 8],
            vec![1, 5, 10, 9, 3],
            vec![1, 2, 6, 10, 4],
            vec![2, 7, 11, 10, 5],
            vec![2, 0, 8, 11, 6],
            vec![0, 3, 9, 11, 7],
            vec![3, 4, 10, 11, 8],
            vec![4, 5, 6, 11, 9],
            vec![6, 7, 8, 9, 10],
        ];
        let degrees = vec![Degree::exact(5); 12];
        let icosahedral = PseudoConfiguration::from_v_rotations(12, &rotations, degrees);
        let pcs = icosahedral.resolve_degree_issues();
        assert_eq!(pcs.len(), 1);
        let expected = PseudoConfiguration::new(
            12,
            vec![
                d(0, 8, 1, 4),
                d(0, 13, 2, 0),
                d(0, 38, 3, 1),
                d(0, 34, 4, 2),
                d(0, 9, 0, 3),
                d(1, 23, 6, 58),
                d(1, 18, 7, 5),
                d(1, 14, 8, 6),
                d(1, 0, 58, 7),
                d(2, 4, 10, 59),
                d(2, 33, 11, 9),
                d(2, 28, 12, 10),
                d(2, 24, 59, 11),
                d(3, 1, 14, 17),
                d(3, 7, 15, 13),
                d(3, 22, 16, 14),
                d(3, 43, 17, 15),
                d(3, 39, 13, 16),
                d(4, 6, 19, 22),
                d(4, 27, 20, 18),
                d(4, 48, 21, 19),
                d(4, 44, 22, 20),
                d(4, 15, 18, 21),
                d(5, 5, 24, 27),
                d(5, 12, 25, 23),
                d(5, 32, 26, 24),
                d(5, 49, 27, 25),
                d(5, 19, 23, 26),
                d(6, 11, 29, 32),
                d(6, 37, 30, 28),
                d(6, 53, 31, 29),
                d(6, 50, 32, 30),
                d(6, 25, 28, 31),
                d(7, 10, 34, 37),
                d(7, 3, 35, 33),
                d(7, 42, 36, 34),
                d(7, 54, 37, 35),
                d(7, 29, 33, 36),
                d(8, 2, 39, 42),
                d(8, 17, 40, 38),
                d(8, 47, 41, 39),
                d(8, 55, 42, 40),
                d(8, 35, 38, 41),
                d(9, 16, 44, 47),
                d(9, 21, 45, 43),
                d(9, 52, 46, 44),
                d(9, 56, 47, 45),
                d(9, 40, 43, 46),
                d(10, 20, 49, 52),
                d(10, 26, 50, 48),
                d(10, 31, 51, 49),
                d(10, 57, 52, 50),
                d(10, 45, 48, 51),
                d(11, 30, 54, 57),
                d(11, 36, 55, 53),
                d(11, 41, 56, 54),
                d(11, 46, 57, 55),
                d(11, 51, 53, 56),
                d(1, 59, 5, 8),
                d(2, 58, 9, 12),
            ],
            vec![Degree::exact(5); 12],
        );
        assert_eq!(pcs[0].0, expected);
    }

    // free_homomorphism_pair on a larger pair with a single valid gluing.
    #[test]
    fn identify2() {
        let pc0 = PseudoConfiguration::from_v_rotations(
            6,
            &[
                vec![1, 2, 3, 4, 5],
                vec![2, 0, 5, -1],
                vec![3, 0, 1, -1],
                vec![4, 0, 2, -1],
                vec![5, 0, 3, -1],
                vec![1, 0, 4, -1],
            ],
            vec![
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(5),
            ],
        );
        let pc1 = PseudoConfiguration::from_v_rotations(
            10,
            &[
                vec![1, 2, 9, -1],
                vec![2, 0, -1],
                vec![3, 9, 0, 1, -1],
                vec![4, 7, 8, 9, 2, -1],
                vec![5, 6, 7, 3, -1],
                vec![6, 4, -1],
                vec![7, 4, 5, -1],
                vec![8, 3, 4, 6, -1],
                vec![9, 3, 7, -1],
                vec![0, 2, 3, 8, -1],
            ],
            vec![
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
            ],
        );
        let pcs = PseudoConfiguration::free_homomorphism_pair(&pc0, &pc1, 14, 13);
        assert_eq!(pcs.len(), 1);
        let expected = PseudoConfiguration::new(
            11,
            vec![
                d(0, 6, 1, 4),
                d(0, 8, 2, 0),
                d(0, 11, 3, 1),
                d(0, 13, 4, 2),
                d(0, 15, 0, 3),
                d(4, 9, 6, -1),
                d(4, 0, 19, 5),
                d(1, 12, 8, 31),
                d(1, 1, 9, 7),
                d(1, 5, -1, 8),
                d(2, 14, 11, 30),
                d(2, 2, 12, 10),
                d(2, 7, 29, 11),
                d(6, 3, 14, 28),
                d(6, 10, 25, 13),
                d(5, 4, 21, 24),
                d(3, 20, 17, -1),
                d(3, 23, 18, 16),
                d(3, 42, -1, 17),
                d(4, 24, 20, 6),
                d(4, 16, -1, 19),
                d(5, 28, 22, 15),
                d(5, 43, 23, 21),
                d(5, 17, 24, 22),
                d(5, 19, 15, 23),
                d(6, 36, 26, 14),
                d(6, 40, 27, 25),
                d(6, 44, 28, 26),
                d(6, 21, 13, 27),
                d(2, 33, 30, 12),
                d(2, 37, 10, 29),
                d(1, 34, 7, -1),
                d(7, 38, 33, -1),
                d(7, 29, 34, 32),
                d(7, 31, -1, 33),
                d(8, 41, 36, -1),
                d(8, 25, 37, 35),
                d(8, 30, 38, 36),
                d(8, 32, -1, 37),
                d(9, 45, 40, -1),
                d(9, 26, 41, 39),
                d(9, 35, -1, 40),
                d(10, 18, 43, -1),
                d(10, 22, 44, 42),
                d(10, 27, 45, 43),
                d(10, 39, -1, 44),
            ],
            vec![
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
                Degree::exact(6),
            ],
        );
        let (pc, m0, m1) = &pcs[0];
        assert_eq!(*pc, expected);
        assert_eq!(m0.vmap, imap(&[0, 4, 1, 2, 6, 5]));
        assert_eq!(m1.vmap, imap(&[3, 4, 5, 6, 2, 1, 7, 8, 9, 10]));
        assert_eq!(
            m0.dmap,
            imap(&[
                0, 1, 2, 3, 4, 5, 6, 19, 7, 8, 9, 10, 11, 12, 28, 13, 14, 24, 15, 21
            ])
        );
        assert_eq!(
            m1.dmap,
            imap(&[
                16, 17, 18, 19, 20, 21, 22, 23, 24, 14, 25, 26, 27, 28, 12, 29, 30, 10, 31, 7, 32,
                33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45
            ])
        );
    }
}
