//! Phase 5 — the enumeration engine. Port of `../src/cartwheel.{hpp,cpp}`.
//!
//! `CartWheel` embeds a `PseudoConfiguration` and adds `center` + `center_darts`
//! (the darts of the centre vertex, in rotation order). Covers wheel/cartwheel
//! enumeration, in/out-rule fixing, charge-bound pruning, refinement, and
//! `enum_bad_cartwheels`.
//!
//! R5: the enumeration relies on `assert!`s as invariants — always-on.
//! R6: `CartWheel` calls `PseudoConfiguration` behaviour through `self.pc.…`
//! (its charge/containment methods live in `pseudo_configuration.rs`); no trait
//! was needed.

use crate::configuration::Configuration;
use crate::degree::{
    CARTWHEEL_DEG_MAX, CARTWHEEL_DEG_MIN, CARTWHEEL_DEGREES, CARTWHEEL_DEGREES_SIZE, Degree, INFTY,
};
use crate::mapping::Mappings;
use crate::pseudo_configuration::PseudoConfiguration;
use crate::pseudo_triangulation::Dart;
use crate::rule::{CombinedRule, Rule};
use crate::util::{FromFile, get_objects, lex_min};
use rayon::prelude::*;
use std::collections::VecDeque;
use std::path::Path;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CartWheel {
    pub pc: PseudoConfiguration,
    pub center: usize,
    pub center_darts: Vec<usize>,
}

impl CartWheel {
    /// C++ `CartWheel(center, center_darts, N, darts, degrees)`.
    pub fn new(
        center: usize,
        center_darts: Vec<usize>,
        n: usize,
        darts: Vec<Dart>,
        degrees: Vec<Degree>,
    ) -> Self {
        CartWheel {
            pc: PseudoConfiguration::new(n, darts, degrees),
            center,
            center_darts,
        }
    }

    /// Debug view (C++ `to_string`).
    pub fn to_debug_string(&self) -> String {
        let darts = self
            .center_darts
            .iter()
            .map(|d| d.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!("center: {}, center_darts: {}\n", self.center, darts) + &self.pc.show()
    }

    /// Serialise to the `.cartwheel` text format (C++ `to_file`/`write`). The
    /// layout (incl. the trailing space per vertex line) matches the C++.
    pub fn write(&self) -> String {
        let darts = &self.pc.tri.darts;
        let mut res = format!("\n{} {}\n", self.pc.tri.n, self.center + 1);
        let e_rotations = self.pc.tri.get_e_rotations();
        for (v, rotation) in e_rotations.iter().enumerate() {
            let upper = if self.pc.degrees[v].upper == INFTY {
                0
            } else {
                self.pc.degrees[v].upper
            };
            res += &format!("{} {} {} ", v + 1, self.pc.degrees[v].lower, upper);
            for &dart_id in rotation {
                match dart_id {
                    None => res += "-1 ",
                    Some(e) => res += &format!("{} ", darts[darts[e].rev()].head() + 1),
                }
            }
            res += "\n";
        }
        res
    }

    pub fn to_file(&self, path: &Path) {
        std::fs::write(path, self.write())
            .unwrap_or_else(|e| panic!("Failed to write cartwheel file {}: {e}", path.display()));
    }

    /// Load every `.cartwheel` file in `cartwheeldir` (C++ `get_cartwheels`).
    pub fn get_cartwheels(cartwheeldir: &Path) -> Vec<CartWheel> {
        let cartwheels = get_objects::<CartWheel>(cartwheeldir, ".cartwheel");
        tracing::info!("Total {} cartwheels loaded.", cartwheels.len());
        cartwheels
    }

    /// The lex-min neighbour-degree tuples for a centre of degree `center_degree`,
    /// in enumeration order (the inner traversal of C++ `enum_wheels`, with wheel
    /// *generation* split out so it can be parallelised — learned from the Lean
    /// port, where fusing generation into the parallel prune was a further win).
    pub fn enum_wheel_tuples(center_degree: usize) -> Vec<Vec<i32>> {
        let mut tuples = Vec::new();
        let mut degrees = vec![0i32; center_degree];
        for (j, &deg) in CARTWHEEL_DEGREES.iter().enumerate() {
            degrees[0] = deg;
            enum_wheel_degrees(center_degree, &mut degrees, 1, j, &mut tuples);
        }
        tuples
    }

    /// Enumerate all wheels with the given centre degree, up to rotation
    /// (`lex_min`) (C++ `enum_wheels`).
    pub fn enum_wheels(center_degree: usize) -> Vec<CartWheel> {
        Self::enum_wheel_tuples(center_degree)
            .iter()
            .map(|degs| Self::generate_cartwheel(center_degree, degs))
            .collect()
    }

    /// Build the canonical cartwheel for a centre of degree `d` with the given
    /// neighbour degrees, expanding second-neighbours (C++ `generate_cartwheel`).
    pub fn generate_cartwheel(d: usize, degrees: &[i32]) -> CartWheel {
        assert_eq!(degrees.len(), d);
        let mut rotations: Vec<Vec<i32>> = vec![Vec::new(); d + 1];
        for i in 1..=d {
            rotations[0].push(i as i32);
        }
        for (i, rot) in rotations.iter_mut().enumerate().skip(1) {
            let i_next = if i < d { i + 1 } else { 1 };
            let i_prev = if i > 1 { i - 1 } else { d };
            *rot = vec![i_next as i32, 0, i_prev as i32];
        }
        let mut k = d + 1; // next vertex id to assign
        for i in 1..=d {
            if degrees[i - 1] == CARTWHEEL_DEG_MAX {
                continue;
            }
            let a = degrees[i - 1] - rotations[i].len() as i32; // number of second neighbours
            assert!(a >= 0);
            for _ in 0..a {
                let i_last = *rotations[i].last().expect("rotation is non-empty");
                rotations.push(vec![i as i32, i_last]); // rotations[k]
                rotations[i].push(k as i32);
                rotations[i_last as usize].insert(0, k as i32);
                k += 1;
            }
            let i_first = rotations[i][0];
            let i_last = *rotations[i].last().expect("rotation is non-empty");
            rotations[i_first as usize].push(i_last);
            rotations[i_last as usize].insert(0, i_first);
        }
        for i in 1..k {
            if i > d || degrees[i - 1] == CARTWHEEL_DEG_MAX {
                rotations[i].push(-1);
            }
        }
        let mut all_degrees = vec![Degree::new(CARTWHEEL_DEG_MIN, CARTWHEEL_DEG_MAX); k];
        all_degrees[0] = Degree::exact(d as i32);
        for i in 1..=d {
            all_degrees[i] = Degree::exact(degrees[i - 1]);
        }
        let pc = PseudoConfiguration::from_v_rotations(k, &rotations, all_degrees);
        let center_darts = center_darts_of(&pc, 0);
        CartWheel {
            pc,
            center: 0,
            center_darts,
        }
    }

    /// Enumerate wheels of the given centre degree that survive the initial
    /// pruning (C++ `enum_possible_bad_wheels`).
    pub fn enum_possible_bad_wheels(
        center_degree: usize,
        rules: &[Rule],
        combined_rules: &[CombinedRule],
        confs: &[Configuration],
    ) -> Vec<CartWheel> {
        // Embarrassingly parallel (learned from the Lean port): generate + prune
        // each wheel in one parallel pass over the degree-tuples. `prune` is pure
        // and read-only over the shared inputs (R4); rayon's ordered collect keeps
        // the survivor list identical to the serial version (byte-identical output).
        // C++ runs this step serially.
        CartWheel::enum_wheel_tuples(center_degree)
            .into_par_iter()
            .filter_map(|degs| {
                let wheel = CartWheel::generate_cartwheel(center_degree, &degs);
                (!wheel.prune(&[], rules, combined_rules, confs)).then_some(wheel)
            })
            .collect()
    }

    /// Fix the rules sent from neighbours to the centre, one spoke at a time,
    /// pruning in between (C++ `fix_in_rules`).
    pub fn fix_in_rules(
        &self,
        rules: &[Rule],
        combined_rules: &[CombinedRule],
        confs: &[Configuration],
    ) -> Vec<(CartWheel, Vec<CombinedRule>)> {
        let degree_center = self.pc.degrees[self.center].lower as usize;
        let mut cartwheels: Vec<(CartWheel, Vec<CombinedRule>)> = vec![(self.clone(), Vec::new())];
        for i in 0..degree_center {
            let mut new_cartwheels = Vec::new();
            for (cartwheel, combined_rule_with_spokes) in &cartwheels {
                for combined_rule in combined_rules {
                    let updated_cartwheels = cartwheel
                        .update_degree_by_rule(cartwheel.center_darts[i], &combined_rule.rule);
                    for updated_cartwheel in updated_cartwheels {
                        let mut updated_spokes = combined_rule_with_spokes.clone();
                        updated_spokes.push(combined_rule.clone());
                        if updated_cartwheel.prune(&updated_spokes, rules, combined_rules, confs) {
                            continue;
                        }
                        new_cartwheels.push((updated_cartwheel, updated_spokes));
                    }
                }
            }
            cartwheels = new_cartwheels;
        }
        cartwheels
    }

    /// Intersect degrees with a rule applied at `dart_id`, then concretise
    /// (C++ `update_degree_by_rule`).
    pub fn update_degree_by_rule(&self, dart_id: usize, rule: &Rule) -> Vec<CartWheel> {
        let Some(rule2cw) =
            PseudoConfiguration::homomorphism(&rule.pc, rule.st_id, &self.pc, dart_id, |a, b| {
                Degree::has_intersection(&a, &b)
            })
        else {
            return Vec::new();
        };
        let mut updated = self.clone();
        for v_rule in 0..rule.pc.tri.n {
            let v_cw = rule2cw.vmap[v_rule].expect("homomorphism maps every rule vertex");
            updated.pc.degrees[v_cw] =
                Degree::intersection(&updated.pc.degrees[v_cw], &rule.pc.degrees[v_rule]);
        }
        updated.concrete_degree_except_tail()
    }

    /// Enumerate all ways to make every non-tail range degree concrete
    /// (C++ `concrete_degree_except_tail`).
    pub fn concrete_degree_except_tail(&self) -> Vec<CartWheel> {
        let mut cartwheels = vec![self.clone()];
        for v in 0..self.pc.tri.n {
            // already fixed, or a tail degree range [d, 9]
            if self.pc.degrees[v].is_fixed() || self.pc.degrees[v].upper == CARTWHEEL_DEG_MAX {
                continue;
            }
            let mut new_cartwheels = Vec::new();
            for &d in &CARTWHEEL_DEGREES[..CARTWHEEL_DEGREES_SIZE - 1] {
                if Degree::includes(&self.pc.degrees[v], &Degree::exact(d)) {
                    for cartwheel in &cartwheels {
                        let mut new_cartwheel = cartwheel.clone();
                        new_cartwheel.pc.degrees[v] = Degree::exact(d);
                        new_cartwheels.push(new_cartwheel);
                    }
                }
            }
            cartwheels = new_cartwheels;
        }
        cartwheels
    }

    /// Whether this cartwheel can be discarded (C++ `prune`).
    pub fn prune(
        &self,
        combined_rule_with_spokes: &[CombinedRule],
        rules: &[Rule],
        combined_rules: &[CombinedRule],
        confs: &[Configuration],
    ) -> bool {
        self.prune_by_non_associated_rule(combined_rule_with_spokes, rules)
            || self.upper_bound_of_charge(combined_rule_with_spokes, rules, combined_rules) < 0
            || self
                .pc
                .blocked_by_reducible_configuration(self.center, confs)
    }

    /// Prune if a fixed spoke rule applies that the combination doesn't record
    /// (C++ `prune_by_non_associated_rule`).
    pub fn prune_by_non_associated_rule(
        &self,
        combined_rule_with_spokes: &[CombinedRule],
        rules: &[Rule],
    ) -> bool {
        for (j, cr) in combined_rule_with_spokes.iter().enumerate() {
            for (k, rule) in rules.iter().enumerate() {
                assert!(!cr.combined_flag[k] || self.pc.always_apply(self.center_darts[j], rule));
                if !cr.combined_flag[k] && self.pc.always_apply(self.center_darts[j], rule) {
                    return true;
                }
            }
        }
        false
    }

    /// Upper bound on the final charge at the centre (C++ `upper_bound_of_charge`).
    pub fn upper_bound_of_charge(
        &self,
        combined_rule_with_spokes: &[CombinedRule],
        rules: &[Rule],
        combined_rules: &[CombinedRule],
    ) -> i32 {
        let degree_center = self.pc.degrees[self.center].lower as usize;
        let mut in_charge_sum: i32 = combined_rule_with_spokes
            .iter()
            .map(|cr| cr.rule.amount)
            .sum();
        for j in combined_rule_with_spokes.len()..degree_center {
            in_charge_sum += self
                .pc
                .amount_of_possible_charge_send(self.center_darts[j], combined_rules);
        }
        let mut out_charge_sum = 0;
        for i in 0..degree_center {
            let from_center = self.pc.tri.darts[self.center_darts[i]].rev();
            out_charge_sum += self.pc.amount_of_charge_send(from_center, rules);
        }
        let initial_charge = 10 * (6 - degree_center as i32);
        initial_charge - out_charge_sum + in_charge_sum
    }

    /// Fix the rules sent from the centre to neighbours by repeated refinement
    /// (C++ `fix_out_rules`).
    pub fn fix_out_rules(
        &self,
        cartwheels_in_fixed: &[(CartWheel, Vec<CombinedRule>)],
        rules: &[Rule],
        combined_rules: &[CombinedRule],
        confs: &[Configuration],
    ) -> Vec<(CartWheel, Vec<CombinedRule>)> {
        let degree_center = self.pc.degrees[self.center].lower as usize;
        let mut queue: VecDeque<(CartWheel, Vec<CombinedRule>)> =
            cartwheels_in_fixed.iter().cloned().collect();
        let mut cartwheels = Vec::new();
        while let Some((cartwheel, combined_rule_with_spokes)) = queue.pop_front() {
            let mut refined_flag = false;
            'search: for i in 0..degree_center {
                for rule in rules {
                    if !cartwheel.should_refine(i, rule) {
                        continue;
                    }
                    refined_flag = true;
                    for refined_cartwheel in cartwheel.refinement(i, rule) {
                        if refined_cartwheel.prune(
                            &combined_rule_with_spokes,
                            rules,
                            combined_rules,
                            confs,
                        ) {
                            continue;
                        }
                        queue.push_back((refined_cartwheel, combined_rule_with_spokes.clone()));
                    }
                    break 'search; // refine on the first applicable (spoke, rule) only
                }
            }
            if !refined_flag {
                cartwheels.push((cartwheel, combined_rule_with_spokes));
            }
        }
        cartwheels
    }

    /// Whether spoke `i` should be refined for `rule` (C++ `should_refine`).
    pub fn should_refine(&self, i: usize, rule: &Rule) -> bool {
        let from_center = self.pc.tri.darts[self.center_darts[i]].rev();
        !self.pc.always_apply(from_center, rule) && self.pc.dominantly_apply(from_center, rule)
    }

    /// Split into the "always applies" and "never applies" refinements at spoke
    /// `i` for `rule` (C++ `refinement`).
    pub fn refinement(&self, i: usize, rule: &Rule) -> Vec<CartWheel> {
        let from_center = self.pc.tri.darts[self.center_darts[i]].rev();
        let rule2cw = PseudoConfiguration::homomorphism(
            &rule.pc,
            rule.st_id,
            &self.pc,
            from_center,
            |a, b| Degree::has_intersection(&a, &b),
        )
        .expect("should_refine guarantees a homomorphism");
        let mut u_r = Vec::new();
        for v_rule in 0..rule.pc.tri.n {
            let v_cw = rule2cw.vmap[v_rule].expect("homomorphism maps every rule vertex");
            if self.pc.degrees[v_cw].upper == CARTWHEEL_DEG_MAX
                && self.pc.degrees[v_cw].lower < rule.pc.degrees[v_rule].lower
            {
                assert!(rule.pc.degrees[v_rule].upper == INFTY);
                u_r.push(v_rule);
            }
        }
        assert!(!u_r.is_empty());
        let c_always = self.refine_always(&u_r, &rule2cw, rule);
        let mut c_never = self.refine_never(&u_r, &rule2cw, rule);
        c_never.push(c_always);
        c_never
    }

    /// The refinement where every `U_R` vertex takes the rule's lower bound
    /// (C++ `refine_always`).
    pub fn refine_always(&self, u_r: &[usize], rule2cw: &Mappings, rule: &Rule) -> CartWheel {
        let mut c_always = self.clone();
        for &v_rule in u_r {
            let v_cw = rule2cw.vmap[v_rule].expect("homomorphism maps every rule vertex");
            assert!(rule.pc.degrees[v_rule].upper == INFTY);
            assert!(self.pc.degrees[v_cw].upper == CARTWHEEL_DEG_MAX);
            c_always.pc.degrees[v_cw].lower = rule.pc.degrees[v_rule].lower;
        }
        c_always
    }

    /// The refinements where each `U_R` vertex in turn stays below the rule's
    /// lower bound (C++ `refine_never`).
    pub fn refine_never(&self, u_r: &[usize], rule2cw: &Mappings, rule: &Rule) -> Vec<CartWheel> {
        let mut c_never = Vec::new();
        for &v_rule in u_r {
            let v_cw = rule2cw.vmap[v_rule].expect("homomorphism maps every rule vertex");
            assert!(rule.pc.degrees[v_rule].upper == INFTY);
            assert!(self.pc.degrees[v_cw].upper == CARTWHEEL_DEG_MAX);
            let mut base = self.clone();
            base.pc.degrees[v_cw].upper = rule.pc.degrees[v_rule].lower - 1;
            c_never.extend(base.concrete_degree_except_tail());
        }
        c_never
    }

    /// The overall enumeration: fix in-rules, fix out-rules, and keep the
    /// surviving cartwheels (C++ `enum_bad_cartwheels`).
    pub fn enum_bad_cartwheels(
        &self,
        rules: &[Rule],
        combined_rules: &[CombinedRule],
        confs: &[Configuration],
    ) -> Vec<CartWheel> {
        let cartwheels_in_fixed = self.fix_in_rules(rules, combined_rules, confs);
        let cartwheels_fixed =
            self.fix_out_rules(&cartwheels_in_fixed, rules, combined_rules, confs);
        let mut cartwheels = Vec::new();
        for (cartwheel, combined_rule_with_spokes) in cartwheels_fixed {
            let c =
                cartwheel.upper_bound_of_charge(&combined_rule_with_spokes, rules, combined_rules);
            let d = cartwheel.pc.degrees[cartwheel.center].lower;
            let darts_by_deg = cartwheel.center_darts_by_degree();
            assert!(c == 0);
            assert!(d == 7 || d == 8);
            assert!(darts_by_deg[7].len() + darts_by_deg[8].len() + darts_by_deg[9].len() > 0);
            cartwheels.push(cartwheel);
        }
        cartwheels
    }

    /// Group the centre's darts by the (fixed) degree of the neighbour they point
    /// to (C++ `center_darts_by_degree`).
    pub fn center_darts_by_degree(&self) -> [Vec<usize>; CARTWHEEL_DEG_MAX as usize + 1] {
        let mut by_degree: [Vec<usize>; CARTWHEEL_DEG_MAX as usize + 1] =
            std::array::from_fn(|_| Vec::new());
        for &dart_id in &self.center_darts {
            let neighbor = self.pc.tri.darts[self.pc.tri.darts[dart_id].rev()].head();
            let deg = self.pc.degrees[neighbor].lower;
            assert!((CARTWHEEL_DEG_MIN..=CARTWHEEL_DEG_MAX).contains(&deg));
            by_degree[deg as usize].push(dart_id);
        }
        by_degree
    }
}

impl FromFile for CartWheel {
    fn from_file(path: &Path) -> Self {
        let content = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("Failed to open cartwheel file {}: {e}", path.display()));
        let lines: Vec<&str> = content.lines().collect();
        let mut idx = 0;
        while lines[idx].trim().is_empty() {
            idx += 1; // tolerate the leading blank line written by `write`
        }
        let header: Vec<i32> = lines[idx]
            .split_whitespace()
            .map(|t| t.parse().expect("integer"))
            .collect();
        idx += 1;
        let n = header[0] as usize;
        let center = header[1] as usize - 1;

        let mut degrees = vec![Degree::new(1, INFTY); n];
        let mut rotation_vertices: Vec<Vec<i32>> = vec![Vec::new(); n];
        for (u, deg_slot) in degrees.iter_mut().enumerate() {
            let toks: Vec<&str> = lines[idx].split_whitespace().collect();
            idx += 1;
            assert_eq!(toks[0].parse::<i32>().unwrap(), u as i32 + 1);
            let lower: i32 = toks[1].parse().unwrap();
            let mut upper: i32 = toks[2].parse().unwrap();
            if upper == 0 {
                upper = INFTY;
            }
            *deg_slot = Degree::new(lower, upper);
            for tok in &toks[3..] {
                let mut v: i32 = tok.parse().unwrap();
                if v != -1 {
                    v -= 1;
                    assert!(0 <= v && v < n as i32);
                }
                rotation_vertices[u].push(v);
            }
        }
        let pc = PseudoConfiguration::from_v_rotations(n, &rotation_vertices, degrees);
        let center_darts = center_darts_of(&pc, center);
        CartWheel {
            pc,
            center,
            center_darts,
        }
    }
}

/// The centre's darts in rotation order (the centre is interior, so the rotation
/// is closed and has no boundary `None`).
fn center_darts_of(pc: &PseudoConfiguration, center: usize) -> Vec<usize> {
    pc.tri.get_e_rotations()[center]
        .iter()
        .map(|d| d.expect("the cartwheel centre is an interior vertex"))
        .collect()
}

/// Recursive helper for `enum_wheel_tuples`: assign neighbour `i`'s degree from
/// index `i_lowest` upward, collecting the lex-min degree tuples (C++ nested
/// `enum_degree` lambda, with wheel generation split out — see `enum_wheel_tuples`).
fn enum_wheel_degrees(
    center_degree: usize,
    degrees: &mut Vec<i32>,
    i: usize,
    i_lowest: usize,
    tuples: &mut Vec<Vec<i32>>,
) {
    if i == center_degree {
        if lex_min(&degrees[..]) {
            tuples.push(degrees.clone());
        }
        return;
    }
    for &deg in &CARTWHEEL_DEGREES[i_lowest..] {
        degrees[i] = deg;
        enum_wheel_degrees(center_degree, degrees, i + 1, i_lowest, tuples);
    }
}

/// Driver for Lemma A.3 step 1: enumerate the possible bad wheels of a given
/// centre degree and write them out (C++ `run_enum_wheels`).
pub fn run_enum_wheels(
    center_degree: usize,
    confdir: &Path,
    ruledir: &Path,
    combined_ruledir: &Path,
    outdir: &Path,
) {
    let confs = Configuration::get_confs(confdir);
    let rules = Rule::get_rules(ruledir);
    let combined_rules = CombinedRule::get_combined_rules(combined_ruledir);
    let wheels =
        CartWheel::enum_possible_bad_wheels(center_degree, &rules, &combined_rules, &confs);
    tracing::info!("Generated {} wheels.", wheels.len());
    for (i, wheel) in wheels.iter().enumerate() {
        let filename = outdir.join(format!("d{center_degree}_{i}.cartwheel"));
        wheel.to_file(&filename);
    }
}

/// Driver for Lemma A.3 step 2: enumerate the bad cartwheels of a single wheel
/// and write them out (C++ `run_enum_cartwheels`).
pub fn run_enum_cartwheels(
    wheel_file: &Path,
    confdir: &Path,
    ruledir: &Path,
    combined_ruledir: &Path,
    outdir: &Path,
) {
    let cartwheel = CartWheel::from_file(wheel_file);
    let confs = Configuration::get_confs(confdir);
    let rules = Rule::get_rules(ruledir);
    let combined_rules = CombinedRule::get_combined_rules(combined_ruledir);
    let enumed_wheels = cartwheel.enum_bad_cartwheels(&rules, &combined_rules, &confs);
    tracing::info!(
        "Total {} cartwheels after enumerating degrees.",
        enumed_wheels.len()
    );
    let basename = wheel_file
        .file_stem()
        .and_then(|s| s.to_str())
        .expect("wheel file has a stem");
    for (i, wheel) in enumed_wheels.iter().enumerate() {
        let filename = outdir.join(format!("{basename}_{i}.cartwheel"));
        wheel.to_file(&filename);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::combine_rules;
    use std::io::Write;

    fn d(head: i32, rev: i32, succ: i32, pred: i32) -> Dart {
        let opt = |x: i32| if x == -1 { None } else { Some(x as usize) };
        Dart::new(head as usize, rev as usize, opt(succ), opt(pred))
    }

    fn exact(xs: &[i32]) -> Vec<Degree> {
        xs.iter().map(|&x| Degree::exact(x)).collect()
    }

    fn temp_file(tag: &str, ext: &str, content: &str) -> std::path::PathBuf {
        // Unique per call: tests run in parallel and several reuse the same
        // contents, so a name keyed only on (pid, tag, len) would collide.
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "combine_p5_{}_{}_{}.{ext}",
            std::process::id(),
            tag,
            id
        ));
        std::fs::File::create(&path)
            .unwrap()
            .write_all(content.as_bytes())
            .unwrap();
        path
    }

    const CW1: &str = "8 1\n1 7 7 2 3 4 5 6 7 8\n2 5 5 3 1 8 -1\n3 5 5 4 1 2 -1\n4 6 6 5 1 3 -1\n5 5 5 6 1 4 -1\n6 5 5 7 1 5 -1\n7 5 5 8 1 6 -1\n8 9 9 2 1 7 -1\n";
    const CW2: &str = "18 1\n1 7 7 2 3 4 5 6 7 8\n2 5 5 1 8 9 10 3\n3 7 7 1 2 10 11 12 13 4\n4 5 5 1 3 13 14 5\n5 5 5 1 4 14 15 6\n6 9 9 16 7 1 5 15 -1\n7 5 5 1 6 16 17 8\n8 6 6 2 1 7 17 18 9\n9 5 9 10 2 8 18 -1\n10 5 9 11 3 2 9 -1\n11 5 9 12 3 10 -1\n12 5 9 13 3 11 -1\n13 5 9 14 4 3 12 -1\n14 5 9 15 5 4 13 -1\n15 5 9 6 5 14 -1\n16 5 9 17 7 6 -1\n17 5 9 18 8 7 16 -1\n18 5 9 9 8 17 -1\n";

    const RULE1: &str = "\n2 1 2 2\n1 5 5 2 -1\n2 5 0 1 -1\n";
    const RULE2: &str = "\n6 1 2 1\n1 7 7 5 4 3 2 6 -1\n2 7 0 1 3 -1 6\n3 5 5 2 1 4 -1\n4 5 6 3 1 5 -1\n5 5 5 4 1 -1\n6 5 5 1 2 -1\n";
    const RULE3: &str = "\n6 1 2 1\n1 7 7 4 6 2 3 -1\n2 7 0 3 1 6 -1\n3 5 5 1 2 -1\n4 6 6 5 6 1 -1\n5 5 5 6 4 -1\n6 5 5 2 1 4 5 -1\n";
    const RULE4: &str = "\n8 1 2 1\n1 7 7 3 4 2 6 -1\n2 7 7 7 6 1 4 5 -1\n3 5 5 4 1 -1\n4 7 7 5 2 1 3 -1\n5 6 0 2 4 -1\n6 5 5 1 2 7 8 -1\n7 6 6 8 6 2 -1\n8 7 0 6 7 -1\n";

    const CONF1: &str = "\n17 10\n11 5 1 12 17 9 10\n12 5 1 2 13 17 11\n13 6 2 14 16 7 17 12\n14 5 2 3 15 16 13\n15 5 3 4 5 16 14\n16 6 5 6 7 13 14 15\n17 6 7 8 9 11 12 13\n";
    const CONF2: &str =
        "\n11 7\n8 5 1 2 9 11 7\n9 6 2 3 4 10 11 8\n10 5 4 5 6 11 9\n11 5 6 7 8 9 10\n";

    fn load_rules(contents: &[&str]) -> Vec<Rule> {
        contents
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let f = temp_file(&format!("rule{i}"), "rule", c);
                let r = Rule::from_file(&f);
                std::fs::remove_file(&f).unwrap();
                r
            })
            .collect()
    }

    // Port of CartWheelFiles.FromFile (cw1 fully; cw2 structurally).
    #[test]
    fn from_file() {
        let f1 = temp_file("cw1", "cartwheel", CW1);
        let cw1 = CartWheel::from_file(&f1);
        std::fs::remove_file(&f1).unwrap();
        let expected_cw1 = CartWheel::new(
            0,
            vec![0, 1, 2, 3, 4, 5, 6],
            8,
            vec![
                d(0, 8, 1, 6),
                d(0, 11, 2, 0),
                d(0, 14, 3, 1),
                d(0, 17, 4, 2),
                d(0, 20, 5, 3),
                d(0, 23, 6, 4),
                d(0, 26, 0, 5),
                d(1, 12, 8, -1),
                d(1, 0, 9, 7),
                d(1, 25, -1, 8),
                d(2, 15, 11, -1),
                d(2, 1, 12, 10),
                d(2, 7, -1, 11),
                d(3, 18, 14, -1),
                d(3, 2, 15, 13),
                d(3, 10, -1, 14),
                d(4, 21, 17, -1),
                d(4, 3, 18, 16),
                d(4, 13, -1, 17),
                d(5, 24, 20, -1),
                d(5, 4, 21, 19),
                d(5, 16, -1, 20),
                d(6, 27, 23, -1),
                d(6, 5, 24, 22),
                d(6, 19, -1, 23),
                d(7, 9, 26, -1),
                d(7, 6, 27, 25),
                d(7, 22, -1, 26),
            ],
            exact(&[7, 5, 5, 6, 5, 5, 5, 9]),
        );
        assert_eq!(cw1, expected_cw1);

        // cw2: too large to transcribe by hand; check structure + write idempotence.
        let f2 = temp_file("cw2", "cartwheel", CW2);
        let cw2 = CartWheel::from_file(&f2);
        std::fs::remove_file(&f2).unwrap();
        assert_eq!(cw2.center, 0);
        assert_eq!(cw2.pc.tri.n, 18);
        assert_eq!(cw2.center_darts, vec![0, 1, 2, 3, 4, 5, 6]);
        let mut deg2 = exact(&[7, 5, 7, 5, 5, 9, 5, 6]);
        deg2.extend(std::iter::repeat_n(Degree::new(5, 9), 10));
        assert_eq!(cw2.pc.degrees, deg2);
        let f3 = temp_file("cw2b", "cartwheel", &cw2.write());
        assert_eq!(cw2.write(), CartWheel::from_file(&f3).write());
        std::fs::remove_file(&f3).unwrap();
    }

    // Port of CartWheelTest.EnumWheels (counts via Burnside's lemma).
    #[test]
    fn enum_wheels_counts() {
        assert_eq!(CartWheel::enum_wheels(5).len(), 629);
        assert_eq!(CartWheel::enum_wheels(6).len(), 2635);
        assert_eq!(CartWheel::enum_wheels(7).len(), 11165);
    }

    // Port of RuleFiles.Charge.
    #[test]
    fn charge() {
        let rules = load_rules(&[RULE1, RULE2, RULE3]);
        let wheels = [
            CartWheel::generate_cartwheel(7, &[5, 7, 5, 5, 9, 5, 6]),
            CartWheel::generate_cartwheel(7, &[5, 5, 7, 5, 7, 5, 7]),
        ];
        let expected = [(1, 8), (0, 8)]; // (out_charge, in_charge)
        for (wheel, &(exp_out, exp_in)) in wheels.iter().zip(expected.iter()) {
            let mut out_charge = 0;
            let mut in_charge = 0;
            for &dart_id in &wheel.center_darts {
                in_charge += wheel.pc.amount_of_charge_send(dart_id, &rules);
                let rev = wheel.pc.tri.darts[dart_id].rev();
                out_charge += wheel.pc.amount_of_charge_send(rev, &rules);
            }
            assert_eq!(out_charge, exp_out);
            assert_eq!(in_charge, exp_in);
        }
    }

    // Port of RuleFiles.PruneByCharge.
    #[test]
    fn prune_by_charge() {
        let rules = load_rules(&[RULE1, RULE2, RULE3]);
        let combined = combine_rules(&rules, &[]);

        let mut wheel = CartWheel::generate_cartwheel(7, &[7, 5, 7, 5, 7, 5, 5]);
        let spokes1 = vec![combined[0].clone(), combined[1].clone()];
        assert!(!wheel.prune_by_non_associated_rule(&spokes1, &rules));
        assert!(wheel.upper_bound_of_charge(&spokes1, &rules, &combined) > 0);

        wheel.pc.degrees[10] = Degree::exact(5);
        wheel.pc.degrees[11] = Degree::exact(6);
        wheel.pc.degrees[12] = Degree::exact(5);
        let spokes2 = vec![combined[4].clone(), combined[1].clone()];
        assert!(!wheel.prune_by_non_associated_rule(&spokes2, &rules));
        assert!(wheel.upper_bound_of_charge(&spokes2, &rules, &combined) > 0);
        let spokes3 = vec![
            combined[4].clone(),
            combined[1].clone(),
            combined[0].clone(),
            combined[1].clone(),
        ];
        assert!(!wheel.prune_by_non_associated_rule(&spokes3, &rules));
        assert!(wheel.upper_bound_of_charge(&spokes3, &rules, &combined) > 0);
    }

    // Port of RuleFiles.refinement1.
    #[test]
    fn refinement1() {
        let mut cw = CartWheel::generate_cartwheel(7, &[7, 7, 5, 5, 9, 6, 5]);
        cw.pc.degrees[14] = Degree::exact(6);
        let rule4 = load_rules(&[RULE4]).remove(0);
        assert!(cw.should_refine(1, &rule4));
        let refinements = cw.refinement(1, &rule4);
        assert_eq!(refinements.len(), 4);

        let with = |mods: &[(usize, Degree)]| {
            let mut c = cw.clone();
            for &(v, deg) in mods {
                c.pc.degrees[v] = deg;
            }
            c
        };
        let expected = vec![
            with(&[(11, Degree::exact(5))]),
            with(&[(15, Degree::exact(5))]),
            with(&[(15, Degree::exact(6))]),
            with(&[(11, Degree::new(6, 9)), (15, Degree::new(7, 9))]),
        ];
        assert_eq!(refinements, expected);
    }

    // Port of RuleFiles.refinement2.
    #[test]
    fn refinement2() {
        let cw = CartWheel::generate_cartwheel(7, &[7, 7, 5, 5, 9, 6, 5]);
        let rule4 = load_rules(&[RULE4]).remove(0);
        assert!(!cw.should_refine(1, &rule4));
    }

    // Port of RuleFiles.enumBadCartWheels1.
    #[test]
    fn enum_bad_cartwheels1() {
        let rules = load_rules(&[RULE1, RULE2, RULE3, RULE4]);
        let combined = combine_rules(&rules, &[]);
        let cw = CartWheel::generate_cartwheel(7, &[5, 7, 5, 7, 5, 8, 9]);
        let enumerated = cw.enum_bad_cartwheels(&rules, &combined, &[]);

        let mut expected = cw.clone();
        for (v, deg) in [(11, 5), (12, 6), (13, 5), (15, 5), (16, 6), (17, 5)] {
            expected.pc.degrees[v] = Degree::exact(deg);
        }
        assert_eq!(enumerated.len(), 1);
        assert_eq!(enumerated[0], expected);
    }

    // Port of RuleFiles.enumBadCartWheels2.
    #[test]
    fn enum_bad_cartwheels2() {
        let rules = load_rules(&[RULE1, RULE2, RULE3, RULE4]);
        let combined = combine_rules(&rules, &[]);
        let mut cw = CartWheel::generate_cartwheel(7, &[5, 5, 5, 7, 7, 5, 7]);

        let enumerated1 = cw.enum_bad_cartwheels(&rules, &combined, &[]);
        let mut expected1 = cw.clone();
        for (v, deg) in [(8, 6), (9, 5), (20, 5)] {
            expected1.pc.degrees[v] = Degree::exact(deg);
        }
        assert_eq!(enumerated1.len(), 1);
        assert_eq!(enumerated1[0], expected1);

        cw.pc.degrees[17] = Degree::exact(6);
        let enumerated2 = cw.enum_bad_cartwheels(&rules, &combined, &[]);
        expected1.pc.degrees[17] = Degree::exact(6);
        let mut expected2 = vec![expected1.clone(), expected1.clone(), expected1.clone()];
        expected2[0].pc.degrees[14] = Degree::exact(5);
        expected2[1].pc.degrees[18] = Degree::exact(5);
        expected2[2].pc.degrees[18] = Degree::exact(6);
        assert_eq!(enumerated2, expected2);
    }

    // Port of PseudoConfigurationTest.Contain1 / Contain2 (need CartWheel).
    #[test]
    fn contain() {
        let cf1 = temp_file("conf1", "conf", CONF1);
        let confs1 = Configuration::from_file(&cf1);
        std::fs::remove_file(&cf1).unwrap();
        let mut cw = CartWheel::generate_cartwheel(7, &[6, 6, 6, 6, 6, 6, 6]);
        for v in [9, 10, 12, 13] {
            cw.pc.degrees[v] = Degree::exact(5);
        }
        assert!(cw.pc.blocked_by_reducible_configuration(cw.center, &confs1));

        let cf2 = temp_file("conf2", "conf", CONF2);
        let confs2 = Configuration::from_file(&cf2);
        std::fs::remove_file(&cf2).unwrap();
        let mut cw = CartWheel::generate_cartwheel(7, &[5, 6, 6, 6, 6, 6, 5]);
        cw.pc.degrees[8] = Degree::exact(6);
        assert!(!cw.pc.blocked_by_reducible_configuration(cw.center, &confs2));
        cw.pc.degrees[9] = Degree::exact(5);
        assert!(cw.pc.blocked_by_reducible_configuration(cw.center, &confs2));
    }

    // Port of PseudoConfigurationTest.AmountChargeSend.
    #[test]
    fn amount_charge_send() {
        let rules = load_rules(&[RULE1, RULE2, RULE3]);
        let mut cw = CartWheel::generate_cartwheel(7, &[5, 5, 5, 5, 7, 5, 7]);
        cw.pc.degrees[8] = Degree::exact(6);
        cw.pc.degrees[18] = Degree::exact(5);
        assert_eq!(cw.pc.amount_of_charge_send(28, &rules), 1); // (5,0)
        assert_eq!(cw.pc.amount_of_charge_send(41, &rules), 0); // (7,0)
        assert_eq!(cw.pc.amount_of_charge_send(23, &rules), 0); // (4,0)
        assert_eq!(cw.pc.amount_of_charge_send(6, &rules), 1); // (0,7)
        assert_eq!(cw.pc.amount_of_charge_send(0, &rules), 2); // (0,1)
    }

    // Port of PseudoConfigurationTest.AmountPossibleChargeSend.
    #[test]
    fn amount_possible_charge_send() {
        let rules = load_rules(&[RULE1, RULE2, RULE3]);
        let combined = combine_rules(&rules, &[]);
        let mut cw = CartWheel::generate_cartwheel(8, &[5, 7, 5, 7, 5, 9, 9, 9]);
        cw.pc.degrees[13] = Degree::exact(6);
        cw.pc.degrees[14] = Degree::exact(7);
        assert_eq!(cw.pc.amount_of_possible_charge_send(1, &combined), 1); // (0,2)
        assert_eq!(cw.pc.amount_of_possible_charge_send(2, &combined), 2); // (0,3)
        assert_eq!(cw.pc.amount_of_possible_charge_send(3, &combined), 2); // (0,4)
    }
}
