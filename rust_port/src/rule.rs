//! Phase 4 — discharging rules. Port of `../src/rule.{hpp,cpp}`.
//!
//! `Rule` embeds a `PseudoConfiguration` and adds `st_id` (the charge-carrying
//! dart) and `amount`. `CombinedRule` embeds a `Rule` and adds the
//! `combined_flag` bitvector.
//!
//! R3/R7: `combined_flag` indexes rules "ordered by filename" (see
//! `../FORMAT.md`), coupled to the deterministic load order from
//! `util::get_objects`. The `write` output is the proof artifact, so its bytes
//! (including the trailing space after each vertex line) must match the C++.

use crate::configuration::Configuration;
use crate::degree::{Degree, INFTY};
use crate::pseudo_configuration::PseudoConfiguration;
use crate::pseudo_triangulation::Dart;
use crate::util::{FromFile, get_objects};
use std::path::Path;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub pc: PseudoConfiguration,
    pub st_id: usize,
    pub amount: i32,
}

impl Rule {
    /// C++ `Rule(st_id, amount, N, darts, degrees)`.
    pub fn new(
        st_id: usize,
        amount: i32,
        n: usize,
        darts: Vec<Dart>,
        degrees: Vec<Degree>,
    ) -> Self {
        Rule {
            pc: PseudoConfiguration::new(n, darts, degrees),
            st_id,
            amount,
        }
    }

    /// Debug view (C++ `to_string`).
    pub fn to_debug_string(&self) -> String {
        format!("st_id: {}, amount: {}\n", self.st_id, self.amount) + &self.pc.show()
    }

    /// Serialise to the `.rule` text format (C++ `write`). The output is the
    /// proof artifact; byte layout matches the C++ exactly.
    pub fn write(&self) -> String {
        let darts = &self.pc.tri.darts;
        let mut res = format!(
            "\n{} {} {} {}\n",
            self.pc.tri.n,
            darts[darts[self.st_id].rev()].head() + 1,
            darts[self.st_id].head() + 1,
            self.amount
        );
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

    /// Write to a file (C++ `to_file`).
    pub fn to_file(&self, path: &Path) {
        std::fs::write(path, self.write())
            .unwrap_or_else(|e| panic!("Failed to write rule file {}: {e}", path.display()));
    }

    /// Load every `.rule` file in `ruledir`, sorted by filename (C++ `get_rules`).
    pub fn get_rules(ruledir: &Path) -> Vec<Rule> {
        let rules = get_objects::<Rule>(ruledir, ".rule");
        tracing::info!("Total {} rules loaded.", rules.len());
        rules
    }
}

impl FromFile for Rule {
    fn from_file(path: &Path) -> Self {
        let content = read_to_lines(path);
        let lines: Vec<&str> = content.lines().collect();
        let mut cursor = 0;
        parse_rule(&lines, &mut cursor)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CombinedRule {
    pub rule: Rule,
    pub combined_flag: Vec<bool>,
}

impl CombinedRule {
    /// C++ `CombinedRule(combined_flag, st_id, amount, N, darts, degrees)`.
    pub fn new(
        combined_flag: Vec<bool>,
        st_id: usize,
        amount: i32,
        n: usize,
        darts: Vec<Dart>,
        degrees: Vec<Degree>,
    ) -> Self {
        CombinedRule {
            rule: Rule::new(st_id, amount, n, darts, degrees),
            combined_flag,
        }
    }

    /// Serialise: the rule text followed by the flag bits (C++ `to_file`).
    pub fn write(&self) -> String {
        let mut res = self.rule.write();
        for &flag in &self.combined_flag {
            res.push(if flag { '1' } else { '0' });
        }
        res.push('\n');
        res
    }

    pub fn to_file(&self, path: &Path) {
        std::fs::write(path, self.write()).unwrap_or_else(|e| {
            panic!("Failed to write combined rule file {}: {e}", path.display())
        });
    }

    /// Load every `.combined_rule` file in `combined_ruledir` (C++
    /// `get_combined_rules`).
    pub fn get_combined_rules(combined_ruledir: &Path) -> Vec<CombinedRule> {
        let combined_rules = get_objects::<CombinedRule>(combined_ruledir, ".combined_rule");
        tracing::info!("Total {} combined rules loaded.", combined_rules.len());
        combined_rules
    }

    /// Extend this combination by also applying `rules[i]`, dropping results that
    /// are blocked by a reducible configuration (C++ `add_rule_to_combination`).
    pub fn add_rule_to_combination(
        &self,
        rules: &[Rule],
        i: usize,
        confs: &[Configuration],
    ) -> Vec<CombinedRule> {
        let z_tildes = PseudoConfiguration::free_homomorphism_pair(
            &self.rule.pc,
            &rules[i].pc,
            self.rule.st_id,
            rules[i].st_id,
        );
        let mut new_flag = self.combined_flag.clone();
        new_flag[i] = true;

        let r_tildes: Vec<CombinedRule> = z_tildes
            .into_iter()
            .map(|(z_tilde, mappings_combination, _)| {
                CombinedRule::new(
                    new_flag.clone(),
                    mappings_combination.dmap[self.rule.st_id].expect("combination map is total"),
                    self.rule.amount + rules[i].amount,
                    z_tilde.tri.n,
                    z_tilde.tri.darts,
                    z_tilde.degrees,
                )
            })
            .collect();

        if confs.is_empty() {
            return r_tildes;
        }
        r_tildes
            .into_iter()
            .filter(|r_tilde| {
                let center = r_tilde.rule.pc.tri.darts[r_tilde.rule.st_id].head();
                !r_tilde
                    .rule
                    .pc
                    .blocked_by_reducible_configuration(center, confs)
            })
            .collect()
    }
}

impl FromFile for CombinedRule {
    fn from_file(path: &Path) -> Self {
        let content = read_to_lines(path);
        let lines: Vec<&str> = content.lines().collect();
        let mut cursor = 0;
        let rule = parse_rule(&lines, &mut cursor);
        // The next non-empty line is the 0/1 flag string (C++ `ifs >> line`).
        let flag_line = lines[cursor..]
            .iter()
            .map(|l| l.trim())
            .find(|l| !l.is_empty())
            .expect("combined rule file is missing its flag line");
        let combined_flag = flag_line
            .chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                other => panic!("Invalid combined flag '{other}' in {}", path.display()),
            })
            .collect();
        CombinedRule {
            rule,
            combined_flag,
        }
    }
}

/// Enumerate all combined rules reachable from the given rules (C++ `combine_rules`).
pub fn combine_rules(rules: &[Rule], confs: &[Configuration]) -> Vec<CombinedRule> {
    let default_flag = vec![false; rules.len()];
    let z0 = CombinedRule::new(
        default_flag,
        0,
        0,
        2,
        vec![Dart::new(0, 1, None, None), Dart::new(1, 0, None, None)],
        vec![Degree::new(1, INFTY), Degree::new(1, INFTY)],
    );
    let mut combined_rules = vec![z0];
    for i in 0..rules.len() {
        let mut next = combined_rules.clone();
        for combination in &combined_rules {
            next.extend(combination.add_rule_to_combination(rules, i, confs));
        }
        combined_rules = next;
    }
    let max_amount = combined_rules
        .iter()
        .map(|c| c.rule.amount)
        .max()
        .unwrap_or(0);
    tracing::info!("Generated {} combined rules.", combined_rules.len());
    tracing::info!("Max amount among combined rules: {}", max_amount);
    combined_rules
}

/// Driver for Lemma A.1 / A.2: combine rules and write them out
/// (C++ `run_combine_rules`).
pub fn run_combine_rules(confdir: &Path, ruledir: &Path, outdir: &Path) {
    let confs = Configuration::get_confs(confdir);
    let rules = Rule::get_rules(ruledir);
    let combined_rules = combine_rules(&rules, &confs);
    for (i, combined_rule) in combined_rules.iter().enumerate() {
        let filename = outdir.join(format!("combined_rule_{}.combined_rule", i + 1));
        combined_rule.to_file(&filename);
    }
}

fn read_to_lines(path: &Path) -> String {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to open rule file {}: {e}", path.display()))
}

/// Parse one rule starting at `*cursor` (after a leading blank line), advancing
/// the cursor past the rule's lines (C++ `Rule::read`).
fn parse_rule(lines: &[&str], cursor: &mut usize) -> Rule {
    *cursor += 1; // skip the format's leading blank line (C++ getline(dummy))
    let header: Vec<i32> = lines[*cursor].split_whitespace().map(parse_i32).collect();
    *cursor += 1;
    let n = header[0] as usize;
    let s = header[1] - 1;
    let t = header[2] - 1;
    let amount = header[3];

    let mut degrees = vec![Degree::new(1, INFTY); n];
    let mut rotation_vertices: Vec<Vec<i32>> = vec![Vec::new(); n];
    for (u, deg_slot) in degrees.iter_mut().enumerate() {
        let toks: Vec<&str> = lines[*cursor].split_whitespace().collect();
        *cursor += 1;
        assert_eq!(parse_i32(toks[0]), u as i32 + 1);
        let lower = parse_i32(toks[1]);
        let mut upper = parse_i32(toks[2]);
        if upper == 0 {
            upper = INFTY;
        }
        *deg_slot = Degree::new(lower, upper);
        for tok in &toks[3..] {
            let mut v = parse_i32(tok);
            if v != -1 {
                v -= 1;
                assert!(0 <= v && v < n as i32);
            }
            rotation_vertices[u].push(v);
        }
    }

    let pc = PseudoConfiguration::from_v_rotations(n, &rotation_vertices, degrees);
    let st = pc.tri.get_darts(t as usize, s as usize);
    assert_eq!(st.len(), 1);
    Rule {
        st_id: st[0],
        amount,
        pc,
    }
}

fn parse_i32(tok: &str) -> i32 {
    tok.parse()
        .unwrap_or_else(|_| panic!("expected integer token, got {tok:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn d(head: i32, rev: i32, succ: i32, pred: i32) -> Dart {
        let opt = |x: i32| if x == -1 { None } else { Some(x as usize) };
        Dart::new(head as usize, rev as usize, opt(succ), opt(pred))
    }

    fn temp_rule(tag: &str, content: &str) -> std::path::PathBuf {
        let path = std::env::temp_dir().join(format!(
            "combine_p4rule_{}_{}_{}.rule",
            std::process::id(),
            tag,
            content.len()
        ));
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(content.as_bytes()).unwrap();
        path
    }

    const RULE1: &str = "\n2 1 2 2\n1 5 5 2 -1\n2 5 0 1 -1\n";
    const RULE2: &str = "\n6 1 2 1\n1 7 7 5 4 3 2 6 -1\n2 7 0 1 3 -1 6\n3 5 5 2 1 4 -1\n4 5 6 3 1 5 -1\n5 5 5 4 1 -1\n6 5 5 1 2 -1\n";
    const RULE3: &str = "\n6 1 2 1\n1 7 7 4 6 2 3 -1\n2 7 0 3 1 6 -1\n3 5 5 1 2 -1\n4 6 6 5 6 1 -1\n5 5 5 6 4 -1\n6 5 5 2 1 4 5 -1\n";

    // Port of RuleFiles.ReadRuleFile.
    #[test]
    fn read_rule_file() {
        let f1 = temp_rule("r1", RULE1);
        let f2 = temp_rule("r2", RULE2);
        let rule1 = Rule::from_file(&f1);
        let rule2 = Rule::from_file(&f2);
        std::fs::remove_file(&f1).unwrap();
        std::fs::remove_file(&f2).unwrap();

        let rule1_expected = Rule::new(
            1,
            2,
            2,
            vec![d(0, 1, -1, -1), d(1, 0, -1, -1)],
            vec![Degree::exact(5), Degree::new(5, INFTY)],
        );
        let rule2_expected = Rule::new(
            5,
            1,
            6,
            vec![
                d(0, 15, 1, -1),
                d(0, 12, 2, 0),
                d(0, 9, 3, 1),
                d(0, 5, 4, 2),
                d(0, 16, -1, 3),
                d(1, 3, 6, 7),
                d(1, 8, -1, 5),
                d(1, 17, 5, -1),
                d(2, 6, 9, -1),
                d(2, 2, 10, 8),
                d(2, 11, -1, 9),
                d(3, 10, 12, -1),
                d(3, 1, 13, 11),
                d(3, 14, -1, 12),
                d(4, 13, 15, -1),
                d(4, 0, -1, 14),
                d(5, 4, 17, -1),
                d(5, 7, -1, 16),
            ],
            vec![
                Degree::exact(7),
                Degree::new(7, INFTY),
                Degree::exact(5),
                Degree::new(5, 6),
                Degree::exact(5),
                Degree::exact(5),
            ],
        );
        assert_eq!(rule1, rule1_expected);
        assert_eq!(rule2, rule2_expected);
    }

    // R7: the write output is byte-exact (including trailing spaces per line).
    #[test]
    fn write_is_byte_exact() {
        let f1 = temp_rule("rw1", RULE1);
        let rule1 = Rule::from_file(&f1);
        std::fs::remove_file(&f1).unwrap();
        // Same as input but with the C++ trailing space after each vertex line.
        assert_eq!(rule1.write(), "\n2 1 2 2\n1 5 5 2 -1 \n2 5 0 1 -1 \n");
    }

    // R7: `write` is idempotent — its output is a fixpoint under re-parsing.
    //
    // Note `parse∘write` is *not* identity on the in-memory structure: `write`
    // emits each vertex's rotation starting at its boundary (pred==nil) dart, so
    // a rule whose input rotation started elsewhere comes back with renumbered
    // dart-ids (an isomorphic graph). But once written, the order is canonical,
    // so writing again reproduces the exact same bytes. This is the property the
    // combined-rule pipeline (write then read back) actually relies on, and it
    // is what makes the Rust output byte-match the C++ output in P7.
    #[test]
    fn rule_write_is_idempotent() {
        for (tag, content) in [("rt1", RULE1), ("rt2", RULE2), ("rt3", RULE3)] {
            let f = temp_rule(tag, content);
            let w1 = Rule::from_file(&f).write();
            std::fs::remove_file(&f).unwrap();

            let f2 = temp_rule(&format!("{tag}b"), &w1);
            let w2 = Rule::from_file(&f2).write();
            std::fs::remove_file(&f2).unwrap();
            assert_eq!(w1, w2);
        }
    }

    // Port of RuleFiles.CombineRules.
    #[test]
    fn combine_rules_test() {
        let f1 = temp_rule("cr1", RULE1);
        let f2 = temp_rule("cr2", RULE2);
        let f3 = temp_rule("cr3", RULE3);
        let rules = vec![
            Rule::from_file(&f1),
            Rule::from_file(&f2),
            Rule::from_file(&f3),
        ];
        for f in [&f1, &f2, &f3] {
            std::fs::remove_file(f).unwrap();
        }

        let combined = combine_rules(&rules, &[]);
        let expected = [
            CombinedRule::new(
                vec![false, false, false],
                0,
                0,
                2,
                vec![d(0, 1, -1, -1), d(1, 0, -1, -1)],
                vec![Degree::new(1, INFTY), Degree::new(1, INFTY)],
            ),
            CombinedRule::new(
                vec![true, false, false],
                1,
                2,
                2,
                vec![d(0, 1, -1, -1), d(1, 0, -1, -1)],
                vec![Degree::exact(5), Degree::new(5, INFTY)],
            ),
            CombinedRule::new(
                vec![false, true, false],
                5,
                1,
                6,
                vec![
                    d(0, 15, 1, -1),
                    d(0, 12, 2, 0),
                    d(0, 9, 3, 1),
                    d(0, 5, 4, 2),
                    d(0, 16, -1, 3),
                    d(1, 3, 6, 7),
                    d(1, 8, -1, 5),
                    d(1, 17, 5, -1),
                    d(2, 6, 9, -1),
                    d(2, 2, 10, 8),
                    d(2, 11, -1, 9),
                    d(3, 10, 12, -1),
                    d(3, 1, 13, 11),
                    d(3, 14, -1, 12),
                    d(4, 13, 15, -1),
                    d(4, 0, -1, 14),
                    d(5, 4, 17, -1),
                    d(5, 7, -1, 16),
                ],
                vec![
                    Degree::exact(7),
                    Degree::new(7, INFTY),
                    Degree::exact(5),
                    Degree::new(5, 6),
                    Degree::exact(5),
                    Degree::exact(5),
                ],
            ),
            CombinedRule::new(
                vec![false, false, true],
                5,
                1,
                6,
                vec![
                    d(0, 11, 1, -1),
                    d(0, 15, 2, 0),
                    d(0, 5, 3, 1),
                    d(0, 7, -1, 2),
                    d(1, 8, 5, -1),
                    d(1, 2, 6, 4),
                    d(1, 14, -1, 5),
                    d(2, 3, 8, -1),
                    d(2, 4, -1, 7),
                    d(3, 13, 10, -1),
                    d(3, 16, 11, 9),
                    d(3, 0, -1, 10),
                    d(4, 17, 13, -1),
                    d(4, 9, -1, 12),
                    d(5, 6, 15, -1),
                    d(5, 1, 16, 14),
                    d(5, 10, 17, 15),
                    d(5, 12, -1, 16),
                ],
                vec![
                    Degree::exact(7),
                    Degree::new(7, INFTY),
                    Degree::exact(5),
                    Degree::exact(6),
                    Degree::exact(5),
                    Degree::exact(5),
                ],
            ),
            CombinedRule::new(
                vec![false, true, true],
                9,
                2,
                7,
                vec![
                    d(1, 3, 4, -1),
                    d(4, 2, -1, 15),
                    d(0, 1, 3, -1),
                    d(0, 0, -1, 2),
                    d(1, 15, 5, 0),
                    d(1, 19, 6, 4),
                    d(1, 9, 7, 5),
                    d(1, 11, -1, 6),
                    d(2, 12, 9, -1),
                    d(2, 6, 10, 8),
                    d(2, 18, -1, 9),
                    d(3, 7, 12, -1),
                    d(3, 8, -1, 11),
                    d(4, 17, 14, -1),
                    d(4, 20, 15, 13),
                    d(4, 4, 1, 14),
                    d(5, 21, 17, -1),
                    d(5, 13, -1, 16),
                    d(6, 10, 19, -1),
                    d(6, 5, 20, 18),
                    d(6, 14, 21, 19),
                    d(6, 16, -1, 20),
                ],
                vec![
                    Degree::exact(5),
                    Degree::exact(7),
                    Degree::new(7, INFTY),
                    Degree::exact(5),
                    Degree::exact(6),
                    Degree::exact(5),
                    Degree::exact(5),
                ],
            ),
        ];
        assert_eq!(combined.len(), 5);
        assert_eq!(expected.len(), 5);
        for (i, exp) in expected.iter().enumerate() {
            assert_eq!(combined[i], *exp, "combined rule {i}");
        }
    }
}
