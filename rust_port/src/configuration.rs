//! File-backed reducible configurations.
//!
//! `Configuration` embeds a `PseudoConfiguration` and adds a root `dart_id`.
//!
//! The adjacency scratch (`suc`) is a plain 2D vector with a `-1` sentinel, so
//! no ordered-container behaviour is observable; it is a `Vec<Vec<i32>>`.
//! `from_file` parsing reproduces the structures `FORMAT.md` specifies,
//! byte-for-byte.

use crate::degree::{CONF_DEG_MAX, Degree, INFTY};
use crate::pseudo_configuration::PseudoConfiguration;
use crate::pseudo_triangulation::Dart;
use rayon::prelude::*;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Configuration {
    pub pc: PseudoConfiguration,
    pub dart_id: usize,
    /// Cached root-dart endpoint lower degrees (the `contain_conf` bucket
    /// key). Derived and validated by `new`, which every construction goes
    /// through; the fields are never written after construction.
    pub root_head_deg: i32,
    pub root_tail_deg: i32,
}

impl Configuration {
    /// Construct from `(dart_id, N, darts, degrees)`.
    pub fn new(dart_id: usize, n: usize, darts: Vec<Dart>, degrees: Vec<Degree>) -> Self {
        let pc = PseudoConfiguration::new(n, darts, degrees);
        let f = pc.tri.darts[dart_id];
        let head_deg = pc.degrees[f.head()];
        let tail_deg = pc.degrees[pc.tri.darts[f.rev()].head()];
        assert!(head_deg.is_fixed());
        assert!(tail_deg.is_fixed());
        assert!(head_deg.lower <= CONF_DEG_MAX);
        assert!(tail_deg.lower <= CONF_DEG_MAX);
        Configuration {
            pc,
            dart_id,
            root_head_deg: head_deg.lower,
            root_tail_deg: tail_deg.lower,
        }
    }

    /// Reflect the configuration by swapping each dart's `succ`/`pred`.
    pub fn mirror(&self) -> Configuration {
        let mut darts = self.pc.tri.darts.clone();
        for d in &mut darts {
            d.swap_succ_pred();
        }
        Configuration::new(self.dart_id, self.pc.tri.n, darts, self.pc.degrees.clone())
    }

    /// Parse a `.conf` file into one or more configurations.
    ///
    /// Internal vertices list clockwise rotations; the ring vertices' rotations
    /// are reconstructed from the successor relation `suc`. Cut-vertices expand
    /// to several configurations, and each is paired with its mirror.
    pub fn from_file(path: &Path) -> Vec<Configuration> {
        let content = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("Could not open file {}: {e}", path.display()));
        // The format's leading blank line yields no whitespace tokens.
        let mut tok = content.split_whitespace();
        let n = next_usize(&mut tok);
        let r = next_usize(&mut tok);

        let mut degrees = vec![Degree::new(1, INFTY); n];
        let mut rotations: Vec<Vec<i32>> = vec![Vec::new(); n];
        // suc[ring vertex][vertex] = next vertex in the ring vertex's rotation.
        let mut suc = vec![vec![-1i32; n]; r];

        for u in r..n {
            let t = next_usize(&mut tok);
            assert_eq!(t, u + 1);
            let deg = next_usize(&mut tok);
            degrees[u] = Degree::exact(deg as i32);
            for _ in 0..deg {
                let v = next_i32(&mut tok);
                rotations[u].push(v - 1);
            }
            for j in 0..deg {
                let v = rotations[u][j];
                let pre = rotations[u][(j + deg - 1) % deg];
                let nxt = rotations[u][(j + 1) % deg];
                if v < r as i32 {
                    suc[v as usize][nxt as usize] = u as i32;
                    suc[v as usize][u] = pre;
                }
            }
        }

        // Reconstruct each ring vertex's rotation by walking `suc`.
        for v in 0..r {
            let start = (v + 1) % r;
            let end = (v + r - 1) % r;
            let mut curr = start as i32;
            while curr != -1 {
                rotations[v].push(curr);
                curr = suc[v][curr as usize];
            }
            if *rotations[v].last().expect("ring rotation is non-empty") != end as i32 {
                panic!("Invalid configuration file: {}", path.display());
            }
            rotations[v].push(-1); // boundary
        }

        let mut configurations = extend_from_cut_vertices(n, r, &degrees, &rotations);
        let mirrors = get_mirrors(&configurations);
        configurations.extend(mirrors);
        configurations
    }

    /// Load every `.conf` file in `confdir`.
    ///
    /// The 8200 files (19754 configurations) are read + parsed in parallel (rayon) --
    /// the parse is otherwise a serial bottleneck. Containment is an
    /// order-independent `any`, so the load order is irrelevant; output is byte-identical.
    ///
    /// The `par_iter` benefits the *single-process* stages (`combine_rules`, `enum_wheels`,
    /// `check`), which load configs once and fan the parse out across all cores. In the
    /// per-wheel `enum_cartwheels` stage the driver runs 128 of these processes at once, so
    /// it caps each to one thread (`RAYON_NUM_THREADS=1`) to avoid oversubscription -- the
    /// parallelism there comes from running many processes, not many threads per process.
    pub fn get_confs(confdir: &Path) -> Vec<Configuration> {
        let paths: Vec<PathBuf> = std::fs::read_dir(confdir)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", confdir.display()))
            .filter_map(|entry| {
                let path = entry.expect("directory entry").path();
                (path.is_file() && path.extension().and_then(|e| e.to_str()) == Some("conf"))
                    .then_some(path)
            })
            .collect();
        let confs: Vec<Configuration> = paths
            .par_iter()
            .flat_map_iter(|path| Configuration::from_file(path))
            .collect();
        tracing::info!("Total {} configurations loaded.", confs.len());
        confs
    }
}

/// Mirror image of every configuration.
pub fn get_mirrors(confs: &[Configuration]) -> Vec<Configuration> {
    confs.iter().map(Configuration::mirror).collect()
}

/// Expand cut-vertices: for each subset of cut-pairs, remove the unselected ring
/// vertices and build a configuration.
pub fn extend_from_cut_vertices(
    n: usize,
    r: usize,
    degrees: &[Degree],
    rotations: &[Vec<i32>],
) -> Vec<Configuration> {
    let p = find_cut_pairs(n, r, rotations);
    let p_size = p.len();
    if p_size > 1 {
        tracing::warn!(
            "Configuration has {} cut-vertices. This may cause a blow-up in the number of \
             configurations after handling cutvertices.",
            p_size
        );
    }
    let mut configurations = Vec::new();
    for s in 0..(1u32 << p_size) {
        let mut remove = vec![true; r];
        for (i, &(a, b)) in p.iter().enumerate() {
            if s & (1 << i) != 0 {
                remove[a] = false;
            } else {
                remove[b] = false;
            }
        }
        let z = remove_ring(n, r, degrees, rotations, &remove);
        let dart = maximum_degree_dart(&z);
        configurations.push(Configuration::new(
            dart,
            z.tri.n,
            z.tri.darts.clone(),
            z.degrees.clone(),
        ));
    }
    configurations
}

/// Find internal vertices that are cut-vertices, returning their two ring
/// neighbours.
pub fn find_cut_pairs(n: usize, r: usize, rotations: &[Vec<i32>]) -> Vec<(usize, usize)> {
    let mut p = Vec::new();
    for (offset, rot) in rotations[r..n].iter().enumerate() {
        let i = r + offset;
        let mut u_r = Vec::new();
        let mut t = 0;
        let d = rot.len();
        for j in 0..d {
            let k1 = rot[j];
            assert_ne!(k1, -1);
            if k1 < r as i32 {
                u_r.push(k1 as usize);
            }
            let k2 = rot[(j + 1) % d];
            if k1 < r as i32 && k2 >= r as i32 {
                t += 1;
            }
        }
        assert!(t <= u_r.len());
        if t >= 2 && u_r.len() != 2 {
            panic!("Invalid configuration (vertex {i} is an invalid cut-vertex");
        }
        if t == 2 && u_r.len() == 2 {
            p.push((u_r[0], u_r[1]));
        }
    }
    p
}

/// Remove the `remove`-marked ring vertices, renumber, and rebuild as a
/// `PseudoConfiguration`.
pub fn remove_ring(
    n: usize,
    r: usize,
    degrees: &[Degree],
    rotations: &[Vec<i32>],
    remove: &[bool],
) -> PseudoConfiguration {
    // Step 1: assign new vertex ids (removed ring vertices get no id).
    let mut old2new: Vec<Option<usize>> = vec![None; n];
    let mut new_id = 0;
    for (i, slot) in old2new.iter_mut().enumerate() {
        if i < r && remove[i] {
            continue;
        }
        *slot = Some(new_id);
        new_id += 1;
    }
    let new_n = new_id;

    // Step 2: new rotations. A neighbour that was removed becomes a `-1` boundary.
    let mut new_rotations: Vec<Vec<i32>> = vec![Vec::new(); new_n];
    for i in 0..n {
        if i < r && remove[i] {
            continue;
        }
        let k = old2new[i].expect("kept vertex has an id");
        for &j in &rotations[i] {
            if j == -1 {
                new_rotations[k].push(-1);
            } else {
                new_rotations[k].push(old2new[j as usize].map_or(-1, |x| x as i32));
            }
        }
    }

    // Step 3: new degrees.
    let mut new_degrees = vec![Degree::new(1, INFTY); new_n];
    for i in 0..r {
        if remove[i] {
            continue;
        }
        let k = old2new[i].expect("kept ring vertex has an id");
        let d = new_rotations[k].iter().filter(|&&v| v != -1).count();
        assert!(d == 3 || d == 4);
        new_degrees[k] = Degree::new(d as i32 + 1, INFTY);
    }
    for i in r..n {
        let k = old2new[i].expect("internal vertex has an id");
        new_degrees[k] = degrees[i];
    }

    PseudoConfiguration::from_v_rotations(new_n, &new_rotations, new_degrees)
}

/// The dart whose (head-degree, tail-degree) pair is lexicographically largest
/// among fixed-degree endpoints.
pub fn maximum_degree_dart(z: &PseudoConfiguration) -> usize {
    let mut f: Option<usize> = None;
    let mut d_f = (0, 0);
    for (i, dart) in z.tri.darts.iter().enumerate() {
        let y = dart.head();
        let x = z.tri.darts[dart.rev()].head();
        if !z.degrees[y].is_fixed() || !z.degrees[x].is_fixed() {
            continue;
        }
        let d_e = (z.degrees[y].lower, z.degrees[x].lower);
        if d_e > d_f {
            f = Some(i);
            d_f = d_e;
        }
    }
    f.expect("at least one dart has fixed-degree endpoints")
}

fn next_i32<'a>(it: &mut impl Iterator<Item = &'a str>) -> i32 {
    it.next()
        .expect("unexpected end of file")
        .parse()
        .expect("integer token")
}

fn next_usize<'a>(it: &mut impl Iterator<Item = &'a str>) -> usize {
    next_i32(it) as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{CONF1, CONF2, d, temp_with};

    // from_file parses a .conf into configurations, expanding cut-vertices and
    // pairing each with its mirror.
    #[test]
    fn read_file() {
        let f1 = temp_with(CONF1, ".conf");
        let f2 = temp_with(CONF2, ".conf");
        let confs1 = Configuration::from_file(f1.path());
        let confs2 = Configuration::from_file(f2.path());

        let deg8 = || {
            vec![
                Degree::new(4, INFTY),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(6),
            ]
        };
        let confs1_expected0 = Configuration::new(
            9,
            8,
            vec![
                d(0, 22, 1, -1),
                d(0, 10, 2, 0),
                d(0, 18, -1, 1),
                d(1, 7, 4, -1),
                d(1, 23, -1, 3),
                d(2, 12, 6, -1),
                d(2, 24, 7, 5),
                d(2, 3, -1, 6),
                d(3, 15, 9, -1),
                d(3, 19, 10, 8),
                d(3, 1, 11, 9),
                d(3, 25, 12, 10),
                d(3, 5, -1, 11),
                d(4, 17, 14, -1),
                d(4, 20, 15, 13),
                d(4, 8, -1, 14),
                d(5, 21, 17, -1),
                d(5, 13, -1, 16),
                d(6, 2, 19, -1),
                d(6, 9, 20, 18),
                d(6, 14, 21, 19),
                d(6, 16, -1, 20),
                d(7, 0, -1, 25),
                d(7, 4, 24, -1),
                d(7, 6, 25, 23),
                d(7, 11, 22, 24),
            ],
            deg8(),
        );
        let confs1_expected1 = Configuration::new(
            11,
            8,
            vec![
                d(0, 14, 1, -1),
                d(0, 9, 2, 0),
                d(0, 5, -1, 1),
                d(1, 8, 4, -1),
                d(1, 23, -1, 3),
                d(2, 2, 6, -1),
                d(2, 13, 7, 5),
                d(2, 24, 8, 6),
                d(2, 3, -1, 7),
                d(3, 1, 10, 13),
                d(3, 17, 11, 9),
                d(3, 20, -1, 10),
                d(3, 25, 13, -1),
                d(3, 6, 9, 12),
                d(4, 0, -1, 17),
                d(4, 19, 16, -1),
                d(4, 21, 17, 15),
                d(4, 10, 14, 16),
                d(5, 22, 19, -1),
                d(5, 15, -1, 18),
                d(6, 11, 21, -1),
                d(6, 16, 22, 20),
                d(6, 18, -1, 21),
                d(7, 4, 24, -1),
                d(7, 7, 25, 23),
                d(7, 12, -1, 24),
            ],
            deg8(),
        );
        let confs1_expected2 = Configuration::new(
            9,
            8,
            vec![
                d(0, 22, -1, 1),
                d(0, 10, 0, 2),
                d(0, 18, 1, -1),
                d(1, 7, -1, 4),
                d(1, 23, 3, -1),
                d(2, 12, -1, 6),
                d(2, 24, 5, 7),
                d(2, 3, 6, -1),
                d(3, 15, -1, 9),
                d(3, 19, 8, 10),
                d(3, 1, 9, 11),
                d(3, 25, 10, 12),
                d(3, 5, 11, -1),
                d(4, 17, -1, 14),
                d(4, 20, 13, 15),
                d(4, 8, 14, -1),
                d(5, 21, -1, 17),
                d(5, 13, 16, -1),
                d(6, 2, -1, 19),
                d(6, 9, 18, 20),
                d(6, 14, 19, 21),
                d(6, 16, 20, -1),
                d(7, 0, 25, -1),
                d(7, 4, -1, 24),
                d(7, 6, 23, 25),
                d(7, 11, 24, 22),
            ],
            deg8(),
        );
        let confs1_expected3 = Configuration::new(
            11,
            8,
            vec![
                d(0, 14, -1, 1),
                d(0, 9, 0, 2),
                d(0, 5, 1, -1),
                d(1, 8, -1, 4),
                d(1, 23, 3, -1),
                d(2, 2, -1, 6),
                d(2, 13, 5, 7),
                d(2, 24, 6, 8),
                d(2, 3, 7, -1),
                d(3, 1, 13, 10),
                d(3, 17, 9, 11),
                d(3, 20, 10, -1),
                d(3, 25, -1, 13),
                d(3, 6, 12, 9),
                d(4, 0, 17, -1),
                d(4, 19, -1, 16),
                d(4, 21, 15, 17),
                d(4, 10, 16, 14),
                d(5, 22, -1, 19),
                d(5, 15, 18, -1),
                d(6, 11, -1, 21),
                d(6, 16, 20, 22),
                d(6, 18, 21, -1),
                d(7, 4, -1, 24),
                d(7, 7, 23, 25),
                d(7, 12, 24, -1),
            ],
            deg8(),
        );
        let deg4 = || {
            vec![
                Degree::exact(5),
                Degree::exact(6),
                Degree::exact(5),
                Degree::exact(5),
            ]
        };
        let confs2_expected0 = Configuration::new(
            2,
            4,
            vec![
                d(0, 4, 1, -1),
                d(0, 7, -1, 0),
                d(1, 6, 3, -1),
                d(1, 8, 4, 2),
                d(1, 0, -1, 3),
                d(2, 9, 6, -1),
                d(2, 2, -1, 5),
                d(3, 1, 8, -1),
                d(3, 3, 9, 7),
                d(3, 5, -1, 8),
            ],
            deg4(),
        );
        let confs2_expected1 = Configuration::new(
            2,
            4,
            vec![
                d(0, 4, -1, 1),
                d(0, 7, 0, -1),
                d(1, 6, -1, 3),
                d(1, 8, 2, 4),
                d(1, 0, 3, -1),
                d(2, 9, -1, 6),
                d(2, 2, 5, -1),
                d(3, 1, -1, 8),
                d(3, 3, 7, 9),
                d(3, 5, 8, -1),
            ],
            deg4(),
        );

        assert_eq!(confs1.len(), 4);
        assert_eq!(confs1[0], confs1_expected0);
        assert_eq!(confs1[1], confs1_expected1);
        assert_eq!(confs1[2], confs1_expected2);
        assert_eq!(confs1[3], confs1_expected3);
        assert_eq!(confs2.len(), 2);
        assert_eq!(confs2[0], confs2_expected0);
        assert_eq!(confs2[1], confs2_expected1);
    }
}
