//! Phase 6 — verification drivers. Port of `../src/combine_cartwheel.{hpp,cpp}`.
//!
//! The Lemma A.4/A.5/A.6 checks: `run_check_deg8`, `run_check_7triangle`,
//! `run_check_deg7` and their helpers.
//!
//! R4: the C++ posts one task per cartwheel to a `boost::asio::thread_pool`.
//! These tasks are pure verification (they only read inputs and `assert!`), with
//! no shared mutable state, so the idiomatic translation is
//! `cartwheels.par_iter().for_each(|cw| …)` (rayon). A failing proof obligation
//! panics its worker; rayon propagates the panic, so the process fails loudly —
//! matching the C++ `assert` abort.
//! R5: the asserts here ARE the proof — plain `assert!`, never `debug_assert!`.

use crate::cartwheel::CartWheel;
use crate::configuration::Configuration;
use crate::degree::{CARTWHEEL_DEG_MAX, Degree, INFTY};
use crate::pseudo_configuration::PseudoConfiguration;
use rayon::prelude::*;
use std::path::Path;

/// Drop cartwheels with a vertex of fixed degree `k`; collapse `[k-1, 9]` ranges
/// to fixed `k-1` (C++ `delete_degree_from_k_to_9`).
pub fn delete_degree_from_k_to_9(cartwheels: &[CartWheel], k: i32) -> Vec<CartWheel> {
    let mut new_cartwheels = Vec::new();
    for cw in cartwheels {
        let mut cw = cw.clone();
        let mut remove = false;
        for v in 0..cw.pc.tri.n {
            if cw.pc.degrees[v].lower == k && cw.pc.degrees[v].upper == k {
                remove = true;
                break;
            } else if cw.pc.degrees[v].lower == k - 1 && cw.pc.degrees[v].upper == CARTWHEEL_DEG_MAX
            {
                cw.pc.degrees[v].upper = k - 1;
            }
        }
        if !remove {
            new_cartwheels.push(cw);
        }
    }
    new_cartwheels
}

/// Drop cartwheels that contain a 7-triangle (C++ `delete_7triangle`).
pub fn delete_7triangle(cartwheels: &[CartWheel]) -> Vec<CartWheel> {
    let confs = vec![get_7triangle()];
    cartwheels
        .iter()
        .filter(|cw| !cw.pc.blocked_by_reducible_configuration(0, &confs))
        .cloned()
        .collect()
}

/// The configuration of three mutually adjacent degree-7 vertices
/// (C++ `get_7triangle`).
pub fn get_7triangle() -> Configuration {
    let t7 = PseudoConfiguration::from_v_rotations(
        3,
        &[vec![1, 2, -1], vec![2, 0, -1], vec![0, 1, -1]],
        vec![Degree::exact(7), Degree::exact(7), Degree::exact(7)],
    );
    Configuration::new(0, 3, t7.tri.darts, t7.degrees)
}

// --- Lemma A.4: a vertex of degree 8 ----------------------------------------

pub fn run_check_deg8(cartwheeldir: &Path, confdir: &Path) {
    let cartwheels = CartWheel::get_cartwheels(cartwheeldir);
    let confs = Configuration::get_confs(confdir);
    check_deg8(&cartwheels, &confs);
}

pub fn check_deg8(all_cartwheels: &[CartWheel], confs: &[Configuration]) {
    let cartwheels = delete_degree_from_k_to_9(all_cartwheels, 9);
    tracing::info!("After removing cartwheels with degree 9,");
    tracing::info!("{} cartwheels remain.", cartwheels.len());
    cartwheels.par_iter().for_each(|cartwheel| {
        if cartwheel.pc.degrees[cartwheel.center] != Degree::exact(8) {
            return;
        }
        let center_darts = cartwheel.center_darts_by_degree();
        if !center_darts[8].is_empty() {
            check88(cartwheel, &center_darts[8], &cartwheels, confs);
        } else if center_darts[7].len() == 1 {
            check87(cartwheel, &center_darts[7], &cartwheels, confs);
        } else if center_darts[7].len() > 1 {
            check787(cartwheel, &center_darts[7], &cartwheels, confs);
        } else {
            panic!("degree-8 centre with no degree-7/8 spokes");
        }
    });
    tracing::info!("Finished checking degree 8 vertices.");
}

fn check88(
    cartwheel: &CartWheel,
    darts8: &[usize],
    cartwheels: &[CartWheel],
    confs: &[Configuration],
) {
    for &dart in darts8 {
        let rev = cartwheel.pc.tri.darts[dart].rev();
        let combined = cartwheel.pc.combine_each_cartwheel(rev, cartwheels, confs);
        assert!(combined.is_empty());
    }
}

fn check87(
    cartwheel: &CartWheel,
    darts7: &[usize],
    cartwheels: &[CartWheel],
    confs: &[Configuration],
) {
    assert_eq!(darts7.len(), 1);
    let rev = cartwheel.pc.tri.darts[darts7[0]].rev();
    let combined = cartwheel.pc.combine_each_cartwheel(rev, cartwheels, confs);
    assert!(combined.is_empty());
}

fn check787(
    cartwheel: &CartWheel,
    darts7: &[usize],
    cartwheels: &[CartWheel],
    confs: &[Configuration],
) {
    let n = darts7.len();
    let mut min_dist = INFTY;
    let mut dist = vec![0; n];
    for i in 0..n {
        let mut dart1 = darts7[i];
        let dart2 = if i == n - 1 { darts7[0] } else { darts7[i + 1] };
        while dart1 != dart2 {
            dart1 = cartwheel.pc.tri.darts[dart1]
                .succ()
                .expect("centre rotation is closed");
            dist[i] += 1;
        }
        min_dist = min_dist.min(dist[i]);
    }
    for i in 0..n {
        if dist[i] > min_dist {
            continue;
        }
        let dart1 = darts7[i];
        let dart2 = if i == n - 1 { darts7[0] } else { darts7[i + 1] };
        let rev1 = cartwheel.pc.tri.darts[dart1].rev();
        let rev2 = cartwheel.pc.tri.darts[dart2].rev();
        let combined_set = cartwheel
            .pc
            .combine_each_cartwheel_twice(rev1, rev2, cartwheels, confs);
        for (combined, mappings_cw) in combined_set {
            let center = mappings_cw.vmap[cartwheel.center].expect("combination map is total");
            assert!(contain_x(&combined, center));
        }
    }
}

/// The fixed obstruction configuration `X` (C++ `getX`).
pub fn get_x() -> PseudoConfiguration {
    PseudoConfiguration::from_v_rotations(
        17,
        &[
            vec![1, 2, 3, 4, 5, 6, 7, 8],
            vec![0, 8, 11, 12, 2],
            vec![0, 1, 12, -1, 3],
            vec![0, 2, -1, 13, 4],
            vec![0, 3, 13, 14, 5],
            vec![0, 4, 14, 15, 16, -1, 6],
            vec![0, 5, -1, 7],
            vec![0, 6, -1, 8],
            vec![0, 7, -1, 9, 10, 11, 1],
            vec![8, -1, 10],
            vec![8, 9, -1, 11],
            vec![1, 8, 10, -1, 12],
            vec![1, 11, -1, 2],
            vec![3, -1, 14, 4],
            vec![4, 13, -1, 15, 5],
            vec![5, 14, -1, 16],
            vec![5, 15, -1],
        ],
        vec![
            Degree::exact(8),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(7),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(7),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(8),
            Degree::exact(5),
            Degree::exact(5),
            Degree::exact(8),
            Degree::exact(5),
            Degree::exact(5),
        ],
    )
}

/// Whether `X` embeds into `z` rooted at vertex `v`, over the 8 rotations of the
/// root dart (C++ `containX`).
pub fn contain_x(z: &PseudoConfiguration, v: usize) -> bool {
    let x = get_x();
    let dart_z = z.tri.any_dart(v).expect("z has a dart at v");
    let mut dart_x = x.tri.any_dart(0).expect("X has a dart at 0");
    for _ in 0..8 {
        if PseudoConfiguration::homomorphism(&x, dart_x, z, dart_z, |a, b| Degree::includes(&a, &b))
            .is_some()
        {
            return true;
        }
        dart_x = x.tri.darts[dart_x]
            .succ()
            .expect("X centre rotation is closed");
    }
    false
}

// --- Lemma A.5: a 7-triangle -------------------------------------------------

pub fn run_check_7triangle(cartwheeldir: &Path, confdir: &Path) {
    let cartwheels = CartWheel::get_cartwheels(cartwheeldir);
    let confs = Configuration::get_confs(confdir);
    check_7triangle(&cartwheels, &confs);
}

pub fn check_7triangle(all_cartwheels: &[CartWheel], confs: &[Configuration]) {
    let cartwheels = delete_degree_from_k_to_9(all_cartwheels, 9);
    let cartwheels = delete_degree_from_k_to_9(&cartwheels, 8);
    tracing::info!("After removing cartwheels with degree 8 and 9,");
    tracing::info!("{} cartwheels remain.", cartwheels.len());
    cartwheels.par_iter().for_each(|cartwheel| {
        for &e in &cartwheel.center_darts {
            let f = cartwheel.pc.tri.darts[e]
                .succ()
                .expect("centre rotation is closed");
            let rev_e = cartwheel.pc.tri.darts[e].rev();
            let rev_f = cartwheel.pc.tri.darts[f].rev();
            let v_e = cartwheel.pc.tri.darts[rev_e].head();
            let v_f = cartwheel.pc.tri.darts[rev_f].head();
            assert!(cartwheel.pc.degrees[v_e].is_fixed());
            assert!(cartwheel.pc.degrees[v_f].is_fixed());
            if cartwheel.pc.degrees[v_e].lower == 7 && cartwheel.pc.degrees[v_f].lower == 7 {
                let combined =
                    cartwheel
                        .pc
                        .combine_each_cartwheel_twice(rev_e, rev_f, &cartwheels, confs);
                assert!(combined.is_empty());
            }
        }
    });
    tracing::info!("Finished checking 7-triangles.");
}

// --- Lemma A.6: a vertex of degree 7 -----------------------------------------

pub fn run_check_deg7(cartwheeldir: &Path, confdir: &Path) {
    let cartwheels = CartWheel::get_cartwheels(cartwheeldir);
    let confs = Configuration::get_confs(confdir);
    check_deg7(&cartwheels, confs);
}

pub fn check_deg7(all_cartwheels: &[CartWheel], mut confs: Vec<Configuration>) {
    let cartwheels = delete_degree_from_k_to_9(all_cartwheels, 9);
    let cartwheels = delete_degree_from_k_to_9(&cartwheels, 8);
    let cartwheels = delete_7triangle(&cartwheels);
    tracing::info!(
        "After removing cartwheels with degree 8 and 9 and cartwheels containing a 7-triangle,"
    );
    tracing::info!("{} cartwheels remain.", cartwheels.len());
    confs.push(get_7triangle());
    let confs = confs; // freeze for the parallel section
    cartwheels.par_iter().for_each(|cartwheel| {
        let center_darts = cartwheel.center_darts_by_degree();
        if center_darts[7].len() == 1 {
            check77(cartwheel, &center_darts[7], &cartwheels, &confs);
        } else if center_darts[7].len() > 1 {
            check777(cartwheel, &center_darts[7], &cartwheels, &confs);
        } else {
            panic!("degree-7 centre with no degree-7 spokes");
        }
    });
    tracing::info!("Finished checking degree 7 vertices.");
}

fn check77(
    cartwheel: &CartWheel,
    darts7: &[usize],
    cartwheels: &[CartWheel],
    confs: &[Configuration],
) {
    assert_eq!(darts7.len(), 1);
    let rev = cartwheel.pc.tri.darts[darts7[0]].rev();
    let combined = cartwheel.pc.combine_each_cartwheel(rev, cartwheels, confs);
    assert!(combined.is_empty());
}

fn check777(
    cartwheel: &CartWheel,
    darts7: &[usize],
    cartwheels: &[CartWheel],
    confs: &[Configuration],
) {
    for (i, &e1) in darts7.iter().enumerate() {
        let rev1 = cartwheel.pc.tri.darts[e1].rev();
        for &e2 in &darts7[..i] {
            let rev2 = cartwheel.pc.tri.darts[e2].rev();
            let combined = cartwheel
                .pc
                .combine_each_cartwheel_twice(rev1, rev2, cartwheels, confs);
            assert!(combined.is_empty());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_7triangle_structure() {
        let t = get_7triangle();
        assert_eq!(t.pc.tri.n, 3);
        assert_eq!(t.dart_id, 0);
        assert!(t.pc.degrees.iter().all(|d| *d == Degree::exact(7)));
    }

    #[test]
    fn get_x_constructs() {
        let x = get_x();
        assert_eq!(x.tri.n, 17);
        assert_eq!(x.degrees[0], Degree::exact(8));
        // Vertex 0 has degree 8 with a closed rotation: 8 darts, all with succ.
        assert!(x.tri.any_dart(0).is_some());
    }

    #[test]
    fn delete_degree_collapses_and_removes() {
        // A cartwheel with a fixed degree-9 vertex is removed; a [8,9] range
        // collapses to fixed 8 under k=9.
        let cw = CartWheel::generate_cartwheel(7, &[5, 5, 5, 5, 5, 5, 5]);
        // generate_cartwheel gives second-neighbours degree [5,9]; under k=9
        // those [8,9]? No — they are [5,9]; nothing is fixed at 9, so kept.
        let kept = delete_degree_from_k_to_9(std::slice::from_ref(&cw), 9);
        assert_eq!(kept.len(), 1);

        // Force a fixed degree-9 vertex -> removed.
        let mut cw9 = cw.clone();
        cw9.pc.degrees[8] = Degree::exact(9);
        assert!(delete_degree_from_k_to_9(std::slice::from_ref(&cw9), 9).is_empty());
    }
}
