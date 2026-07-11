//! Rust port of the near-linear 4CT computer checks.
//!
//! This crate is a behaviour-preserving port of the C++ library in `computer-checks/src`.
//! It manipulates planar triangulations as combinatorial maps (rotation systems)
//! built from "darts" (half-edges) and runs discharging-method verification.
//!
//! The modules are declared below in dependency order, bottom-up.

// --- core value types & helpers ---------------------------------------------
pub mod compact_index;
pub mod degree;
pub mod mapping;
pub mod util;
pub mod work_queue;

// --- combinatorial map ------------------------------------------------------
pub mod pseudo_triangulation;

// --- configurations with degrees --------------------------------------------
pub mod pseudo_configuration;

// --- file-backed types ------------------------------------------------------
pub mod configuration;
pub mod rule;

// --- the enumeration engine -------------------------------------------------
pub mod cartwheel;

// --- drivers (combine_rules, enum_*, check_*) -------------------------------
pub mod combine_cartwheel;

// --- shared test fixtures/helpers (test builds only) ------------------------
#[cfg(test)]
mod test_support;
