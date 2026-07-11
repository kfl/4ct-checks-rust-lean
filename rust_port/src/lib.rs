//! Rust port of the near-linear 4CT computer checks.
//!
//! This crate is a behaviour-preserving port of the C++ library in `../src`.
//! It manipulates planar triangulations as combinatorial maps (rotation systems)
//! built from "darts" (half-edges) and runs discharging-method verification.
//!
//! The port is built bottom-up. Modules are declared here in dependency order;
//! each is filled in (with its ported tests) phase by phase. See `PORTING_PLAN.md`
//! for the phases and the risk register (R1–R7) referenced throughout the code.
//!
//! Risk-register quick reference (full text in `PORTING_PLAN.md`):
//! - R1: index / `nil = -1` sentinel modeling (use `Option`/newtypes carefully).
//! - R2: `std::map`/`std::set` are ordered  -> use `BTreeMap`/`BTreeSet`, not Hash*.
//! - R3: deterministic file load order -> sort directory entries by path explicitly.
//! - R4: parallelism -> rayon `par_iter`; pure verification, no shared mutable state.
//! - R5: asserts ARE the proof -> use `assert!`, never `debug_assert!`.
//! - R6: inheritance -> composition (embedded fields + small traits, no `Deref` abuse).
//! - R7: output is the proof artifact -> byte-identical file formats (see `FORMAT.md`).

// --- Phase 1: leaf types -----------------------------------------------------
pub mod compact_index;
pub mod degree;
pub mod mapping;
pub mod util;
pub mod work_queue;

// --- Phase 2: combinatorial map ---------------------------------------------
pub mod pseudo_triangulation;

// --- Phase 3: configurations with degrees -----------------------------------
pub mod pseudo_configuration;

// --- Phase 4: file-backed types ---------------------------------------------
pub mod configuration;
pub mod rule;

// --- Phase 5: the enumeration engine ----------------------------------------
pub mod cartwheel;

// --- Phase 6: drivers (combine_rules, enum_*, check_*) -----------------------
pub mod combine_cartwheel;
