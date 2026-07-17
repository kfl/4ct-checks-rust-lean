# Near-linear 4CT computer checks -- Rust & Lean ports

Independent **Rust** and **Lean 4** re-implementations of the computer checks
for the near-linear-time proof of the Four Colour Theorem. They verify the same
combinatorial-map discharging argument as the reference C++ program: enumerating
cartwheels, combining discharging rules, and checking reducibility.

## Relationship to the C++ reference

The reference C++ implementation lives in a separate repository,
[`near-linear-4ct/computer-checks`](https://github.com/near-linear-4ct/computer-checks).
These ports are re-implementations of the C++ reference: each port module
mirrors the same-named C++ source file (e.g. `configuration.rs` /
`Configuration.lean` from `computer-checks/src/configuration`).

The two repositories share one contract: **`FORMAT.md`**, the on-disk format
spec for configurations, rules, combined rules, and cartwheels. A copy lives
here so the ports are self-describing and the `../FORMAT.md` references resolve.
Both ports read and write byte-identical files, which is what makes the
differential testing against C++ meaningful.

## Layout

- **`rust_port/`** -- the Rust port: a library crate (`combine`) plus a `main`
  CLI mirroring the C++ `main`.
- **`lean4_port/`** -- the Lean 4 port: the `NearLinear4ct` library plus `main`
  and `test` executables; runtime proof obligations are always-on asserts, and
  a machine-checked theorem layer covers the core algorithms (the homomorphism
  BFS is proved sound, complete and total over certified configurations).
  `lean4_port/FIDELITY.md` records the correspondence to the paper's
  Appendix A pseudocode, the deliberate deviations, and the machine-checked
  claims; `lean4_port/PERFORMANCE_NOTES.md` the measured characterisation.
- **`modi/`** -- scripts to build and run the full 3-way differential (C++ /
  Rust / Lean) on the MODI Linux HPC cluster.
- **`FORMAT.md`** -- shared on-disk format spec (copied from the C++ repo).
- **`RESULTS.md`** -- verification + performance writeup (correctness vs C++,
  parallel speedups).

## Running the tests

**Rust** (unit + property tests):
```sh
cd rust_port
cargo test
```
Build the CLI with `cargo build --release` (binary at
`rust_port/target/release/main`).

**Lean** (the `test` executable runs the in-repo proof-obligation checks):
```sh
cd lean4_port
lake exe test      # builds if needed, then runs the checks
```
`lake build` compiles the library and both executables. A failing proof
obligation makes the process exit non-zero -- "success" is "the run completes".

## Full validation

The complete validation reproduces Lemmas A.1-A.6 of the article and checks that
all three implementations (C++, Rust, Lean) agree end-to-end. It needs two extra
data repositories,

```sh
git clone --depth 1 git@github.com:near-linear-4ct/reducible-configurations.git
git clone --depth 1 git@github.com:near-linear-4ct/discharging-rules.git
```

and, for the differential, the C++ reference binary built from the
`computer-checks` repo. The pipeline is: combine rules (A.1/A.2) -> enumerate
wheels and cartwheels (A.3) -> the degree/triangle checks (A.4-A.6). On a laptop
the cheap byte-identical subset (the `combine_rules` stage) runs directly; the
full enumeration is many-core work.

`modi/` packages this for the MODI HPC cluster -- see `modi/README.md` for the
end-to-end 3-way differential and the parallel scaling runs, and `RESULTS.md`
for the measured outcomes (full correctness vs C++, and the per-degree
speedups).

## License

MIT -- see [`LICENSE`](LICENSE). These ports re-implement the original C++
computer checks, which are likewise MIT-licensed (see the
[`near-linear-4ct/computer-checks`](https://github.com/near-linear-4ct/computer-checks)
repository).
