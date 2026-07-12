# Running the ports on MODI (Linux HPC)

Scripts for running the near-linear-4CT **Rust and Lean ports** on
[MODI](https://erda.ku.dk/user-docs/html/sections/erda/jupyter/modi/index.html)
(or any Linux node). Two goals:

1. **Full binary correctness** of the Rust and Lean ports vs the C++ original --
   end-to-end, not just the cheap subset we can run on a laptop.
2. **Parallel wall-clock speedup** of the two ports on real many-core Linux
   hardware (without the macOS `_tlv_get_addr` / system-allocator artefacts).

The ports are built **in place** under the MODI mount and run inside MODI's
**stock Apptainer image** -- MODI blocks rootless `apptainer build --fakeroot`, so
there is no custom image to build. The C++ reference is supplied as a prebuilt
static binary from the sibling `computer-checks` repo.

## Layout on MODI

`~/modi_mount` is the only directory the compute nodes can see, so everything
lives there as two **sibling** checkouts:

```
~/modi_mount/
  4ct-checks-rust-lean/   <- this repo (Rust + Lean ports, these scripts)
  computer-checks/        <- the C++ reference; its build/src/main is the C++ oracle
```

The scripts resolve the C++ binary at `../computer-checks/build/src/main` relative
to this repo, matching that layout (override with `CPP=...`).

## Files

- **`modi_setup.sh`** -- one-shot, idempotent setup: clone/update the repos and data, stage the C++ binary from the ERDA root, install rustup/elan if missing, build both ports. Start here.
- **`Dockerfile`** -- toolchain image to build the **C++ reference binary** (in the sibling `computer-checks` repo) as a static glibc-only ELF.
- **`run_p7.sh`** -- the cheap byte-identical subset (combine_rules A.1/A.2); **run this first**.
- **`p7_job.sh`** -- `sbatch` wrapper that runs `run_p7.sh 0` inside the stock image.
- **`full_differential.sh`** -- **full** 3-way pipeline differential (A.3-A.6): combine_rules -> enum_wheels -> enum_cartwheels -> check_*.
- **`full_job.sh`** -- `sbatch` wrapper for `full_differential.sh` (single degree; degree-7 gate by default).
- **`full_array.sh`** -- `sbatch` job ARRAY: all degrees 7-11 as separate jobs, checkpoint+resume via a ledger.
- **`scaling.sh`** -- parallel wall-clock thread sweep (Rust & Lean vs serial C++).
- **`scaling_job.sh`** -- `sbatch` wrapper for `scaling.sh` (stock image).

## MODI facts these scripts assume (from the MODI user guide)
- **Apptainer** is the container runtime (not Singularity).
- **`~/modi_mount`** is the *only* directory the compute nodes can see; the repos,
  and any retrievable job output, must live there (50 GB/user cap). **Submit jobs
  from `~/modi_mount`.**
- **`~/modi_images/`** holds the `.sif` images (the stock `hpc-notebook-*.sif`).
- **`srun`/`sacct` are not supported** -- run `apptainer` directly in the job body.
- Interactive node: **`salloc`**. Partitions: **`modi_devel`** (20 min, default) |
  **`modi_short`** (48 h) | **`modi_long`** (7 d) | **`modi_max`** (1 mo). No
  account/QOS needed.

Only `modi_setup.sh` (and the C++ `cpp_main`) need delivering by hand: `sftp` them
to the user's ERDA root, visible on MODI as `~/erda_mount/`. Every other script is
run from the cloned repo. (The Jupyter terminal does not handle `cat <<EOF`
heredocs, and `apptainer` only runs inside `sbatch` jobs, not on the login node.)

## 0. One-shot setup: `modi_setup.sh`
`modi/modi_setup.sh` performs this section and the next end-to-end (clone/update,
data repos, C++ binary staged from the ERDA root, toolchains, optimised builds).
Bootstrap it once by `sftp` from your own machine, then run it on the MODI
Jupyter terminal:
```
# from your machine:              sftp <you>@io.erda.dk : put modi/modi_setup.sh
# on the MODI Jupyter terminal:   sh ~/erda_mount/modi_setup.sh
```
The manual equivalent follows. From the MODI Jupyter terminal (which has internet):
```
git clone https://github.com/kfl/4ct-checks-rust-lean.git ~/modi_mount/4ct-checks-rust-lean
```
The C++ source repo (https://github.com/near-linear-4ct/computer-checks) is *not*
needed on MODI: it **cannot be compiled there** (its build dependencies are not
available), so only its prebuilt binary is staged, at
`~/modi_mount/computer-checks/build/src/main`.

## 1. Build the ports in place + supply the C++ binary
Rust and Lean build without root using rustup/elan installed in `$HOME`; run them
from a shell where the toolchains are on `PATH`:
```
cd ~/modi_mount/4ct-checks-rust-lean
( cd rust_port  && cargo build --release )
( cd lean4_port && lake build )

# the differential reads the data repos from rust_port/:
cd rust_port
git clone --depth 1 https://github.com/near-linear-4ct/discharging-rules.git
git clone --depth 1 https://github.com/near-linear-4ct/reducible-configurations.git
cd ../..
```

The **C++ reference binary** cannot be built on MODI (its build dependencies are
not available there), so it is built separately -- on any Mac/Linux box with Docker,
via `modi/Dockerfile` + the `computer-checks` repo's `STATIC_DEPS` CMake option -- as a
static, glibc-only ~2.9 MB binary, then shipped to
`~/modi_mount/computer-checks/build/src/main`. Build commands are in `modi/Dockerfile`'s
header; `sftp` the result to the ERDA root as `cpp_main` (where one already lives,
from the 2026-06 verification runs) -- `modi_setup.sh` copies it into place.

## 2. Run the cheap correctness check FIRST (minutes)
The cross-platform determinism gate -- if it's `IDENTICAL` on Linux, the
ordering/hashing is platform-stable and the multi-hour full run is trustworthy.
p7 fits the default `modi_devel` 20-min limit. As a batch job (submit from `~/modi_mount`):
```
cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/p7_job.sh
cat ~/modi_mount/p7-*.out
```
or interactively after `salloc`:
```
cd ~/modi_mount/4ct-checks-rust-lean
apptainer exec ~/modi_images/hpc-notebook-*.sif modi/run_p7.sh 0
```
Expect:
```
  A.1 (empty C) Lean vs C++:  IDENTICAL
  A.1 (empty C) Lean vs Rust: IDENTICAL
  A.2 (real configs) Lean vs C++:  IDENTICAL
  ...
All differential checks passed.
```
If anything `DIFFER`s, stop -- we've caught a cross-platform issue cheaply (the whole
point of running the subset first).

## 3. Measure parallel scaling (goal 2)
Submit from `~/modi_mount` (defaults to `modi_short`):
```
cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/scaling_job.sh
cat ~/modi_mount/scaling-*.out
```
Prints a table of best-of-N wall-clock per thread count for Rust and Lean, their
self-speedups, and Rust-vs-serial-C++.

> **Caveat:** `combine_rules` is light and partly I/O-bound (~45% config loading
> single-threaded), so its scaling plateaus early. For a representative *compute*
> scaling curve, use a `check_*` phase once the cartwheel data is staged (step 4).

## 4. Full correctness -- the whole A.3-A.6 pipeline (goal 1)
> **Lemma coverage:** this script covers **A.2-A.6** (its `combine_rules` stage is the
> A.2 non-blocked variant, `-C reducible-configurations/D`, needed as input to A.3). The
> **A.1** empty-config combine (`-C empty`) is byte-diffed by `run_p7.sh 0` (step 2). So a
> full A.1-A.6 reproduction = `run_p7.sh 0` **and** `full_differential.sh all`.

`full_differential.sh` runs the entire pipeline -- `combine_rules` -> `enum_wheels` ->
`enum_cartwheels` -> `check_{deg7,deg8,7triangle}` -- for all three ports, byte-diffing
every file-producing stage and requiring exit-code **agreement** on the assertion-only
`check_*` phases (they emit no files; success == no assertion fires). It is parameterised
by degree so you can gate cheaply before the heavy run:

```
# Cheap GATE first (degree 7, minutes) -- validates the machinery end-to-end:
cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/full_job.sh
cat ~/modi_mount/full-*.out

# Even quicker smoke test (first 20 wheels of degree 7):
cd ~/modi_mount && WHEEL_LIMIT=20 sbatch --export=ALL 4ct-checks-rust-lean/modi/full_job.sh

# FULL run (degrees 7..11, hours) once the gate is green:
cd ~/modi_mount && SCOPE=all sbatch --export=ALL --partition=modi_long --time=24:00:00 4ct-checks-rust-lean/modi/full_job.sh
```

For the full run prefer the **job array** `full_array.sh` over a single `SCOPE=all` job:
it runs each degree as its own whole-node job and records a PASS/FAIL line per degree in
`full-summary.txt`, so a degree that times out or fails neither loses the others nor the
completed ones -- re-submitting simply skips degrees already marked PASS.

```
cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/full_array.sh   # degrees 7..11, 2 at a time
cat ~/modi_mount/full-summary.txt              # ledger; one line per finished degree
cat ~/modi_mount/full-d10-*.out                # full per-stage detail for a degree
```

Each stage prints its object count (e.g. `d7: 5439 wheels`) and `rust == C++ / lean == C++`.
Any byte divergence stops the run at that stage; any `check_*` disagreement is reported
with the three exit codes. Validated end-to-end on macOS (all three ports agree through
the checks) before shipping.

## Gotchas
- **C++23**: the `Dockerfile` uses `ubuntu:24.04` (g++-13). If the C++ build errors on a
  C++23 feature, bump the base / install `g++-14`.
- **Lean shared lib**: the build records `libleanshared`'s dir in `.lean_libdir` and the
  scripts add it to `LD_LIBRARY_PATH`; if the Lean binary still can't find it,
  `export LD_LIBRARY_PATH=$(dirname $(find $HOME/.elan -name 'libleanshared*' | head -1))`.
- **No mathlib**: the Lean port only imports core/Std, so `lake build` is quick and
  needs no extra package cache.

## References
- MODI user guide: https://erda.ku.dk/user-docs/html/sections/erda/jupyter/modi/index.html
- MODI helper scripts: https://modi-helper-scripts.readthedocs.io/en/latest/
- Custom-software examples: https://github.com/The-First-Billion-Years/MODI_scripts
