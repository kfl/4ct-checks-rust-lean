# Performance notes -- the Lean port

What the Lean port costs relative to the Rust port and the C++ reference, why,
and how the numbers were obtained. Companion to `RESULTS.md` (which reports the
full-pipeline many-core runs); this file covers the single-machine
characterisation and the durable codegen lessons.

**House Rules.** Correctness and readable, natural Lean come first; performance
is a *measured secondary* goal. Optimisation levers are decided on profiles, one
change at a time, preferably not bundled with fidelity changes -- and a lever
that costs clarity must earn it with a big measured win.

## Methodology

- **Machine / toolchains**: Apple M1 Pro (10-core), macOS 15.7.7; Lean 4.31.0,
  rustc 1.96.0, hyperfine 1.20.0; C++ reference from sibling `computer-checks` @
  `6cb8566`. All three binaries verified native `arm64` (no Rosetta).

- **Gate**: a measurement counts only if the measured binaries are byte-exact --
  the full-corpus 3-way differential (`p7_differential.sh 0`: 84 rules x 8200
  configs, A.1 and A.2) passed IDENTICAL for C++/Rust/Lean immediately before
  timing, and the `enum_wheels` outputs of the timed runs were byte-diffed too.

- **Single-thread pinning**: `LEAN_NUM_THREADS=1` (Lean), `RAYON_NUM_THREADS=1`
  (Rust); the C++ reference is serial. "Default" rows are the binaries as
  shipped.

- **Timing**: hyperfine; `combine_rules` with 2 warmup + 6 runs, `enum_wheels`
  with 3 runs (40-90 s per run). Wall and user CPU both recorded.

- **Attribution**: macOS `sample` on the Lean binary during single-thread runs
  (4 s over `combine_rules`, 30 s mid-`enum_wheels`), kernel-wait symbols of
  parked worker threads excluded, top-of-stack samples bucketed into compute /
  RC-free / alloc.

- **Reading the "x" figures**: two conventions appear. In the results tables,
  "vs C++" is a *time ratio* -- that binary's wall-clock divided by C++'s, so
  above 1 is slower than C++ and below 1 is faster (Lean at 2.10x takes 2.10
  times as long). In the codegen lessons and levers, "measured 1.21x" is a
  *speedup from a single change* -- time before the change divided by time
  after, so bigger is better -- and a "15-25% regression" means the time
  increased by that much.

## Results (measured 2026-07-08)

`combine_rules`, full corpus (84 rules x 8200 configs):

| binary         | wall (mean ± σ) | user CPU | vs C++ |
|:---------------|----------------:|---------:|-------:|
| C++ (serial)   | 2.261 ± 0.013 s |   2.08 s |  1.00x |
| Rust, 1 thread | 1.406 ± 0.003 s |   1.23 s |  0.62x |
| Lean, 1 thread | 4.757 ± 0.022 s |   4.56 s |  2.10x |
| Rust, default  | 0.619 ± 0.015 s |   1.57 s |  0.27x |
| Lean, default  | 1.274 ± 0.014 s |   6.73 s |  0.56x |

`enum_wheels -d 7` (671 non-blocked rules, 5439 wheels):

| binary         |  wall (mean ± σ) | user CPU | vs C++ |
|:---------------|-----------------:|---------:|-------:|
| C++ (serial)   | 41.299 ± 0.361 s |   40.4 s |  1.00x |
| Rust, 1 thread | 27.078 ± 0.036 s |   26.1 s |  0.66x |
| Lean, 1 thread | 87.578 ± 0.752 s |   86.5 s |  2.12x |
| Rust, default  |  4.707 ± 0.023 s |   35.0 s |  0.11x |
| Lean, default  | 12.984 ± 0.049 s |  120.0 s |  0.31x |

Headlines:

- **Single-thread price: Lean ≈ 2.1x C++ and ≈ 3.2-3.4x Rust, on both
  workloads.** Two very different workloads landing in one narrow band says
  constant factor (runtime/codegen), not an algorithmic difference.
- **As shipped, the Lean port beats the serial C++ reference on wall-clock**
  (0.56x / 0.31x): `parMap`/`parForEach` parallelism more than covers the
  single-thread price. Lean's self-speedup on `enum_wheels` is 6.7x on 10 cores
  (87.6 s pinned -> 13.0 s default; the parallel run burns ~39% more total CPU
  than the pinned one, 120 s vs 86.5 s user, so user/wall overstates it).
- Many-core, full pipeline: see `RESULTS.md` (128-way MODI runs; whole-pipeline
  Lean 1.3x faster than serial C++, Rust 6.5x).

## Where the single-thread price comes from

`sample` attribution of the Lean binary, single-threaded (top-of-stack, busy
samples only):

| workload      | compute | RC/free | alloc | tlv   |
|:--------------|--------:|--------:|------:|------:|
| combine_rules |   68.4% |   15.6% | 12.7% |  3.3% |
| enum_wheels   |   67.6% |   15.5% | 14.3% |  2.5% |

- The hotspot is the homomorphism BFS itself (`homCoreGo`, specialised at its
  `rootedContainConf`/`neverApply` call sites) plus the `containConf` sweep --
  i.e. the algorithm, not runtime overhead.

- **Trust checks, re-verified on these profiles**: `lean_copy_array` = 0 (no
  copy-on-write => persistent arrays are being mutated in place, no accidental
  O(n²)) and no `lean_box` traffic (the unboxed `OptIdx`/`SmallNatPair`
  encodings, see `FIDELITY.md`, are doing their job).

- The remaining ~30% reference-counting + allocator tax is the price of Lean's
  automatic memory management over manual/ownership models. It used to be ~50%:
  some of the reduction came from *style* changes (below), how the code is
  written affects the Perceus mechanisms.

- `_tlv_get_addr` (~3%) is a macOS thread-local artefact; it does not appear on
  Linux.

## Codegen lessons (measured; they generalise)

- **Proof-carrying hot indexing (measured 2026-07-17).** Swapping
  `homStep`'s eight `!`-indexed reads and writes for proof-carrying ones
  (bounds from the erased `HomIndexSafe` invariant plus the `WFConfig`
  facts) removes every bounds check and panic branch from the BFS loop: the
  specialised `homCoreGo` IR has 7 unchecked `getInternalBorrowed` reads and
  2 unchecked `set` writes, no `get!`/panic paths. Single-thread user-CPU
  A/B against the pre-change binary: enum_wheels d7 faster on every rep,
  medians pre-change 77.98 s vs post-change 75.64 s (~1.03x); combine_rules
  medians pre-change 3.62 s vs post-change 3.59 s;
  outputs byte-identical on both workloads (671 + 5439 files). The
  2026-07-10 `sorry`-backed probe forecast ~1.05x against its older
  baseline; the honest version confirms the direction on the current one.

- **An erased-invariant wrapper type compiles away (measured 2026-07-17).**
  Moving the homomorphism pipeline onto `WFConfig` (a `PseudoConfiguration`
  plus an erased well-formedness/packability proof) leaves the compiled loop
  unchanged: the trivial-structure optimisation represents the wrapper as its
  single relevant field, so the specialised `homCoreGo` IR shows the same
  borrowed parameters and projection chains as before (checked with
  `trace.compiler.ir.result`). The runtime additions are the `wfCheck`
  certifications at object boundaries (`Configuration`/`Rule`/`CartWheel`
  construction, one per combination in `combineEachCartwheel`).
  Single-thread user-CPU A/B against the pre-change binary: combine_rules
  (84 rules, 8200 confs) medians 3.50 vs 3.52 s, enum_wheels d7 medians 77.1
  vs 77.4 s, ranges overlapping; outputs byte-identical (671 combine files,
  5439 enum files).

- **Only self tail-calls seem to compile to loops.** A mutually tail-recursive
  split of a loop is real C calls (no TCO) -- measured 15-25% regression when a
  sweep and its kernel were split into mutually recursive functions.

- **`Id.run do` / `while` lowering is expensive in hot loops.** It compiles via
  `whileM` -- closure body, monadic state threading, per-iteration heartbeat --
  which Perceus cannot analyse cleanly. Rewriting the hottest loop (`homCoreGo`)
  as an explicit tail-recursive function threading its state as arguments
  measured 1.21x on its own. For fixed-size scans, a short-circuiting `Array`
  combinator (`any`/`find?`/`foldl`) achieves the same without manual recursion.

- **One result constructor per iteration eats a buffer-reuse win.** Handing
  scratch buffers back through even a single flat constructor per trial measured
  break-even against per-trial allocation.

- **`ST.Ref` plumbing is free at per-call granularity** (the world token is
  erased; take/set compile to direct calls), so `runST`-scoped ambient scratch
  is the parallel-safe pattern when scratch is ever revisited.

- **Buffer reuse pays only while the buffers never cross a function boundary
  (prototyped, then backed out).** The containment sweep (`containConf`,
  sketched -- `bucket` is the degree-bucket lookup) is three nested loops:

  ```lean
  confs.any fun conf =>                        -- 1: configurations
    bucket.any fun fStar =>                    -- 2: candidate root darts
      guard && rootedContainConf fStar conf    -- 3: runs the BFS (homCoreGo)
  ```

  The prototype fused all three into one self-recursive function: "which
  configuration / which candidate dart / where in the BFS" and the BFS scratch
  buffers (the two index maps and the worklist) all become arguments, and each
  recursive call either advances the BFS, moves to the next candidate, or moves
  to the next configuration. No call ever returns or re-allocates the buffers,
  nothing is allocated per trial: a further ~1.21x. Re-factoring the same design
  readably -- an outer loop owns the buffers and passes them to a
  per-configuration helper that returns them -- measured exactly baseline.
  Reason: most configurations have tiny or empty candidate buckets, so the
  helper boundary is crossed about as often as there are BFS trials, and each
  crossing returns the buffers through a constructor (previous lesson). The win
  is therefore inseparable from the loop fusion -- and since the fused function
  is unacceptable on clarity grounds, the whole design was discarded, never
  landed (see the lever below).

- **Forced inlining can flip borrow inference (and `@[noinline]` can be a
  win).** Inlining a small match-bodied helper (`pushLink`, the BFS's
  conditional push) into the hottest loop duplicated the loop's continuation
  into the match arms and made the borrow inference turn a read-only parameter
  owned -- doubling the loop's reference-count traffic, measured 1.27x slower on
  enum_wheels.

  As an `@[noinline]` call with scalar arguments the loop kept its borrowed
  parameters and a smaller body than before the factoring. Settle such
  questions with `set_option trace.compiler.ir.result true` on a probe
  definition -- count `ctor` allocations, `inc`/`dec`, and borrowed (`@&`)
  parameters.

- **Sharing sometimes beats copying, which beats computing (small sequences).**
  Six byte-identical variants of the wheel-tuple enumeration ranked cleanly:
  `List` cons with structurally shared suffixes -- arrays realised once, at the
  consumer boundary -- was fastest at every degree measured; the block-copy
  shapes (`Array ++` prepend, copy-on-write `set!` buffer) sat a few percent
  behind, memcpy of tagged scalars being near-free; and every per-element
  construction (`Array.ofFn` over div/mod index arithmetic, odometer `push`
  loops) lost by 20-30%, a closure call plus arithmetic per element costing
  several copied elements. The refcount traffic on the shared list tails did not
  offset the win. Pre-sizing with `mkEmpty` and fusing `flatMap` spines measured
  exactly nothing.

## Nested check parallelism and its thread-count sensitivity

- The check drivers are parallel at two levels: `parForEach` over the checked
  cartwheels and, inside each, `combineEachCartwheel`'s candidate sweep as an
  order-preserving `parFlatMap` (one task per candidate). At full thread
  count this removes the per-cartwheel tail floor -- previously a single
  ~440 s (d7) / ~3000 s (d8) cartwheel pinned the stage's wall-clock at any
  concurrency. Measured on a 128-SMT EPYC node: d7 check 1421 -> 929 s, d8
  check 2736 -> 1018 s.
- **Known sensitivity**: at explicitly reduced thread counts on many-core
  nodes, the tens of millions of fine tasks tax Lean's eager task pool --
  spawn/completion/join traffic through the shared queue is ~2 futex
  transitions per task, measured at 96% of syscall time and ~69% of total
  CPU (kernel side) at 32 threads -- costing `check_7triangle` 1014 -> 1975 s
  at x32. Sum-bound small machines pay ~8% (`check_deg7`, 10-core M1). The
  default (all hardware threads) is the winning configuration everywhere
  measured.
- The granularity itself is not the defect: the identical one-combinator
  change in the Rust port (inner `par_iter`) wins uniformly at every thread
  count under rayon's work-stealing (d7 check ALL 406/381/477 ->
  208/211/312 s at x128/x64/x32) -- unstolen work never becomes a scheduled
  task and joins steal instead of sleeping. A work-stealing layer under the
  `par*` combinators is the planned remedy for the Lean side.

## Levers deliberately not pulled

- **Fused zero-alloc BFS + epoch scratch** (the loop-fusion prototype from the
  codegen lessons) -- measured a further ~1.21x on top of the tail-rec rewrite;
  prototyped off-tree and discarded: the 8-line spec-shaped sweep becomes a
  ~130-line 16-argument state machine, the BFS kernel exists twice (drift risk
  against `homCoreGo`, the port's most-audited function), and `isSome` domain
  reads become epoch arithmetic -- fails the mandate for a port already beating
  C++ wall-clock.

- **Caller-provided scratch reuse** -- measured break-even to negative: the
  constructor handback per trial eats the win.

- **SoA `Dart` layout** -- no hotspot to attack: re-profiled, `Dart` reads never
  appear high in either workload.

- **Nested / inner parallelism** -- measured a regression: the outer
  `parForEach` already saturates the cores.

- **Fast-fail degree pre-check** -- formulated, measured, no win; rejected.

- **Proof-carrying hot indexing** -- LANDED (2026-07-17); see the codegen
  lesson above for the mechanism and the measured numbers.

## Reproduce

```sh
# all commands from the repo root
CPP=../computer-checks/build/src/main
RUST=rust_port/target/release/main
LEAN=lean4_port/.lake/build/bin/main
R=rust_port/discharging-rules/R
C=rust_port/reducible-configurations/D

# gate (full corpus, 3-way byte-diff)
( cd lean4_port && ./p7_differential.sh 0 )

# combine_rules, single-thread
hyperfine --warmup 2 --runs 6 \
  "$CPP --combine_rules -R $R -C $C -o /tmp/o" \
  "env RAYON_NUM_THREADS=1 $RUST --combine_rules -R $R -C $C -o /tmp/o" \
  "env LEAN_NUM_THREADS=1 $LEAN --combine_rules -R $R -C $C -o /tmp/o"

# enum_wheels d7 (generate nb once per port via combine_rules -o nb, then)
hyperfine --runs 3 \
  "env LEAN_NUM_THREADS=1 $LEAN --enum_wheels -d 7 -R $R -C $C -S nb -o /tmp/d7"

# profile: start the pinned run in the background, sample it mid-run
# short workload (combine_rules, ~5 s): sample right away
env LEAN_NUM_THREADS=1 $LEAN --combine_rules -R $R -C $C -o /tmp/o & PID=$!
sample $PID 4 -f /tmp/prof_combine.txt
wait $PID

# long workload (enum_wheels d7, ~90 s): skip startup/parsing, land mid-BFS
env LEAN_NUM_THREADS=1 $LEAN --enum_wheels -d 7 -R $R -C $C -S nb \
  -o /tmp/d7 & PID=$!
sleep 20
sample $PID 30 -f /tmp/prof_enum.txt
wait $PID

# read the "Sort by top of stack" section at the end of the output; ignore
# the parked worker threads (__ulock_wait/kevent/__psynch_cvwait)
```
