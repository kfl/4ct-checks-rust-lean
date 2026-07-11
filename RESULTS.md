# Results: Rust and Lean ports of the near-linear 4CT computer checks

The near-linear 4CT computer-check pipeline has been **independently re-implemented in
Rust and Lean 4**, and both ports are verified **byte-identical to the C++ original *and*
to the paper's published counts** across the complete A.3-A.6 run on the real data.

This is two independent results at once:

- **Correctness.** Three independent implementations (C++, Rust, Lean), in three languages,
  produce byte-for-byte identical output at every file-producing stage, and every count
  matches the values published in the paper. A bug shared by all three would have to be a
  *shared* bug surviving three separate translations *and* coincidentally matching the
  published numbers -- vanishingly unlikely.
- **Performance.** The ports parallelize the stages the C++ original runs serially, making
  Rust the fastest implementation end-to-end (up to **50x faster** than C++ where it
  matters) and Lean competitive at high degree, while staying byte-identical.

Run on MODI (University of Copenhagen HPC), 128-core / 240 GB nodes, 2026-06-26.
For *how* to build and run, see [`modi/README.md`](modi/README.md).

---

## 1. What was verified

The pipeline (paper Lemmas A.1-A.6), each stage run for all three ports and compared:

| Lemma | stage | what it computes |
|---|---|---|
| A.1 | `combine_rules` (empty configs) | the combined rule set `R*` |
| A.2 | `combine_rules` (real configs)  | `R*` minus rules blocked by a reducible configuration |
| A.3 | `enum_wheels` (`enumPossibleBadWheels`) | candidate "bad" wheels, per centre degree 7-11 |
| A.3 | `enum_cartwheels` | the bad cartwheels with tail ranges |
| A.4 | `check_deg8` | every degree-8-centred bad cartwheel is dischargeable |
| A.5 | `check_7triangle` | every 7-triangle bad cartwheel is dischargeable |
| A.6 | `check_deg7` | every degree-7-centred bad cartwheel is dischargeable |

**Verification method.** A 3-way differential ([`modi/full_differential.sh`](modi/full_differential.sh)),
run per centre-degree as a SLURM job array ([`modi/full_array.sh`](modi/full_array.sh)):

- **File-producing stages** (`combine_rules`, `enum_wheels`, `enum_cartwheels`) -- each port's
  output directory is byte-compared (`diff -r`) against C++. Any mismatch stops the run.
- **Published-count assertions** -- each stage's object count is checked against the paper's
  value (not just port-vs-port agreement), catching a systematic error all three might share.
- **Assertion-only checks** (`check_deg7/deg8/7triangle`) -- these produce *no* output;
  "success" is "no assertion fires" (the C++ uses live `assert()`, the ports use
  `assert!`/`panic!`/`proofAssert` -- never compiled out). They are compared by **exit-code
  agreement**: all three ports must agree (all pass, or all fail identically). Agreement is
  meaningful even on a partial slice.

All inputs are staged on node-local tmpfs (`/dev/shm`) so timings reflect compute, not the
shared filesystem.

---

## 2. Correctness results -- every count matches

All five degrees **PASS**: at every stage, `rust == C++` and `lean == C++` byte-for-byte,
and every count equals the published value.

| metric | published | C++ = Rust = Lean |
|---|---|---|
| A.1 `|R*|` (empty configs) | 1832 | **1832** ✓ |
| A.2 `|R*-D|` (real configs) | 671 | **671** ✓ |
| A.3 wheels, centre degree 7 | 5439 | **5439** ✓ |
| A.3 wheels, centre degree 8 | 6790 | **6790** ✓ |
| A.3 wheels, centre degree 9 | 3285 | **3285** ✓ |
| A.3 wheels, centre degree 10 | 626 | **626** ✓ |
| A.3 wheels, centre degree 11 | 8 | **8** ✓ |
| A.3 bad cartwheels, centre degree 7 | 9366 | **9366** ✓ |
| A.3 bad cartwheels, centre degree 8 | 728 | **728** ✓ |
| A.3 bad cartwheels, degrees 9-11 | (none) | **0** ✓ |
| A.4/A.5/A.6 checks | all pass | all three exit 0 ✓ |

(The paper also reports max combined-rule charge 8 for `R*` and 5 for `R*-D`; the
byte-identical rule sets realize those.)

```
full-summary.txt:
  degree 7   exit=0  PASS
  degree 8   exit=0  PASS
  degree 9   exit=0  PASS
  degree 10  exit=0  PASS
  degree 11  exit=0  PASS
```

---

## 3. Performance results

Per-port wall-clock (seconds), 128-way parallel, one degree per row-block. `enum_cartwheels`
("cart") is parallelized across processes; the other stages are single-process (internally
parallel where the port supports it). Ratios are vs C++.

### Per degree

```
degree 7 (5439 wheels, 9366 bad cartwheels)
   stage         C++      Rust      Lean   Rust/C++  Lean/C++
   combine      4.48      1.06      3.95     0.24x     0.88x
   wheels      96.26      1.60     17.62     0.02x     0.18x
   cart       267.45    325.39   1368.28     1.22x     5.12x
   check      151.75    140.61    708.60     0.93x     4.67x
   TOTAL      519.94    468.66   2098.45     0.90x     4.04x

degree 8 (6790 wheels, 728 bad cartwheels)
   combine      4.54      1.06      4.30     0.23x     0.95x
   wheels     120.85      2.29     13.08     0.02x     0.11x
   cart       305.86    386.40   1454.87     1.26x     4.76x
   check      301.96    298.14   1976.59     0.99x     6.55x
   TOTAL      733.21    687.89   3448.84     0.94x     4.70x

degree 9 (3285 wheels, 0 bad cartwheels)
   combine      4.53      1.07      4.27     0.24x     0.94x
   wheels     282.09      5.75     40.18     0.02x     0.14x
   cart        81.20    116.83    383.54     1.44x     4.72x
   check        1.04      0.39      0.89     0.38x     0.86x
   TOTAL      368.86    124.04    428.88     0.34x     1.16x

degree 10 (626 wheels, 0 bad cartwheels)
   combine      4.55      1.08      3.87     0.24x     0.85x
   wheels    1329.10     24.93    209.46     0.02x     0.16x
   cart         8.45     15.48     33.63     1.83x     3.98x
   check        1.05      0.37      0.88     0.35x     0.84x
   TOTAL     1343.15     41.86    247.84     0.03x     0.18x

degree 11 (8 wheels, 0 bad cartwheels)
   combine      4.58      1.05      4.32     0.23x     0.94x
   wheels    6538.82    127.89   1081.81     0.02x     0.17x
   cart         0.68      0.62      1.70     0.91x     2.50x
   check        1.04      0.41      0.82     0.39x     0.79x
   TOTAL     6545.12    129.97   1088.65     0.02x     0.17x
```

### End-to-end summary

| deg | wheels | bad cw | C++ TOTAL (s) | Rust/C++ | Lean/C++ |
|---|---|---|---|---|---|
| 7 | 5439 | 9366 | 519.94 | 0.90x | 4.04x |
| 8 | 6790 | 728 | 733.21 | 0.94x | 4.70x |
| 9 | 3285 | 0 | 368.86 | 0.34x | 1.16x |
| 10 | 626 | 0 | 1343.15 | 0.03x | 0.18x |
| 11 | 8 | 0 | 6545.12 | **0.02x** | **0.17x** |
| **7-11** | **16148** | **10094** | **9510.28** | **0.15x** | **0.77x** |

**Rust is the fastest implementation end-to-end at every degree** (≤ C++), increasingly so as
degree rises. At degree 11, Rust is **50x faster** than C++ and Lean **5.9x** faster.

### Total across all five degrees

Summing each port's wall-clock over all degrees -- how long that port alone would take to run
the whole verification (all stages, degrees 7-11):

| port | total | vs C++ |
|---|---|---|
| C++ | 9510 s (≈ 2 h 39 m) | 1.0x |
| **Rust** | **1452 s (≈ 24 m)** | **6.5x faster** (0.15x) |
| Lean | 7313 s (≈ 2 h 02 m) | 1.3x faster (0.77x) |

So **Rust runs the entire pipeline ~6.5x faster than C++ on MODI**. But this total is
**dominated by degree 11**: C++'s d11 alone (6545 s) is 69% of C++'s entire total, almost all
of it the single serial `enum_wheels` pass (6539 s = 1 h 49 m). So the 6.5x is *not* a uniform
per-operation speedup -- it is overwhelmingly "the ports parallelize the one stage the C++
original runs serially, and at high degree that stage is enormous." On the stages that are
compute-bound and similarly parallel in all ports (`cart` + `check`), Rust is par-to-slightly-
behind C++ (it loses the per-process `cart` stage, ties `check`).

---

## 4. Performance analysis -- two parallelism axes

The ranking flips stage-to-stage because the stages parallelize differently:

**`enum_wheels` -- internal parallelism; C++ is serial.** A single invocation. The Rust and
Lean ports parallelize it internally (rayon `par_iter` / Lean `parMap`); the C++ original runs
it serially (it got parallelism only by running degrees concurrently at the shell level). The
search space *explodes* with degree even though few wheels survive:

| deg | C++ `enum_wheels` | Rust | Lean |
|---|---|---|---|
| 7 | 96 s | 1.6 s | 17.6 s |
| 8 | 121 s | 2.3 s | 13.1 s |
| 9 | 282 s | 5.8 s | 40.2 s |
| 10 | 1329 s | 24.9 s | 209 s |
| 11 | **6539 s** (1 h 49 m) | **128 s** | 1082 s |

This single serial stage is what makes C++ slow at high degree, and it is the dominant reason
Rust/Lean win the pipeline. It is also the strongest argument for the ports' design choice to
parallelize the driver steps.

**`enum_cartwheels` -- external parallelism; per-process overhead.** Run as one process *per
wheel* (`xargs -P 128`), matching the reference. The cost is per-invocation overhead -- each
process re-reads and re-parses the whole configuration database (8200 files, 19754
configurations). With the per-process thread pool capped (`RAYON_NUM_THREADS=1`, see sec 5),
Rust *beats* C++ here (0.90x); Lean stays ~4.7x (per-process Lean startup + compute). An
*internal* variant (one process, `par_iter` over wheels, configs loaded once) was tested and
**does not help at 128 cores** -- see sec 5.

**`check` -- internal parallelism in *all three* ports.** All three parallelize over cartwheels
(C++ `boost::asio::thread_pool`, Rust `par_iter`, Lean `parForEach`), so Rust ≈ C++. Lean is
4.7-6.5x only on per-element compute (its `homCore` homomorphism hot path), not concurrency.
`check` time scales with the *bad-cartwheel* count, so it is ~0 for degrees 9-11.

**`combine_rules` -- internal parallelism.** Rust ~0.24x C++ (mimalloc + parallel parse), Lean
~0.9x.

---

## 5. Measurement methodology and caveats

The performance numbers were hard-won; several intuitive measurements were misleading. Recorded
here so the methodology is reproducible and the pitfalls are not re-hit.

- **`sinfo`/`scontrol` `CPULoad` is unreliable on MODI.** It reported byte-identical values
  (`0.04`/`0.02`) across separate jobs over an hour while jobs were demonstrably computing.
  Do not diagnose CPU-vs-I/O with it; use the harness's own per-stage `done: N wheels in Xs`
  timing instead. (`sstat` is also unavailable -- the accounting plugin isn't configured.)
- **Stage data on node-local tmpfs, not NFS.** Running the per-wheel `enum_cartwheels` against
  the NFS-mounted data has every one of the 128 processes re-open ~8200 files, saturating NFS
  metadata -- the job crawls with the CPUs idle. Staging the data on `/dev/shm` first (~1.75x
  here) is essential.
- **Cap threads in the external stage.** Rust/Lean parallelize config loading internally, so
  128 concurrent per-wheel processes each spawn a full thread pool -> ~16k threads oversubscribe
  128 cores. Run the per-wheel stage with `RAYON_NUM_THREADS=1` / `LEAN_NUM_THREADS=1` (the
  external parallelism comes from `xargs`, 1 thread x 128 procs = clean 1:1). This alone takes
  Rust's `cart` from 1.22x to **0.90x** C++ -- it is the whole fix for Rust on that stage.
- **Process startup is *not* the per-wheel bottleneck.** Measured ~2 ms/spawn; the per-wheel
  cost is the redundant config re-parse (CPU + I/O), not exec/link.

**External-vs-internal cart experiment -- and a scale-dependence trap.** A one-off experiment
compared the external per-wheel model against an *internal* variant (load configs once, then
`par_iter`/`parForEach` over all wheels in one process -- byte-identical output, verified). The
question was whether avoiding the redundant per-wheel config load wins. **The answer depends on
the core count**, which is why it had to be measured at target scale:

| | external (`=1`) | internal | winner |
|---|---|---|---|
| **10 cores**, 500 wheels (Rust) | 32.1 s | **17.8 s** | internal, ~1.8x |
| **128 cores**, 5439 wheels (Rust) | **235 s** (0.90x C++) | 270 s (1.03x) | external |
| **128 cores**, 5439 wheels (Lean) | **1232 s** (4.71x) | 1328 s (5.07x) | external |

At 10 cores internal wins big -- the `sys`-time collapse (config loaded once, not 500x) shows
why. But at **128 cores internal *loses*** for both ports: the workload is allocation-heavy (the
`homCore` hotspot), so 128 threads sharing one address space contend on the allocator and memory
bandwidth (and cross-socket NUMA), whereas 128 independent *processes* each get a NUMA-local,
contention-free working set. At low core counts the saved config-reloads dominate; at high core
counts the contention dominates and outweighs them. **The intuitive (and 10-core-confirmed)
"internal wins" conclusion is wrong at the scale that matters.** So the per-process external
model -- with threads capped -- is the right choice for `cart`; internal parallelism is not. (The
internal variant and its benchmark were removed after this finding was recorded; the chosen
`cart` path is per-process external with `RAYON_NUM_THREADS=1`/`LEAN_NUM_THREADS=1`.)

---

## 6. Reproducing

The differential and benchmark scripts live in [`modi/`](modi/); see [`modi/README.md`](modi/README.md)
for building the three binaries (the C++ reference ships as a static glibc-only binary built via
`modi/Dockerfile`) and running on a Linux HPC node. In brief:

```
# correctness: all degrees, checkpointing job array
cp ~/erda_mount/full_array.sh ~/modi_mount/ && cd ~/modi_mount && sbatch full_array.sh
cat ~/modi_mount/full-summary.txt          # one PASS/FAIL line per degree

# one degree, with the per-stage byte-diffs, paper-count asserts, and timing table
bash modi/full_differential.sh 7
```
