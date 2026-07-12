# Results: Rust and Lean ports of the near-linear 4CT computer checks

The near-linear 4CT computer-check pipeline has been independently
re-implemented in Rust and Lean 4, and both ports are verified
byte-identical to the C++ original and to the paper's published counts
across the complete A.3-A.6 run on the real data.

This is two independent results:

- **Correctness.** Three independent implementations (C++, Rust, Lean), in three
  languages, produce byte-for-byte identical output at every file-producing
  stage, and every count matches the values published in the paper. A bug
  shared by all three would have to survive three separate translations and
  coincidentally match the published numbers.

- **Performance.** The ports parallelise the stages the C++ original runs
  serially. On the nodes described below, that makes Rust the fastest of the
  three end-to-end -- 5.8x faster than C++ over the whole pipeline, and at or
  below C++'s wall-clock on every stage of every degree -- and Lean 1.5x
  faster than C++ overall. These ratios are properties of this hardware and
  dispatch setup, not per-operation speedups; Sec. 3 and 4 give the breakdown.

Run on MODI (University of Copenhagen, SCIENCE HPC centre): 2 x AMD EPYC 7501
nodes -- 64 physical cores presenting 128 SMT hardware threads -- with 256 GB
RAM. Measured at commit `0d05d5e` (SLURM job array 229); the raw per-degree
logs are archived in [`modi/runs/`](modi/runs/). For *how* to build and run,
see [`modi/README.md`](modi/README.md).

---

## 1. What was verified

The pipeline (paper Lemmas A.1-A.6), each stage run for all three ports and
compared:

| Lemma | stage                                   | what it computes                                      |
|-------|-----------------------------------------|-------------------------------------------------------|
| A.1   | `combine_rules` (empty configs)         | the combined rule set `R*`                            |
| A.2   | `combine_rules` (real configs)          | `R*` minus rules blocked by a reducible configuration |
| A.3   | `enum_wheels` (`enumPossibleBadWheels`) | candidate "bad" wheels, per centre degree 7-11        |
| A.3   | `enum_cartwheels`                       | the bad cartwheels with tail ranges                   |
| A.4   | `check_deg8`                            | every degree-8-centred bad cartwheel is dischargeable |
| A.5   | `check_7triangle`                       | every 7-triangle bad cartwheel is dischargeable       |
| A.6   | `check_deg7`                            | every degree-7-centred bad cartwheel is dischargeable |

**Verification method.** A 3-way differential
([`modi/full_differential.sh`](modi/full_differential.sh)), run per
centre-degree as a SLURM job array ([`modi/full_array.sh`](modi/full_array.sh)):

- **File-producing stages** (`combine_rules`, `enum_wheels`, `enum_cartwheels`)
  -- each port's output directory is byte-compared (`diff -r`) against C++. Any
  mismatch stops the run.
- **Published-count assertions** -- each stage's object count is checked against
  the paper's value (not just port-vs-port agreement), catching a systematic
  error all three might share.
- **Assertion-only checks** (`check_deg7/deg8/7triangle`) -- these produce *no*
  output; "success" is "no assertion fires" (the C++ uses live `assert()`, the
  ports use `assert!`/`panic!`/`proofAssert` -- never compiled out). They are
  compared by exit-code agreement: all three ports must agree (all pass, or
  all fail identically). Agreement is meaningful even on a partial slice.

All inputs are staged on node-local tmpfs (`/dev/shm`) so timings reflect
compute, not the shared filesystem.

---

## 2. Correctness results -- every count matches

All five degrees pass: at every stage, `rust == C++` and `lean == C++`
byte-for-byte, and every count equals the published value.

| metric                              | published | C++ = Rust = Lean  |
| ----------------------------------- | --------- | ------------------ |
| A.1 `#R*` (empty configs)           | 1832      | **1832** ✓         |
| A.2 `#(R*-D)` (real configs)        | 671       | **671** ✓          |
| A.3 wheels, centre degree 7         | 5439      | **5439** ✓         |
| A.3 wheels, centre degree 8         | 6790      | **6790** ✓         |
| A.3 wheels, centre degree 9         | 3285      | **3285** ✓         |
| A.3 wheels, centre degree 10        | 626       | **626** ✓          |
| A.3 wheels, centre degree 11        | 8         | **8** ✓            |
| A.3 bad cartwheels, centre degree 7 | 9366      | **9366** ✓         |
| A.3 bad cartwheels, centre degree 8 | 728       | **728** ✓          |
| A.3 bad cartwheels, degrees 9-11    | (none)    | **0** ✓            |
| A.4/A.5/A.6 checks                  | all pass  | all three exit 0 ✓ |

(The paper also reports max combined-rule charge 8 for `R*` and 5 for `R*-D`;
the byte-identical rule sets realise those.)

---

## 3. Performance results

Per-port wall-clock (seconds), 128-way parallel (one worker per SMT thread;
the nodes have 64 physical cores), one degree per row-block. `enum_cartwheels`
("cart") is parallelised across processes; the other stages are single-process
(internally parallel where the port supports it). Ratios are vs C++.

### Per degree

```
degree 7 (5439 wheels, 9366 bad cartwheels)
   stage         C++      Rust      Lean   Rust/C++  Lean/C++
   combine      6.95      0.84      2.74     0.12x     0.39x
   wheels      91.52      1.36      5.09     0.01x     0.06x
   cart       305.69    248.73    826.87     0.81x     2.70x
   check      495.94    408.90   1455.01     0.82x     2.93x
   TOTAL      900.10    659.83   2289.71     0.73x     2.54x

degree 8 (6790 wheels, 728 bad cartwheels)
   combine      6.91      0.84      2.59     0.12x     0.37x
   wheels     114.66      2.12      7.95     0.02x     0.07x
   cart       321.07    275.52    885.12     0.86x     2.76x
   check      750.18    615.41   2921.07     0.82x     3.89x
   TOTAL     1192.82    893.89   3816.73     0.75x     3.20x

degree 9 (3285 wheels, 0 bad cartwheels)
   combine      6.88      0.84      2.68     0.12x     0.39x
   wheels     280.84      5.27     23.68     0.02x     0.08x
   cart        86.50     64.25    206.06     0.74x     2.38x
   check        0.92      0.32      0.85     0.35x     0.92x
   TOTAL      375.14     70.68    233.27     0.19x     0.62x

degree 10 (626 wheels, 0 bad cartwheels)
   combine      6.89      0.84      2.80     0.12x     0.41x
   wheels    1281.59     25.80    118.25     0.02x     0.09x
   cart         8.61      8.14     20.51     0.95x     2.38x
   check        0.92      0.32      0.84     0.35x     0.91x
   TOTAL     1298.01     35.10    142.40     0.03x     0.11x

degree 11 (8 wheels, 0 bad cartwheels)
   combine      6.94      0.83      2.59     0.12x     0.37x
   wheels    6537.95    125.76    623.77     0.02x     0.10x
   cart         0.64      0.48      1.33     0.75x     2.08x
   check        0.93      0.32      0.85     0.34x     0.91x
   TOTAL     6546.46    127.39    628.54     0.02x     0.10x
```

### End-to-end summary

| deg      | wheels    | bad cw    | C++ TOTAL (s) | Rust/C++  | Lean/C++  |
| -------- | --------- | --------- | ------------- | --------- | --------- |
| 7        | 5439      | 9366      | 900.10        | 0.73x     | 2.54x     |
| 8        | 6790      | 728       | 1192.82       | 0.75x     | 3.20x     |
| 9        | 3285      | 0         | 375.14        | 0.19x     | 0.62x     |
| 10       | 626       | 0         | 1298.01       | 0.03x     | 0.11x     |
| 11       | 8         | 0         | 6546.46       | **0.02x** | **0.10x** |
| **7-11** | **16148** | **10094** | **10312.53**  | **0.17x** | **0.69x** |

Rust's total is at or below C++'s at every degree, increasingly so as degree
rises: from 0.73x at degree 7 to 0.02x (51x faster, on this setup) at degree
11, where the C++ total is almost entirely its serial `enum_wheels` pass.
Lean's total is below C++'s from degree 9 upward.

### Total across all five degrees

Summing each port's wall-clock over all degrees -- how long that port alone
would take to run the whole verification (all stages, degrees 7-11):

| port     | total                | vs C++                  |
| -------- | -------------------- | ----------------------- |
| C++      | 10313 s (≈ 2 h 52 m) | 1.0x                    |
| **Rust** | **1787 s (≈ 30 m)**  | **5.8x faster** (0.17x) |
| Lean     | 7111 s (≈ 1 h 59 m)  | 1.5x faster (0.69x)     |

The totals are dominated by degree 11: C++'s d11 alone (6546 s) is 63% of its
entire total, almost all of it the single serial `enum_wheels` pass (6538 s =
1 h 49 m). The end-to-end speedups are therefore not uniform per-operation
speedups -- they mostly measure that the ports parallelise the one stage the
C++ original runs serially, on a node with 128 hardware threads to spread it
over. On the stages that are compute-bound and similarly parallel in all
ports (`cart` + `check`), Rust runs at 0.74-0.95x of C++ and Lean at
2.1-3.9x.

---

## 4. Performance analysis -- two parallelism axes

The ranking flips stage-to-stage because the stages parallelise differently:

**`enum_wheels` -- internal parallelism; C++ is serial.** A single invocation.
The Rust and Lean ports parallelise it internally (rayon `par_iter` / Lean
`parMap`); the C++ original runs it serially (it got parallelism only by running
degrees concurrently at the shell level). The search space grows steeply with
degree even though few wheels survive:

| deg | C++ `enum_wheels`     | Rust      | Lean  |
| --- | --------------------- | --------- | ----- |
| 7   | 92 s                  | 1.4 s     | 5.1 s |
| 8   | 115 s                 | 2.1 s     | 8.0 s |
| 9   | 281 s                 | 5.3 s     | 24 s  |
| 10  | 1282 s                | 25.8 s    | 118 s |
| 11  | **6538 s** (1 h 49 m) | **126 s** | 624 s |

This single serial stage is what makes C++ slow at high degree, and it
accounts for most of the ports' end-to-end advantage. It is also the main
payoff of the ports' design choice to parallelise the driver steps.

**`enum_cartwheels` -- external parallelism; per-process overhead.** Run as one
process *per wheel* (`xargs -P 128`), matching the reference. The cost is
per-invocation overhead -- each process re-reads and re-parses the whole
configuration database (8200 files, 19754 configurations). With the per-process
thread pool capped (`RAYON_NUM_THREADS=1`, see sec 5), Rust runs at
0.74-0.95x of C++; Lean is 2.1-2.8x (per-process Lean startup + the
reference-counted BFS inner loop). An *internal* variant (one process,
`par_iter` over wheels, configs loaded once) was tested and does not help at
this scale: the workload is allocation-heavy, so 128 threads sharing one
address space contend on the allocator and memory bandwidth, whereas 128
independent processes each get a NUMA-local working set.

**`check` -- internal parallelism in *all three* ports.** All three parallelise
over cartwheels (C++ `boost::asio::thread_pool`, Rust `par_iter`, Lean
`parForEach`), so Rust ≈ C++ (0.82x). Lean is 2.9-3.9x only on per-element
compute (its `homCoreGo` homomorphism hot path), not concurrency. `check` time
scales with the *bad-cartwheel* count, so it is ~0 for degrees 9-11.

**`combine_rules` -- internal parallelism.** Rust ~0.12x C++ (mimalloc +
parallel parse), Lean ~0.4x.

---

## 5. Measurement methodology and caveats

Recorded here so the methodology is reproducible and the pitfalls are not
re-hit.

- **`sinfo`/`scontrol` `CPULoad` is unreliable on MODI.** It reported
  byte-identical values (`0.04`/`0.02`) across separate jobs over an hour while
  jobs were demonstrably computing. Do not diagnose CPU-vs-I/O with it; use the
  harness's own per-stage `done: N wheels in Xs` timing instead. (`sstat` is
  also unavailable -- the accounting plugin isn't configured.)

- **Stage data on node-local tmpfs, not NFS.** Running the per-wheel
  `enum_cartwheels` against the NFS-mounted data has every one of the 128
  processes re-open ~8200 files, saturating NFS metadata -- the job crawls with
  the CPUs idle. Staging the data on `/dev/shm` first gave better data.

- **Cap threads in the external stage.** The Rust and Lean binaries size
  their internal thread pools to all visible CPUs, so each of the 128
  concurrent per-wheel processes would start 128 threads of its own --
  ~16k threads oversubscribing 128 hardware threads. The per-wheel stage
  therefore sets `RAYON_NUM_THREADS=1` / `LEAN_NUM_THREADS=1`, leaving the
  `xargs -P 128` process dispatch as the only source of parallelism
  (128 processes x 1 thread).

- **Process startup is *not* the per-wheel bottleneck.** Measured ~2 ms/spawn;
  the per-wheel cost is the redundant config re-parse (CPU + I/O), not
  exec/link.

---

## 6. Reproducing

The differential and benchmark scripts live in [`modi/`](modi/); see
[`modi/README.md`](modi/README.md) for building the three binaries (the C++
reference ships as a static glibc-only binary built via `modi/Dockerfile`) and
running on a Linux HPC node. In brief:

```
# one-shot setup (clone repos + data, stage the C++ oracle, build both ports)
sh ~/erda_mount/modi_setup.sh

# correctness: all degrees, checkpointing job array
cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/full_array.sh
cat ~/modi_mount/full-summary.txt          # one PASS/FAIL line per degree

# one degree, with the per-stage byte-diffs, paper-count asserts, and timing table
bash modi/full_differential.sh 7
```
