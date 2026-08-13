# Results: Rust and Lean ports of the near-linear 4CT computer checks

The near-linear 4CT computer-check pipeline has been independently
re-implemented in Rust and Lean 4. Across paper Lemmas A.2-A.6, every
file-producing stage is byte-identical to the C++ original, every published
count matches, and every assertion-only check passes. Lemma A.1 is covered by a
separate `combine_rules` differential.

This gives two results:

- **Differential correctness evidence.** The C++, Rust, and Lean
  implementations produce byte-for-byte identical output at every
  file-producing stage, and every count matches the values published in the
  paper. The separately written ports reduce the risk of port-specific
  transcription errors. This comparison does not exclude a defect shared by
  the paper's pseudocode, the reference implementation, and both ports.

- **Performance.** The ports parallelise the stages the C++ original runs
  serially. On the nodes described below, that makes Rust the fastest of the
  three end-to-end -- 8.7x faster than C++ over the whole pipeline, and at or
  below C++'s wall-clock on every stage of every degree -- and Lean 2.6x
  faster than C++ overall. These ratios are properties of this hardware and
  dispatch setup, not per-operation speedups; Sec. 3 and 4 give the breakdown.

Run on MODI (University of Copenhagen, SCIENCE HPC centre). Each degree used one
node with two AMD EPYC 7501 processors: 64 physical cores, 128 SMT hardware
threads, and 256 GB RAM. Measured at commit `9cf81f2` (degrees 8-11 from SLURM
job array 1393, degree 7 from array 1396); the
raw per-degree logs for Lemmas A.2-A.6 are archived in
[`modi/runs/`](modi/runs/). The separate Lemma A.1 run is not archived there.
For *how* to build and run, see
[`modi/README.md`](modi/README.md).

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

**Verification method.** Two 3-way differentials: `modi/run_p7.sh 0` checks
Lemma A.1 (and repeats Lemma A.2), while
[`modi/full_differential.sh`](modi/full_differential.sh) checks Lemmas A.2-A.6
per centre degree as a SLURM job array
([`modi/full_array.sh`](modi/full_array.sh)):

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

Per-port wall-clock (seconds), 128-way parallel (one worker per SMT hardware
thread on a 64-physical-core node), one degree per row-block. `enum_cartwheels`
("cart") is parallelised across processes; the other stages are single-process
(internally parallel where the port supports it). Ratios are vs C++.

### Per degree

```
degree 7 (5439 wheels, 9366 bad cartwheels)
   stage         C++      Rust      Lean   Rust/C++  Lean/C++
   combine      6.87      0.80      2.66     0.12x     0.39x
   wheels      92.11      1.32      4.74     0.01x     0.05x
   cart       320.50    240.51    699.42     0.75x     2.18x
   check      496.95    219.37    591.34     0.44x     1.19x
   TOTAL      916.43    462.00   1298.16     0.50x     1.42x

degree 8 (6790 wheels, 728 bad cartwheels)
   combine      6.95      0.82      2.63     0.12x     0.38x
   wheels     113.11      2.03      7.35     0.02x     0.06x
   cart       319.09    265.77    768.65     0.83x     2.41x
   check      749.92    228.73   1010.59     0.31x     1.35x
   TOTAL     1189.07    497.35   1789.22     0.42x     1.50x

degree 9 (3285 wheels, 0 bad cartwheels)
   combine      6.98      0.81      2.66     0.12x     0.38x
   wheels     276.28      5.24     22.61     0.02x     0.08x
   cart        82.99     66.10    191.73     0.80x     2.31x
   check        0.93      0.32      0.90     0.34x     0.97x
   TOTAL      367.18     72.47    217.90     0.20x     0.59x

degree 10 (626 wheels, 0 bad cartwheels)
   combine      6.91      0.81      2.60     0.12x     0.38x
   wheels    1291.85     24.67    112.77     0.02x     0.09x
   cart         8.58      8.05     18.68     0.94x     2.18x
   check        0.94      0.32      0.91     0.34x     0.97x
   TOTAL     1308.28     33.85    134.96     0.03x     0.10x

degree 11 (8 wheels, 0 bad cartwheels)
   combine      6.97      0.79      2.56     0.11x     0.37x
   wheels    6535.98    120.97    569.94     0.02x     0.09x
   cart         0.63      0.47      1.33     0.75x     2.11x
   check        0.93      0.32      0.91     0.34x     0.98x
   TOTAL     6544.51    122.55    574.74     0.02x     0.09x
```

### End-to-end summary

| deg      | wheels    | bad cw    | C++ TOTAL (s) | Rust/C++  | Lean/C++  |
| -------- | --------- | --------- | ------------- | --------- | --------- |
| 7        | 5439      | 9366      | 916.43        | 0.50x     | 1.42x     |
| 8        | 6790      | 728       | 1189.07       | 0.42x     | 1.50x     |
| 9        | 3285      | 0         | 367.18        | 0.20x     | 0.59x     |
| 10       | 626       | 0         | 1308.28       | 0.03x     | 0.10x     |
| 11       | 8         | 0         | 6544.51       | **0.02x** | **0.09x** |
| **7-11** | **16148** | **10094** | **10325.47**  | **0.12x** | **0.39x** |

Rust's total is at or below C++'s at every degree, increasingly so as degree
rises: from 0.50x at degree 7 to 0.02x (53x faster, on this setup) at degree
11, where the C++ total is almost entirely its serial `enum_wheels` pass.
Lean's total is below C++'s from degree 9 upward.

### Total across all five degrees

Summing each port's wall-clock over all degrees -- how long that port alone
would take to run the whole verification (all stages, degrees 7-11):

| port     | total                | vs C++                  |
| -------- | -------------------- | ----------------------- |
| C++      | 10325 s (≈ 2 h 52 m) | 1.0x                    |
| **Rust** | **1188 s (≈ 20 m)**  | **8.7x faster** (0.12x) |
| Lean     | 4015 s (≈ 1 h 07 m)  | 2.6x faster (0.39x)     |

The totals are dominated by degree 11: C++'s d11 alone (6545 s) is 63% of its
entire total, almost all of it the single serial `enum_wheels` pass (6536 s =
1 h 49 m). The end-to-end speedups are therefore not uniform per-operation
speedups -- they mostly measure that the ports parallelise the one stage the
C++ original runs serially, on a node with 128 hardware threads to spread it
over. Across `cart` and the non-trivial degree-7/8 `check` stages, where all
three ports exploit comparable parallelism, Rust runs at 0.31-0.94x of C++
and Lean at 1.19-2.41x.

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
| 7   | 92 s                  | 1.3 s     | 4.7 s |
| 8   | 113 s                 | 2.0 s     | 7.4 s |
| 9   | 276 s                 | 5.2 s     | 23 s  |
| 10  | 1292 s                | 24.7 s    | 113 s |
| 11  | **6536 s** (1 h 49 m) | **121 s** | 570 s |

This single serial stage is what makes C++ slow at high degree, and it
accounts for most of the ports' end-to-end advantage. It is also the main
payoff of the ports' design choice to parallelise the driver steps.

**`enum_cartwheels` -- external parallelism.** Run as one process *per wheel*
(`xargs -P 128`), matching the reference. With the per-process thread pools
capped (`RAYON_NUM_THREADS=1` / `LEAN_NUM_THREADS=1`, see Sec. 5), Rust runs at
0.75-0.94x of C++ and Lean at 2.11-2.41x. An *internal* variant (one process,
`par_iter` over wheels, configurations loaded once, byte-identical output) was
slower at 128 threads -- Rust 235 -> 270 s, Lean 1232 -> 1328 s -- despite
avoiding the repeated loads. Allocator, memory-bandwidth and NUMA contention
are plausible causes, but this experiment did not isolate them. In the
measured Rust case at 10 cores, the internal variant was ~1.8x faster.

**`check` -- internal parallelism in *all three* ports.** All three parallelise
over cartwheels (C++ `boost::asio::thread_pool`, Rust `par_iter`, Lean
`parForEach`), and both new ports also parallelise the candidate sweep within
a cartwheel, which is where the phase's time concentrates: at degrees 7 and
8, Rust runs at 0.31-0.44x of C++ and Lean at 1.19-1.35x. `check` time scales
with the *bad-cartwheel* count, so it is ~0 for degrees 9-11.

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

- **Toolchains.** rustc 1.97.1, Lean 4.33.0, and MODI's stock Apptainer image
  `hpc-notebook-25.11.5.sif`. The C++ reference is the static binary built from
  `computer-checks` @ `6cb8566` (see `modi/Dockerfile`).

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
