# Verification run logs

Raw output of the full A.3-A.6 differential on MODI (one 64-core /
128-SMT-thread node per degree). Two runs are archived, named by SLURM job
array id:

- **`229`** -- repository state `2f330d1`. The primary evidence behind
  [`../../RESULTS.md`](../../RESULTS.md).
- **`143319`** -- an earlier run of the pre-optimisation port state (predates
  the published history, so it has no git ref). Kept as an archive; its
  timings are not comparable to `229`'s in absolute terms (different stock
  image, drifted environment).

Per run:

- `full-summary-<array>.txt` -- the ledger: one `PASS`/`FAIL` line per centre
  degree (all 7-11 `PASS` in both runs).
- `full-d<N>-<array>.out` -- per-degree record: each stage's count vs the paper
  (`MATCH`), the per-port byte-identical checks (`rust == C++`, `lean == C++`),
  the assertion-only `check_*` agreement, and the per-port wall-clock timing
  table.

Reproduce with `modi/full_array.sh` (see [`../README.md`](../README.md)).
