# Verification run logs

Raw output of the full A.3-A.6 differential on MODI (128-core node, 2026-06-26),
SLURM job array `143319`. These are the primary evidence behind [`../../RESULTS.md`](../../RESULTS.md).

- `full-summary.txt` -- the ledger: one `PASS`/`FAIL` line per centre degree (all 7-11 `PASS`).
- `full-d<N>-143319.out` -- per-degree record: each stage's count vs the paper (`MATCH`),
  the per-port byte-identical checks (`rust == C++`, `lean == C++`), the assertion-only
  `check_*` agreement, and the per-port wall-clock timing table.

Reproduce with `modi/full_array.sh` (see [`../README.md`](../README.md)).
