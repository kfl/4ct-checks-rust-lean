# Verification run logs

Raw output of the full differential for paper Lemmas A.2-A.6 on MODI (one
64-core / 128-SMT-thread node per degree). Three complete matrices are
archived; file suffixes record the SLURM job array ids:

- **`1393` + `1396`** -- repository state `9cf81f2`. Degrees 8-11 ran as
  array `1393`; degree 7 was rerun as array `1396` because its earlier run,
  job `1389`, predated that repository state. Both arrays appended to one
  ledger, `full-summary-1393+1396.txt`. This matrix is the primary evidence
  behind [`../../RESULTS.md`](../../RESULTS.md).
- **`229`** -- repository state `0d05d5e`. The previous published run.
- **`143319`** -- an earlier run of the pre-optimisation port state (predates
  the published history, so it has no git ref). Kept as an archive; its
  timings are not comparable to `229`'s in absolute terms (different stock
  image, drifted environment).

These per-degree logs start with Lemma A.2's non-blocked `combine_rules` stage.
The separate Lemma A.1 empty-configuration differential is run by
`modi/run_p7.sh 0` and is not archived here.

Per matrix:

- `full-summary-<run>.txt` -- the ledger: one `PASS`/`FAIL` line per centre
  degree (all 7-11 `PASS` in all three runs).
- `full-d<N>-<array>.out` -- per-degree record: each stage's count vs the paper
  (`MATCH`), the per-port byte-identical checks (`rust == C++`, `lean == C++`),
  the assertion-only `check_*` agreement, and the per-port wall-clock timing
  table.

Reproduce with `modi/full_array.sh` (see [`../README.md`](../README.md)).
