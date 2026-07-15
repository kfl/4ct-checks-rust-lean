# Linen

Linen is a small data-parallel executor for Lean. Its name follows the textile
lineage from Cilk to Rayon while giving a nod to Lean. The implementation is
kept independent of `NearLinear4ct` so it can eventually be extracted into a
stand-alone package.

## Goal

The check drivers need fine-grained load balancing because individual
cartwheel candidates vary greatly in cost. The original `parMap` achieved that
by eagerly creating one Lean `Task` per candidate. On reduced thread counts at
the many-core host, the resulting tens of millions of queue operations and
futex transitions dominate CPU time.

Linen keeps candidate-level dynamic balancing without representing every
candidate as a runtime task.

## Design

`Linen.mapM` creates an atomic claim cursor for each parallel region. A bounded
team of at most one Lean task per configured worker repeatedly:

1. claims the next small, half-open chunk;
2. computes it outside the atomic claim operation;
3. appends indexed results to its worker-local buffer; and
4. returns to claim more work.

After the workers join, their buffers are merged into input order serially. No
result-side synchronization occurs in the hot path.

The default chunk size is one because a cartwheel candidate is the measured
natural work unit. The worker count follows this precedence:

1. `LINEN_WORKERS`;
2. `LEAN_NUM_THREADS`; and
3. hardware concurrency.

`LINEN_CHUNK_SIZE` overrides the claim size. Invalid or zero overrides are
ignored.

Pure `Linen.map` has `xs.map f` as its Lean definition and installs the worker
engine only with `implemented_by`. Consequently, proofs see exactly the serial
specification, while compiled executables get parallel evaluation.
`Linen.mapIO` collects every `Except` result before re-raising the first failure
in input order, matching the existing observable error policy. NearLinear4ct's
existing `par*` functions are thin compatibility wrappers around this API.

## Scope and limitations

This is a bounded dynamic executor, not yet a full Rayon clone: there are no
per-worker deques or global cross-region stealing. Each nested parallel region
creates its own bounded team. Lean's task runtime prevents nested joins from
starving the pool, but concurrent nested regions can still queue up to the
square of the worker count. The prototype is intended to establish whether
removing per-candidate task traffic fixes the measured low-thread regression
before considering a persistent global pool or help-join protocol.

The claim cursor is still shared by every worker. Candidate work is large
enough that one atomic claim should be cheap, but `LINEN_CHUNK_SIZE`
provides the granularity lever and profiling should verify the assumption on
the full check.

## Validation and benchmark

Run the normal correctness gate:

```sh
lake exe test
lake exe linenTest
```

Run the side-by-side scheduler microbenchmark:

```sh
lake exe linenBench
LEAN_NUM_THREADS=1 lake exe linenBench
LEAN_NUM_THREADS=4 LINEN_CHUNK_SIZE=4 lake exe linenBench
```

A one-run smoke measurement on the 10-core M1 Pro (2026-07-15, chunk size 1)
was directionally positive in every row. Times are milliseconds and are not a
replacement for the full repeated benchmark:

| Threads | Trivial: task/element | Trivial: Linen | Uneven: task/element | Uneven: Linen |
|--------:|----------------------:|---------------:|---------------------:|--------------:|
|       1 |                    35 |              1 |                  103 |            75 |
|       4 |                   108 |             45 |                   59 |            25 |
|      10 |                   296 |            155 |                  113 |            15 |

The decisive experiment remains the full `check_7triangle`/`check_deg7` matrix
at x128, x64, and x32, followed by the byte-exact differential gate described
in `PERFORMANCE_NOTES.md`.
