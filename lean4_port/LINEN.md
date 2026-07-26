# Linen

Linen is a small data-parallel executor for Lean. Its name follows the textile
lineage from Cilk to Rayon while giving a nod to Lean. The implementation is
independent of `NearLinear4ct` and can be extracted into a stand-alone
package.

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
3. appends results and the chunk's start index to its worker-local buffers; and
4. returns to claim more work.

After the workers join, their chunk runs are merged into input order serially.
No result-side synchronisation occurs in the hot path.

The per-call `chunkSize` argument controls claim granularity and is clamped to
at least one. Smaller chunks preserve balancing when element costs vary;
larger chunks amortise claim overhead. The default of one preserves
candidate-level balancing.

At process startup, Linen reads the worker count once using this precedence:

1. `LINEN_WORKERS`;
2. `LEAN_NUM_THREADS`; and
3. the machine's logical core count.

Invalid or zero-valued worker overrides are ignored. If querying the logical
core count fails, Linen falls back to one worker.

Pure `Linen.map` has `xs.map f` as its Lean definition and installs the worker
engine only with `implemented_by`. Consequently, proofs see exactly the serial
specification, while compiled executables get parallel evaluation.
`Linen.mapIO` is fail-fast: after any worker reports an error, workers stop
claiming new chunks and finish the chunks they already claimed (a failing
worker stops its own chunk at the error); then the error with the smallest
input index is re-raised. NearLinear4ct's existing `par*` functions
are thin compatibility wrappers around this API.

`Linen.mapReduce` folds each claimed chunk to one partial within its worker,
then restores the partials to input order. If the partials outnumber the
configured workers, one bounded parallel pass folds contiguous runs, leaving
at most one partial per worker for the final serial fold.

Its specification is the sequential left fold. A `Std.Associative` instance
for the combining operation is the caller's obligation that makes the
specification and the parallel runtime agree. Commutativity is not required,
so associative non-commutative operations reduce deterministically.

## Scope and limitations

Linen is inspired by Rayon but is not yet a Rayon clone. It is a bounded
dynamic executor without per-worker deques, global cross-region work stealing,
a persistent worker pool, or a help-join protocol. Each nested parallel region
creates its own bounded team and atomic claim cursor. Lean's task runtime
prevents nested joins from starving the pool. With one level of nesting and
`W` configured workers, the outer workers can collectively queue up to `W²`
inner tasks; deeper nesting or multiple concurrent regions can queue more.

## Validation and benchmark

Run the normal correctness gate:

```sh
lake exe test
lake exe linenTest
```

Run the microbenchmark suite (the first argument sets the repetition count,
defaulting to three):

```sh
lake exe linenBench
LEAN_NUM_THREADS=1 lake exe linenBench
LEAN_NUM_THREADS=4 lake exe linenBench
```

Each run sweeps the claim granularities in-process and covers the pure, `IO`,
and reducing entry points plus refcount-heavy and allocation-heavy workloads.

Smoke measurements for the pure map cases on a 10-core M1 Pro (2026-07-26)
are medians of three back-to-back runs, in milliseconds, against the eager
one-task-per-element baseline. `Scheduler` maps `(· + 1)` over 200,000
elements; `Uneven` maps `unevenWork` over 50,000 elements. `Threads` is the
configured worker count (`LEAN_NUM_THREADS` in these runs). The machine has
eight performance and two efficiency cores, so eight is the largest
homogeneous configuration and the ten-row mixes in the slower cores.

| Threads | Scheduler: eager | Scheduler: Linen c=1 | Scheduler: Linen c=64 | Uneven: eager | Uneven: Linen c=1 | Uneven: Linen c=64 |
|--------:|-----------------:|---------------------:|----------------------:|--------------:|------------------:|-------------------:|
|       1 |               37 |                  1.7 |                   1.6 |           104 |                76 |                 76 |
|       4 |              140 |                   37 |                    23 |            64 |                24 |                 21 |
|       8 |              246 |                  102 |                    21 |           100 |                15 |                 12 |
|      10 |              319 |                  166 |                    34 |           120 |                17 |                 11 |

## TODO

- [ ] Profile the full checks at 128, 64, and 32 workers.
- [ ] Measure claim-cursor contention at high worker counts (the c=1 columns
      degrade as workers grow; data above 8 threads on the M1 is confounded by
      its efficiency cores). Only if it binds, weigh structural remedies:
      guided chunk decay or per-worker deques.
- [ ] Attribute the pure-scan anomaly: with near-zero per-element work the
      parallel worker loop costs an order of magnitude more per element than
      the serial paths and grows with worker count (`sum` and `scheduler`
      cases in `linenBench`). The `static` task baseline at identical
      granularity does not show it, and neither does the serial fast path,
      so the cost sits in the monadic worker loop itself -- not in claim
      traffic, chunk granularity, or task scheduling.
- [ ] Add deterministically shuffled or replayed cost distributions to the
      benchmark (the clustered case covers the adversarial-for-static
      extreme; shuffled covers the no-spatial-structure one).
- [ ] Rotate configuration order between repetition rounds: execution order
      is fixed within a process, so slow thermal and allocator drift stays
      correlated with configuration.
