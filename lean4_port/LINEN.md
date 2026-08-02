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

`Linen.mapM` creates an atomic claim cursor for each parallel region. Each
worker in the region's team repeatedly:

1. claims the next small, half-open chunk;
2. computes it outside the atomic claim operation;
3. appends results and the chunk's start index to its worker-local buffers; and
4. returns to claim more work.

After the workers join, their chunk runs are merged into input order serially.
No result-side synchronisation occurs in the hot path.

Teams are drawn from a single process-wide slot budget of `config.workers`
worker slots. A region spawns a worker task only while it can reserve a slot,
and always runs one worker inline on its caller, so at most `config.workers`
Linen worker tasks are live or queued at any time and nested work without a
slot runs serially on its caller. Workers retry reservation once per
successful claim (two scalar-counter reads when nothing is free), so a team
that started small grows as other regions retire and release slots; in the
measured nested check workloads most workers were spawned by this growth
path rather than at region entry. The
inline worker holds a slot when one is free, making a saturated budget
visible to the growth gates.

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

## Diagnostics

The slot budget keeps an always-on reservation ledger, updated only on
reservation events (never on the per-claim gate path); the engine's
measured results include this cost. `Linen.activeSlots` and
`Linen.budgetStats` expose it as supported diagnostics, and the test suite
asserts its invariants: at quiescence `underflows` is zero, granted
reservations equal `releases`, `active` is zero, and `peak` never exceeds
the configured worker count. The check driver prints the ledger to stderr
under `--budget_stats`.

## Scope and limitations

Linen is inspired by Rayon but is not yet a Rayon clone. It is a bounded
dynamic executor without per-worker deques, global cross-region work stealing,
a persistent worker pool, or a help-join protocol. Each nested parallel region
has its own atomic claim cursor, but all regions share the worker-slot
budget, so nesting depth and concurrent regions cannot multiply the task
count. Lean's task runtime prevents nested joins from starving the pool. Two
known conservatisms under-provision teams slightly rather than oversubscribe:
an outer worker blocked joining its inner region keeps its slot, and a
slotted worker entering a nested region reserves a second slot for its
inline role.

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
and reducing entry points, refcount-heavy and allocation-heavy workloads, and
nested two-level compositions -- wide and narrow outer levels -- in all four
serial/parallel splits.

Smoke measurements for the pure map cases on a 10-core M1 Pro (2026-07-26)
are medians of three back-to-back runs, in milliseconds, against the eager
one-task-per-element baseline. `Scheduler` maps `(· + 1)` over 200,000
elements; `Uneven` maps `unevenWork` over 50,000 elements. `Threads` is the
configured worker count (`LEAN_NUM_THREADS` in these runs). The machine has
eight performance and two efficiency cores, so eight is the largest
homogeneous configuration and the ten-row mixes in the slower cores.

| Threads | Scheduler: eager | Scheduler: Linen c=1 | Scheduler: Linen c=64 | Uneven: eager | Uneven: Linen c=1 | Uneven: Linen c=64 |
|--------:|-----------------:|---------------------:|----------------------:|--------------:|------------------:|-------------------:|
|       1 |               36 |                  1.3 |                   1.2 |           104 |                76 |                 76 |
|       4 |              139 |                   48 |                   3.7 |            63 |                23 |                 21 |
|       8 |              241 |                  124 |                   4.7 |            98 |                13 |                 11 |
|      10 |              339 |                  209 |                   5.8 |           120 |                21 |                 10 |

## TODO

- [ ] Profile the full checks at 128, 96, 64, and 32 workers.
- [ ] Amortise claim overhead at fine granularity: the shared cursor makes
      c=1 collapse as worker count grows on cheap elements. Coarser claims
      retain useful scaling on uneven and clustered workloads, although the
      best granularity depends on the workload and machine topology.
      Candidates include guided chunk decay (large early claims, finer tail)
      with run descriptors for variable-size merging. Team sizing is now
      handled by the occupancy budget and no longer coupled to `chunkSize`
      (a chunk-count cap aside), so this is purely a claim-granularity
      question.
- [ ] Route the pure runtimes' serial fast paths through the unchecked chunk
      loops: they fold with generic closure calls today (~40x a literal fold
      on trivial operations), while the parallel workers' direct loops come
      within ~7x of it.
- [ ] Add deterministically shuffled or replayed cost distributions to the
      benchmark (the clustered case covers the adversarial-for-static
      extreme; shuffled covers the no-spatial-structure one).
- [ ] Rotate configuration order between repetition rounds: execution order
      is fixed within a process, so slow thermal and allocator drift stays
      correlated with configuration.
