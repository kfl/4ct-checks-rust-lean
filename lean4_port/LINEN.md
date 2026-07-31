# Linen

Linen is a small data-parallel executor for Lean inspired by the Rust library
Rayon. Its name continues the textile lineage from Cilk through Rayon. The
implementation is independent of `NearLinear4ct` and intended for extraction
into a standalone package.

## Goal

The check drivers from `NearLinear4ct` need fine-grained load balancing because
individual cartwheel candidates vary greatly in cost. The original `parMap`
achieved that by eagerly creating one Lean `Task` per candidate. At 32 workers
on the 128-thread benchmark host, queue operations and futex transitions put 69%
of CPU time in the kernel.

Linen keeps candidate-level dynamic balancing without representing every
candidate as a runtime task.

## Design

A parallel region is one invocation of a Linen operation over an input array.
The function applied to an element may itself invoke Linen, creating nested
regions.

Linen divides each region's input into chunks: contiguous ranges of indices
written as `[start, stop)`, including `start` but not `stop`.

Each region has its own claim cursor, a counter shared by its workers. It
points to the first index not yet assigned. A worker claims a chunk by moving
the cursor past it. This update is atomic, so workers cannot claim overlapping
chunks. Every worker repeatedly:

1. claims the next chunk by atomically advancing the cursor;
2. computes the chunk outside the atomic operation;
3. appends its results and `start` to worker-local buffers; and
4. returns to claim another chunk.

After the workers join, Linen uses the recorded start indices to merge their
chunk runs into input order. The result path requires no synchronisation while
workers run.

All regions, including nested ones, share a process-wide budget of
`config.workers` slots. A region runs one worker inline and spawns another only
after reserving a slot, so no more than `config.workers` Linen worker tasks are
live or queued. A region that cannot reserve a slot still makes progress
inline. Workers retry reservations once per successful claim, before
computing the claimed chunk, so a new sibling starts working while the
claimer computes; surviving regions thereby grow as other regions finish.

The per-call `chunkSize` controls claim granularity and is clamped to at least
one. Small chunks improve balancing when element costs vary; large chunks
amortise claim overhead. The default is one.

Pure `Linen.map` is defined as `xs.map f` and installs the parallel executor
through `implemented_by`. Proofs therefore see the serial specification while
compiled programs use the parallel implementation.

`Linen.mapIO` stops its failing chunk and further claims in that region, lets
other claimed chunks finish, and rethrows the failure with the lowest input
index.

`Linen.mapReduce` takes a `[Std.Associative op]` instance, which supplies a
proof that `op` is associative. Its runtime folds each chunk to one partial and
combines the partials in input order, using one bounded parallel combine pass
when necessary. The operation need not be commutative, and `init` need not be
an identity.

At startup, Linen reads the worker count from `LINEN_WORKERS`, then
`LEAN_NUM_THREADS`, then the machine's logical core count. Invalid and zero
values are ignored; a failed core-count query falls back to one worker.

## Verification status

Lean reasons about serial specifications for the pure combinators. In
particular, `Linen.map` is defined as `xs.map f`, and `Linen.mapReduce` as
`(xs.map f).foldl op init`. `filterMap` and `flatMap` are built from this serial
`map`. Consequently, proofs using these functions see no tasks, cursors, or
scheduling decisions.

The `[Std.Associative op]` instance required by `Linen.mapReduce` proves that
`op` is associative, which permits the runtime to regroup contiguous values
without changing the result. Commutativity is not required, and `init` need
not be an identity.

The compiled parallel implementations replace the serial definitions through
`implemented_by` and cross an `unsafeBaseIO`/`unsafeCast` boundary. Their
equivalence to the serial specifications has not been proved in Lean. The pure
worker loops contain local proofs for their array bounds, but these do not
establish end-to-end correctness.

The following remain to be proved:

- the equivalence of `mapImpl` and `mapReduceImpl` to their serial
  specifications;
- formal result-order and error specifications for `mapM`, `mapReduceM`, and
  `mapIO`, including any required assumptions about effects; and
- the worker-budget, release, and liveness invariants of nested regions.

The contract tests exercise these properties across worker counts and
scheduling shapes, but tests are evidence rather than proofs.

## Diagnostics

Linen keeps always-on counters for reservation attempts, releases, and worker
creation. Per-claim read gates do not update them, and the benchmarks include
their cost. `Linen.activeSlots` reports current occupancy;
`Linen.budgetStats` returns the cumulative counters.

At quiescence, `underflows` and `active` must be zero, granted reservations
must equal `releases`, and `peak` must not exceed `config.workers`. The test
suite checks these invariants.

## Scope and limitations

Linen is inspired by Rayon but is not a Rayon clone. It has no per-worker
deques, cross-region work stealing, persistent worker pool, or help-join
protocol. The shared slot budget bounds live or queued worker tasks across
nested and concurrent regions, while Lean's task runtime prevents nested joins
from starving the pool.

Two conservative accounting choices avoid oversubscription but can
under-provision nested work: an outer worker retains its slot while waiting for
an inner region, and a slotted worker reserves another slot for the nested
region's inline worker.

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

The suite sweeps claim sizes and covers pure maps, `IO` maps, reductions,
reference-counting, allocation, and nested composition. Nested cases include
wide and narrow steady states, a draining outer tail, repeated short regions,
allocating fan-out, and three parallel levels. Two-level cases run all four
serial/parallel splits, with worker-budget traffic reported for
parallel/parallel execution.

The table reports medians of three pure-map runs on a 10-core M1 Pro on
2026-07-26, in milliseconds. `Scheduler` maps `(· + 1)` over 200,000 elements;
`Uneven` maps `unevenWork` over 50,000. The machine has eight performance and
two efficiency cores, so the ten-worker results include the slower cores.

| Threads | Scheduler: eager | Scheduler: Linen c=1 | Scheduler: Linen c=64 | Uneven: eager | Uneven: Linen c=1 | Uneven: Linen c=64 |
|--------:|-----------------:|---------------------:|----------------------:|--------------:|------------------:|-------------------:|
|       1 |               36 |                  1.3 |                   1.2 |           104 |                76 |                 76 |
|       4 |              139 |                   48 |                   3.7 |            63 |                23 |                 21 |
|       8 |              241 |                  124 |                   4.7 |            98 |                13 |                 11 |
|      10 |              339 |                  209 |                   5.8 |           120 |                21 |                 10 |

## TODO

- [ ] Prove that `mapImpl` and `mapReduceImpl` implement their serial
      specifications for every chunk size and worker schedule, assuming
      `[Std.Associative op]` for `mapReduce`.
- [ ] Give `mapM`, `mapReduceM`, and `mapIO` formal specifications covering
      result order and error selection, with explicit assumptions about
      effects where needed.
- [ ] Prove the slot-budget and release invariants, and liveness of nested
      region growth and joins.
- [ ] Amortise fine-grained claim overhead. The shared cursor makes `c=1`
      collapse on cheap elements as worker count grows, while the best fixed
      claim size depends on the workload and machine. Evaluate guided decay --
      large early claims followed by a finer tail -- with run descriptors for
      variable-size merging. The occupancy budget already handles team sizing,
      so this is a separate claim-granularity problem.
- [ ] Isolate and reduce the fixed cost of short-lived regions.
      `nested-repeated` measures repeated setup and joins; `nested-fanout`
      adds allocation and ordered flattening; `nested-depth3` compounds region
      overhead and slot retention. `nested-draining-tail` is the control that
      any change must preserve.

      First report worker-budget deltas for every nested composition containing
      Linen, not only parallel/parallel. Then evaluate two independent A/B
      changes:

      1. allocate the region's team counter and task registry only when the
         first worker can be spawned; and
      2. replace entry seeding with growth-only startup.

      Run each change across the full claim-size sweep and all nested cases at
      several worker counts. Growth-only startup is most likely to regress
      coarse and `onewave` claims, which provide few opportunities to expand
      the team. If depth-three overhead remains after region setup is cheaper,
      isolate retained parent slots and the extra inline-slot reservation.
      Prefer removing structural overhead before adding a small-region cutoff.
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
