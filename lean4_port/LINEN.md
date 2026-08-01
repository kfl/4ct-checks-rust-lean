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

The implementation follows a functional-data-path, imperative-scheduler
split: chunk computation, copying, placement, and assembly are bounded
`Array.foldl`/`foldlM` definitions or pure step functions (fused loops, no
intermediate collections), while the scheduler -- claiming, reservation,
growth, joining -- uses explicit control flow where atomic sequencing and
retries are the point.

The per-call `chunkSize` controls claim granularity and is clamped to at least
one. Small chunks improve balancing when element costs vary; large chunks
amortise claim overhead. The default is one.

Pure `Linen.map` is defined as `xs.map f` and installs the parallel executor
through `implemented_by`. Proofs therefore see the serial specification while
compiled programs use the parallel implementation. The serial fast paths (one
worker configured, or the whole input within one chunk) run the same
unchecked chunk loops as the parallel workers, so single-threaded and
small-array calls avoid both task setup and per-element bounds checks.

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
equivalence to the serial specifications has not been proved in Lean. The
pure worker loops contain local proofs for their array bounds, and the
serial chunk loops are proved equal to their specification slices in
`Linen.lean`'s verified-properties section -- so the serial fast paths are
verified outright, and the associative regrouping core for `mapReduce` is
proved -- but the parallel path's correctness remains unproved.

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

The budget bounds concurrent workers but does not make team growth profitable.
On cheap, short nested regions, per-claim growth can create nearly one worker
per claim before the region drains. Repeating that ramp across many regions
pays task creation and joining costs without enough work to amortise them.
Released slots are also biased by attempt frequency: growth attempts are
per-claim, so concurrent regions with cheap claims outcompete a region with
expensive claims for freed capacity, which can leave an expensive surviving
region effectively serial while short-lived teams churn around it.

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
allocating fan-out, three parallel levels, a contention-free team-ramp probe
crossing claim count with per-claim cost, and a matched draining-tail probe
crossing light-claim frequency with heavy-region runway. Two-level cases run all four
serial/parallel splits, with worker-budget traffic reported for
every composition containing Linen.

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

- [ ] Close the `mapImpl`/`mapReduceImpl` correspondence along the ladder
      split at the `unsafeBaseIO` trust boundary. Done, in `Linen.lean`:
      `mapChunkPure` computes the mapped slice appended to its accumulator
      and `reduceChunkPure` the left fold of the mapped slice (verifying the
      serial fast paths as the specifications), and `foldl_seeded_partials`
      is the associative regrouping core. Also done: the well-formedness
      predicates (`WFWorkerOut`, `WFOuts` -- aligned in-range starts, buffers
      exactly the folded chunk slices of their runs, each ordinal claimed
      exactly once) and the pure assembly layer (`foldl_chunkSlice_range`:
      ordered chunk slices reconstruct `xs.map f`; `extract_foldl_pieces`:
      block extraction at prefix-sum offsets yields each run's slice).
      Also done: `merge` is proved equal to a pure fold of `mergeStep` over
      chunk ordinals (`merge_eq_foldl`), and the data path now follows the
      functional-data-path/imperative-scheduler split: the chunk loops,
      copy loop, and monadic per-chunk iterations are bounded
      `Array.foldl`/`foldlM` definitions (their theorems collapse to core
      fold lemmas), and `placeChunks` is a pure nested fold over named
      state structures -- no loop-to-fold characterisation is needed there
      at all. The well-formedness and extraction theory is parameterised by
      a per-start `piece : Nat → Array β`, shared between the map
      instantiation (chunk slices) and the reduce instantiation (singleton
      partials). Also done, closing the map side: the `placeChunks`
      table-correctness proof (`placeWorker_foldl_spec` /
      `placeChunks_spec`: a proof-carrying run witness identifies an
      ordinal's unique owner, worker index, and prefix-sum offset) and the
      final assembly `merge_wf`: for any `WFOuts`-well-formed worker output,
      `merge outs xs.size chunkSize = xs.map f`, so worker count and
      claim order cannot affect the result. Open: the reduce-side
      instantiation via the regrouping lemma. The final bridge, that the
      concurrent runtime always produces well-formed output, requires
      reasoning about atomic claims and tasks; it stays an explicitly
      trusted step.
- [ ] Give `mapM`, `mapReduceM`, and `mapIO` formal specifications covering
      result order and error selection, with explicit assumptions about
      effects where needed.
- [ ] Prove the slot-budget and release invariants, and liveness of nested
      region growth and joins.
- [ ] Deferred design note -- fair slot handoff. The attempt-frequency bias
      is real (draining-matched), but the v1 FIFO-queue handoff collapsed
      Linen's slot-turnover loop and was reverted; the runs journal records
      the failure. Any future handoff must maintain only live waiters,
      support O(1) cancellation on region completion, return slots directly
      to the pool when no live waiter exists, and atomically coordinate
      completion with handoff -- a real concurrent waiter structure, i.e. a
      scheduler mechanism. Do not build it without evidence from a real
      workload beyond the synthetic fine/coarse case.
- [ ] Short-region fixed cost: three mechanisms tested and rejected
      (growth-only startup, the remaining-work growth gate, lazy region-state
      allocation -- the runs journal records each). The ~13-15 microsecond
      worker-lifetime cost (task creation, scheduling, join) remains the
      leading explanation, though not proved by elimination. Meaningful
      further reduction most plausibly requires avoiding or amortising worker
      lifetimes -- through work-first spawning or a persistent pool -- which
      is scheduler-class work under the same real-workload evidence bar as
      the deferred fair-handoff note.
- [ ] Idle-budget over-ramping stays open and is outside any claim-count
      rule: 32-claim cheap and 32-claim medium regions have identical
      geometry and opposite profitability, so a fix requires an explicit
      granularity hint or an online work-first policy. Deliberately
      deferred.
- [ ] Isolate the `mapIO` success-path overhead. A trivial `IO` mapper remains
      slower than its serial control at every measured width; separate the
      costs of the generic monadic worker, error bookkeeping, and ordered
      merging before changing the failure semantics.
- [ ] Add deterministically shuffled or replayed cost distributions to the
      benchmark (the clustered case covers the adversarial-for-static
      extreme; shuffled covers the no-spatial-structure one).
- [ ] Rotate configuration order between repetition rounds: execution order
      is fixed within a process, so slow thermal and allocator drift stays
      correlated with configuration.
