# Linen

Linen is a small data-parallel executor for Lean inspired by the Rust library
Rayon, though it is not a Rayon clone. Its name continues the textile lineage
from Cilk through Rayon. The implementation is intended for extraction into a
standalone package.

## Goal

The check drivers from `NearLinear4ct` need fine-grained load balancing because
individual cartwheel candidates vary greatly in cost. The original `parMap`
achieved that by eagerly creating one Lean `Task` per candidate. At 32 workers
on the 128-thread benchmark host, queue operations and futex transitions put
69% of CPU time in the kernel.

Linen keeps candidate-level dynamic balancing without representing every
candidate as a runtime task. The same design applies to other irregular
workloads whose element costs vary substantially.

## Design

A parallel region is one invocation of a Linen operation over an input. The
function applied to an element may itself invoke Linen, creating nested
regions.

Linen divides each region into chunks: contiguous, half-open ranges of indices
written as `[start, stop)`, including `start` but not `stop`.

Each region has a claim cursor, a counter shared by its workers that counts
chunk ordinals. A worker claims a chunk by atomically incrementing the
cursor. Because that read-and-update is indivisible, two workers cannot claim
the same chunk. Every worker repeatedly:

1. claims the next chunk ordinal by atomically advancing the cursor;
2. computes the chunk `[start, stop)` outside the atomic operation;
3. appends its results and the ordinal to worker-local buffers; and
4. returns to claim another chunk.

After the workers join, Linen uses the recorded ordinals to merge their
chunk runs into input order. Workers never synchronise on the result path.

Internally, `Chunking` stores a positive chunk size and its proved, cached
chunk count. Worker outputs are indexed by that exact chunking and record
`Fin` ordinals; placement tables are vectors of the same length. Alignment,
range, plan consistency, and table bounds therefore hold by construction.
Proof fields erase, while the count is computed once per region.

All regions, including nested ones, share a process-wide budget of
`config.workers` slots. A region runs one worker inline and spawns another only
after reserving a slot, so no more than `config.workers` Linen worker tasks are
live or queued. A region that cannot reserve a slot still makes progress
inline.

Workers retry reservations once per successful claim, before computing the
claimed chunk. A new sibling can therefore begin while the claimant computes,
and surviving regions can grow as other regions finish and release slots.

The implementation separates a functional data path from an imperative
scheduler. Chunk computation, copying, placement, and assembly use bounded
`Array.foldl`/`foldlM` definitions or pure step functions. Claiming,
reservation, growth, and joining use explicit control flow because atomic
sequencing and retries are their purpose.

The per-call `chunkSize` controls claim granularity and is clamped to at least
one. Small chunks improve balancing when element costs vary; large chunks
amortise claim overhead. The default is one.

### Operations

The semantic primitive is indexed tabulation. `Linen.tabulate n g` builds the
array whose entry at `i` is `g i`; its pure specification is `Array.ofFn g`.
The callback observes only its index, not workers, claims, or chunk boundaries,
so `chunkSize` cannot change a pure result.

For `tabulateM` and `tabulateIO`, result positions remain deterministic, but
effects can reveal scheduling. Effects within a chunk run in index order;
effect order across chunks is unspecified. `tabulateIO` and `mapIO` stop new
claims after a failure and rethrow the failure with the lowest input index
after already claimed chunks finish.

`map`, `mapM`, and `mapIO` instantiate the tabulation engine with an indexed
reader of their input. `filterMap` and `flatMap` build on pure `map`.
`mapReduce` and `mapReduceM` use array-specific reducing loops so each chunk
produces one partial rather than an intermediate mapped array.

The compiled engine receives a factory that constructs the callback separately
for each worker. Specialisation and the public `@[inline]` monadic wrappers let
ordinary callback lambdas reach that factory before closure conversion,
avoiding reference-count contention on one shared callback closure. A
preconstructed callback may still contain shared nested closures.

Pure `map` is defined as `xs.map f` and installs its parallel executor through
`implemented_by`. Proofs therefore see the serial specification while compiled
programs use the parallel implementation. Pure `tabulate` uses the same
arrangement with `Array.ofFn` as its specification.

The pure serial fast paths -- one configured worker, or the whole input
contained in one chunk -- use the same unchecked chunk loops as parallel
workers without task setup.

`mapReduce` requires `[Std.Associative op]`. The runtime folds each chunk to one
partial and combines partials in input order, with one bounded parallel combine
pass when needed. `op` need not be commutative, and `init` need not be an
identity.

At startup, Linen reads the worker count from `LINEN_WORKERS`, then
`LEAN_NUM_THREADS`, then the machine's logical core count. Invalid and zero
values are ignored; failure to query the core count falls back to one worker.

## Verification status

The pure compiled implementations cross an `unsafeBaseIO`/`unsafeCast`
boundary. Their complete equivalence to the serial specifications has not yet
been proved in Lean.

The following parts are proved in `Linen.lean`:

- The tabulation chunk loop computes the corresponding `Array.ofFn` slice.
- Tabulating indexed reads gives `xs.map f`, and the serial map fast path is
  therefore exact.
- The pure reduce chunk loop computes the seeded mapped fold
  `reducePartial` for one claimed chunk.
- `orderedPartials` reconstructs every chunk's partial in ordinal order
  from well-formed reduce output (`orderedPartials_wf`), and by
  associativity their ordered fold is the serial fold
  (`orderedPartials_foldl_wf`); the optional second reduction level is the
  same theorem at the identity mapper (`orderedPartials_foldl_wf_id`).
- `WFWorkerOut` and `WFOuts` describe aligned, in-range, uniquely claimed
  chunks and their worker-local buffers.
- Placement tables depend only on the logical runs, not their order.
- Given `WFOuts`, `merge_wf` reconstructs `xs.map f`; its `Array.ofFn`
  instantiation, `merge_wf_ofFn`, reconstructs a tabulation result.

`tabulateChunk_piece` connects one tabulation claim to the piece expected by
that assembly proof. It does not prove that concurrent runtime workers produce
`WFOuts`.

The following remain open:

- proving that atomic claims and task execution always produce `WFOuts`, which
  would close the pure parallel correspondence across the unsafe boundary;
- formal result-order and error specifications for the effectful combinators,
  with explicit assumptions about observable effects; and
- the worker-budget, release, and liveness invariants of nested growth and
  joins.

The contract tests exercise these properties across worker counts and
scheduling shapes, but tests are evidence rather than proofs.

## Diagnostics

Linen keeps always-on counters for reservation attempts, releases, and worker
creation. Per-claim read gates do not update them. `Linen.activeSlots` reports
current occupancy; `Linen.budgetStats` returns the cumulative counters.

At quiescence, `underflows` and `active` must be zero, granted reservations must
equal `releases`, and `peak` must not exceed `config.workers`. The test suite
checks these invariants.

## Scope and limitations

Linen has no per-worker deques, cross-region work stealing, persistent worker
pool, or help-join protocol. The shared slot budget bounds live or queued Linen
workers across nested and concurrent regions; Lean's task runtime supplies the
underlying scheduler.

Two conservative accounting choices avoid oversubscription but can
under-provision nested work: an outer worker retains its slot while waiting for
an inner region, and a slotted worker reserves another slot for the nested
region's inline worker.

The budget bounds concurrency but cannot decide whether team growth is
profitable. Cheap, short nested regions may create and join workers too quickly
to amortise their lifetime cost. Per-claim growth also favours regions with
cheap claims when several regions compete for newly released slots. Addressing
either limitation likely requires scheduler-level mechanisms such as work-first
execution, a persistent pool, or fair handoff.

## Validation and benchmark

Run the Linen contract tests:

```sh
lake exe linenTest
```

Run the benchmark suite with its default repetition count, or select a worker
count explicitly:

```sh
lake exe linenBench
LEAN_NUM_THREADS=1 lake exe linenBench
LEAN_NUM_THREADS=4 lake exe linenBench
```

`LinenBench` compares serial, eager-task, static-partition, and Linen execution.
It covers cheap and uneven work, allocation, reference counting, reductions,
effectful callbacks, matched tabulation/map controls, nested composition, team
growth, and draining regions. It verifies results and reports raw samples and
worker-budget traffic.

Stable conclusions from the current benchmark evidence are:

- claim size must reflect work granularity; no fixed size is portable;
- dynamic claiming helps uneven and clustered costs but adds overhead to cheap
  work;
- the process-wide slot budget bounds nested execution, but parallelising cheap
  inner regions can still be substantially slower than leaving them serial;
- worker-local callback construction avoids a shared-closure contention floor;
  and
- scheduler changes need evidence from representative workloads, not only
  synthetic microbenchmarks.

Raw machine-specific results and rejected experiments belong in the runs
journal rather than this document.

## TODO

- [ ] Prove that concurrent tabulation, map, and reduce workers establish
      `WFOuts`, then close their correspondence with the serial
      specifications across the `unsafeBaseIO` boundary. The proof-carrying
      carriers reduce the obligation to value correspondence and exactly-once
      coverage: alignment and range hold by construction.
- [ ] Give `tabulateM`, `tabulateIO`, `mapM`, `mapReduceM`, and `mapIO` formal
      specifications for result order and error selection. Carry failure
      indices as `Fin n` first: `runChunk` already holds the proof it
      passes to the callback, making valid-position structural.
- [ ] Prove the slot-budget and release invariants and liveness of nested region
      growth and joins. Start with bounded counter types (`activeRef` at
      `{a // a ≤ config.workers}`, `Region.spawned` at `s ≤ slots`) for
      the cap conjunct; reservation/release correspondence and liveness
      are the substance.
- [ ] Add general combinators built on indexed tabulation: `zip`/`zipWith`,
      `mapIdx`, and gather/permute; investigate an indexed producer interface
      without exposing chunk boundaries to callbacks.
- [ ] Revisit short-region scheduling only with evidence from a representative
      workload. Likely directions are work-first execution, a persistent pool,
      or a live-waiter fair-handoff mechanism.
- [ ] Add deterministically shuffled or replayed cost distributions to
      `LinenBench`.
- [ ] Rotate benchmark configuration order between repetition rounds so slow
      thermal and allocator drift is not correlated with configuration.
