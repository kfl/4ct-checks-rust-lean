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

The public semantic primitive is indexed tabulation: `Linen.tabulate n g`
builds the array whose entry at `i` is `g i`, with the pure specification
`Array.ofFn g` installed through `implemented_by`. The semantic object is a
value at a stable index; workers, claims, offsets, and chunk boundaries
are scheduling details that `g` cannot observe, so for pure tabulation
`chunkSize` is a performance hint that cannot change the result. For the
effectful variants (`tabulateM`, `tabulateIO`), result positions and the
selected error are deterministic, but effects can reveal scheduling:
within a chunk, effects run in index order; cross-chunk effect order is
unspecified.

The internal runtime primitive is narrower: schedule chunks and invoke a
chunk folder once per claim, so abstraction costs are amortised over the
chunk rather than paid per element. `tabulate` supplies a `Fin`-iteration
chunk loop; pure `map` (and with it `filterMap` and `flatMap`) and the
parallel paths of `mapM` and `mapIO` instantiate the tabulation engine
with an indexed reader of their input; `mapReduce` and `mapReduceM`
supply array-specific reducing folders, and the monadic maps' serial fast
paths traverse their array directly. The tabulation engine chain is
specialised per instantiation (`@[specialize]`), which lets a specialised
inner loop receive its instantiation's inputs directly instead of calling
through a composed indexed closure -- the pure paths achieve this, while
the `mapIO` numbers show the monadic reading path does not yet. The worker-callback factory boundary
sits on the implemented functions behind `@[inline]` public wrappers, so
a lambda at an ordinary call site is beta-reduced into the factory before
closure conversion and the callback is constructed inside each worker's
task (`makeWorkerFn`).

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
chunk loops carry their index-bound proofs (`Fin` construction erases at
compile time), and the serial chunk loops are proved equal to their
specification slices in `Linen.lean`'s verified-properties section: the
tabulation loop over the full range is exactly `Array.ofFn g`, tabulating
the indexed reads of `xs` is `xs.map f`, and the reduce chunk loop is the
fused left fold of the mapped slice -- so the serial fast paths of
`tabulate`, `map`, and `mapReduce` are verified outright, and the
associative regrouping core for `mapReduce` is proved -- but the parallel
path's correctness remains unproved.

The following remain to be proved:

- the equivalence of `tabulateWithWorkerFnImpl`, `mapImpl`, and
  `mapReduceImpl` to their serial specifications;
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

- [ ] Close the `tabulateWithWorkerFnImpl`/`mapReduceImpl` correspondence
      along the ladder split at the `unsafeBaseIO` trust boundary. Done, in
      `Linen.lean`: `tabulateChunk` computes the `Array.ofFn` slice
      appended to its accumulator (with `ofFn_read_eq_map` carrying it to
      the `map` instantiation) and `reduceChunkPure` the left fold of the
      mapped slice, verifying the serial fast paths as the
      specifications, and `foldl_seeded_partials` is the associative
      regrouping core. Also done: the well-formedness
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
      claim order cannot affect the result. The table-correctness proof
      factors `placeChunks` through a flat trace of logical writes
      (`placementTrace`) and shows the tables depend only on the set of
      writes, not their order (`foldl_set_constant` needs agreement among
      the writes hitting an ordinal, not a unique writer) -- the
      order-invariance that the trusted concurrent bridge will lean on:
      any schedule producing the same set of aligned, uniquely-claimed
      runs produces identical tables. Open: the reduce-side
      instantiation via the regrouping lemma. Tabulation assembly needs
      no separately restated proof: `merge_wf` instantiated with
      `xs := Array.ofFn g` and `f := id` covers it, and only the
      worker-output instantiation is new. The final bridge, that the
      concurrent runtime always produces well-formed output, requires
      reasoning about atomic claims and tasks; it stays an explicitly
      trusted step.
- [ ] Give `tabulateM`, `tabulateIO`, and the monadic map family formal
      specifications covering result order and error selection, with
      explicit assumptions about effects where needed.
- [ ] Callback-closure contention, to validate on MODI. Contention on a
      closure shared across workers is real: before the factory boundary,
      `tabulate` called with a runtime closure paid per-element
      reference-count traffic on that shared closure. Placing the
      factory boundary on the implemented functions behind `@[inline]`
      public wrappers restored the `tabulate-cheap` rows to parity with
      the specialised map instantiation, and the fix should now be
      validated at MODI worker counts, where contention grows with the
      team. Residual exposure: a preconstructed runtime callback passed
      as `g` may still contain a shared nested closure; an eventual
      advanced `tabulateWith` API exposing the worker factory could
      address that case explicitly, in the spirit of worker-local
      initialisation combinators.
- [ ] Candidate, measure-first: `usize` inner chunk loops. The tabulation
      chunk loops step a boxed `Nat` counter where the array-backed map
      loops step a `usize`; the remaining comparison is cheap direct
      tabulation against the array-backed `usize` map loop (reduction is
      array-backed again and no longer affected). A `usize`
      implementation behind the proof-carrying `Nat` definition (the
      `Array.foldlMUnsafe` pattern) would remove the difference.
- [ ] Combinators to build on `tabulate`: `zip`/`zipWith` (tabulate over
      the minimum size), `mapIdx`, gather/permute (read at a computed
      index), and eventually a producer interface in the style of Rayon's
      indexed parallel iterators -- all without exposing chunk boundaries
      to callbacks.
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
- [ ] Isolate the `mapIO` success-path overhead. A trivial `IO` mapper
      remains slower than its serial control at every measured width. The
      `tabulate-io-cheap` control has excluded most of the previously
      proposed causes: direct `tabulateIO` runs the same monadic worker,
      error bookkeeping, and ordered merging at a fraction of `mapIO`'s
      cost on the same index function. The remaining suspect is how
      `mapIO`'s composed reading callback is constructed and
      specialised.
- [ ] Add deterministically shuffled or replayed cost distributions to the
      benchmark (the clustered case covers the adversarial-for-static
      extreme; shuffled covers the no-spatial-structure one).
- [ ] Rotate configuration order between repetition rounds: execution order
      is fixed within a process, so slow thermal and allocator drift stays
      correlated with configuration.
