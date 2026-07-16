# Fidelity to the near-linear-4CT paper

The paper "The Four Color Theorem with Linearly Many Reducible
Configurations and Near-Linear Time Coloring"
(https://arxiv.org/abs/2603.24880v2) gives a Four Color Theorem proof
that uses only *linearly* many reducible configurations, together with
a near-linear-time 4-colouring algorithm. This port implements the
paper's checking pseudocode.

This file gives an overview of how the Lean code in the repo
corresponds to the paper's pseudocode -- the correspondence, the
deliberate deviations, the cross-cutting design decisions, and what
has been reduced to machine-checked proof. The reference is the
**Appendix A pseudocode** of v2 of the arXiv paper (local copy at
`../2603.24880v2.pdf`, not in repo).

Fidelity is established two ways:

- **Behavioural** -- the byte-exact oracle tests (`lake exe test`, 137 oracles)
  and the differential harness (`p7_differential.sh`) pin the output to the
  reference C++ implementation. The on-disk file formats it parses and emits
  (configurations, rules, combined rules, cartwheels) are specified
  byte-for-byte in `../FORMAT.md`.

- **Structural** -- naming follows the appendix (lowerCamelCase, terse), so each
  routine maps to a like-named Lean function. The code is an article supplement,
  so there are no glossaries or renames.

## Correspondence: a 1:1 transcription of Appendix A

Every routine in Appendix A (A.2 `homomorphism` through A.10's cartwheel-combine
checks) ports to a like-named Lean function in the module for its section:
`PseudoTriangulation`, `PseudoConfiguration`, `Configuration`, `Cartwheel`,
`CombineCartwheel`. The pseudocode's imperative shape is preserved -- `Queue`
worklists, early exits, in-place updates -- so the code reads as it does on the
page. Only the deviations below depart from a literal transcription.

## Deliberate deviations

- **A.3.1 root compaction.** The paper's identification map lands in the *root
  subset* of the original indices; the port compacts roots to `[0, numRoots)`
  via `Unionfind.indexRoots`. This is a refinement of A.3.1's codomain, not a
  departure -- the `toFun` theorems in `MappingProofs.lean` describe exactly that
  compaction.

- **Named flags (A.9.14, A.10.1).** `fixOutRules`'s `refined_flag` +
  double-`break` becomes `firstRefinable : Option (Nat × Rule)` ("the first
  refinable spoke/rule"), then `match`ed; `deleteDegreeFromKTo9` is a `filterMap`
  ("remove iff a fixed-`k` vertex exists, else collapse `[k-1, 9]`") rather than
  a scan-with-`break`. Same behaviour, named intent.

- **A.3 adjacency steps as named helpers.** The gluing loop's two three-way
  `succ`/`pred` matches are lifted verbatim into `glueSucc`/`gluePred`
  (`PseudoTriangulation.lean`), each returning the darts/queue it may touch;
  the union-find logic stays inline, so the loop keeps the pseudocode's shape.
  Behaviour is unchanged (byte-exact oracles) and the compiled code is
  IR-verified identical modulo shared join points -- the `@[inline]` helpers
  leave no calls or extra allocations. The factoring exists for the proofs:
  each helper carries a three-case specification lemma, replacing the nine-way
  cross-product a monolithic loop body forces on the verifier.

- **Panics vs. proof obligations.** The spec's `assert` lines split by kind:
  genuine invariants (`assert C = 0`, `d ∈ {7, 8}`) become `proofAssert`;
  input-wellformedness failures (malformed parse, unreachable `assert false`
  tails) are `panic!`. Only the former are candidate proof obligations. (What
  `proofAssert` is, and why not `assert!`, is under Cross-cutting design
  decisions.)

## Cross-cutting design decisions

- **The type hierarchy is `extends`.** "A configuration *is* a
  pseudo-triangulation with degrees" -- fields and parent methods are inherited
  (`pc.firstDart`, `cw.center`), matching the math's is-a relationship.

- **Null / boundary is `OptIdx`.** A dart with no successor is
  `Dart.succ`/`pred : OptIdx`, a compact `Option Nat` whose `OptIdx ≃ Option Nat`
  is machine-checked (`OptIdx.lean`). The BFS reads in `none`/`some`/`isSome`
  terms (spec clarity) but stores unboxed (Lean has no niche optimisation, so
  `Array (Option Nat)` would box each `some`). The verification is what lets a
  sentinel-style representation appear in a public, audited type.

- **Packed queue element is `SmallNatPair`.** The homomorphism BFS worklist is a
  `Queue SmallNatPair`: each `(f, fStar)` dart pair is packed into one `Nat`
  (`f * 2^32 + fStar`, via `pack`/`fst`/`snd`). As a single-field structure over
  `Nat` it *is* a `Nat` at runtime (a pointer-tagged scalar below `2^63`), so
  `Array SmallNatPair` is a dense scalar array -- versus `Array (Nat × Nat)`,
  which heap-allocates and reference-counts a pair cell per entry. The round-trip
  is machine-checked (`fst_pack`/`snd_pack` under `s < 2^32`, `SmallNatPair.lean`):
  the same verified-compact-encoding move as `OptIdx`, so the packing can appear
  in the audited BFS. The packing is usable in *this* project because what it
  holds -- dart indices into constant-size configurations and cartwheels -- is
  guaranteed small enough for the encoding to be valid, and the loader checks
  that bound at read time (see "What is machine-checked").

- **Worklists are `Util.Queue`.** One named `Queue` (`push`/`pop?`) backs all
  four BFS sites, so each loop reads
  `while let some (x, q') := q.pop? do` -- the pseudocode's
  `while not Q.empty()` / `x <- Q.pop()` as one total step (no partial
  dequeue anywhere). The queue carries its head bound in the type
  (`queue_invariant`, erased at runtime), so the emptiness test doubles as the
  bounds proof and the proofs never thread queue well-formedness.

- **`Configuration` caches its root degree pair.** The containment sweep
  (`containConf`, A.6.6) keys its bucket lookup on the root dart's endpoint
  lower degrees. The reference re-derives the pair from `darts`/`degrees` on
  every visit of every configuration; the port computes it once in
  `Configuration.new` (`rootHeadDeg`/`rootTailDeg`) and the sweep reads the
  fields -- a hoist of a per-configuration constant, not a reordering: the
  sweep runs the same trials in the same order. The cache cannot drift:
  `root_deg_invariant` pins both fields to their derivation (erased at
  runtime), so every construction proves consistency.

- **Pseudocode `assert` lines become `proofAssert`** -- an always-on `IO`
  obligation that *throws* (`throw (IO.userError …)`) on failure, halting the run
  and keeping each spec assertion a literal line.

  A plain Lean `assert!`/`panic!` won't do: a `panic!` prints and returns
  `default` (it aborts only under `LEAN_ABORT_ON_PANIC=1`), so a failed check
  would silently continue with a wrong value.

- **Imperative stays imperative -- except `homomorphism`.** The BFS and
  enumeration routines are written imperatively *in the paper*; rewriting them as
  folds would read further from the spec, not closer, so they are left imperative
  on purpose.

  The exception is the `homomorphism` BFS from Appendix A.2. Its loop body is
  a named single-step function (`homStep` -- pop one obligation, re-check or
  expand it; the pseudocode's loop body) driven by a three-line tail-recursive
  trampoline (`homCoreGo`), rather than `Id.run do`/`while`, for three
  reasons:

    1. it is the hottest loop in the program, and the tail-recursive form is
       faster -- the `while` lowering adds per-iteration reference-counting and
       heartbeat that explicit argument threading avoids (`homStep` is
       `@[inline]`, so the compiled loop is exactly the unfactored code);

    2. as a `partial_fixpoint` the driver exposes `.partial_correctness`, the
       induction principle the soundness proofs ride on; and

    3. the invariant proofs become recursion-free statements about `homStep`
       alone ("one step preserves `Bounded`/`Sound`/`Agrees`"), lifted through
       the driver in a few lines each.

  The `homomorphism`'s worklist and early exits still read as the pseudocode's;
  only the loop's host construct differs. That said, the accumulated distance
  from A.2's text -- the step/driver factoring, the merged `pop?`, the encoded
  `OptIdx`/`SmallNatPair` reads -- is by now large enough that auditing the
  correspondence by eye is no longer trivial. The soundness/completeness
  theorems pin the code to Sec. 9's homomorphism *predicate* (what the BFS
  decides), not to A.2's *algorithm* (how); a machine-checked equivalence
  against a direct transcription of A.2's loop would close that remaining gap,
  and the recursion-free `homStep` is the natural site for it -- transcribe
  A.2's body once and prove it computes the same step.

  A second, smaller exception: the wheel-degree-tuple enumeration (A.9.5's
  `enumDegree` recursion) is a total functional formulation -- shared list
  suffixes, realised into arrays at the boundary -- rather than the spec's
  mutating recursion. Preferred because it is cleaner: total (no `partial`,
  so open to proof), no `!`-reads, no mutable state -- and measured to be faster.
  The enumeration order, and therefore every output file, is unchanged.

  Separately, the *proofs* reformulate the imperative loops as functional models
  throughout -- see "Functional models in the proofs" below.

- **Data parallelism only as obviously-correct combinators.** The reference
  parallelises exactly one stage: the per-cartwheel `check_*` sweeps (a C++
  thread pool), ported as `Util.parForEach`. The port found further
  data-parallel opportunities the reference runs serially -- the
  wheel-enumeration filter (each candidate wheel is tested independently,
  `Cartwheel.lean`), rule expansion (`Rule.lean`), and configuration-file
  parsing (`Configuration.lean`) -- but exploits them only because each packs
  into a pure, order-preserving combinator (`parMap`/`parFilterMap`/`parMapM`):
  one `Task` per element, no shared mutable state, so the parallel run computes
  the same function as the serial run by construction. Anything that would need
  shared state or ad-hoc synchronisation stays serial. The byte-exact oracles
  and the differential run against these parallel defaults.

- **Degrees are `Nat`, curvature is `Int`.** A degree is `>= 1` (validated at
  load by `assertDegreesValid`); the signed curvature `10*(6-d)` coerces the
  degree to `Int`, so the `Nat` representation carries the natural invariant
  without changing the signed charge arithmetic.

## Functional models in the proofs

The executable code stays imperative (above), but the *proofs* almost never
reason about a `do`/`forIn` loop directly. Each imperative loop is reformulated
as a **loop-free functional model**, proved equal to the loop, and all reasoning
happens on the functional side. Two mechanisms:

- **Functional spec + one refinement lemma** -- the `UtilProofs.lean` pattern.
  An algorithmic loop gets a pure specification, its meaning is proved on the
  spec side, and a single refinement shows the imperative loop computes it:
  - `indexRootsFun` refines `indexRoots` (`indexRoots_eq_fun`) -- the union-find
    relabelling.
  - `loopGo` / `List.foldl`: a generic reduction of `forIn` over an index range
    to structural recursion or a fold (`forIn_range_eq_loopGo`,
    `forIn_range_eq_foldl`), so no proof depends on the elaborated `do`-block
    shape -- the sole `Std.Legacy.Range` coupling point is `forIn_range_eq_range'`.

  Code that is already functional needs no model: `lexMin` is proved directly
  against its core-vocabulary specification (`lexMin_iff_forall_rotateLeft`).

- **Fuel-based total twins for `partial` recursion.** A `partial def` /
  `partial_fixpoint` exposes no equational lemmas, so where a proof must recurse
  we add a fuel-indexed total copy:
  - `Unionfind.rootAux` totalises `root` (fuel = `n`); its equational lemmas are
    what make `RootsWF` provable at all.
  - `homCoreGoImp` is a fuel-bounded driver of the *same* `homStep` as
    `homCoreGo`: completeness is ordinary induction on fuel (`homStep_agrees`
    strictly drops the measure) bridged back by a one-split transport, while
    soundness rides directly on `homCoreGo.partial_correctness` -- there is no
    twin body to keep in sync.

The imperative host code is what the byte-exact oracles test; the functional
models are what the proofs reason about.

## What is machine-checked

These reduce a representation or algorithm claim to theorems rather than tests:

- **The compact encodings carry exactly their abstract value** -- this is what
  makes it *valid* to use `OptIdx`/`SmallNatPair` in public, audited types rather
  than just testing them: the encoding is proved sound, so every read is the
  abstract read and the spec is not weakened.
  - `OptIdx` (`OptIdx.lean`; `0 = none`, `i+1 = some i`) encodes the paper's
    `nil` boundary sentinel (a dart with no successor/predecessor) -- which is
    `-1` on disk (`FORMAT.md`: "`a = -1` represents the boundary") and in the C++
    reference, but `0` in memory here. It round-trips with `Option Nat` *both
    ways* (`ofOption_get?`, `get?_ofOption`) and its `isSome` agrees with
    `get?.isSome` (`isSome_eq`) -- a total bijection, no precondition, so every
    `none`/`some`/`isSome`/`idx!` read *is* the `Option Nat` read. And
    `raw_le_iff_get?_lt` proves a raw bound *is* a bound on the decoded index
    (`none = 0` sits below every `some i = i+1`), so the same `darts.size ≤ 2^31`
    load bound keeps every `some i` a pointer-tagged scalar.
  - `SmallNatPair` (`SmallNatPair.lean`; `pack f s = f*2^32 + s`) is a faithful
    pair round-trip (`fst_pack`, `snd_pack`, `pack_fst_snd`) *under* `s < 2^32`.
    The soundness/completeness theorems carry that as a hypothesis
    (`darts.size ≤ pairBase`), and it is *legitimate here because the entities
    are bounded*: the paper's reducible configurations and cartwheels are
    constant-size, and the loader enforces it -- `assertDartCountPackable`
    proof-asserts `darts.size ≤ 2^31 (< pairBase)` when a configuration/rule is
    read (`Configuration.lean`, `Rule.lean`; `2^31` also keeps the pack a
    pointer-tagged scalar). So the packing precondition is a *checked* fact, not
    an assumption -- an over-large graph halts rather than miscomputing.

- **The degree gate is sufficient for the refinement subtraction**
  (`CartwheelProofs.lean`): `Degree` fields are `Nat`, so the one `lower - 1`
  on a loaded degree (`CartWheel.refineNever`, A.9.19) truncates at `0`.
  `refineNever_sub_exact` proves that on gate-valid degrees
  (`assertDegreesValid`, checked on every rule at load) the `Nat` subtraction
  equals the paper's integer arithmetic -- so the load-time check is the only
  check needed. Rule degrees are never written after parsing, and `fixOutRules`
  refines only with rules from the gated array. The port's one other degree
  subtraction, `deleteDegreeFromKTo9`'s `k - 1`, is likewise proved exact
  (`deleteDegreeFromKTo9_sub_exact`); its `k` is never loaded data -- the only
  calls pass the literals `9` and `8`.

- **The map layer** (`MappingProofs.lean`): a well-formed `IndexMap` *is* the
  paper's `ϕ★ : X → Y ∪ {⊥}` between finite index sets (decode `toFun`);
  `initialMappings` *is* `id_X`, `composeMap` *is* Kleisli composition, and
  `splitMap` *is* restriction along the disjoint-union domain.

- **Homomorphism soundness and completeness** (`HomomorphismProofs.lean`): the
  BFS decides the paper's homomorphism predicate. The spec is `IsRootedHom`: a
  transcription of Sec. 9's dart-homomorphism conditions (`head`/`rev` commute,
  `succ`/`pred` where both sides are interior, degree compatibility), *pinned at
  a root dart pairing* `dartFrom ↦ dartTo`. "Rooted" is our descriptor, not the
  paper's -- Sec. 9 says only "homomorphism" -- and it names a fact Sec. 9 relies
  on: such a homomorphism is unique once the image of a single oriented edge is
  chosen, the rest being forced by the dart incidences. Fixing that one image and
  propagating is the paper's own `rootedContainConf` (Algorithm A.6.8), hence the
  name. On that spec, each invariant is preserved by a recursion-free lemma
  about the single step (`homStep_bounded` / `homStep_next_sound` /
  `homStep_agrees`): `Bounded` gives output well-formedness, `Sound` gives
  `homCore_sound` / `homomorphismExists_sound` (no false positives), and
  folding `homStep_agrees` over the fuel-bounded driver gives completeness
  (no false negatives).

- **`lexMin`** (`UtilProofs.lean`): `lexMin` decides "no rotation of the list
  is lexicographically smaller" (`lexMin_iff_forall_rotateLeft`), stated in
  core vocabulary -- `List.rotateLeft` and `List.Lex (· < ·)`.

- **Union-find relabelling** (`UtilProofs.lean`): `indexRoots` is a well-formed,
  total relabelling onto the compact root indices. `root` is total (fuel-bounded)
  and `RootsWF` -- every representative lands on a genuine root -- is proved from
  a `WF` invariant preserved by `new`/`unite`, so `relabel_wf` is unconditional.
  The structural half of well-formedness (one slot per node, parent pointers in
  range) is carried by the type itself (`unionfind_invariant`, erased at
  runtime), so `WF` is exactly the acyclicity content; maintaining the bound in
  `unite` adds a range guard whose skipped write is precisely the one that
  would corrupt the forest (unreachable on in-range inputs -- behaviour is
  unchanged, as the byte-exact oracles confirm).

- **The free homomorphism produces a well-formed, coherent quotient**
  (`PseudoTriangulationProofs.lean`): on a well-formed graph with in-range
  dart pairs, A.3's gluing loop terminates (measure: `3 * numRoots + live`,
  each glue merges two dart classes), the quotient graph is well-formed, and
  the returned vertex/dart maps are total, well-formed relabellings onto its
  index ranges (`Mappings.WF`) -- `freeHomomorphism_wf`. The coherence tier
  (`freeHomomorphism_coherent`) states the quotient-map property: the maps
  commute with every dart field (`head` through the vertex map,
  `rev`/`succ`/`pred` through the dart map) and every requested pair has one
  quotient image. The proof runs Lemma 9.4's uniform `succ`/`pred` argument
  once (`LinkKind`), with mid-loop obligations interpreted by the equivalence
  closure of the merged classes and the still-pending queue (`PendingEq`).
  `freeHomomorphismPair_wf`/`_coherent` restrict both results along
  `disjointUnion` to the two-graph gluing the loaders call. Also
  `fromVRotations_wf`: A.5's loader produces a well-formed graph
  unconditionally.

- **A.4's degree-resolution steps preserve well-formedness**
  (`PseudoTriangulationProofs.lean`): each step the resolution BFS applies to
  a well-formed configuration answers a well-formed one --
  `dartIdentification_wf` (gluing in-range pairs, via `freeHomomorphism_wf`),
  `addBoundaryDarts_wf` (the appended boundary fan and every rewritten link
  stay in the grown dart range), `singleOutLowerDegree_wf` (degree splits
  reuse the dart array unchanged) and `fixSingleDegreeIssue_wf` (the
  dispatcher: over-incidence forces a nonempty graph, so the picked dart and
  its `lower`-th successor are in range; the remaining arms delegate to the
  boundary closure or cannot answer `some`). The BFS driver
  (`resolveDegreeIssues`) is the remaining lift: stating a loop rule for its
  `while` needs A.4.4's termination potential.

Everything else rests on the byte-exact oracles above -- faithful by test, not
yet by mechanised proof.
