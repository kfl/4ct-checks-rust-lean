# Fidelity to the paper's pseudocode

The canonical spec for this port is the **Appendix A pseudocode** of
`../2603.24880v2.pdf`. This document is the auditor's aid: it records how the
Lean realizes that pseudocode -- the correspondence, the deliberate deviations,
the cross-cutting design decisions, and what has been reduced to machine-checked
proof. Everything here is measured against the paper alone.

Fidelity is established two ways:

- **Behavioural** -- the byte-exact oracle tests (`lake exe test`, 137 oracles)
  and the differential harness (`p7_differential.sh`) pin the output to the
  reference implementation.
- **Structural** -- naming follows the appendix (lowerCamelCase, terse), so each
  routine maps to a like-named Lean function. The code is an article supplement,
  so there are no glossaries or renames.

## Correspondence: a 1:1 transcription of Appendix A

Every routine in Appendix A (A.2 `homomorphism` through A.10's cartwheel-combine
checks) ports to a like-named Lean function in the module for its section:
`PseudoTriangulation`, `PseudoConfiguration`, `Configuration`, `CartWheel`,
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
- **Panics vs. proof obligations.** The spec's `assert` lines split by kind:
  genuine invariants (`assert C = 0`, `d ∈ {7, 8}`) are `proofAssert` (always-on,
  aborting); input-wellformedness failures (malformed parse, unreachable
  `assert false` tails) are `panic!`. Only the former are candidate proof
  obligations.

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
- **Worklists are `Util.Queue`.** One named `Queue` (`push`/`pop!`/`isEmpty`)
  backs all four BFS sites, so each loop reads
  `while !q.isEmpty do let (x, q') := q.pop!` -- the pseudocode's
  `while not Q.empty()` / `x <- Q.pop()`.
- **`assert` lines are `proofAssert`** -- executable, always-on obligations that
  abort, keeping each spec assertion a literal line.
- **Imperative stays imperative -- except `homCore`.** The BFS and enumeration
  routines are written imperatively *in the paper*; rewriting them as folds would
  read further from the spec, not closer, so they are left imperative on purpose.
  The one exception is the `homomorphism` BFS (`homCoreGo`), written as an
  explicit tail-recursive `partial def` rather than `Id.run do`/`while`, for two
  reasons: (1) it is the hottest loop in the program, and the recursive form is
  faster -- the `while` lowering adds per-iteration reference-counting and
  heartbeat that explicit argument threading avoids (~1.21x on that loop); and
  (2) as a `partial_fixpoint` it exposes `.partial_correctness`, the induction
  principle the soundness and completeness proofs ride on. The worklist and early
  exits still read as the pseudocode's; only the loop's host construct differs.
- **Degrees are `Nat`, curvature is `Int`.** A degree is `>= 1` (validated at
  load by `assertDegreesValid`); the signed curvature `10*(6-d)` coerces the
  degree to `Int`, so the `Nat` representation carries the natural invariant
  without changing the signed charge arithmetic.

## What is machine-checked

These reduce a representation or algorithm claim to theorems rather than tests:

- **The map layer** (`MappingProofs.lean`): a well-formed `IndexMap` *is* the
  paper's `ϕ★ : X → Y ∪ {⊥}` between finite index sets (decode `toFun`);
  `initialMappings` *is* `id_X`, `composeMap` *is* Kleisli composition, and
  `splitMap` *is* restriction along the disjoint-union domain.
- **Homomorphism soundness and completeness** (`HomomorphismProofs.lean`): the
  BFS decides the paper's homomorphism predicate. `IsRootedHom` transcribes the
  spec; the `Bounded` invariant gives output well-formedness; the `Sound`
  invariant gives `homCore_sound` / `homomorphismExists_sound` (no false
  positives), and a fuel-based total twin gives completeness (no false
  negatives).
- **`lexMin`** (`UtilProofs.lean`): the lexicographic-minimum loop matches its
  loop-free functional specification.
- **Union-find relabelling** (`UtilProofs.lean`): `indexRoots` is a well-formed,
  total relabelling onto the compact root indices (conditional on the
  reachability lemma `RootsWF`, which awaits `root` becoming non-`partial`).

Everything else rests on the byte-exact oracles above -- faithful by test, not
yet by proof.
