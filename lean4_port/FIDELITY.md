# Fidelity to the paper's pseudocode (P9)

The canonical spec for this port is the **Appendix A pseudocode** of
`../2603.24880v2.pdf`. This document is the auditor's aid: it maps each algorithm
to its Lean function and records (a) where the Lean reads **closer to the
pseudocode than the C++ or Rust**, and (b) the clarity simplifications applied.
Behaviour is unchanged — fidelity is proved by the byte-exact tests (`lake exe
test`, 137 oracles) and the differential (`p7_differential.sh`).

Naming follows the appendix (lowerCamelCase, terse) — the code is an article
supplement, so no glossaries or renames (see `[[code-is-article-supplement]]`).

## Cross-cutting: where Lean is closer to the math than C++ *and* Rust

These advantages apply throughout, so they are stated once here rather than
repeated per row.

| Pseudocode notion | Lean | C++ | Rust |
|---|---|---|---|
| "a configuration **is** a pseudo-triangulation with degrees" (the type hierarchy) | `extends` — fields **and** parent methods inherited (`pc.firstDart`, `cw.center`) | `: public` inheritance (matches) | composition (`pc.tri.…`) — an extra indirection the math doesn't have |
| `null` / boundary (a dart with no successor) | `Dart.succ`/`pred : OptIdx` — the verified-unboxed `Option Nat` (`OptIdx ≃ Option Nat` machine-checked); `none` = null, read `isSome`/`idx!` in the hot path (`get?` at cold sites). P13: chosen over `Option Nat` so an `Array Dart` read in the BFS does not reference-count a boxed `Option` per visit (~5%) | `int` with `-1`; `== -1` arithmetic | `Option<usize>` (matches) |
| `x ← Q.pop()`, `Q.push(x)`, `Q.empty()` | `Util.Queue` with `pop!` / `push` / `isEmpty` (P9) | `std::queue` (matches) | `VecDeque` / open-coded `WorkQueue` |
| `return … ≠ null` (homomorphism exists) | `.isSome` on the returned `Option` | `.has_value()` | `.is_some()` |
| `assert C = 0` etc. as literal lines | `proofAssert` — an executable, always-on proof obligation that aborts (L1) | `assert` (matches) | `assert!` (matches) |
| `{ x | P(x) }`, "for all … add to set" | `Array.filterMap` / `Array.filter` | hand `for`+`push`+`break` | iterator `.filter().collect()` |
| "the first `i` such that …" then stop | early `return` inside `Id.run do` (exits all loops) | `flag` + nested `break` | labelled `break 'lbl` |

The `extends` and `Option`-as-`null` rows are the two places Lean beats **both**
references at once: it has the C++'s zero-cost inheritance *and* Rust's
sentinel-free safety, with no composition indirection and no `-1` arithmetic.

## Per-algorithm audit

`Z` = `PseudoTriangulation`, `PC` = `PseudoConfiguration`, `Cfg` =
`Configuration`, `CW` = `CartWheel`, `CC` = `CombineCartwheel` module.

| Appendix | Lean function | Fidelity note |
|---|---|---|
| A.2.1 `homomorphism` | `PC.homomorphism` / `homomorphismExists` | BFS with `Queue`; the four `≠ null` early exits are `return none`; the literal `return Mappings(...) ≠ null` checks become `.isSome`/`homomorphismExists` at call sites. **P11 note:** the scratch and the public `Mappings` use `OptIdx` — the *verified-sound* compact `Option Nat` (`OptIdx.lean`; `OptIdx ≃ Option Nat` is machine-checked). So the loop reads in `none`/`some`/`isSome` terms (P9 clarity) yet stores unboxed (Lean has no niche optimisation, so `Array (Option Nat)` would box each `some`). The verification is what lets a sentinel-style representation appear in a *public, audited* type without weakening R1. **P13 note:** the BFS loop is an explicit tail-recursive `partial def` (`homCoreGo`) rather than `Id.run do`/`while` — 1.21× faster (the `whileM` lowering added per-iteration RC/heartbeat; see `PERF.md` §P13), `partial` because the worklist grows (termination argument + soundness/equivalence recorded as future obligations in `PROOFS.md`). `vmap`/`dmap` are kept as separate `Array OptIdx` (an earlier one-buffer fusion was measured neutral under tail-recursion and reverted for clarity). Behaviour is byte-identical to the spec/C++/Rust (the differential), pending the formal soundness theorem. |
| A.3.1 `freeHomomorphismTriangulation` | `Z.freeHomomorphism` | `Queue` of gluing obligations; union-find roots; `none` boundary in `succ`/`pred` gluing matches the spec's null guards exactly. |
| A.4.1 `dartIdentification` | `PC.dartIdentification` | Returns `Option (PC × Mappings)` — the spec's "loop error / degree-mismatch error → null" become `none` (vs C++ returning a sentinel-laden struct). |
| A.4.3 `freeHomomorphismConfiguration` | `PC.freeHomomorphism` | `match` on the `dartIdentification` `Option`; `none ⇒ #[]` mirrors "if null return ∅". |
| A.4.4 `resolveDegreeIssues` | `PC.resolveDegreeIssues` | `Queue` BFS; the three branch outcomes (`continue` / split / emit) read as the spec's if/else-if/else. |
| A.4.5–A.4.9 | `innerSubdegreeError`, `vertexSingleDegreeIssue`, `fixSingleDegreeIssue`, `addBoundaryDarts`, `singleOutLowerDegree` | Direct; `vertexSingleDegreeIssue : Option Nat` ("a vertex, or none"). `fixSingleDegreeIssue`'s `assert false` tail is `panic!` (provably unreachable). |
| A.5.1 `fromVRotations` | `Z.fromVRotations` | Two-pass dart assignment; malformed-input `throw`s → `panic!` (input wellformedness, not a proof obligation). |
| A.6.1–A.6.8 | `extendFromCutVertices`, `findCutPairs`, `removeRing`, `maximumDegreeDart`, `Cfg.mirror`, `containConf`, `dartsByDegree`, `rootedContainConf` | `removeRing` uses `Option Nat` `old2new` (removed vertex = `none`) vs C++ `-1`. `rootedContainConf` = `homomorphism(...).isSome`. |
| A.7.1–A.7.2 | `blockedByReducibleConfiguration`, `representativeDegree` | `blocked… = (representativeDegree …).all (·.containConf …)` — the "∀ representative, contains a reducible config" reads as one `.all`. |
| A.8.1–A.8.2 | `addRuleToCombination`, `combineRules` | `combineRules` kept pure (the spec returns a set); the driver does I/O. |
| A.9.1–A.9.4, A.9.15 | `alwaysApply`, `neverApply`, `amountOf{,Possible}ChargeSend`, `dominantlyApply` | Each is `homomorphism(...).isSome/.isNone` with the spec's `g`-predicate passed directly as a `Degree → Degree → Bool`. |
| A.9.8–A.9.13 | `fixInRules`, `updateDegreeByRule`, `concreteDegreeExceptTail`, `prune`, `pruneByNonAssociatedRule`, `upperBoundOfCharge` | `prune` is the spec's three-way `or`. `upperBoundOfCharge` is `Int` (curvature `10·(6−d)` is genuinely signed); **P14:** `Degree` fields are now `Nat` (a degree is `≥ 1`; validated at load by `assertDegreesValid`), and this signed curvature coerces `(degreeCenter : Int)` — so the `Nat` representation removes `Int.toNat` from the hot degree-bucket indexing without changing the signed charge arithmetic (`PERF.md` §P14, `PROOFS.md` §3b). |
| A.9.14 `fixOutRules` | `CW.fixOutRules` | `Queue` BFS; the spec's `refined_flag` + double-`break` (lines 8–27) is named `firstRefinable : Option (Nat × Rule)` ("the first refinable spoke/rule"), then `match`ed — clearer than the spec's own flag. |
| A.9.16–A.9.19 | `shouldRefine`, `refinement`, `refineAlways`, `refineNever` | Direct; `U_R`-nonempty `assert` → `panic!` (guaranteed by `shouldRefine`). |
| A.9.21–A.9.22 | `CW.enumBadCartwheels`, `centerDartsByDegree` | The spec's `assert C = 0` / `assert d ∈ {7,8}` / `assert |…| > 0` (lines 7–9) are `proofAssert` — so `enumBadCartwheels : IO …` (the obligations can abort). |
| A.10.1–A.10.12 | `deleteDegreeFromKTo9`, `delete7triangle`, `get7triangle`, `getX`, `containX`, `combineEachCartwheel{,Twice}`, `checkDeg8/7triangle/deg7`, `check88/87/787/77/777` | `deleteDegreeFromKTo9` is a `filterMap` ("remove iff a fixed-`k` vertex exists, else collapse `[k-1,9]`") — closer to the set-builder than the C++ scan-with-`break`. The `check_*` `assert`s are `proofAssert`; the per-cartwheel `thread_pool` `post` is `Util.parForEach`. |

## Simplifications applied in P9

1. **`Util.Queue`** — replaced the open-coded flat-array-plus-`head`-index BFS at
   **four** sites (`homomorphism`, `freeHomomorphism`, `resolveDegreeIssues`,
   `fixOutRules`) with a named `Queue` (`empty`/`ofArray`/`push`/`pop!`/`isEmpty`),
   so each loop reads `while !q.isEmpty do let (x, q') := q.pop!` ≈ the pseudocode's
   `while not Q.empty()` / `x ← Q.pop()`. Same representation (flat array + head
   index), so byte-identical output and **no perf change** (12.75 s vs 12.63 s on
   `combine_rules`, within noise).

Two clarity simplifications were made *before* P9 and are catalogued here:
2. **`firstRefinable`** (in `fixOutRules`) — names the spec's flag+double-`break`.
3. **`deleteDegreeFromKTo9`** as a `filterMap` rather than a scan+`break`.

## Opportunities considered and deliberately not taken

- **Sequential parse cursors** (`Configuration.fromFile`, `Rule.parse`,
  `CartWheel.ofString`): the `idx := idx + 1` / line cursors are inherently
  sequential and **faithfully mirror the C++ `ifs >> x`** stream reads. A "cleaner"
  combinator form would obscure that correspondence — kept as is.
- **`!`-indexing noise** (`arr[i]!`): pervasive but each one matches a direct
  pseudocode array access; mass-converting to proof-carrying indexing would add
  proof obligations (noise) for no fidelity gain. Revisited only in P10 where a
  *measured* hot loop justifies it.
- **Functionalising imperative algorithms**: the BFS/enumeration routines are
  written imperatively *in the paper*; rewriting them as folds would read *further*
  from the spec, not closer. Left imperative on purpose (L3).
- **Homomorphism scratch representation** (`Array (Option Nat)`): a
  clarity-vs-speed question deferred to **P10** — the readable `Option Nat` is kept
  at every audited boundary; any compaction is confined to the internal hot scratch
  behind accessors.
