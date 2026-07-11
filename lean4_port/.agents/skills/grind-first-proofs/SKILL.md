---
name: grind-first-proofs
description: >-
  Construct Lean 4 proofs grind-first. Invoke
  BEFORE writing any non-trivial proof or tactic block in a .lean file, so
  proofs come out minimal and automation-forward the first time instead of being
  written verbose and golfed later. Covers the grind hint taxonomy, what
  grind will NOT do (and the one scaffold to hand it), which tactics fold into
  grind, and the repo's proof-style constraints. Not for Coq/Agda/Isabelle.
---

# Grind-first proof construction

Goal: **write the golfed proof directly.** In this codebase almost every
"simple property" closes with `grind` + the right hints; the manual parts are a
small, predictable set. Reach for `grind` *first*, and only add scaffolding for
the specific things grind provably won't do.

## The recipe

1. **State the goal, then try `grind [hints]` before any manual tactics.** Pick
   hints from the taxonomy below. Read the goal with `lean_goal` if unsure.
2. **If it fails, identify which "won't-do" case you hit** (list below) and hand
   grind *exactly that one scaffold* — a witness, a constructor term, a `cases`,
   or a hinted type — then let grind finish the rest. Do not fall back to a full
   manual chain.
3. **Verify with `lake build <Module>` and grep `error:`** (not just `error` —
   that catches "build failed" meta-lines and miscounts). A quick "no
   goals"/success from an interactive checker can mislead on `∃`/structure
   goals — a real build is the only authority.
4. **Identify and minimise hints with `grind?`.** To find a hint set,
   over-hint and let `grind?` cut it down; on success it prints the minimised
   `grind only [...]`, including the tagged library lemmas that fired — names
   you didn't know to hint. It suggests nothing on a failing goal (diagnose
   instead, step 5). Already-`@[grind =]`/`@[simp]`-tagged lemmas fire
   un-hinted; listing them is a lint error.
5. **When grind fails, diagnose.** An unreduced application in the failure
   state names the missing reduction; check the definition's equation lemmas
   (`#check @fn.eq_1`, `eq_2`, `eq_def`) and pick the hint that addresses the
   cause. Shotgunning a broad hint set to unlodge a stuck grind is fine — but
   once it closes, understand which hint did the work and minimise (step 4);
   don't stop at the first hint soup that happens to build.

## What to hand grind (hint taxonomy)

- **A structure/def TYPE — to BUILD or DESTRUCTURE it.** `grind [Bounded]`,
  `grind [DartOfWF]`, `grind [Unionfind.WF]`. Hinting the type lets grind build
  the record (intro ∀, case-split disjuncts, fill fields) AND destructure a
  hypothesis of that type, exposing its `∀`-fields as ground e-matchable facts.

- **A bridge lemma** — the one connector, usually `isSome → ∃`, a `get?`/decode,
  or an array-read characterisation (`getElem!_setIfInBounds`,
  `getElem!_replicate_replicate`). "grind failed" is usually one bridge short.
  Handing a read-bridge to grind also shortens that bridge's *consumers*.

- **A def whose numeral/guard must reconcile** — e.g. `pairBase` (= 2^32): add
  `pairBase` so grind unfolds it consistently and derives the guard itself.

- **`<fn>.eq_def` for a def by `match` with an overlapping catch-all.**
  Hinting `fn` gives `eq_1` (unconditional, fires) but the catch-all's `eq_2`
  is guarded by a negative premise that e-matching never discharges, so those
  branches sit unreduced (the failure state shows opaque `fn …` applications).
  `fn.eq_def` exposes the literal `match` term, which grind splits itself —
  no manual case scaffold needed.

- **Nothing for def-unfolding you might expect to need.** grind unfolds
  `Array.set!`, reducible defs, and splits `ite`/`dite` on its own — do NOT
  prefix `simp only [Array.set!]` or write `by_cases` on a decidable/`ite`.

- **A fold-preserving read equation instead of `unfold f` mid-proof.** State
  `f`'s reads as small lemmas (`f_pos`/`f_neg` via `dif_pos`/`dif_neg`, a
  `getElem_f` via one `simp [f]`) and rewrite/hint those. Unfolding `f` into
  the goal while other lemmas speak about folded `f` makes goals ill-typed at
  `.instances` transparency (brittle instance/simp matching, opaque errors) —
  the bridge keeps `f` folded everywhere and grind-friendly.

## Two failure smells worth knowing

- **A hang (not a failure) usually means two hinted unfolds feed each other**
  — e.g. a decoder def plus a def that reads through it, each rewrite
  spawning the other's trigger terms. Heartbeat limits do NOT stop this;
  bisect the hint set under a wall-clock timeout to find the pair, then keep
  one side folded via a bridge equation.
- **Degenerate equalities in the failure state (`x = x - k`, `n = m + n`)
  mean e-matching mis-instantiated a lemma** whose conclusion pattern is too
  unifiable (sums, shifts). Ground the case split (`by_cases` on the index
  boundary) or hand grind the instantiated fact and let it glue.

## What grind will probably NOT do — write exactly this scaffold

- **Invent an `∃`-witness that's a context term** (a specific `Nat`, `q.head`,
  an obtained `i`). → `refine ⟨w, ...⟩; grind` or `exact ⟨w, ..., by grind⟩`.
  *But* it WILL invent a witness that's a **hinted constructor application**:
  `grind [Chain.step]` closes `∃ l', Chain uf z r l'` itself.
- **Build a constructor-application term to feed another lemma.** `grind
  [Chain.step, Chain.unique]` fails to make `Chain.step hp hpr` and pass it on.
  → `have h := Chain.unique (Chain.step hp hpr) hl'; grind`.
- **Instantiate a bare local `∀`-hypothesis or an `h.field` projection.**
  `grind [h.inrange]` fails. → EITHER apply it explicitly (`exact h.inrange z hz
  p hp`), OR — better — **hint the def/structure TYPE** so grind destructures
  `h` and uses the field itself (see taxonomy).
- **Invert an inductive hypothesis.** To reconcile two `Chain`/`Sound`/… hyps or
  case on how one was built: `cases h <;> grind`. grind won't do the inversion.
- **A bespoke rewrite with a side-condition proof.** `idx?_composeMap
  (h2.size_eq ▸ h1.bounded)`, `mirror_darts`, a `.map`/`.extract` decode —
  grind can't supply the proof argument. Keep that one `rw` manual, grind the
  rest.

## Which tactics fold into grind (don't write them)

- `by_cases X <;> simp [d]` → `grind [d]`.
- `by_cases`/`split`/`rcases` on a decidable / `ite` / membership → `grind`
  (grind does the case analysis; e.g. the pigeonhole's `n ∈ l` split lives
  inside grind via `List.length_erase`'s `ite`).
- `simp only [reducible-def]; grind` → `grind`.
- **Stays manual:** `cases <inductive hyp>` (inversion), an `induction` (grind
  won't recurse), and applying a `∀`-hyp/`ih` at a specific argument.

## Repo proof-style constraints (apply while constructing)

- **No `... at h`** — reason forward / term-mode; prefer `simpa using h`,
  `x ▸ h`, `(set!_ne hwr).trans hw`. Never `simp/rw ... at h; exact h`.
- **Short, high-automation, term-mode where clean.** A `have` is justified only
  when it holds a term grind can't synthesise (a witness or constructor app);
  don't stash a `∀`-fact in a `have` expecting grind to use it — it won't.
- **Comments state the mechanism, not history/metaphor**

## Calibration

"grind failed" / "this looks tight" / "resists automation" is a **lead to
probe**, not a verdict — including your own prior "verified" claims (they only
hold for the exact shape tested; whole-goal `grind` failing says nothing about
scaffold-then-grind, or type-hint-then-grind). Probe with `lake build`.
