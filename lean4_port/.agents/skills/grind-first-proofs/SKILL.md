---
name: grind-first-proofs
description: >-
  Construct Lean 4 proofs with `grind` before writing non-trivial manual tactic
  blocks. Use for proofs in this repository to select useful hints, add only the
  scaffolding `grind` cannot synthesise, minimise the result with `grind?`, and
  follow the repository's proof-style constraints. Not for Coq, Agda, or
  Isabelle.
---

# Grind-first proof construction

## Workflow

1. State the goal and try `grind [hints]` before writing manual tactics. For an
   inductive argument, first try `induction x <;> grind [hints]`; introduce any
   bound needed by the induction hypothesis before the induction.
2. If the probe fails, inspect the remaining goal and add one necessary
   scaffold: a witness, constructor term, `cases`, `induction`, or explicit
   rewrite. Let `grind` handle the surrounding case splits and arithmetic.
3. Once the proof closes, run `grind?` to identify a minimal `grind only [...]`
   hint set. Do not list lemmas already available through `@[grind]` or
   `@[simp]` attributes.
4. Verify the containing target with `lake build <Module>`. When inspecting
   build output, search for `error:` rather than the broader word `error`.

## Choosing hints

- Hint a structure or predicate type, such as `LoopInv` or `Forest.WF`, when
  `grind` must construct it or expose quantified fields from a hypothesis.
- Hint a bridge lemma for representations: `isSome` to an existential,
  encoded-to-decoded reads, or reads after an array update.
- Hint a named constant when folded and unfolded forms must agree.
- For a match definition with an overlapping catch-all, prefer `fn.eq_def`.
  Hinting `fn` may expose only an unconditional equation and leave the guarded
  branch opaque.
- Keep a definition folded when other lemmas mention its folded form. Prove a
  small read equation, such as `getElem_f`, and give that equation to `grind`
  instead of unfolding the definition throughout the goal.

Do not pre-emptively unfold reducible definitions or split `ite`/`dite` terms;
`grind` normally handles these itself.

## Manual scaffolds

Use manual syntax only for terms or inversions that automation does not invent:

- Supply a specific existential witness with `refine ⟨w, ...⟩; grind`.
  A hinted constructor may be enough when the witness is that constructor
  application.
- Build a constructor or proof term explicitly when it must be passed to
  another lemma, then use `grind` for the remaining facts.
- Use `cases h <;> grind` to invert an inductive hypothesis; use
  `induction x <;> grind` for recursion.
- Keep a bespoke `rw` manual when its proof argument must be assembled from
  transports or projections.
- Apply a projection explicitly when `grind [h.field]` cannot discover its
  instantiation, or hint the enclosing structure type so the field is exposed.

## Diagnosing failures

- An unreduced application usually identifies the missing equation or bridge.
  Check the definition's generated equations (`eq_1`, `eq_2`, `eq_def`).
- If a broad probe works, use `grind?` and remove hints until the relevant one
  is clear.
- If elaboration hangs, check whether two hinted unfolds generate terms that
  trigger each other; keep one side folded behind a bridge lemma.
- Degenerate equalities such as `x = x - k` can indicate a bad e-matching
  instantiation. Ground the boundary case or provide the correctly instantiated
  fact.

## Repository proof style

- Do not rewrite hypotheses in place with `... at h`. Prefer forward reasoning
  and terms such as `simpa using h`, `x ▸ h`, or `h₁.trans h₂`.
- Keep proofs short and automation-forward. Introduce a `have` only for a term
  automation cannot synthesise, not merely to restate a quantified fact.
- Comments describe the proof mechanism, not the history of attempts.
- Treat a failed `grind` probe as evidence about that goal shape, not as proof
  that automation cannot solve a nearby formulation.
