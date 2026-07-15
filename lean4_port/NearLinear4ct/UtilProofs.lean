import NearLinear4ct.Util
import NearLinear4ct.MappingProofs

/-!
Machine-checked correctness of `Util`'s algorithms.

- `lexMin_iff_forall_rotateLeft`: **`lexMin` decides "no rotation is
  lexicographically smaller"**, stated in core vocabulary (`List.rotateLeft`,
  `List.Lex`). The proof splits at `lexMin`'s seams: `ltPrefix` decides
  `List.Lex` (`ltPrefix_eq_true_iff_lex`), the suffix walk quantifies it over
  the doubled list (`lexMin_go_eq_true_iff`), and pure list identities turn
  doubled-list suffixes into rotations.
- `Unionfind.indexRoots_wf`: `indexRoots` is a well-formed relabelling, via a
  loop-free functional model (`indexRootsFun`) and a single refinement proof.
- `Unionfind.WF.root_spec` (with `wf_new` / `WF.unite` preservation): parent
  forests stay acyclic, so `root`'s fuel bound `n` always suffices -- `root`
  lands on a root, in range.

The proofs live here, not in `Util.lean`, so the port files keep reading like
the paper; this module is the verification layer (imported by the library
root, so `lake build` checks it).

Reusable machinery: `forIn_range_eq_range'` is the *single* point of
`Std.Legacy.Range` coupling -- the loop reductions factor through it, taking
the loop body as a *hypothesis*, so nothing here depends on the exact
elaborated shape of a `do` block. Accumulator (`yield`-only) loops go straight
to `List.foldl` via core's `forIn_pure_yield_eq_foldl`
(`forIn_range_eq_foldl`); early-return scans use the bespoke `loopGo`
recursion (`forIn_range_eq_loopGo`).
-/

namespace NearLinear4ct

namespace Queue

/-- `push` grows the live length by one. -/
theorem live_push {α} {q : Queue α} {x : α} : (q.push x).live = q.live + 1 := by
  have := q.queue_invariant
  simp only [Queue.live, Queue.push, Array.size_push]; omega

/-- A successful `pop?`, decoded: the front element and the advanced head
(items untouched). -/
theorem pop?_some {α} {q q' : Queue α} {x : α} (h : q.pop? = some (x, q')) :
    q.items[q.head]? = some x ∧ q'.items = q.items ∧ q'.head = q.head + 1 := by
  grind [Queue.pop?]

/-- `pop?` shrinks the live length by one. -/
theorem live_pop {α} {q q' : Queue α} {x : α} (h : q.pop? = some (x, q')) :
    q'.live + 1 = q.live := by
  obtain ⟨hx, hi, hh⟩ := Queue.pop?_some h
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hx
  simp only [Queue.live, hi, hh]; omega

/-- An exhausted `pop?` means an empty queue. -/
theorem pop?_none {α} {q : Queue α} (h : q.pop? = none) : q.isEmpty = true := by
  grind [Queue.pop?, Queue.isEmpty, Array.getElem?_eq_none]

end Queue

/-! ### Generic loop reduction -/

/-- Structural recursion computing a pure `forIn` over `List.range' i n 1`. -/
def loopGo (f : Nat → σ → ForInStep σ) : Nat → Nat → σ → σ
  | _, 0, s => s
  | i, n + 1, s =>
    match f i s with
    | .done t => t
    | .yield t => loopGo f (i + 1) n t

/-- A pure-bodied `forIn` over `List.range'` is `loopGo`. The body is
characterised by the hypothesis `hbody`, so callers never need to match the
elaborated `do`-block syntactically. -/
private theorem forIn_range'_eq_loopGo {σ : Type _}
    (body : Nat → σ → Id (ForInStep σ)) (f : Nat → σ → ForInStep σ)
    (hbody : ∀ i s, body i s = pure (f i s)) :
    ∀ (n i : Nat) (s : σ),
      forIn (List.range' i n 1) s body = pure (loopGo f i n s)
  | 0, _, _ => rfl
  | n + 1, i, s => by
    rw [List.range'_succ, List.forIn_cons, hbody]
    simp only [pure_bind]
    cases hf : f i s with
    | done t => simp [loopGo, hf]
    | yield t =>
      simp only [loopGo, hf]
      exact forIn_range'_eq_loopGo body f hbody n (i + 1) t

/-- **The single point of `Std.Legacy.Range` coupling**: `for i in [0:n]`
iterates `List.range' 0 n 1`. Both reductions below factor through this, so the
legacy-range dependency lives in exactly one lemma (a future switch to another
range type would touch only here). -/
theorem forIn_range_eq_range' {σ : Type _} (n : Nat)
    (body : Nat → σ → Id (ForInStep σ)) (init : σ) :
    forIn [0:n] init body = forIn (List.range' 0 n 1) init body := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range',
      (by simp [Std.Legacy.Range.size] : ([0:n] : Std.Legacy.Range).size = n),
      (rfl : ([0:n] : Std.Legacy.Range).start = 0),
      (rfl : ([0:n] : Std.Legacy.Range).step = 1)]

/-- `forIn_range'_eq_loopGo` at a whole `[0:n]` range (the form every scan
loop's unfold produces). -/
theorem forIn_range_eq_loopGo {σ : Type _} (n : Nat)
    (body : Nat → σ → Id (ForInStep σ)) (f : Nat → σ → ForInStep σ)
    (hbody : ∀ i s, body i s = pure (f i s)) (init : σ) :
    forIn [0:n] init body = pure (loopGo f 0 n init) := by
  rw [forIn_range_eq_range']
  exact forIn_range'_eq_loopGo body f hbody n 0 init

/-- Accumulator (`yield`-only) loops go straight to `List.foldl` via core's
`forIn_pure_yield_eq_foldl` -- no `loopGo` detour. Only the early-return scans
(below) need the bespoke recursion. -/
theorem forIn_range_eq_foldl {σ : Type _} (n : Nat)
    (body : Nat → σ → Id (ForInStep σ)) (g : Nat → σ → σ)
    (hbody : ∀ i s, body i s = pure (.yield (g i s))) (init : σ) :
    forIn [0:n] init body = pure ((List.range' 0 n 1).foldl (fun s i => g i s) init) := by
  have hb : body = fun i s => pure (.yield (g i s)) := by funext i s; exact hbody i s
  rw [forIn_range_eq_range', hb, List.forIn_pure_yield_eq_foldl]

/-! ### `lexMin` decides "no rotation is smaller"

The specification is stated in core vocabulary -- no `List.rotateLeft` of `xs`
is `List.Lex (· < ·)`-below `xs` -- and the proof splits at `lexMin`'s own
seams: `ltPrefix_eq_true_iff_lex` decodes the comparison walker into
`List.Lex`, `lexMin_go_eq_true_iff` decodes the suffix walk into a quantifier
over the doubled list's suffixes, and two pure list facts (`lex_take_iff`,
`take_drop_doubled_eq_rotateLeft`) turn those suffixes into rotations. -/

/-- `ltPrefix` decides `List.Lex (· < ·)` when the left list is at least as
long -- then `Lex`'s nil case ("left ran out first") cannot fire, and the two
walks agree position by position. -/
private theorem ltPrefix_eq_true_iff_lex [Ord α] [LT α] [LE α]
    [Std.LawfulOrderOrd α] [Std.LawfulOrderLT α] [Std.LawfulEqOrd α] :
    ∀ (ys xs : List α), xs.length ≤ ys.length →
      (ltPrefix ys xs = true ↔ List.Lex (· < ·) ys xs)
  | _, [], _ => by grind [ltPrefix, List.not_lex_nil]
  | [], _ :: _, h => absurd h (by simp)
  | y :: ys, x :: xs, h => by
    have ih := ltPrefix_eq_true_iff_lex ys xs (by simpa using h)
    grind [ltPrefix, List.cons_lex_cons_iff, Std.compare_eq_lt,
      Std.LawfulEqOrd.compare_eq_iff_eq]

/-- The suffix walk falls through iff no examined suffix opens below `xs`:
suffix `r` of `ys`, for `r` below the counter's length. -/
private theorem lexMin_go_eq_true_iff [Ord α] (xs : List α) :
    ∀ (cnt ys : List α),
      (lexMin.go xs ys cnt = true ↔
        ∀ r < cnt.length, ltPrefix (ys.drop r) xs = false)
  | [], _ => by simp [lexMin.go]
  | _ :: cnt, [] => by grind [lexMin.go, ltPrefix]
  | _ :: cnt, y :: ys => by
    have ih := lexMin_go_eq_true_iff xs cnt ys
    refine ⟨fun hgo r hr => ?_, fun hall => ?_⟩
    · cases r <;> grind [lexMin.go]
    · have h0 := hall 0 (by simp)
      have hgo : lexMin.go xs ys cnt = true := ih.mpr fun r hr => by
        simpa using hall (r + 1) (by simpa using Nat.succ_lt_succ hr)
      grind [lexMin.go]

/-- `List.Lex` against `xs` reads at most `|xs|` positions of the left list:
when a full-length prefix is available, truncating there does not change the
verdict. -/
private theorem lex_take_iff {r : α → α → Prop} :
    ∀ (ys xs : List α), xs.length ≤ ys.length →
      (List.Lex r (ys.take xs.length) xs ↔ List.Lex r ys xs)
  | _, [], _ => by simp
  | [], _ :: _, h => absurd h (by simp)
  | y :: ys, x :: xs, h => by
    have ih := lex_take_iff (r := r) ys xs (by simpa using h)
    grind [List.cons_lex_cons_iff]

/-- For `r < |xs|`, rotation `r` of `xs` is the `|xs|`-long prefix of the
`r`-th suffix of the doubled list. -/
private theorem take_drop_doubled_eq_rotateLeft (xs : List α) {r : Nat}
    (h : r < xs.length) :
    ((xs ++ xs).drop r).take xs.length = xs.rotateLeft r := by
  grind [List.rotateLeft, List.take_append, List.take_of_length_le,
    Nat.mod_eq_of_lt]

/-- **`lexMin` decides "no rotation is lexicographically smaller."** -/
theorem lexMin_iff_forall_rotateLeft [Ord α] [LT α] [LE α]
    [Std.LawfulOrderOrd α] [Std.LawfulOrderLT α] [Std.LawfulEqOrd α]
    (xs : List α) :
    lexMin xs = true ↔
      ∀ r < xs.length, ¬ List.Lex (· < ·) (xs.rotateLeft r) xs := by
  rw [lexMin, lexMin_go_eq_true_iff]
  refine forall_congr' fun r => imp_congr_right fun hr => ?_
  have hlen : xs.length ≤ ((xs ++ xs).drop r).length := by simp; omega
  rw [← take_drop_doubled_eq_rotateLeft xs hr, Bool.eq_false_iff]
  exact not_congr ((ltPrefix_eq_true_iff_lex _ _ hlen).trans
    (lex_take_iff _ _ hlen).symm)

/-! ### `Unionfind.indexRoots` is a well-formed relabelling

`indexRoots` is a push loop (accumulator, no early return), so its functional
model is a `foldl` (via `forIn_range_eq_foldl`). The model says: entry `i` is `some (rootRank i)` iff `i` is a root, where
`rootRank i` counts the roots before `i` -- so `indexRoots` assigns roots
fresh sequential indices (`WF uf.n uf.numRoots`, strictly monotone), which is
exactly the "relabelling map" its doc comment promises. -/

namespace Unionfind

/-- The compact index `indexRoots` assigns to a root `i`: the number of roots
before it. -/
def rootRank (uf : Unionfind) (i : Nat) : Nat :=
  (List.range i).countP (fun j => uf.parents[j]!.isNone)

/-- The functional model of `indexRoots`. -/
def indexRootsFun (uf : Unionfind) : IndexMap :=
  (Array.range uf.n).map fun i =>
    if uf.parents[i]!.isNone then OptIdx.some (uf.rootRank i) else OptIdx.none

private theorem rootRank_succ (uf : Unionfind) (i : Nat) :
    uf.rootRank (i + 1)
      = uf.rootRank i + (if uf.parents[i]!.isNone then 1 else 0) := by
  simp [rootRank, List.range_succ, List.countP_append, List.countP_cons]

/-- `rootRank` is monotone, strictly across a root: distinct roots get
distinct compact indices. -/
theorem rootRank_lt_rootRank (uf : Unionfind) {i j : Nat} (hij : i < j)
    (hi : uf.parents[i]!.isNone) : uf.rootRank i < uf.rootRank j := by
  induction j with
  | zero => omega
  | succ k ih => grind [rootRank_succ]

/-- The step function of `indexRoots`' loop (state: next index × output). -/
private def indexRootsStep (uf : Unionfind) (i : Nat)
    (s : MProd Nat (Array OptIdx)) : MProd Nat (Array OptIdx) :=
  if uf.parents[i]!.isNone then ⟨s.1 + 1, s.2.push (OptIdx.some s.1)⟩
  else ⟨s.1, s.2.push OptIdx.none⟩

/-- Prefix of the functional model: the output after processing `[0:i)`. -/
private def outPrefix (uf : Unionfind) (i : Nat) : Array OptIdx :=
  (Array.range i).map fun j =>
    if uf.parents[j]!.isNone then OptIdx.some (uf.rootRank j) else OptIdx.none

private theorem outPrefix_succ (uf : Unionfind) (i : Nat) :
    uf.outPrefix (i + 1) = (uf.outPrefix i).push
      (if uf.parents[i]!.isNone then OptIdx.some (uf.rootRank i) else OptIdx.none) := by
  simp [outPrefix, Array.range_succ]

private theorem foldl_indexRootsStep (uf : Unionfind) :
    ∀ (k i : Nat),
      (List.range' i k 1).foldl (fun s j => uf.indexRootsStep j s)
          ⟨uf.rootRank i, uf.outPrefix i⟩
        = ⟨uf.rootRank (i + k), uf.outPrefix (i + k)⟩
  | 0, i => by simp
  | k + 1, i => by
    have := foldl_indexRootsStep uf k (i + 1)
    grind [List.range'_succ, indexRootsStep, rootRank_succ, outPrefix_succ]

/-- **The bridge**: the push loop computes the functional model. -/
theorem indexRoots_eq_fun (uf : Unionfind) : uf.indexRoots = uf.indexRootsFun := by
  unfold indexRoots
  simp only [pure_bind]
  rw [forIn_range_eq_foldl uf.n _ uf.indexRootsStep
        (fun i s => by grind [indexRootsStep])]
  have h0 : (⟨0, Array.mkEmpty uf.n⟩ : MProd Nat (Array OptIdx))
      = ⟨uf.rootRank 0, uf.outPrefix 0⟩ := by
    simp [rootRank, outPrefix]
  rw [h0, foldl_indexRootsStep uf uf.n 0]
  simp [outPrefix, indexRootsFun]

@[simp] theorem size_indexRoots (uf : Unionfind) : uf.indexRoots.size = uf.n := by
  simp [indexRoots_eq_fun, indexRootsFun]

theorem getElem!_indexRoots (uf : Unionfind) {i : Nat} (h : i < uf.n) :
    uf.indexRoots[i]!
      = if uf.parents[i]!.isNone then OptIdx.some (uf.rootRank i) else OptIdx.none := by
  rw [getElem!_pos uf.indexRoots i (by simp [h])]
  simp [indexRoots_eq_fun, indexRootsFun]

/-- Entry `i` is mapped iff `i` is a root (`Test.lean`'s fixture check, proved
universally). -/
theorem isSome_indexRoots_iff (uf : Unionfind) {i : Nat} (h : i < uf.n) :
    (uf.indexRoots[i]!).isSome ↔ uf.parents[i]!.isNone := by
  rw [getElem!_indexRoots uf h]
  by_cases hr : uf.parents[i]!.isNone <;> simp [hr]

/-- `numRoots` is the root count over the whole range -- i.e. `rootRank` at
the end. -/
theorem numRoots_eq_rootRank (uf : Unionfind) : uf.numRoots = uf.rootRank uf.n := by
  rw [numRoots, allRoots, rootRank, ← Array.countP_eq_size_filter,
    ← Array.countP_toList, Array.toList_range]

private theorem get?_indexRoots (uf : Unionfind) {i : Nat}
    (h : i < uf.indexRoots.size) :
    (uf.indexRoots[i]'h).get? = if uf.parents[i]!.isNone then some (uf.rootRank i) else none := by
  rw [← getElem!_pos uf.indexRoots i h, getElem!_indexRoots uf (by simpa using h)]
  split <;> simp

/-- **`indexRoots` is a well-formed relabelling map** `uf.n → uf.numRoots`
(the compact codomain of the quotient renumbering; genuinely *not* `Total` --
non-roots are unmapped by design). -/
theorem indexRoots_wf (uf : Unionfind) :
    IndexMap.WF uf.indexRoots uf.n uf.numRoots := by
  grind [IndexMap.WF, IndexMap.Bounded, size_indexRoots,
    get?_indexRoots, numRoots_eq_rootRank, rootRank_lt_rootRank]

/-! ### `root` totality: `RootsWF` from a preserved acyclicity invariant

`root uf x = rootAux uf x uf.n` follows parent pointers, stuttering once it hits
a root. It lands on a genuine in-range root provided the parent forest is
acyclic and in range -- the `Unionfind.WF` invariant below, which `new`/`unite`
preserve. The fuel `uf.n` suffices because an acyclic chain visits distinct
in-range nodes (the pigeonhole `nodup_lt_length_le`). -/

/-- Following parents `k` then `j` steps = following `k + j` steps: once a root
is hit the walk stutters, so the two agree. The composition law behind
everything else. -/
theorem rootAux_none {uf : Unionfind} {x : Nat} (h : uf.parents[x]! = .none) :
    ∀ j, uf.rootAux x j = x
  | 0 => rfl
  | _ + 1 => by grind [rootAux]

/-- Unfold one step at a non-root: `rootAux x (fuel+1) = rootAux (parent x) fuel`. -/
theorem rootAux_succ_some {uf : Unionfind} {x p : Nat} (h : uf.parents[x]! = .some p)
    (fuel : Nat) : uf.rootAux x (fuel + 1) = uf.rootAux p fuel := by
  grind [rootAux]

theorem rootAux_add (uf : Unionfind) (j : Nat) : ∀ x k,
    uf.rootAux x (k + j) = uf.rootAux (uf.rootAux x k) j := by
  intro x k
  induction k generalizing x with
  | zero => simp [rootAux]
  | succ k ih =>
    cases hpx : uf.parents[x]! with
    | none => simp [rootAux_none hpx]
    | some p => rw [Nat.succ_add, rootAux_succ_some hpx, rootAux_succ_some hpx, ih p]

/-- Once the walk hits a root it stays: `rootAux x k` a root ⇒ more fuel is idempotent. -/
theorem rootAux_stable {uf : Unionfind} {x k : Nat} (h : uf.parents[uf.rootAux x k]! = .none)
    (j : Nat) : uf.rootAux x (k + j) = uf.rootAux x k := by
  rw [rootAux_add]; exact rootAux_none h j

/-- The explicit parent path from `x` to its root `r`. A derivation is finite,
so this encodes acyclicity; its `Nodup` is that content and its length bounds
the fuel `rootAux` needs. -/
inductive Chain (uf : Unionfind) : Nat → Nat → List Nat → Prop where
  | root {x} : uf.parents[x]! = .none → Chain uf x x [x]
  | step {x p r l} : uf.parents[x]! = .some p → Chain uf p r l → Chain uf x r (x :: l)

/-- `rootAux` at the path length reaches the path's root. -/
theorem Chain.rootAux_length {uf : Unionfind} {x r : Nat} {l : List Nat}
    (h : Chain uf x r l) : uf.rootAux x l.length = r := by
  induction h with grind [rootAux_none, rootAux_succ_some]

theorem Chain.isNone {uf : Unionfind} {x r : Nat} {l : List Nat}
    (h : Chain uf x r l) : uf.parents[r]! = .none := by
  induction h with grind

/-- The path's root is in range. -/
theorem Chain.lt {uf : Unionfind}
    (hin : ∀ z, z < uf.n → ∀ p, uf.parents[z]! = .some p → p < uf.n) :
    ∀ {x r l}, Chain uf x r l → x < uf.n → r < uf.n := by
  intro x r l h
  induction h with
  | root _ => exact id
  | step hp _ ih => exact fun hx => ih (hin _ hx _ hp)

/-- Every node on the path is in range. -/
theorem Chain.mem_lt {uf : Unionfind}
    (hin : ∀ z, z < uf.n → ∀ p, uf.parents[z]! = .some p → p < uf.n) :
    ∀ {x r l}, Chain uf x r l → x < uf.n → ∀ z ∈ l, z < uf.n := by
  intro x r l h
  induction h <;> grind

/-- Parent paths are unique (the parent map is a function). -/
theorem Chain.unique {uf : Unionfind} : ∀ {a r₁ r₂ l₁ l₂},
    Chain uf a r₁ l₁ → Chain uf a r₂ l₂ → l₁ = l₂ := by
  intro a r₁ r₂ l₁ l₂ h₁
  induction h₁ generalizing r₂ l₂ <;> intro h₂ <;> cases h₂ <;> grind

/-- A node on the path starts its own (no-longer) subpath. -/
theorem Chain.mem_subchain {uf : Unionfind} : ∀ {a r l z},
    Chain uf a r l → z ∈ l → ∃ l', Chain uf z r l' ∧ l'.length ≤ l.length := by
  intro a r l z h
  induction h <;> grind [Chain.root, Chain.step]

/-- The acyclicity payoff: a parent path repeats no node. -/
theorem Chain.nodup {uf : Unionfind} : ∀ {x r l}, Chain uf x r l → l.Nodup := by
  intro x r l h
  induction h with
  | root _ => simp
  | step hp hpr ih =>
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih⟩
    obtain ⟨l', hl', hle⟩ := hpr.mem_subchain hmem
    have heq := Chain.unique (Chain.step hp hpr) hl'
    grind

/-- **Pigeonhole**: a `Nodup` list of naturals all `< n` has length `≤ n`. -/
theorem nodup_lt_length_le : ∀ (n : Nat) (l : List Nat),
    l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro l _ hlt; cases l with
    | nil => simp
    | cons a t => exact absurd (hlt a (by simp)) (Nat.not_lt_zero a)
  | succ n ih =>
    intro l hnd hlt
    have hle := ih (l.erase n) (hnd.erase n) (by grind [List.Nodup.mem_erase_iff])
    grind

/-- Reachability well-formedness: every representative lands in range, on a
root. Derived from `WF` below. -/
def RootsWF (uf : Unionfind) : Prop :=
  ∀ i, i < uf.n → uf.root i < uf.n ∧ uf.parents[uf.root i]!.isNone

/-- Array read helpers for the `set!`/`replicate` updates in `new`/`unite`. -/
private theorem set!_self {a : Array OptIdx} {i : Nat} {v : OptIdx}
    (h : i < a.size) : (a.set! i v)[i]! = v := by grind

private theorem set!_ne {a : Array OptIdx} {i j : Nat} {v : OptIdx}
    (hne : j ≠ i) : (a.set! i v)[j]! = a[j]! := by grind

private theorem replicate_none_get {n z : Nat} :
    (Array.replicate n (OptIdx.none))[z]! = .none := by grind

/-- **Well-formedness**: every node reaches a root -- the acyclicity content.
The structural half (sizes match, parents in range) is carried by the type
itself (`unionfind_invariant`), so `WF` is exactly what `new`/`unite` must
preserve *semantically*. -/
structure WF (uf : Unionfind) : Prop where
  reaches : ∀ z, z < uf.n → ∃ r l, Chain uf z r l

/-- Under `WF`, `root` lands on a genuine in-range root. The fuel `uf.n` reaches
it because the parent path is `Nodup` and in range, so at most `n` long. -/
theorem WF.root_spec {uf : Unionfind} (h : uf.WF) {x : Nat} (hx : x < uf.n) :
    uf.parents[uf.root x]! = .none ∧ uf.root x < uf.n := by
  obtain ⟨r, l, hl⟩ := h.reaches x hx
  have hlen : l.length ≤ uf.n :=
    nodup_lt_length_le uf.n l hl.nodup (hl.mem_lt uf.unionfind_invariant.2 hx)
  have hroot : uf.root x = r := by
    have hsum : l.length + (uf.n - l.length) = uf.n := by omega
    rw [root, ← hsum, rootAux_stable (hl.rootAux_length ▸ hl.isNone), hl.rootAux_length]
  exact ⟨hroot ▸ hl.isNone, hroot ▸ hl.lt uf.unionfind_invariant.2 hx⟩

theorem WF.rootsWF {uf : Unionfind} (h : uf.WF) : uf.RootsWF := by
  intro i hi
  obtain ⟨h1, h2⟩ := h.root_spec hi
  exact ⟨h2, by simp [h1]⟩

/-- `new n` is well-formed: every node is its own root. -/
theorem wf_new (n : Nat) : (Unionfind.new n).WF where
  reaches := fun z _ => ⟨z, [z], .root (by simp [Unionfind.new, replicate_none_get])⟩

/-- `unite` preserves well-formedness (given both arguments are in range). The
new edge points a root at a *different* root, which cannot reach back, so no
cycle is created: every old chain transports across the single new edge. -/
theorem WF.unite {uf : Unionfind} (h : uf.WF) {x y : Nat} (hx : x < uf.n) (hy : y < uf.n) :
    (uf.unite x y).WF := by
  obtain ⟨hrxn, hrxlt⟩ := h.root_spec hx
  obtain ⟨hryn, hrylt⟩ := h.root_spec hy
  simp only [Unionfind.unite]
  split
  · exact h
  · rename_i hbeq
    obtain ⟨hne, -⟩ : uf.root x ≠ uf.root y ∧ ¬ uf.n ≤ uf.root y := by simpa using hbeq
    have hsz : uf.root x < uf.parents.size := by
      rw [uf.unionfind_invariant.1]; exact hrxlt
    refine ⟨fun z hz => ?_⟩
    obtain ⟨r, l, hl⟩ := h.reaches z hz
    clear hz
    induction hl with
    | @root w hw =>
      by_cases hwr : w = uf.root x
      · subst hwr
        exact ⟨uf.root y, _, .step (set!_self hsz) (.root ((set!_ne hne.symm).trans hryn))⟩
      · exact ⟨w, _, .root ((set!_ne hwr).trans hw)⟩
    | @step w p r l hw hch ih =>
      have hwr : w ≠ uf.root x := by rintro rfl; grind
      obtain ⟨r', l', hr'⟩ := ih
      exact ⟨r', _, .step ((set!_ne hwr).trans hw) hr'⟩

@[simp] theorem size_eachRoot (uf : Unionfind) : uf.eachRoot.size = uf.n := by
  simp [eachRoot]

/-- The `eachRoot` entry read, folded. -/
@[simp] theorem getElem_eachRoot {uf : Unionfind} {i : Nat} (h : i < uf.eachRoot.size) :
    uf.eachRoot[i]'h = uf.root i := by
  simp [eachRoot]

/-- **The keystone**: the quotient relabelling (`eachRoot` then `indexRoots`,
the composition pattern `disjointUnion`/`freeHomomorphism` uses) is a *total,
well-formed* map onto the compact root indices, for any well-formed union-find.
`WF` is provable and preserved by `new`/`unite` (`wf_new`, `WF.unite`), so unlike
the earlier `RootsWF` assumption this holds unconditionally. -/
theorem relabel_wf (uf : Unionfind) (hwf : uf.WF) :
    IndexMap.WF (composeMap (uf.eachRoot.map OptIdx.some) uf.indexRoots) uf.n uf.numRoots
    ∧ IndexMap.Total (composeMap (uf.eachRoot.map OptIdx.some) uf.indexRoots) := by
  have h := hwf.rootsWF
  have hm1wf : IndexMap.WF (uf.eachRoot.map OptIdx.some) uf.n uf.n := by
    simpa [eachRoot, Function.comp_def] using
      (range_map_some_wf (n := uf.n) (codom := uf.n) (f := uf.root)
        (fun i hi => (h i hi).1))
  refine ⟨composeMap_wf hm1wf (uf.indexRoots_wf), ?_⟩
  intro i hi
  have hin : i < uf.n := by simpa using hi
  have hroot := h i hin
  rw [getElem_composeMap (by simpa using hin)]
  simp [getElem!_indexRoots uf hroot.1, hroot.2]

end Unionfind
end NearLinear4ct
