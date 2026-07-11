import Std.Data.Iterators
import NearLinear4ct.Util
import NearLinear4ct.MappingProofs

/-!
Machine-checked correctness of `Util`'s algorithmic loops.

Each algorithm gets a loop-free functional specification, its meaning proved
on the specification side, and a single refinement proof showing the
imperative loop computes it:

- `arrCompareFun` (first non-`eq` pointwise comparison over the lazy zip,
  else the size tiebreak; no `Inhabited`, no `!`-indexing), refined by
  `arrCompare_eq_arrCompareFun`, decoded by `arrCompareFun_eq_lt_iff` /
  `arrCompare_eq_lt_iff`: **`arrCompare` decides the lexicographic order**.
- `lexMinFun` (no lazily-unfolded rotation compares below `a`), refined by
  `lexMin_eq_lexMinFun`, decoded by `lexMinFun_true_iff` /
  `lexMin_true_iff`: **`lexMin` decides "no rotation is smaller"**.
- `rotateLeftN` with `rotateLeftN_eq_map`: "rotation" in those statements
  means reading every index shifted mod size.

The proofs live here, not in `Util.lean`, so the port files keep reading like
the paper; this module is the verification layer (imported by the library
root, so `lake build` checks it; `Test.lean` builds `lexMin_eq_brute` on it).

Reusable machinery: `forIn_range_eq_range'` is the *single* point of
`Std.Legacy.Range` coupling -- every reduction factors through it, taking the
loop body as a *hypothesis*, so nothing here depends on the exact elaborated
shape of a `do` block. Accumulator (`yield`-only) loops go straight to
`List.foldl` via core's `forIn_pure_yield_eq_foldl` (`forIn_range_eq_foldl`);
only early-return scans need the bespoke `loopGo` recursion, which they resolve
to `List.findSome?` over the index range (`forIn_range_eq_loopGo` +
`loopGo_scan_eq_findSome?`). `arrCompare_eq_findSome?` exposes `arrCompare` in
that normal form, which is what `Test.lean` relates its independent oracle to.
-/

namespace NearLinear4ct

namespace Queue

/-- `push` grows the live length by one (queue well-formed). -/
theorem live_push {α} [Inhabited α] {q : Queue α} {x : α}
    (h : q.head ≤ q.items.size) : (q.push x).live = q.live + 1 := by
  simp only [Queue.live, Queue.push, Array.size_push]; omega

/-- `pop` shrinks the live length by one (non-empty). -/
theorem live_pop {α} [Inhabited α] {q : Queue α} (h : q.isEmpty = false) :
    q.pop!.2.live + 1 = q.live := by
  have : q.head < q.items.size := by
    simp only [Queue.isEmpty, ge_iff_le, decide_eq_false_iff_not, Nat.not_le] at h; exact h
  simp only [Queue.live, Queue.pop!]; omega

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

/-! ### Scan loops are `List.findSome?` over the index range

`arrCompare` (and `Test.lean`'s `lexLt`) are scan loops: probe each index,
early-return on the first hit. That scan *is* the stdlib's `List.findSome?`
on `List.range' i n`, so no bespoke recursion is needed -- the `none` decode
is core's `findSome?_eq_none_iff`, and the `some` decode below merely
re-indexes core's first-hit characterisation into range form. -/

/-- The loop body of a scan (a named function, so per-loop instantiations
share one symbol and `rw` matches syntactically). -/
def scanStep (p : Nat → Option β) (j : Nat) (_ : MProd (Option β) PUnit) :
    ForInStep (MProd (Option β) PUnit) :=
  match p j with
  | some b => .done ⟨some b, PUnit.unit⟩
  | none => .yield ⟨none, PUnit.unit⟩

/-- The scan loop (state: the early-return marker) is `findSome?` over the
index range. -/
theorem loopGo_scan_eq_findSome? (p : Nat → Option β) :
    ∀ (n i : Nat),
      loopGo (scanStep p) i n ⟨none, PUnit.unit⟩
        = ⟨(List.range' i n).findSome? p, PUnit.unit⟩
  | 0, _ => rfl
  | n + 1, i => by
    have ih := loopGo_scan_eq_findSome? p n (i + 1)
    grind [loopGo, scanStep, List.range'_succ]

/-- `findSome?` over an index range falls through iff the probe never fires
(core's `findSome?_eq_none_iff`, in range form). -/
private theorem findSome?_range'_eq_none_iff (p : Nat → Option β) (n i : Nat) :
    (List.range' i n).findSome? p = none ↔
      ∀ j, i ≤ j → j < i + n → p j = none := by
  rw [List.findSome?_eq_none_iff]
  grind

/-- `findSome?` over an index range returns `some b` iff the *first* firing
probe yields `b`. -/
private theorem findSome?_range'_eq_some_iff (p : Nat → Option β) (b : β) :
    ∀ (n i : Nat),
      (List.range' i n).findSome? p = some b ↔
        ∃ j, i ≤ j ∧ j < i + n ∧ p j = some b ∧
          ∀ l, i ≤ l → l < j → p l = none
  | 0, _ => by simp; grind
  | n + 1, i => by
    have ih := findSome?_range'_eq_some_iff p b n (i + 1)
    grind [List.range'_succ]

/-! ### Rotations: `rotateLeftN` and its element view -/

/-- `a` rotated left `k` times (the proof-side power of `rotateLeft1`). -/
def rotateLeftN [Inhabited α] (a : Array α) : Nat → Array α
  | 0 => a
  | k + 1 => rotateLeft1 (rotateLeftN a k)

private theorem size_rotateLeft1 [Inhabited α] (a : Array α) :
    (rotateLeft1 a).size = a.size := by
  grind [rotateLeft1]

private theorem size_rotateLeftN [Inhabited α] (a : Array α) (k : Nat) :
    (rotateLeftN a k).size = a.size := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rotateLeftN, size_rotateLeft1, ih]

/-- Element view of one rotation: index `j` reads the source at `j + 1`,
wrapping at the end. -/
private theorem getElem!_rotateLeft1 [Inhabited α] (a : Array α) (j : Nat)
    (hj : j < a.size) : (rotateLeft1 a)[j]! = a[(j + 1) % a.size]! := by
  -- split at the wrap point: `%` by a variable is outside `grind`'s
  -- arithmetic, so each branch names the applicable modulus law
  rcases Nat.lt_or_ge (j + 1) a.size with hlt | hge
  · grind [rotateLeft1, Nat.mod_eq_of_lt]
  · grind [rotateLeft1, Nat.mod_self]

private theorem rotateLeftN_rotateLeft1 [Inhabited α] (a : Array α) (k : Nat) :
    rotateLeftN (rotateLeft1 a) k = rotateLeft1 (rotateLeftN a k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rotateLeftN, ih]

/-- Element view of `k` rotations: index `j` reads the source at `j + k`
mod size. -/
private theorem getElem!_rotateLeftN [Inhabited α] (a : Array α) (k : Nat) :
    ∀ j : Nat, j < a.size → (rotateLeftN a k)[j]! = a[(j + k) % a.size]! := by
  induction k with
  | zero => grind [rotateLeftN, Nat.mod_eq_of_lt]
  | succ k ih =>
    grind [rotateLeftN, getElem!_rotateLeft1, size_rotateLeftN,
      Nat.mod_lt, Nat.mod_add_mod]

/-- **`rotateLeftN` is what "rotation" means**: rotating `k` times is reading
every index shifted by `k`, mod size (the form `isLexMinBrute` in `Test.lean`
builds by hand). -/
theorem rotateLeftN_eq_map [Inhabited α] (a : Array α) (k : Nat) :
    rotateLeftN a k = (Array.range a.size).map fun j => a[(j + k) % a.size]! := by
  apply Array.ext
  · simp [size_rotateLeftN]
  · intro i h1 h2
    have hi : i < a.size := by simpa [size_rotateLeftN] using h1
    rw [Array.getElem_map, Array.getElem_range,
        ← getElem!_pos (rotateLeftN a k) i h1,
        getElem!_rotateLeftN a k i hi]

/-- Rotating by the full size is the identity. -/
private theorem rotateLeftN_size_self [Inhabited α] (a : Array α) :
    rotateLeftN a a.size = a := by
  apply Array.ext
  · simp [size_rotateLeftN]
  · intro i h1 h2
    have e1 : (rotateLeftN a a.size)[i]! = (rotateLeftN a a.size)[i] :=
      getElem!_pos (rotateLeftN a a.size) i h1
    have e2 : a[i]! = a[i] := getElem!_pos a i h2
    rw [← e1, getElem!_rotateLeftN a a.size i h2, ← e2]
    congr 1
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt h2

/-! ### `arrCompare` decides the lexicographic order

Layered functional-first, like `lexMin` below: `arrCompareFun` is the
loop-free specification -- the first non-`eq` pointwise comparison over the
lazy zip (which stops at the shorter array), else the size tiebreak. Note it
needs no `Inhabited` and no `!`-indexing: the zip hands over the elements.
`arrCompare_eq_arrCompareFun` is the loop-refines-spec bridge, and the
public decode transports across it. -/

/-- Functional specification of `arrCompare`: the first non-`eq` pointwise
comparison over the zip of the two arrays, defaulting to the size tiebreak.
Pull-based iterators give it the loop's exact cost model. -/
def arrCompareFun [Ord α] (x y : Array α) : Ordering :=
  ((x.iter.zip y.iter).findSome? fun p =>
      if compare p.1 p.2 != Ordering.eq then some (compare p.1 p.2) else none).getD
    (compare x.size y.size)

/-- `arrCompare`'s probe in index form: the comparison at `j`, if not `eq`
(the decode workhorse; `arrCompareFun`'s pairwise probe composed with
indexing). -/
private def cmpP [Ord α] [Inhabited α] (x y : Array α) (j : Nat) : Option Ordering :=
  if compare x[j]! y[j]! != Ordering.eq then some (compare x[j]! y[j]!) else none

/-- Pairing elements by index is `zip` (up to the shorter side). -/
private theorem toList_zip_eq_map_range' [Inhabited α] (x y : Array α) :
    x.toList.zip y.toList
      = (List.range' 0 (min x.size y.size)).map fun i => (x[i]!, y[i]!) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hx : i < x.size := by simp at h1; omega
    have hy : i < y.size := by simp at h1; omega
    simp [List.getElem_zip, getElem!_pos x i hx, getElem!_pos y i hy]

/-- `arrCompareFun`, re-indexed to the `findSome?`-over-range normal form. -/
private theorem arrCompareFun_eq_findSome? [Ord α] [Inhabited α] (x y : Array α) :
    arrCompareFun x y
      = ((List.range' 0 (min x.size y.size)).findSome? (cmpP x y)).getD
          (compare x.size y.size) := by
  rw [arrCompareFun, ← Std.Iter.findSome?_toList, Std.Iter.toList_zip_of_finite,
      Array.toList_iter, Array.toList_iter, toList_zip_eq_map_range',
      List.findSome?_map]
  rfl

/-- **The imperative `arrCompare` computes its functional specification.** -/
theorem arrCompare_eq_arrCompareFun [Ord α] [Inhabited α] (x y : Array α) :
    arrCompare x y = arrCompareFun x y := by
  unfold arrCompare
  simp only [Id.run, pure_bind]
  rw [forIn_range_eq_loopGo (min x.size y.size) _ (scanStep (cmpP x y))
        (fun i s => by by_cases h : compare x[i]! y[i]! != Ordering.eq <;>
          simp [scanStep, cmpP, h]),
      loopGo_scan_eq_findSome?, arrCompareFun_eq_findSome?]
  cases (List.range' 0 (min x.size y.size)).findSome? (cmpP x y) <;> rfl

/-- `arrCompare`, in `findSome?` normal form: the first non-`eq` comparison
by index, else the size tiebreak (the computation rule `Test.lean`'s oracle
bridge rewrites against). -/
theorem arrCompare_eq_findSome? [Ord α] [Inhabited α] (x y : Array α) :
    arrCompare x y
      = ((List.range' 0 (min x.size y.size)).findSome? fun j =>
          if compare x[j]! y[j]! != Ordering.eq then some (compare x[j]! y[j]!)
          else none).getD (compare x.size y.size) := by
  rw [arrCompare_eq_arrCompareFun, arrCompareFun_eq_findSome?]
  rfl

/- `arrCompareFun_eq_lt_iff` must rewrite its hypothesis into `compare`-terms
(via the two iffs below) before calling `grind`: `grind [cmpP]` alone does
not solve the first-difference uniqueness goal. -/

private theorem cmpP_eq_none_iff [Ord α] [Inhabited α] (x y : Array α) (j : Nat) :
    cmpP x y j = none ↔ compare x[j]! y[j]! = Ordering.eq := by
  grind [cmpP]

private theorem cmpP_eq_some_iff [Ord α] [Inhabited α] (x y : Array α) (j : Nat)
    (c : Ordering) :
    cmpP x y j = some c ↔ compare x[j]! y[j]! = c ∧ c ≠ Ordering.eq := by
  grind [cmpP]

/-- **`arrCompareFun` decides the lexicographic order** (`lt` case): a first
difference comparing `lt`, or all of the shorter side `eq` and `x` shorter --
proved on the specification side. -/
theorem arrCompareFun_eq_lt_iff [Ord α] [Inhabited α] (x y : Array α) :
    arrCompareFun x y = Ordering.lt ↔
      (∃ i, i < min x.size y.size ∧ compare x[i]! y[i]! = Ordering.lt ∧
        ∀ j, j < i → compare x[j]! y[j]! = Ordering.eq)
      ∨ (x.size < y.size ∧
        ∀ j, j < min x.size y.size → compare x[j]! y[j]! = Ordering.eq) := by
  rw [arrCompareFun_eq_findSome?]
  rcases h : (List.range' 0 (min x.size y.size)).findSome? (cmpP x y) with _ | c
  · rw [findSome?_range'_eq_none_iff] at h
    simp only [cmpP_eq_none_iff] at h
    simp only [Option.getD_none, Nat.compare_eq_lt]
    grind
  · rw [findSome?_range'_eq_some_iff] at h
    simp only [cmpP_eq_some_iff, cmpP_eq_none_iff] at h
    simp only [Option.getD_some]
    grind

/-- **`arrCompare` decides the lexicographic order** -- the specification
meaning, transported across the refinement equality. -/
theorem arrCompare_eq_lt_iff [Ord α] [Inhabited α] (x y : Array α) :
    arrCompare x y = Ordering.lt ↔
      (∃ i, i < min x.size y.size ∧ compare x[i]! y[i]! = Ordering.lt ∧
        ∀ j, j < i → compare x[j]! y[j]! = Ordering.eq)
      ∨ (x.size < y.size ∧
        ∀ j, j < min x.size y.size → compare x[j]! y[j]! = Ordering.eq) := by
  rw [arrCompare_eq_arrCompareFun]
  exact arrCompareFun_eq_lt_iff x y

/-! ### `lexMin` decides "no rotation is smaller"

Layered as functional-first refinement: `lexMinFun` is the loop-free
specification and `lexMinFun_true_iff` gives it meaning by a spec-side
argument (no loop state anywhere); `lexMin_eq_lexMinFun` is the *only*
imperative-side proof (the loop refines the specification); `lexMin`'s
meaning then transports across the equality. -/

/-- Functional specification of `lexMin`, loop-free and with the loop's exact
cost model: `a` is lexicographically minimal iff none of its rotations
`0..a.size - 1` compares strictly below it (rotation `0` is `a` itself).
`Std.Iter.repeat` is the lazy unfold of `rotateLeft1`, and iterator
pipelines are pull-based, so `all` interleaves construction with testing and
stops at the first failure -- O(size²) worst case, early exit after O(size),
no intermediate list. The loop checks rotations `1..a.size` instead; the two
ranges decide the same predicate because rotation `a.size` *is* rotation `0`
(`rotateLeftN_size_self`), so `lexMin_eq_lexMinFun` holds for *every* `Ord`,
lawful or not. -/
def lexMinFun [Ord α] [Inhabited α] (a : Array α) : Bool :=
  (Std.Iter.repeat rotateLeft1 a).take a.size
    |>.all fun r => arrCompare r a != Ordering.lt

/-- The unfold's elements mean what they should: entry `i` of the first `k`
items is the `i`-fold rotation (`toList_take_repeat_succ` is the cons-step). -/
private theorem toList_take_repeat_rotations [Inhabited α] :
    ∀ (k : Nat) (a : Array α),
      ((Std.Iter.repeat rotateLeft1 a).take k).toList
        = (List.range k).map (rotateLeftN a)
  | 0, _ => by simp
  | k + 1, a => by
    simp [Std.Iter.toList_take_repeat_succ,
      toList_take_repeat_rotations k (rotateLeft1 a),
      List.range_succ_eq_map, Function.comp_def,
      rotateLeftN_rotateLeft1, rotateLeftN]

/-- **`lexMinFun` decides "no rotation is lexicographically smaller"** --
proved on the specification side alone (`all` over a `map`), with no loop
state in sight. -/
theorem lexMinFun_true_iff [Ord α] [Inhabited α] (a : Array α) :
    lexMinFun a ↔
      ∀ k, k < a.size → arrCompare (rotateLeftN a k) a ≠ Ordering.lt := by
  rw [lexMinFun, ← Std.Iter.all_toList, toList_take_repeat_rotations,
      List.all_eq_true]
  grind

/-- The loop's `loopGo` refines `lexMinFun`'s scan: the early-return marker
(`getD true`) and `List.all`'s short-circuit agree at every rotation. The
single imperative-side induction. -/
private theorem loopGo_lexMin_eq [Ord α] [Inhabited α] (a : Array α) :
    ∀ (n i : Nat) (r : Array α),
      ((loopGo (fun _ (p : MProd (Option Bool) (Array α)) =>
          if arrCompare (rotateLeft1 p.snd) a == Ordering.lt then
            .done ⟨some false, rotateLeft1 p.snd⟩
          else .yield ⟨none, rotateLeft1 p.snd⟩) i n ⟨none, r⟩).fst.getD true)
        = ((Std.Iter.repeat rotateLeft1 (rotateLeft1 r)).take n).toList.all
            fun x => arrCompare x a != Ordering.lt
  | 0, _, _ => by simp [loopGo]
  | n + 1, i, r => by
    have ih := loopGo_lexMin_eq a n (i + 1) (rotateLeft1 r)
    grind [loopGo, Std.Iter.toList_take_repeat_succ]

/-- The loop's rotation range (`1..a.size`) and the specification's
(`0..a.size - 1`) decide the same scan: rotation `a.size` *is* rotation `0`.
The single place the off-by-one between loop and spec is paid. -/
private theorem all_rotations_succ_eq [Ord α] [Inhabited α] (a : Array α) :
    (((Std.Iter.repeat rotateLeft1 (rotateLeft1 a)).take a.size).toList.all
        fun r => arrCompare r a != Ordering.lt)
      = lexMinFun a := by
  have hstep : ∀ k, rotateLeft1 (rotateLeftN a k) = rotateLeftN a (k + 1) :=
    fun _ => rfl
  rw [lexMinFun, ← Std.Iter.all_toList, Bool.eq_iff_iff,
      List.all_eq_true, List.all_eq_true,
      toList_take_repeat_rotations, toList_take_repeat_rotations]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro h x ⟨i, hi, rfl⟩
    match i with
    | 0 =>
      have h0 := h (rotateLeftN (rotateLeft1 a) (a.size - 1))
        ⟨a.size - 1, by omega, rfl⟩
      rw [rotateLeftN_rotateLeft1, hstep, show a.size - 1 + 1 = a.size by omega,
          rotateLeftN_size_self] at h0
      exact h0
    | i + 1 =>
      have h1 := h (rotateLeftN (rotateLeft1 a) i) ⟨i, by omega, rfl⟩
      rwa [rotateLeftN_rotateLeft1, hstep] at h1
  · rintro h x ⟨i, hi, rfl⟩
    rw [rotateLeftN_rotateLeft1, hstep]
    rcases Nat.lt_or_ge (i + 1) a.size with hlt | hge
    · exact h (rotateLeftN a (i + 1)) ⟨i + 1, hlt, rfl⟩
    · rw [show i + 1 = a.size by omega, rotateLeftN_size_self]
      exact h (rotateLeftN a 0) ⟨0, by omega, rfl⟩

/-- **The imperative `lexMin` computes its functional specification.** -/
theorem lexMin_eq_lexMinFun [Ord α] [Inhabited α] (a : Array α) :
    lexMin a = lexMinFun a := by
  unfold lexMin
  simp only [Id.run, pure_bind]
  rw [forIn_range_eq_loopGo a.size _
        (fun _ p =>
          if arrCompare (rotateLeft1 p.snd) a == Ordering.lt then
            .done ⟨some false, rotateLeft1 p.snd⟩
          else .yield ⟨none, rotateLeft1 p.snd⟩)
        (fun i s => by
          by_cases h : arrCompare (rotateLeft1 s.snd) a == Ordering.lt <;>
            simp [h]),
      ← all_rotations_succ_eq, ← loopGo_lexMin_eq a a.size 0 a]
  rcases loopGo _ 0 a.size _ with ⟨mark, rot⟩
  cases mark <;> rfl

/-- **`lexMin` decides "no rotation is lexicographically smaller"** -- the
specification meaning, transported across the refinement equality.
`rotateLeftN_eq_map` gives `rotateLeftN` its meaning and
`arrCompare_eq_lt_iff` gives `arrCompare`'s. -/
theorem lexMin_true_iff [Ord α] [Inhabited α] (a : Array α) :
    lexMin a ↔
      ∀ k, k < a.size → arrCompare (rotateLeftN a k) a ≠ Ordering.lt := by
  rw [lexMin_eq_lexMinFun]
  exact lexMinFun_true_iff a

/-! ### `Unionfind.indexRoots` is a well-formed relabelling

`indexRoots` is a push loop (accumulator, no early return), so its functional
model is a `foldl`; `loopGo_yield_eq_foldl` below is the yield-only sibling of
`loopGo_scan_eq_findSome?`, reusable for every future accumulator loop. The
model says: entry `i` is `some (rootRank i)` iff `i` is a root, where
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
  | succ k ih =>
    rw [rootRank_succ]
    rcases Nat.lt_or_ge i k with h | h
    · have := ih h; omega
    · have : i = k := by omega
      subst this
      simp [hi]

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
    rw [List.range'_succ, List.foldl_cons]
    have hstep : uf.indexRootsStep i ⟨uf.rootRank i, uf.outPrefix i⟩
        = ⟨uf.rootRank (i + 1), uf.outPrefix (i + 1)⟩ := by
      unfold indexRootsStep
      rw [rootRank_succ, outPrefix_succ]
      split <;> simp_all
    rw [hstep]
    have harith : i + 1 + k = i + (k + 1) := by omega
    have := foldl_indexRootsStep uf k (i + 1)
    rw [this, harith]

/-- **The bridge**: the push loop computes the functional model. -/
theorem indexRoots_eq_fun (uf : Unionfind) : uf.indexRoots = uf.indexRootsFun := by
  unfold indexRoots
  simp only [Id.run, pure_bind]
  rw [forIn_range_eq_foldl uf.n _ uf.indexRootsStep
        (fun i s => by by_cases h : uf.parents[i]!.isNone <;> simp [indexRootsStep, h])]
  have h0 : (⟨0, Array.mkEmpty uf.n⟩ : MProd Nat (Array OptIdx))
      = ⟨uf.rootRank 0, uf.outPrefix 0⟩ := by
    simp [rootRank, outPrefix]
  rw [h0, foldl_indexRootsStep uf uf.n 0]
  simp [outPrefix, indexRootsFun]
  rfl

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

/-- **`indexRoots` is a well-formed relabelling map** `uf.n → uf.numRoots`
(the compact codomain of the quotient renumbering; genuinely *not* `Total` --
non-roots are unmapped by design). -/
theorem indexRoots_wf (uf : Unionfind) :
    IndexMap.WF uf.indexRoots uf.n uf.numRoots := by
  constructor
  · simp
  · intro i h j hj
    rw [← getElem!_pos uf.indexRoots i (by simpa using h),
      getElem!_indexRoots uf (by simpa using h)] at hj
    by_cases hr : uf.parents[i]!.isNone
    · simp [hr] at hj
      subst hj
      rw [numRoots_eq_rootRank]
      exact uf.rootRank_lt_rootRank (by simpa using h) hr
    · simp [hr] at hj

/-- Reachability well-formedness, stated but not yet proved: `root` is a
`partial def`, so its value-level facts are currently unstatable. Records the
intended property -- every representative lands in range, on a root. -/
def RootsWF (uf : Unionfind) : Prop :=
  ∀ i, i < uf.n → uf.root i < uf.n ∧ uf.parents[uf.root i]!.isNone

/-- **The conditional keystone**: the quotient relabelling (`eachRoot` then
`indexRoots`, the composition pattern `disjointUnion`/`freeHomomorphism`
uses) is a *total, well-formed* map onto the compact root indices --
conditional on `RootsWF`. Once `RootsWF` is proved, this upgrades unconditionally. -/
theorem relabel_wf (uf : Unionfind) (h : uf.RootsWF) :
    IndexMap.WF (composeMap (uf.eachRoot.map OptIdx.some) uf.indexRoots) uf.n uf.numRoots
    ∧ IndexMap.Total (composeMap (uf.eachRoot.map OptIdx.some) uf.indexRoots) := by
  have hm1wf : IndexMap.WF (uf.eachRoot.map OptIdx.some) uf.n uf.n := by
    simpa [eachRoot, Function.comp_def] using
      (IndexMap.range_map_some_wf (n := uf.n) (codom := uf.n) (f := uf.root)
        (fun i hi => (h i hi).1))
  refine ⟨IndexMap.composeMap_wf hm1wf (uf.indexRoots_wf), ?_⟩
  intro i hi
  have hin : i < uf.n := by
    simpa [composeMap, eachRoot] using hi
  have hroot := h i hin
  unfold composeMap
  rw [Array.getElem_map]
  simp [eachRoot, getElem!_indexRoots uf hroot.1, hroot.2]

end Unionfind
end NearLinear4ct
