import NearLinear4ct.OptIdx
import NearLinear4ct.Degree

/-!
Shared helpers.

Contains `proofAssert` (the proof-obligation primitive), `Unionfind`, `lexMin`
(lexicographically-minimal rotation test), the token helpers for the flat
integer file formats (`FORMAT.md`), the `FromFile` class, and the `getObjects`
directory loader.
-/

namespace NearLinear4ct

/-- Proof-obligation assert. **The proof IS the assert**: for the `check_*`
lemmas, "success" is "no obligation fires and the run completes". Never use
bare `panic!` for a proof obligation -- it prints but **continues with exit
code 0**, so a swallowed failure would read as a passed proof; `throw`
propagates to `main` and exits non-zero. -/
def proofAssert (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError s!"proof obligation failed: {msg}")

/-- Disjoint-set forest (union-find) without path compression or union-by-rank,
matching the C++ `Unionfind`.

The C++ marks a root with `parents[x] < 0` (value `-1`). Here a root is
`none`; an interior node is `some parent`. Mutating operations return an updated
`Unionfind` (the underlying `Array.set` is in-place when uniquely referenced). -/
structure Unionfind where
  n : Nat
  parents : Array (Option Nat)
  /-- One slot per node, and every parent pointer lands in range: a
  `Unionfind` is structurally well-formed by construction (erased at
  runtime). Acyclicity is *not* carried here -- that stays a proof-side
  invariant (`Unionfind.WF`). -/
  unionfind_invariant :
    parents.size = n ∧ ∀ z, z < n → ∀ p, parents[z]! = some p → p < n

instance : Inhabited Unionfind := ⟨⟨0, #[], by simp⟩⟩

namespace Unionfind

/-- A fresh forest of `n` singletons. Named `new` to avoid
clashing with the structure's auto-generated `Unionfind.mk`. -/
protected def new (n : Nat) : Unionfind := ⟨n, Array.replicate n none, by grind⟩

/-- Follow parent pointers from `x` for at most `fuel` steps. The range test
is the comparison `getElem!` would make anyway, minus its panic path: on any
real forest `unionfind_invariant` keeps every followed pointer in range, so
the `else` is dead code and every read is proof-carrying. -/
def rootAux (uf : Unionfind) : Nat → Nat → Nat
  | x, 0 => x
  | x, fuel + 1 =>
    if h : x < uf.parents.size then
      match uf.parents[x] with
      | none => x
      | some p => uf.rootAux p fuel
    else x

/-- Representative of `x`. The C++ recurses with no path compression, so this is
behaviourally identical on a well-formed forest. Total via a fuel bound of
`uf.n`: a well-formed parent chain visits distinct in-range nodes, so `n` steps
always reach a root (proved as `Unionfind.WF.root_spec` in `UtilProofs.lean`).

TODO: revisit whether omitting path compression here is the intended algorithm --
confirm we have not diverged from the reference. -/
def root (uf : Unionfind) (x : Nat) : Nat := uf.rootAux x uf.n

/-- Attach `x`'s tree under `y`'s root: `parents[root(x)] = root(y)`. The
`uf.n ≤ ry` guard skips the write when `y`'s representative is out of range
(only reachable on malformed input, where the C++ would corrupt the forest);
on in-range inputs it never fires, so behaviour is unchanged. -/
def unite (uf : Unionfind) (x y : Nat) : Unionfind :=
  let rx := uf.root x
  let ry := uf.root y
  if h : rx == ry || uf.n ≤ ry then uf
  else
    ⟨uf.n, uf.parents.set! rx (some ry), by grind [Unionfind]⟩

def same (uf : Unionfind) (x y : Nat) : Bool := uf.root x == uf.root y

/-- `root(i)` for every `i`. Always total. -/
def eachRoot (uf : Unionfind) : Array Nat :=
  (Array.range uf.n).map (fun i => uf.root i)

/-- The indices that are roots. -/
def allRoots (uf : Unionfind) : Array Nat :=
  (Array.range uf.n).filter (fun i => uf.parents[i]!.isNone)

/-- A relabelling map: each root gets a fresh sequential index; non-roots map to
`OptIdx.none` (the C++ `-1`). Composes with `eachRoot` via `composeMap` to
renumber a quotient (see `disjointUnion`). -/
def indexRoots (uf : Unionfind) : Array OptIdx := Id.run do
  let mut index : Nat := 0
  let mut out : Array OptIdx := Array.mkEmpty uf.n
  for i in [0:uf.n] do
    if uf.parents[i]!.isNone then
      out := out.push (OptIdx.some index)
      index := index + 1
    else
      out := out.push OptIdx.none
  return out

def numRoots (uf : Unionfind) : Nat := uf.allRoots.size

end Unionfind

/-- Whether `xs` is lexicographically strictly below `ys`; running out of
either list is "not below" (`ltPrefix_eq_true_iff_lex`, `UtilProofs.lean`). -/
def ltPrefix [Ord α] : List α → List α → Bool
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => true
    | .gt => false
    | .eq => ltPrefix xs ys
  | _, _ => false

/-- Whether `xs` is lexicographically minimal among its rotations
(`lexMin_iff_forall_rotateLeft`, `UtilProofs.lean`). Rotation `r` is a prefix
of the `r`-th suffix of the doubled list `xs ++ xs`, so `go` walks those
suffixes -- shared structure, no rotation materialised -- with `xs` as the
rotation counter. -/
def lexMin [Ord α] (xs : List α) : Bool := go (xs ++ xs) xs
where
  go : List α → List α → Bool
    | ys@(_ :: rest), _ :: cnt => if ltPrefix ys xs then false else go rest cnt
    | _, _ => true

/-- A FIFO queue for the BFS worklists (`homomorphism`, `freeHomomorphism`,
`resolveDegreeIssues`, `fixOutRules`). Mirrors the pseudocode's `Q ← ∅` /
`Q.push` directly, with `Q.empty()` / `Q.pop()` merged into the total `pop?`.
The representation is a flat array walked by a head index, so nothing is paid
over the open-coded form -- only the bookkeeping is named. -/
structure Queue (α : Type) where
  items : Array α
  head : Nat
  /-- The head never runs past the backing array: a `Queue` is well-formed by
  construction (erased at runtime), so the proofs never carry a separate
  queue-wellformedness invariant. -/
  queue_invariant : head ≤ items.size

instance : Inhabited (Queue α) := ⟨⟨#[], 0, Nat.le_refl 0⟩⟩

namespace Queue

/-- The empty queue (pseudocode `Q ← ∅`). -/
protected def empty : Queue α := ⟨#[], 0, Nat.le_refl 0⟩

/-- An empty queue whose backing array reserves `cap` slots, so `push` never
regrows mid-BFS (the final size is known up front). -/
def emptyWithCapacity (cap : Nat) : Queue α := ⟨Array.mkEmpty cap, 0, Nat.zero_le _⟩

/-- A queue seeded with `xs` (the initial obligations). -/
def ofArray (xs : Array α) : Queue α := ⟨xs, 0, Nat.zero_le _⟩

/-- Whether the queue is exhausted (pseudocode `Q.empty()`). -/
def isEmpty (q : Queue α) : Bool := q.head ≥ q.items.size

/-- Number of not-yet-popped elements (`push` +1, `pop?` −1). Used as a
termination measure in the proofs. -/
def live (q : Queue α) : Nat := q.items.size - q.head

/-- Enqueue `x` (pseudocode `Q.push(x)`).

`@[inline]` so the wrapper `Queue` rebuild is visible to the caller's reuse
analysis (Perceus cannot reuse constructors across a call boundary). -/
@[inline] def push (q : Queue α) (x : α) : Queue α :=
  ⟨q.items.push x, q.head, by simpa [Array.size_push] using Nat.le_succ_of_le q.queue_invariant⟩

/-- The pseudocode's `Q.empty()` test and `x ← Q.pop()` as one total step:
the front element and the advanced queue, or `none` when exhausted. The
emptiness test *is* the bounds proof (`queue_invariant` makes them the same
fact), so the read is proof-carrying -- no `!`/`?` indexing. For
`while let some (x, q') := q.pop? do` worklist loops. -/
@[inline] def pop? (q : Queue α) : Option (α × Queue α) :=
  if h : q.head < q.items.size then
    some (q.items[q.head], ⟨q.items, q.head + 1, h⟩)
  else none

end Queue

/-! ### Token helpers for the flat integer file formats (`FORMAT.md`) -/

/-- The whitespace-separated tokens of `s`, dropping the empty tokens that
runs of whitespace and newlines produce. -/
def tokens (s : String) : Array String :=
  ((s.split Char.isWhitespace).filterMap (fun t =>
    if t.isEmpty then none else some t.toString)).toArray

/-- Parse an integer token. Panics on anything else: the inputs are
machine-generated artefacts, so a malformed token is a corrupt file. -/
def parseInt (tok : String) : Int :=
  match tok.toInt? with
  | some v => v
  | none => panic! s!"expected integer token, got {tok}"

/-- Decode a vertex row `v lower upper n₁ n₂ ...` of the shared
`.rule`/`.cartwheel` layout (`FORMAT.md`): upper `0` means unbounded
(`INFTY`), and the 1-based neighbour entries shift to 0-based with the `-1`
boundary marker preserved. -/
def parseVertexLine (toks : Array String) : Degree × Array Int := Id.run do
  let lower := (parseInt toks[1]!).toNat
  let upperRaw := (parseInt toks[2]!).toNat
  let upper := if upperRaw == 0 then INFTY else upperRaw
  let mut rot : Array Int := #[]
  for k in [3:toks.size] do
    let v := parseInt toks[k]!
    rot := rot.push (if v != -1 then v - 1 else v)
  return (⟨lower, upper⟩, rot)

/-- Serialise the vertex rows of the shared `.rule`/`.cartwheel` layout, the
write-side counterpart of `parseVertexLine`: `v lower upper n₁ n₂ ...`, all
1-based, upper `INFTY` written as `0`, boundary `-1` kept, a trailing space
per row (`FORMAT.md`). `vRotations` holds each vertex's neighbours 0-based,
as `getVRotations` produces them. -/
def writeVertexLines (degrees : Array Degree) (vRotations : Array (Array Int)) :
    String := Id.run do
  let mut res := ""
  for v in [0:degrees.size] do
    let upper := if (degrees[v]!).upper == INFTY then 0 else (degrees[v]!).upper
    res := res ++ s!"{v + 1} {(degrees[v]!).lower} {upper} "
    for w in vRotations[v]! do
      res := res ++ (if w == -1 then "-1 " else s!"{w + 1} ")
    res := res ++ "\n"
  return res

/-! ### Parallel combinators (pure, `Task`-based, order-preserving)

A small vocabulary of order-preserving parallel patterns. Each spawns its work on
the `Task` scheduler and joins in index order, so the result is **identical to the
sequential version regardless of thread count** -- valid for a read-only `f` over
shared immutable data. The parallelism is wall-clock only; it never changes
results. Centralising the `Task` plumbing here means the parallelism is audited
once, and call sites read as the pattern they are (`parFilterMap`, `parFlatMap`). -/

/-- Parallel `Array.map` (≡ `xs.map f`, order-preserving). -/
def parMap (xs : Array α) (f : α → β) : Array β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map (·.get)

/-- Parallel `Array.filterMap` (≡ `xs.filterMap f`): map in parallel, keep the
`some`s in order. -/
def parFilterMap (xs : Array α) (f : α → Option β) : Array β :=
  (parMap xs f).filterMap id

/-- Parallel flat-map (≡ `(xs.map f).flatten`): map each element to an array in
parallel, then concatenate in order. -/
def parFlatMap (xs : Array α) (f : α → Array β) : Array β :=
  (parMap xs f).flatten

/-- Map an `IO` action over `xs` in parallel, preserving order and re-raising the
first failure. Each `f x` is spawned with `IO.asTask`; results are joined in index
order. For independent IO (e.g. reading + parsing many files), this overlaps the
work across cores. -/
def parMapM (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let tasks ← xs.mapM (fun x => IO.asTask (f x))
  tasks.mapM (fun t => IO.ofExcept t.get)

/-- Run `f` on every element in parallel and fail the whole computation if any
invocation fails. Each `f x` is spawned as a `Task`; we then join every task and
re-raise the first error -- so a failing `proofAssert` inside a worker aborts the
process with a non-zero exit. The closures only read shared immutable data (shared
by reference-counting, not copied), so results are thread-count independent. -/
def parForEach (xs : Array α) (f : α → IO Unit) : IO Unit := do
  let tasks ← xs.mapM (fun x => IO.asTask (f x))
  for t in tasks do
    match t.get with
    | .ok _ => pure ()
    | .error e => throw e

/-- A type loadable from a single file. `fromFile` runs in `IO` because parsing
reads the file; it may fail (throw) on malformed input. -/
class FromFile (α : Type) where
  fromFile : System.FilePath → IO α

/-- Load every regular file in `dir` whose extension matches `extension`
(e.g. `".rule"`), as `α`, **sorted by path**.

Ordering is observable (it defines the `combined_flag` rule order, see
`../FORMAT.md`), so we sort explicitly rather than rely on filesystem order.
`System.FilePath.extension` yields the suffix without the leading dot; we
normalise so callers can pass ".rule". -/
def getObjects (α : Type) [FromFile α] (dir : System.FilePath) (extension : String) :
    IO (Array α) := do
  let want : String :=
    if extension.startsWith "." then (extension.drop 1).toString else extension
  let entries ← dir.readDir
  let mut paths : Array System.FilePath := #[]
  for entry in entries do
    let p := entry.path
    if !(← p.isDir) && p.extension == some want then
      paths := paths.push p
  paths := paths.qsort (fun a b => decide (a.toString < b.toString))
  -- parse in parallel; `parMapM` preserves the sorted order, so the observable
  -- load order (the `combined_flag` indexing) is unchanged.
  parMapM paths FromFile.fromFile

end NearLinear4ct
