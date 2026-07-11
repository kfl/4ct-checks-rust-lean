import NearLinear4ct.OptIdx

/-!
Phase 1 — shared helpers. Port of `../src/util.hpp`.

Contains `proofAssert` (the L1 proof-obligation primitive), `Unionfind`, `lexMin`
(lexicographically-minimal rotation test), the `FromFile` class (replacing the
C++ `HasFromFile` concept), and the `getObjects` directory loader.
-/

namespace NearLinear4ct

/--
Proof-obligation assert (L1 / R5). **The proof IS the assert**: for the
`check_*` lemmas, "success" is "no obligation fires and the run completes".

Lean's `panic!` is unusable here: it prints a backtrace but **continues and the
process still exits 0** (verified empirically) — a swallowed proof failure would
read as a passed proof. Instead we `throw`, which propagates to `main` and makes
Lean exit non-zero (code 1), matching the C++ `assert`/`exit(1)` that constitutes
the proof. Never use bare `panic!` for a proof obligation.
-/
def proofAssert (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError s!"proof obligation failed: {msg}")

/-- Disjoint-set forest (union-find) without path compression or union-by-rank,
matching `../src/util.hpp`'s `Unionfind`.

R1: the C++ marks a root with `parents[x] < 0` (value `-1`). Here a root is
`none`; an interior node is `some parent`. Mutating operations return an updated
`Unionfind` (the underlying `Array.set` is in-place when uniquely referenced — see
the L3 performance notes). -/
structure Unionfind where
  n : Nat
  parents : Array (Option Nat)
deriving Inhabited

namespace Unionfind

/-- A fresh forest of `n` singletons (C++ `Unionfind(n)`). Named `new` to avoid
clashing with the structure's auto-generated `Unionfind.mk`. -/
def new (n : Nat) : Unionfind := { n, parents := Array.replicate n none }

/-- Representative of `x` (C++ `root`). The C++ recurses with no path
compression, so this is behaviourally identical. `partial` (L5): terminating on a
forest, but not structurally so. -/
partial def root (uf : Unionfind) (x : Nat) : Nat :=
  match uf.parents[x]! with
  | none => x
  | some p => uf.root p

/-- Attach `x`'s tree under `y`'s root (C++ `unite`: `parents[root(x)] = root(y)`). -/
def unite (uf : Unionfind) (x y : Nat) : Unionfind :=
  let rx := uf.root x
  let ry := uf.root y
  if rx == ry then uf
  else { uf with parents := uf.parents.set! rx (some ry) }

def same (uf : Unionfind) (x y : Nat) : Bool := uf.root x == uf.root y

/-- `root(i)` for every `i` (C++ `each_root`). Always total. -/
def eachRoot (uf : Unionfind) : Array Nat :=
  (Array.range uf.n).map (fun i => uf.root i)

/-- The indices that are roots (C++ `all_roots`). -/
def allRoots (uf : Unionfind) : Array Nat :=
  (Array.range uf.n).filter (fun i => uf.parents[i]!.isNone)

/-- A relabelling map: each root gets a fresh sequential index; non-roots map to
`OptIdx.none` (the C++ `-1`). Composes with `eachRoot` via `composeMap` to
renumber a quotient (see P2 `disjointUnion`). -/
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

/-- Lexicographic comparison of two arrays via element `Ord` (the C++ `vector`
`operator<`). Equal-length inputs (rotations) never reach the size tiebreak. -/
def arrCompare [Ord α] [Inhabited α] (x y : Array α) : Ordering := Id.run do
  let n := min x.size y.size
  for i in [0:n] do
    let c := compare x[i]! y[i]!
    if c != Ordering.eq then return c
  return compare x.size y.size

/-- Rotate an array left by one (`std::rotate(begin, begin+1, end)`).
This mutates the buffer when it is unreferenced elsewhere:
`eraseIdx` shifts left in place and leaves capacity slack, so the `push` is
in place too (the head is bound *before* the erase, so that read is a
completed borrow). -/
def rotateLeft1 [Inhabited α] (a : Array α) : Array α :=
  if a.size == 0 then a else
    let x := a[0]!
    (a.eraseIdxIfInBounds 0).push x

/-- Whether `a` is lexicographically minimal among all its rotations
(C++ `lex_min`). -/
def lexMin [Ord α] [Inhabited α] (a : Array α) : Bool := Id.run do
  let mut rotated := a
  for _ in [0:a.size] do
    rotated := rotateLeft1 rotated
    if arrCompare rotated a == Ordering.lt then
      return false
  return true

/-- A FIFO queue for the BFS worklists (`homomorphism`, `freeHomomorphism`,
`resolveDegreeIssues`, `fixOutRules`). Mirrors the pseudocode's `Q ← ∅` /
`Q.push` / `Q.pop` / `Q.empty()` directly, instead of an open-coded
flat-array-plus-head-index. The representation *is* that flat array walked by a
head index (same FIFO order as the C++ `std::queue`, without ring-buffer
bookkeeping), so there is no perf cost over the open-coded form — only the
bookkeeping is named. -/
structure Queue (α : Type) where
  items : Array α
  head : Nat
deriving Inhabited

namespace Queue

/-- The empty queue (pseudocode `Q ← ∅`). -/
def empty : Queue α := ⟨#[], 0⟩

/-- An empty queue whose backing array reserves `cap` slots, so `push` does not
reallocate until `cap` is exceeded (avoids the `lean_copy_expand_array` regrowth
in the BFS hot loops, where the final size is known up front). -/
def emptyWithCapacity (cap : Nat) : Queue α := ⟨Array.mkEmpty cap, 0⟩

/-- A queue seeded with `xs` (the initial obligations). -/
def ofArray (xs : Array α) : Queue α := ⟨xs, 0⟩

/-- Whether the queue is exhausted (pseudocode `Q.empty()`). -/
def isEmpty (q : Queue α) : Bool := q.head ≥ q.items.size

/-- Number of not-yet-popped elements (`push` +1, `pop!` −1). Used as a
termination measure in the proofs. -/
def live (q : Queue α) : Nat := q.items.size - q.head

/-- Enqueue `x` (pseudocode `Q.push(x)`). `@[inline]` so the wrapper `Queue`
rebuild is visible to the caller's reuse analysis (Perceus cannot reuse
constructors across a call boundary). -/
@[inline] def push (q : Queue α) (x : α) : Queue α := { q with items := q.items.push x }

/-- Dequeue the front element (pseudocode `x ← Q.pop()`); the head advances.
Assumes the queue is non-empty — guard with `isEmpty` (as the BFS loops do).
`@[inline]` so the returned tuple and rebuilt `Queue` are visible to the
caller's reuse analysis instead of being fresh allocations per pop. -/
@[inline] def pop! [Inhabited α] (q : Queue α) : α × Queue α :=
  (q.items[q.head]!, { q with head := q.head + 1 })

end Queue

/-! ### Parallel combinators (pure, `Task`-based, order-preserving)

A small vocabulary of order-preserving parallel patterns. Each spawns its work on
the `Task` scheduler and joins in index order, so the result is **identical to the
sequential version regardless of thread count** — valid for a read-only `f` over
shared immutable data (R4). The parallelism is wall-clock only; it never changes
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
invocation fails (L7 / R4). Replaces the C++ `boost::asio::thread_pool` + per-item
`post`. Each `f x` is spawned as a `Task`; we then join every task and re-raise the
first error — so a failing `proofAssert` inside a worker aborts the process with a
non-zero exit (L1), matching the C++ `assert` abort. The closures only read shared
immutable data (shared by reference-counting, not copied), so results are
thread-count independent. -/
def parForEach (xs : Array α) (f : α → IO Unit) : IO Unit := do
  let tasks ← xs.mapM (fun x => IO.asTask (f x))
  for t in tasks do
    match t.get with
    | .ok _ => pure ()
    | .error e => throw e

/-- A type loadable from a single file (replaces the C++ `HasFromFile` concept).
`fromFile` runs in `IO` because parsing reads the file; like the C++ it may fail
(throw) on malformed input. -/
class FromFile (α : Type) where
  fromFile : System.FilePath → IO α

/-- Load every regular file in `dir` whose extension matches `extension`
(e.g. `".rule"`), as `α`, **sorted by path** (C++ `get_objects`).

R3: ordering is observable (it defines the `combined_flag` rule order, see
`../FORMAT.md`), so we sort explicitly rather than rely on filesystem order.
`System.FilePath.extension` yields the suffix without the leading dot, while the
C++ `fs::path::extension` includes it; we normalise so callers can pass ".rule". -/
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
  -- load order (R3, the `combined_flag` indexing) is unchanged.
  parMapM paths FromFile.fromFile

end NearLinear4ct
