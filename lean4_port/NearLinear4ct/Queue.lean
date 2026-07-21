module

/-!
A FIFO queue with a **private** representation.

The worklist type of the BFS loops. The representation (a flat array walked
by a head index) is private to this file: consumers construct queues with
`empty`/`emptyWithCapacity`/`ofArray`, run them with `push`/`pop?`/`isEmpty`,
and reason through `live` and the `Active` vocabulary -- the lemma suite
below is the queue's entire proof interface, mirroring `OptIdx.lean` and
`SmallNatPair.lean`.
-/

namespace NearLinear4ct

public section

/-- A FIFO queue for the BFS worklists (`homomorphism`, `freeHomomorphism`,
`resolveDegreeIssues`, `fixOutRules`). Mirrors the pseudocode's `Q ← ∅` /
`Q.push` directly, with `Q.empty()` / `Q.pop()` merged into the total `pop?`.
The representation is a flat array walked by a head index, so nothing is paid
over the open-coded form -- only the bookkeeping is named. -/
structure Queue (α : Type) where
  private mk ::
  private items : Array α
  private head : Nat
  /-- The head never runs past the backing array: a `Queue` is well-formed by
  construction (erased at runtime), so the proofs never carry a separate
  queue-wellformedness invariant. -/
  private queue_invariant : head ≤ items.size

namespace Queue

/-- The empty queue (pseudocode `Q ← ∅`). -/
protected def empty : Queue α := ⟨#[], 0, Nat.le_refl 0⟩

instance : Inhabited (Queue α) := ⟨.empty⟩

/-- An empty queue whose backing array reserves `cap` slots, so `push` never
regrows mid-BFS (the final size is known up front). -/
def emptyWithCapacity (cap : Nat) : Queue α := ⟨Array.mkEmpty cap, 0, Nat.zero_le _⟩

/-- A queue seeded with `xs` (the initial obligations). -/
def ofArray (xs : Array α) : Queue α := ⟨xs, 0, Nat.zero_le _⟩

/-- The capacity is a runtime allocation hint only -- the queue's value does
not depend on it. -/
theorem emptyWithCapacity_eq {c c' : Nat} :
    (Queue.emptyWithCapacity c : Queue α) = Queue.emptyWithCapacity c' := by
  grind [Queue.emptyWithCapacity, Array.mkEmpty_eq]

/-- Whether the queue is exhausted (pseudocode `Q.empty()`). -/
def isEmpty (q : Queue α) : Bool := q.head ≥ q.items.size

/-- Number of not-yet-popped elements (`push` +1, `pop?` −1). Used as a
termination measure in the proofs. -/
def live (q : Queue α) : Nat := q.items.size - q.head

/-- Active (not-yet-popped) queue entries: an index `≥ head` holding `p`.
The queue's abstract interface for the proofs -- worklist invariants
quantify over active entries and are maintained through the `active_*`
lemmas below, never through `items`/`head`. -/
def Active (q : Queue α) (p : α) : Prop :=
  ∃ i, q.head ≤ i ∧ q.items[i]? = some p

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

/-! ### The proof interface: `live` arithmetic and the active-set vocabulary -/

/-- `push` grows the live length by one. -/
theorem live_push {α} {q : Queue α} {x : α} : (q.push x).live = q.live + 1 := by
  have := q.queue_invariant
  simp only [Queue.live, Queue.push, Array.size_push]; omega

/-- A successful `pop?`, decoded: the front element and the advanced head
(items untouched). Private: its statement is representation-level, so the
module system will not export it. -/
private theorem pop?_some {α} {q q' : Queue α} {x : α} (h : q.pop? = some (x, q')) :
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

/-- `pop?` only shrinks the active set (`head` advances; `items` is untouched). -/
theorem active_pop {α} {q q' : Queue α} {x p : α}
    (hp : q.pop? = some (x, q')) (h : Active q' p) : Active q p := by
  obtain ⟨-, hi, hh⟩ := Queue.pop?_some hp
  grind [Active]

/-- `push` adds exactly the new element to the active set. -/
theorem active_push {α} {q : Queue α} {x p : α}
    (h : Active (q.push x) p) : Active q p ∨ p = x := by
  grind [Active, Queue.push]

/-- The just-popped element was active. -/
theorem active_head {α} {q q' : Queue α} {x : α}
    (hp : q.pop? = some (x, q')) : Active q x :=
  ⟨q.head, Nat.le_refl _, (Queue.pop?_some hp).1⟩

/-- On an empty queue nothing is active. -/
theorem not_active_of_isEmpty {α} {q : Queue α} (h : q.isEmpty = true)
    (p : α) : ¬ Active q p := by
  grind [Active, Queue.isEmpty]

/-- `push` only adds to the active set. -/
theorem active_push_mono {α} {q : Queue α} {x p : α}
    (h : Active q p) : Active (q.push x) p := by
  obtain ⟨i, hi, hp⟩ := h
  exact ⟨i, hi, by grind [Queue.push, Array.getElem?_push_lt, Array.getElem?_eq_none]⟩

/-- The just-pushed element is active. -/
theorem active_push_self {α} {q : Queue α} {x : α} :
    Active (q.push x) x :=
  ⟨q.items.size, q.queue_invariant, by simp [Queue.push]⟩

/-- Popping either keeps `p` active or reveals it as the just-popped element. -/
theorem active_pop_cases {α} {q q' : Queue α} {x p : α}
    (hp : q.pop? = some (x, q')) (h : Active q p) :
    Active q' p ∨ p = x := by
  obtain ⟨hx, hi, hh⟩ := Queue.pop?_some hp
  grind [Active]

/-- An `emptyWithCapacity` queue has nothing active. -/
theorem not_active_emptyWithCapacity {α} {cap : Nat} (p : α) :
    ¬ Active (Queue.emptyWithCapacity cap) p := by
  simp [Active, Queue.emptyWithCapacity]

/-- A seeded queue's active entries are the seed array's members. -/
theorem active_ofArray {α} {xs : Array α} {p : α}
    (h : (Queue.ofArray xs).Active p) : p ∈ xs := by
  grind [Active, Queue.ofArray, Array.getElem?_eq_some_iff, Array.mem_iff_getElem]

/-- Conversely, every seed member starts active. -/
theorem active_ofArray_of_mem {α} {xs : Array α} {p : α}
    (h : p ∈ xs) : (Queue.ofArray xs).Active p := by
  obtain ⟨i, hi, hip⟩ := Array.mem_iff_getElem.mp h
  exact ⟨i, Nat.zero_le _, Array.getElem?_eq_some_iff.mpr ⟨hi, hip⟩⟩

end Queue

end

end NearLinear4ct
