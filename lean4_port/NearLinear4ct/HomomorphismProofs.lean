import NearLinear4ct.PseudoConfiguration
import NearLinear4ct.MappingProofs
import NearLinear4ct.PseudoTriangulationProofs
import NearLinear4ct.UtilProofs

/-!
Machine-checked correctness of the homomorphism BFS
(`PseudoConfiguration.homStep`/`homCoreGo`, Appendix A.2), organised as three
invariants, each established by a **recursion-free lemma about the single
step** and lifted through the driver loop:

* `Bounded`: structural well-formedness -- sizes and in-bounds
  (`homStep_bounded`), yielding output well-formedness.
* `Sound`: dart-local consistency (the paper's Sec. 9 homomorphism definition;
  `homStep_next_sound`/`homStep_done_sound`), yielding soundness of
  `homCore`/`homomorphismExists`.
* `Agrees`: agreement with a reference homomorphism (`homStep_agrees`, which
  also strictly drops the `measure`), yielding completeness (no false
  negatives).

The driver `homCoreGo` is a `partial_fixpoint`, so it exposes
`homCoreGo.partial_correctness` -- a partial-correctness (Scott) induction
principle needing no termination proof; `Bounded` and `Sound` lift through it
in a few lines each. Completeness needs the BFS to actually return, so
`Agrees` folds over `homCoreGoImp`, a fuel-bounded driver of the *same*
`homStep`, and `homCoreGoImp_le` bridges back to `homCoreGo`.
-/

namespace NearLinear4ct

-- The obligation type's members (`pack`, `pairBase`, `fst_pack`, ...) are used
-- throughout; the bare type `SmallNatPair` still appears in signatures.
open SmallNatPair

namespace IndexMap

/-- Writing `some v` (`v < codom`) preserves `WF`: `set!` keeps the size, and
the new entry is in range while the others are untouched. -/
theorem wf_set!_some {m : IndexMap} {dom codom i v : Nat}
    (hm : m.WF dom codom) (hv : v < codom) :
    IndexMap.WF (m.set! i (OptIdx.some v)) dom codom := by
  grind [IndexMap.WF, IndexMap.Bounded, Array.set!, OptIdx.get?_some, Array.size_setIfInBounds]

/-- `idx?` at the just-written (in-range) index is the written value. -/
theorem idx?_set!_self {m : IndexMap} {i v : Nat} (h : i < m.size) :
    idx? (m.set! i (OptIdx.some v)) i = Option.some v := by
  simp [idx?, Array.set!, h]

/-- `idx?` at a different index is unchanged by `set!`. -/
theorem idx?_set!_ne {m : IndexMap} {i j v : Nat} (hne : i ≠ j) :
    idx? (m.set! i (OptIdx.some v)) j = idx? m j := by
  grind [idx?, Array.set!]

/-- Extending a restriction `m ≤ mref` by a mapping the reference already
contains (`mref.idx? k = some v`) stays a restriction. The single fact behind
both the `dmap`/`vmap` cases of `agrees_expand_base`. -/
theorem idx?_set!_le {m mref : IndexMap} {k v : Nat} (hk : k < m.size)
    (hle : ∀ i j, idx? m i = Option.some j → idx? mref i = Option.some j)
    (hnew : idx? mref k = Option.some v) :
    ∀ i j, idx? (m.set! k (OptIdx.some v)) i = Option.some j → idx? mref i = Option.some j := by
  grind [idx?_set!_self, idx?_set!_ne]

/-- Read `idx?` off a `!`-read: `m[i]! = some v` (in range) means `idx? i = some v`. -/
theorem idx?_eq_of_getElem! {m : IndexMap} {i v : Nat} (h : i < m.size)
    (he : m[i]! = OptIdx.some v) : idx? m i = Option.some v := by
  grind [IndexMap.idx?, OptIdx.get?_some]

/-- A non-`isSome` `!`-read (in range) means `idx? i = none`. -/
theorem idx?_eq_none_of_not_isSome {m : IndexMap} {i : Nat} (h : i < m.size)
    (hns : ¬ (m[i]!.isSome = true)) : idx? m i = Option.none := by
  grind [IndexMap.idx?, OptIdx.isSome_eq, OptIdx.get?]

/-- The all-`none` replicate is unmapped everywhere. -/
theorem idx?_replicate_none {n i : Nat} :
    idx? (Array.replicate n OptIdx.none) i = Option.none := by
  grind [idx?, OptIdx.get?_none]

/-- The all-`none` replicate is a well-formed (empty) map. -/
theorem wf_replicate_none {n codom : Nat} :
    IndexMap.WF (Array.replicate n OptIdx.none) n codom := by
  grind [IndexMap.WF, IndexMap.Bounded, OptIdx.get?_none]

end IndexMap

namespace PseudoConfiguration.HomState

/-- Active (not-yet-popped) queue entries: an index `≥ head` holding `p`. -/
def Active (q : Queue SmallNatPair) (p : SmallNatPair) : Prop :=
  ∃ i, q.head ≤ i ∧ q.items[i]? = some p

/-- `pop?` only shrinks the active set (`head` advances; `items` is untouched). -/
theorem active_pop {q q' : Queue SmallNatPair} {x p : SmallNatPair}
    (hp : q.pop? = some (x, q')) (h : Active q' p) : Active q p := by
  obtain ⟨-, hi, hh⟩ := Queue.pop?_some hp
  grind [Active]

/-- `push` adds exactly the new element to the active set. -/
theorem active_push {q : Queue SmallNatPair} {x p : SmallNatPair}
    (h : Active (q.push x) p) : Active q p ∨ p = x := by
  grind [Active, Queue.push]

/-- The just-popped element was active. -/
theorem active_head {q q' : Queue SmallNatPair} {x : SmallNatPair}
    (hp : q.pop? = some (x, q')) : Active q x :=
  ⟨q.head, Nat.le_refl _, (Queue.pop?_some hp).1⟩

/-- **Structural invariant** (`Bounded` half of `HomState.WF`): sizes + all
indices in bounds. Enough for output-WF; no dart-local (semantic) content. -/
structure Bounded (src dst : PseudoConfiguration)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Prop where
  queued_bd  : ∀ p, Active q p → p.fst < src.darts.size ∧ p.snd < dst.darts.size
  vmap_wf    : IndexMap.WF vmap src.n dst.n
  dmap_wf    : IndexMap.WF dmap src.darts.size dst.darts.size

/-- The maps `homCoreGo` returns are well-formed `IndexMap`s. -/
def OutputWF (src dst : PseudoConfiguration) (r : IndexMap × IndexMap) : Prop :=
  IndexMap.WF r.1 src.n dst.n ∧ IndexMap.WF r.2 src.darts.size dst.darts.size

/-- A pushed `pack a b` decodes in bounds, given the dst side fits the pair base. -/
theorem pack_bounded {src dst : PseudoConfiguration}
    (hpack : dst.darts.size ≤ pairBase) {a b : Nat}
    (ha : a < src.darts.size) (hb : b < dst.darts.size) :
    (pack a b).fst < src.darts.size ∧
      (pack a b).snd < dst.darts.size := by
  grind [fst_pack, snd_pack, pairBase]

/-- Pushing an in-bounds element keeps `Bounded` (maps untouched). -/
theorem bounded_push {src dst : PseudoConfiguration}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {x : SmallNatPair}
    (hb : Bounded src dst q vmap dmap)
    (hx : x.fst < src.darts.size ∧ x.snd < dst.darts.size) :
    Bounded src dst (q.push x) vmap dmap := by
  grind [Bounded, active_push]

/-! `pushLink` is the expand step's conditional push, so the invariant
lemmas speak about it as one operation. Each lemma case-splits the two links;
the both-`some` arm is a plain `push`, every other arm is the identity. -/

/-- `pushLink` grows the live length by at most one. -/
theorem live_pushLink_le {q : Queue SmallNatPair} {os od : OptIdx} :
    (pushLink q os od).live ≤ q.live + 1 := by
  grind [pushLink.eq_def, Queue.live, Queue.push]

/-- `pushLink` on in-range links (the dart `InBounds` fields) keeps `Bounded`. -/
theorem bounded_pushLink {src dst : PseudoConfiguration}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {os od : OptIdx}
    (hb : Bounded src dst q vmap dmap) (hpack : dst.darts.size ≤ pairBase)
    (hs : ∀ j, os.get? = Option.some j → j < src.darts.size)
    (hd : ∀ j, od.get? = Option.some j → j < dst.darts.size) :
    Bounded src dst (pushLink q os od) vmap dmap := by
  cases os <;> cases od
  all_goals try exact hb
  exact bounded_push hb (pack_bounded hpack (hs _ rfl) (hd _ rfl))

/-- **Re-pop branch preservation**: popping (maps unchanged) keeps `Bounded`. -/
theorem bounded_pop {src dst : PseudoConfiguration}
    {q q' : Queue SmallNatPair} {x : SmallNatPair} {vmap dmap : IndexMap}
    (hp : q.pop? = some (x, q')) (hb : Bounded src dst q vmap dmap) :
    Bounded src dst q' vmap dmap := by
  grind [Bounded, active_pop]

/-- The dart at an in-range index is `InBounds` (unfolding the `!`-read). The
shared `hsrcD`/`hdstD` step in every loop-body proof. -/
theorem dart_inBounds {c : PseudoConfiguration} (hwf : c.WF) {i : Nat}
    (h : i < c.darts.size) : (c.darts[i]!).InBounds c.n c.darts.size := by
  simpa only [getElem!_pos c.darts i h] using hwf.1 i h

/-- **One step preserves `Bounded`**: a continuing step's state is `Bounded`,
and a `done` exit that answers `some` is well-formed output. Recursion-free --
the driver lemma `homCoreGo_output_wf` lifts it through the loop. -/
theorem homStep_bounded
    {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (hb : Bounded src dst q vmap dmap) :
    match homStep src dst degreeTest q vmap dmap with
    | .done r => ∀ p, r = some p → OutputWF src dst p
    | .next q' vmap' dmap' => Bounded src dst q' vmap' dmap' := by
  unfold homStep
  rcases heq : q.pop? with _ | ⟨packed, q1⟩ <;> simp only []
  · -- base case: `pop?` exhausted, the maps are the answer
    grind [OutputWF, Bounded]
  · -- q not empty: pop, then re-pop / expand
    have hfb := hb.queued_bd packed (active_head heq)
    have hsrcD := dart_inBounds hsrc hfb.1
    have hdstD := dart_inBounds hdst hfb.2
    have hbase : Bounded src dst q1
        (vmap.set! (src.darts[packed.fst]!).head (OptIdx.some (dst.darts[packed.snd]!).head))
        (dmap.set! packed.fst (OptIdx.some packed.snd)) :=
      ⟨(bounded_pop heq hb).queued_bd,
        IndexMap.wf_set!_some hb.vmap_wf hdstD.head_lt,
        IndexMap.wf_set!_some hb.dmap_wf hfb.2⟩
    -- `Bounded` through the three pushes, in order
    have hb1 := bounded_push hbase (pack_bounded hpack hsrcD.rev_lt hdstD.rev_lt)
    have hb2 := bounded_pushLink hb1 hpack hsrcD.succ_lt hdstD.succ_lt
    have hb3 := bounded_pushLink hb2 hpack hsrcD.pred_lt hdstD.pred_lt
    grind [OutputWF, Bounded]

/-- **Output well-formedness**: whenever `homCoreGo` returns from a `Bounded`
state, both maps are well-formed `IndexMap`s. `homStep_bounded` lifted through
the driver by `partial_correctness` (no termination needed). -/
theorem homCoreGo_output_wf
    {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    (hsrc : src.WF) (hdst : dst.WF)
    (hpack : dst.darts.size ≤ pairBase)
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {r : IndexMap × IndexMap}
    (hb : Bounded src dst q vmap dmap)
    (hrun : homCoreGo src dst degreeTest q vmap dmap = some r) :
    OutputWF src dst r := by
  revert hb
  refine homCoreGo.partial_correctness src dst degreeTest
    (motive := fun q vmap dmap r => Bounded src dst q vmap dmap → OutputWF src dst r)
    ?step q vmap dmap r hrun
  intro rec ih q vmap dmap r hstep hb
  grind [homStep_bounded]

/-! ### The semantic `Sound` layer (dart-local consistency = paper Sec. 9)

`Sound` extends `Bounded` with the homomorphism conditions. Heads are forced
*synchronously* (the step sets `vmap[head]` the instant it maps a dart), so
`dart_head_ok` is a plain implication. The neighbours `rev`/`succ`/`pred` are
*asynchronous* -- pushed onto the queue and mapped later -- so they are carried
as "done *or* pending in the queue" (`DoneOrQueued`), which collapses to "done"
once the queue drains. -/

/-- A pending queue obligation: `(f, fStar)` is (still) somewhere in the queue. -/
def Queued (q : Queue SmallNatPair) (f fStar : Nat) : Prop :=
  ∃ p, Active q p ∧ p.fst = f ∧ p.snd = fStar

/-- Either already mapped consistently, or pending in the queue. -/
def DoneOrQueued (q : Queue SmallNatPair) (dmap : IndexMap) (f fStar : Nat) : Prop :=
  dmap.idx? f = Option.some fStar ∨ Queued q f fStar

/-- On an empty queue nothing is active. -/
theorem not_active_of_isEmpty {q : Queue SmallNatPair} (h : q.isEmpty = true)
    (p : SmallNatPair) : ¬ Active q p := by
  grind [Active, Queue.isEmpty]

/-- On an empty queue, `DoneOrQueued` collapses to `Done`. -/
theorem done_of_isEmpty {q : Queue SmallNatPair} {dmap : IndexMap} {f fStar : Nat}
    (h : q.isEmpty = true) (hd : DoneOrQueued q dmap f fStar) :
    dmap.idx? f = Option.some fStar := by
  grind [DoneOrQueued, Queued, not_active_of_isEmpty]

/-- `push` only adds to the active set. -/
theorem active_push_mono {q : Queue SmallNatPair} {x p : SmallNatPair}
    (h : Active q p) : Active (q.push x) p := by
  obtain ⟨i, hi, hp⟩ := h
  exact ⟨i, hi, by grind [Queue.push, Array.getElem?_push_lt, Array.getElem?_eq_none]⟩

/-- The just-pushed element is active. -/
theorem active_push_self {q : Queue SmallNatPair} {x : SmallNatPair} :
    Active (q.push x) x :=
  ⟨q.items.size, q.queue_invariant, by simp [Queue.push]⟩

theorem active_pushLink_mono {q : Queue SmallNatPair} {os od : OptIdx} {p : SmallNatPair}
    (h : Active q p) : Active (pushLink q os od) p := by
  grind [pushLink.eq_def, active_push_mono]

/-- The pair `pushLink` queues on interior links is active. -/
theorem active_pushLink_self {q : Queue SmallNatPair} {s t : Nat} :
    Active (pushLink q (OptIdx.some s) (OptIdx.some t)) (pack s t) :=
  active_push_self

/-- Popping either keeps `p` active or reveals it as the just-popped element. -/
theorem active_pop_cases {q q' : Queue SmallNatPair} {x p : SmallNatPair}
    (hp : q.pop? = some (x, q')) (h : Active q p) :
    Active q' p ∨ p = x := by
  obtain ⟨hx, hi, hh⟩ := Queue.pop?_some hp
  grind [Active]

/-- `DoneOrQueued` is monotone under `push` (the queue only grows). -/
theorem doneOrQueued_push {q : Queue SmallNatPair} {dmap : IndexMap} {g gStar : Nat}
    {x : SmallNatPair} (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued (q.push x) dmap g gStar := by
  grind [DoneOrQueued, Queued, active_push_mono]

theorem doneOrQueued_pushLink {q : Queue SmallNatPair} {dmap : IndexMap} {g gStar : Nat}
    {os od : OptIdx} (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued (pushLink q os od) dmap g gStar := by
  grind [DoneOrQueued, Queued, active_pushLink_mono]

/-- **Re-pop transport**: popping keeps `DoneOrQueued`, given the popped element
is already consistently mapped (so if it was the sole witness, it is now done). -/
theorem doneOrQueued_pop {q q' : Queue SmallNatPair} {x : SmallNatPair}
    {dmap : IndexMap} {g gStar : Nat}
    (hp : q.pop? = some (x, q'))
    (hdone : dmap.idx? x.fst = Option.some x.snd)
    (hd : DoneOrQueued q dmap g gStar) : DoneOrQueued q' dmap g gStar := by
  grind [DoneOrQueued, active_pop_cases, Queued]

/-- **Expand transport**: popping the fresh `(f, fStar)` and mapping it keeps
`DoneOrQueued`. A done witness `g ≠ f` survives the `set!`; the popped witness
becomes done via the fresh mapping. -/
theorem doneOrQueued_expand_pop {q q' : Queue SmallNatPair} {x : SmallNatPair}
    {dmap : IndexMap} {g gStar : Nat}
    (hp : q.pop? = some (x, q')) (hfsz : x.fst < dmap.size)
    (hfresh : dmap.idx? x.fst = Option.none)
    (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued q' (dmap.set! x.fst (OptIdx.some x.snd)) g gStar := by
  grind [DoneOrQueued, Queued, active_pop_cases, IndexMap.idx?_set!_ne, IndexMap.idx?_set!_self]

/-- A pending optional link (`succ`/`pred`): the source resolving forces a `DoneOrQueued` target. -/
def LinkPending (q : Queue SmallNatPair) (dmap : IndexMap) (srcLink dstLink : OptIdx) : Prop :=
  ∀ s, srcLink.get? = Option.some s → ∃ t, dstLink.get? = Option.some t ∧ DoneOrQueued q dmap s t

/-- Transport a `LinkPending` along any `DoneOrQueued` transport (queue and map
may both change); drives the re-pop and expand steps of soundness. -/
theorem LinkPending.transport {q q' : Queue SmallNatPair} {dmap dmap' : IndexMap}
    {srcLink dstLink : OptIdx} (hlp : LinkPending q dmap srcLink dstLink)
    (htrans : ∀ {f fStar}, DoneOrQueued q dmap f fStar → DoneOrQueued q' dmap' f fStar) :
    LinkPending q' dmap' srcLink dstLink := by
  grind [LinkPending]

/-- The fresh-dart (`g = f`) half of `succ_pending`/`pred_pending`: once `f` is
mapped and its `succ`/`pred` obligation pushed, that link is `LinkPending`. -/
theorem freshLink_pending {q' : Queue SmallNatPair} {dmap' : IndexMap} {os od : OptIdx}
    {D : Nat} (hpack : D ≤ pairBase) (hdb : ∀ j, od.get? = Option.some j → j < D)
    (hg : ¬(os.isSome && od.isNone) = true)
    (hactive : ∀ s t, os = OptIdx.some s → od = OptIdx.some t → Active q' (pack s t)) :
    LinkPending q' dmap' os od := by
  intro s hs
  cases os with
  | none => exact absurd hs (by simp)
  | some so =>
    obtain rfl : so = s := by simpa using hs
    cases od with
    | none => exact absurd hg (by simp)
    | some t =>
      have hlt : t < pairBase := Nat.lt_of_lt_of_le (hdb t rfl) hpack
      exact ⟨t, rfl, Or.inr ⟨pack so t, hactive so t rfl rfl,
        fst_pack so t hlt, snd_pack so t hlt⟩⟩

/-- The soundness spec for `homCore`: `(vmap, dmap)` encode a genuine
homomorphism `src → dst` pinned at the root dart pairing `dartFrom ↦ dartTo`.

"Rooted" is our descriptor, not the paper's term -- Sec. 9 says only "homomorphism".
It names a fact Sec. 9 relies on: a homomorphism of a 2-connected near-triangulation
is unique once the image `ϕ(xy)` of a single oriented edge is chosen, the rest
being forced by the dart incidences. Fixing that one dart image and propagating
along successors/predecessors/reverses is exactly the `rootedContainConf`
subroutine (Algorithm A.6.8), hence the name.

The conjuncts, spelled out below, are Sec. 9's dart-homomorphism conditions:
* the root -- `dmap` sends `dartFrom` to `dartTo`;
* dart-local consistency for every mapped dart `f` (`dmap f = some fStar`):
  `head` and `rev` commute always, `succ`/`pred` where both sides are interior
  (the boundary guards); and
* degree compatibility -- `degreeTest` holds on every mapped vertex. -/
def IsRootedHom (src dst : PseudoConfiguration) (degreeTest : Degree → Degree → Bool)
    (dartFrom dartTo : Nat) (vmap dmap : IndexMap) : Prop :=
  dmap.idx? dartFrom = Option.some dartTo ∧
  (∀ f fStar, dmap.idx? f = Option.some fStar →
    vmap.idx? (src.darts[f]!).head = Option.some (dst.darts[fStar]!).head ∧
    dmap.idx? (src.darts[f]!).rev = Option.some (dst.darts[fStar]!).rev ∧
    (∀ s, (src.darts[f]!).succ.get? = Option.some s →
      ∃ t, (dst.darts[fStar]!).succ.get? = Option.some t ∧ dmap.idx? s = Option.some t) ∧
    (∀ s, (src.darts[f]!).pred.get? = Option.some s →
      ∃ t, (dst.darts[fStar]!).pred.get? = Option.some t ∧ dmap.idx? s = Option.some t)) ∧
  (∀ v vStar, vmap.idx? v = Option.some vStar →
    degreeTest (src.degrees[v]!) (dst.degrees[vStar]!) = true)

/-- **Semantic invariant**, extending `Bounded`. -/
structure Sound (src dst : PseudoConfiguration) (degreeTest : Degree → Degree → Bool)
    (dartFrom dartTo : Nat) (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Prop
    extends Bounded src dst q vmap dmap where
  root_pending : DoneOrQueued q dmap dartFrom dartTo
  dart_head_ok : ∀ f fStar, dmap.idx? f = Option.some fStar →
    vmap.idx? (src.darts[f]!).head = Option.some (dst.darts[fStar]!).head
  degree_ok : ∀ v vStar, vmap.idx? v = Option.some vStar →
    degreeTest (src.degrees[v]!) (dst.degrees[vStar]!) = true
  rev_pending : ∀ f fStar, dmap.idx? f = Option.some fStar →
    DoneOrQueued q dmap (src.darts[f]!).rev (dst.darts[fStar]!).rev
  succ_pending : ∀ f fStar, dmap.idx? f = Option.some fStar →
    LinkPending q dmap (src.darts[f]!).succ (dst.darts[fStar]!).succ
  pred_pending : ∀ f fStar, dmap.idx? f = Option.some fStar →
    LinkPending q dmap (src.darts[f]!).pred (dst.darts[fStar]!).pred

/-- **Base case**: at an empty queue, `Sound` *is* `IsRootedHom` -- every pending
obligation collapses to done. -/
theorem isRootedHom_of_sound_isEmpty
    {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap) (hq : q.isEmpty = true) :
    IsRootedHom src dst degreeTest dartFrom dartTo vmap dmap := by
  grind [IsRootedHom, Sound, LinkPending, done_of_isEmpty]

/-- Discharge the re-pop consistency test: `¬(dv != some n)` means `dv = some n`. -/
theorem optIdx_eq_of_not_bne {dv : OptIdx} {n : Nat}
    (h : ¬(dv != OptIdx.some n) = true) : dv = OptIdx.some n := by
  simpa using h

/-- **Re-pop preservation** of `Sound`: popping an already-consistent element
keeps the invariant (maps unchanged; every pending clause transports by
`doneOrQueued_pop`). -/
theorem sound_pop {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {q q' : Queue SmallNatPair} {x : SmallNatPair}
    {vmap dmap : IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hp : q.pop? = some (x, q'))
    (hdone : dmap.idx? x.fst = Option.some x.snd) :
    Sound src dst degreeTest dartFrom dartTo q' vmap dmap := by
  grind [Sound, bounded_pop, doneOrQueued_pop, LinkPending.transport]

/-- Flatten a guard: an early `done none` exit equals `.next` iff the guard
fails and the continuation reaches `.next` -- the `HomNext` sibling of
`Option.ite_none_left_eq_some`. -/
theorem ite_done_none_eq_next {c : Prop} [Decidable c] {x : HomNext}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} :
    ((if c then HomNext.done none else x) = HomNext.next q vmap dmap)
      ↔ ¬c ∧ x = HomNext.next q vmap dmap := by
  grind

/-- **One step preserves `Sound`**: a continuing step's state is `Sound`.
Base case of the invariant argument; recursion-free. -/
theorem homStep_next_sound
    {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    {q q' : Queue SmallNatPair} {vmap dmap vmap' dmap' : IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hst : homStep src dst degreeTest q vmap dmap = .next q' vmap' dmap') :
    Sound src dst degreeTest dartFrom dartTo q' vmap' dmap' := by
  unfold homStep at hst
  simp only [] at hst
  split at hst
  · grind
  · rename_i packed q1 heq
    have hfb := hs.queued_bd packed (active_head heq)
    have hfsz : packed.fst < dmap.size := by
      simpa only [hs.dmap_wf.size_eq] using hfb.1
    split at hst
    · -- already mapped; the consistency guard passes, then re-pop
      rename_i d hdd
      simp only [ite_done_none_eq_next] at hst
      obtain ⟨hcons, hst⟩ := hst
      cases hst
      grind [sound_pop, IndexMap.idx?_eq_of_getElem!]
    · -- unmapped: expand
      rename_i hdv
      have hfresh : dmap.idx? packed.fst = Option.none :=
        IndexMap.idx?_eq_none_of_not_isSome hfsz (by grind [OptIdx.isSome])
      have hsrcD := dart_inBounds hsrc hfb.1
      have hdstD := dart_inBounds hdst hfb.2
      -- flatten the four early-return guards (vmap-conflict, degree, succ/pred
      -- boundary); on the success path each `else` is taken, so all pass
      simp only [ite_done_none_eq_next] at hst
      obtain ⟨hvvc, hdeg, hsg, hpg, hst⟩ := hst
      cases hst
      have hvsz : src.darts[packed.fst]!.head < vmap.size := by
        simpa only [hs.vmap_wf.size_eq] using hsrcD.head_lt
      have hvv : vmap.idx? src.darts[packed.fst]!.head = Option.none ∨
          vmap.idx? src.darts[packed.fst]!.head =
            Option.some dst.darts[packed.snd]!.head := by
        by_cases hsome : vmap[src.darts[packed.fst]!.head]!.isSome = true
        · exact Or.inr (IndexMap.idx?_eq_of_getElem! hvsz
            (optIdx_eq_of_not_bne (by simpa only [hsome, Bool.true_and] using hvvc)))
        · exact Or.inl (IndexMap.idx?_eq_none_of_not_isSome hvsz hsome)
      have hbase : Bounded src dst q1
          (vmap.set! src.darts[packed.fst]!.head (OptIdx.some dst.darts[packed.snd]!.head))
          (dmap.set! packed.fst (OptIdx.some packed.snd)) :=
        ⟨(bounded_pop heq hs.toBounded).queued_bd,
          IndexMap.wf_set!_some hs.vmap_wf hdstD.head_lt,
          IndexMap.wf_set!_some hs.dmap_wf hfb.2⟩
      have hexp : ∀ {g gStar}, DoneOrQueued q dmap g gStar →
          DoneOrQueued q1 (dmap.set! packed.fst (OptIdx.some packed.snd)) g gStar :=
        fun hdq => doneOrQueued_expand_pop heq hfsz hfresh hdq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- toBounded: `Bounded` through the three pushes, in order
        exact bounded_pushLink (bounded_pushLink
            (bounded_push hbase (pack_bounded hpack hsrcD.rev_lt hdstD.rev_lt))
            hpack hsrcD.succ_lt hdstD.succ_lt)
          hpack hsrcD.pred_lt hdstD.pred_lt
      · -- root_pending
        grind [doneOrQueued_push, doneOrQueued_pushLink, hexp hs.root_pending]
      · -- dart_head_ok
        grind [IndexMap.idx?_set!_self, IndexMap.idx?_set!_ne, hs.dart_head_ok]
      · -- degree_ok
        grind [IndexMap.idx?_set!_self, IndexMap.idx?_set!_ne, hs.degree_ok]
      · -- rev_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set!_self hfsz ▸ hg)).symm
          refine Or.inr ⟨pack src.darts[packed.fst]!.rev
            dst.darts[packed.snd]!.rev, ?_,
            fst_pack _ _ (Nat.lt_of_lt_of_le hdstD.rev_lt hpack),
            snd_pack _ _ (Nat.lt_of_lt_of_le hdstD.rev_lt hpack)⟩
          grind [active_push_self, active_pushLink_mono]
        · grind [doneOrQueued_push, doneOrQueued_pushLink,
            hexp (hs.rev_pending g gStar (IndexMap.idx?_set!_ne (Ne.symm hgf) ▸ hg))]
      · -- succ_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set!_self hfsz ▸ hg)).symm
          refine freshLink_pending hpack hdstD.succ_lt hsg (fun s t hss hdd => ?_)
          grind [active_pushLink_self, active_pushLink_mono]
        · exact (hs.succ_pending g gStar (IndexMap.idx?_set!_ne (Ne.symm hgf) ▸ hg)).transport
            (fun hdq => by grind [doneOrQueued_push, doneOrQueued_pushLink, hexp hdq])
      · -- pred_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set!_self hfsz ▸ hg)).symm
          refine freshLink_pending hpack hdstD.pred_lt hpg (fun s t hss hdd => ?_)
          grind [active_pushLink_self, active_pushLink_mono]
        · exact (hs.pred_pending g gStar (IndexMap.idx?_set!_ne (Ne.symm hgf) ▸ hg)).transport
            (fun hdq => by grind [doneOrQueued_push, doneOrQueued_pushLink, hexp hdq])


/-- **A `some` answer from a `Sound` state is a homomorphism**: the step only
answers `some` at an exhausted queue, where `Sound` collapses to
`IsRootedHom`. -/
theorem homStep_done_sound
    {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    {p : IndexMap × IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hst : homStep src dst degreeTest q vmap dmap = .done (some p)) :
    IsRootedHom src dst degreeTest dartFrom dartTo p.1 p.2 := by
  grind [homStep, isRootedHom_of_sound_isEmpty, Queue.pop?_none]

/-- **Soundness of `homCoreGo`**: from a `Sound` state, any `some (vmap, dmap)`
result is a genuine rooted homomorphism (`IsRootedHom`) -- the BFS decides the
paper's Sec. 9 predicate. `homStep_next_sound`/`homStep_done_sound` lifted
through the driver by `partial_correctness`. -/
theorem homCoreGo_sound
    {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {r : IndexMap × IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hrun : homCoreGo src dst degreeTest q vmap dmap = some r) :
    IsRootedHom src dst degreeTest dartFrom dartTo r.1 r.2 := by
  revert hs
  refine homCoreGo.partial_correctness src dst degreeTest
    (motive := fun q vmap dmap r =>
      Sound src dst degreeTest dartFrom dartTo q vmap dmap →
      IsRootedHom src dst degreeTest dartFrom dartTo r.1 r.2)
    ?step q vmap dmap r hrun
  intro rec ih q vmap dmap r hstep hs
  grind [homStep_done_sound, homStep_next_sound]

/-- An `emptyWithCapacity` queue has nothing active. -/
theorem not_active_emptyWithCapacity {cap : Nat} (p : SmallNatPair) :
    ¬ Active (Queue.emptyWithCapacity cap) p := by
  simp [Active, Queue.emptyWithCapacity]

/-- The seeded queue's only obligation is the root pair, and it unpacks to
`(dartFrom, dartTo)`. The shared setup of `homCore_sound`/`homCore_complete`. -/
theorem seed_root {dst : PseudoConfiguration} {dartTo : Nat} (dartFrom cap : Nat)
    (hpack : dst.darts.size ≤ pairBase) (hdt : dartTo < dst.darts.size) :
    (pack dartFrom dartTo).fst = dartFrom ∧ (pack dartFrom dartTo).snd = dartTo ∧
    ∀ p, Active ((Queue.emptyWithCapacity cap).push (pack dartFrom dartTo)) p →
      p = pack dartFrom dartTo := by
  have hxb : dartTo < pairBase := Nat.lt_of_lt_of_le hdt hpack
  exact ⟨fst_pack dartFrom dartTo hxb, snd_pack dartFrom dartTo hxb,
    fun p hp => (active_push hp).resolve_left (not_active_emptyWithCapacity p)⟩

/-- **Soundness of `homCore`** (the seeded BFS, A.2): if it returns
`some (vmap, dmap)`, that is a genuine rooted homomorphism `src → dst`. The seed
state satisfies `Sound` (the root pair is queued; the maps start empty), so this
is `homCoreGo_sound` at the initial state. Requires the root darts in range. -/
theorem homCore_sound {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} (hsrc : src.WF) (hdst : dst.WF)
    (hpack : dst.darts.size ≤ pairBase)
    (hdf : dartFrom < src.darts.size) (hdt : dartTo < dst.darts.size)
    {r : IndexMap × IndexMap} (hrun : homCore src dartFrom dst dartTo degreeTest = some r) :
    IsRootedHom src dst degreeTest dartFrom dartTo r.1 r.2 := by
  obtain ⟨hxfst, hxsnd, hactive⟩ := seed_root dartFrom (src.darts.size * 3 + 1) hpack hdt
  refine homCoreGo_sound hsrc hdst hpack (r := r) ?_ hrun
  refine ⟨⟨?_, IndexMap.wf_replicate_none, IndexMap.wf_replicate_none⟩,
    Or.inr ⟨pack dartFrom dartTo, active_push_self, hxfst, hxsnd⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals grind [IndexMap.idx?_replicate_none]

/-- **`homomorphismExists` is sound**: if the `.isSome` fast path reports a
homomorphism, one genuinely exists. (The converse is `homomorphismExists_complete`.) -/
theorem homomorphismExists_sound {src dst : PseudoConfiguration}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    (hdf : dartFrom < src.darts.size) (hdt : dartTo < dst.darts.size)
    (h : homomorphismExists src dartFrom dst dartTo degreeTest = true) :
    ∃ vmap dmap, IsRootedHom src dst degreeTest dartFrom dartTo vmap dmap := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  exact ⟨r.1, r.2, homCore_sound hsrc hdst hpack hdf hdt hr⟩

/-! ### Completeness scaffolding: a fuel-based total twin of `homCoreGo`

`homCoreGo` is a `partial_fixpoint`, so proving it *returns* `some` (needed for
completeness -- no false negatives) requires a termination argument. The fuel
twin drives the same `homStep`, so the bridge is a one-split transport;
completeness is then ordinary induction on fuel, stepped by `homStep_agrees`. -/

/-- Fuel-bounded driver of `homStep` (`0` fuel = give up with `none`). -/
def homCoreGoImp (src dst : PseudoConfiguration) (degreeTest : Degree → Degree → Bool) :
    Nat → Queue SmallNatPair → IndexMap → IndexMap → Option (IndexMap × IndexMap)
  | 0, _, _, _ => none
  | fuel + 1, q, vmap, dmap =>
    match homStep src dst degreeTest q vmap dmap with
    | .done r => r
    | .next q vmap dmap => homCoreGoImp src dst degreeTest fuel q vmap dmap

/-- **The termination bridge**: whenever the fuel driver returns `some r`, so
does the `partial_fixpoint` driver (they run the same `homStep`). -/
theorem homCoreGoImp_le {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool} :
    ∀ fuel q vmap dmap r, homCoreGoImp src dst degreeTest fuel q vmap dmap = some r →
      homCoreGo src dst degreeTest q vmap dmap = some r := by
  intro fuel
  induction fuel <;> grind [homCoreGoImp, homCoreGo.eq_def]

/-- The **completeness invariant**: the BFS state agrees with a fixed reference
homomorphism `(vm, dm)`. The built maps are restrictions of the reference, and
the queue holds only *correct* obligations (`dm.idx? f = some f★`). Under this,
the reference witnesses consistency at every step, so no `none` branch fires. -/
structure Agrees (src dst : PseudoConfiguration) (vm dm : IndexMap)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Prop where
  toBounded : Bounded src dst q vmap dmap
  dmap_le : ∀ f fStar, dmap.idx? f = Option.some fStar → dm.idx? f = Option.some fStar
  vmap_le : ∀ v vStar, vmap.idx? v = Option.some vStar → vm.idx? v = Option.some vStar
  queue_ok : ∀ p, Active q p → dm.idx? p.fst = Option.some p.snd

/-- Number of still-unmapped dart cells `< dmap.size` -- the primary termination
measure (strictly drops on every expand; re-pops shrink the queue instead). -/
def unmapped (dmap : IndexMap) : Nat :=
  (List.range dmap.size).countP (fun f => (dmap.idx? f).isNone)

/-- The lexicographic measure flattened: every step strictly decreases it. The
live queue length `items.size - head` drops on a re-pop; on an expand the ≤3
pushes add at most `+2` but `unmapped` drops (weighted `×4`), so the sum falls. -/
def measure (q : Queue SmallNatPair) (dmap : IndexMap) : Nat :=
  q.live + 4 * unmapped dmap

/-- `countP` monotonicity under a pointwise-weaker predicate (project has no
Mathlib; proved here). -/
private theorem countP_le {α} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, q x = true → p x = true) : l.countP q ≤ l.countP p := by
  induction l <;> grind

/-- Strict `countP` decrease: a weaker predicate with one strictly-dropped
element counts less. -/
private theorem countP_lt {α} (p q : α → Bool) (l : List α)
    (hle : ∀ x ∈ l, q x = true → p x = true)
    (x : α) (hx : x ∈ l) (hpx : p x = true) (hqx : q x = false) :
    l.countP q < l.countP p := by
  induction l with
  | nil => grind
  | cons a t ih =>
    have hat : ∀ y ∈ t, q y = true → p y = true := fun y hy => hle y (List.mem_cons_of_mem _ hy)
    have := hle a List.mem_cons_self
    have := countP_le p q t hat
    simp only [List.countP_cons]
    rcases List.mem_cons.1 hx with rfl | hxt
    · grind
    · have := ih hat hxt; grind

/-- Mapping a fresh in-range dart strictly drops `unmapped`. -/
theorem unmapped_set!_lt {dmap : IndexMap} {f v : Nat} (hf : f < dmap.size)
    (hnone : dmap.idx? f = Option.none) :
    unmapped (dmap.set! f (OptIdx.some v)) < unmapped dmap := by
  have hsize : (dmap.set! f (OptIdx.some v)).size = dmap.size := by
    simp [Array.set!, Array.size_setIfInBounds]
  unfold unmapped
  rw [hsize]
  refine countP_lt _ _ _ (fun k _ hk => ?_) f (by simp [hf]) (by simp [hnone]) ?_
  · grind [IndexMap.idx?_set!_self, IndexMap.idx?_set!_ne]
  · rw [IndexMap.idx?_set!_self hf]; simp

/-- **Re-pop measure decrease**: popping (maps unchanged) drops the measure. -/
theorem measure_pop_lt {q q' : Queue SmallNatPair} {x : SmallNatPair} {dmap : IndexMap}
    (hp : q.pop? = some (x, q')) : measure q' dmap < measure q dmap := by
  grind [Queue.live_pop, measure]

/-- A read that `isSome` corresponds to a `some` in `idx?`. -/
theorem idx?_of_isSome {m : IndexMap} {i : Nat} (hi : i < m.size) (h : m[i]!.isSome = true) :
    m.idx? i = Option.some m[i]!.idx! := by
  grind [IndexMap.idx?, OptIdx.isSome_eq, OptIdx.idx!_of_get?_some, Option.isSome_iff_exists]

/-- Reverse of `idx?_eq_of_getElem!`: a mapped index reads back as `some`. -/
theorem getElem!_eq_of_idx? {m : IndexMap} {i v : Nat} (h : m.idx? i = Option.some v) :
    m[i]! = OptIdx.some v := by
  grind [IndexMap.idx?, OptIdx.get?_eq_some_iff]

/-- **Re-pop preservation** of `Agrees`: popping keeps the invariant (maps
unchanged; the popped obligation just leaves the queue). -/
theorem agrees_pop {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q q' : Queue SmallNatPair} {x : SmallNatPair} {vmap dmap : IndexMap}
    (ha : Agrees src dst vm dm q vmap dmap) (hp : q.pop? = some (x, q')) :
    Agrees src dst vm dm q' vmap dmap := by
  grind [Agrees, bounded_pop, active_pop]

/-- Pushing an in-bounds, *correct* obligation keeps `Agrees`. -/
theorem agrees_push {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {x : SmallNatPair}
    (ha : Agrees src dst vm dm q vmap dmap)
    (hxb : x.fst < src.darts.size ∧ x.snd < dst.darts.size)
    (hxc : dm.idx? x.fst = Option.some x.snd) :
    Agrees src dst vm dm (q.push x) vmap dmap := by
  grind [Agrees, bounded_push, active_push]

/-- Pushing a `pack a b` of a correct in-bounds obligation keeps `Agrees`. -/
theorem agrees_push_pack {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {a b : Nat}
    (ha : Agrees src dst vm dm q vmap dmap) (hpk : dst.darts.size ≤ pairBase)
    (hab : a < src.darts.size) (hbb : b < dst.darts.size) (hc : dm.idx? a = Option.some b) :
    Agrees src dst vm dm (q.push (pack a b)) vmap dmap := by
  grind [agrees_push, fst_pack, snd_pack, pairBase]

/-- `pushLink` keeps `Agrees`: when both links are interior, the queued pair
must be a correct in-bounds obligation of the reference. -/
theorem agrees_pushLink {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {os od : OptIdx}
    (ha : Agrees src dst vm dm q vmap dmap) (hpk : dst.darts.size ≤ pairBase)
    (hf : ∀ s t, os = OptIdx.some s → od = OptIdx.some t →
      s < src.darts.size ∧ t < dst.darts.size ∧ dm.idx? s = Option.some t) :
    Agrees src dst vm dm (pushLink q os od) vmap dmap := by
  cases os <;> cases od
  all_goals try exact ha
  obtain ⟨h1, h2, h3⟩ := hf _ _ rfl rfl
  exact agrees_push_pack ha hpk h1 h2 h3

/-- The updated maps + queue after an expand still agree with the reference
(base case, before the ≤3 pushes). -/
theorem agrees_expand_base {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q1 : Queue SmallNatPair} {vmap dmap : IndexMap} {f fStar : Nat}
    (ha1 : Agrees src dst vm dm q1 vmap dmap)
    (hfsz : f < dmap.size) (hfs : fStar < dst.darts.size)
    (hvsz : (src.darts[f]!).head < vmap.size)
    (hcorrect : dm.idx? f = Option.some fStar)
    (hhead : vm.idx? (src.darts[f]!).head = Option.some (dst.darts[fStar]!).head)
    (hdlt : (dst.darts[fStar]!).head < dst.n) :
    Agrees src dst vm dm q1 (vmap.set! (src.darts[f]!).head (OptIdx.some (dst.darts[fStar]!).head))
      (dmap.set! f (OptIdx.some fStar)) := by
  exact ⟨⟨ha1.toBounded.queued_bd,
    IndexMap.wf_set!_some ha1.toBounded.vmap_wf hdlt,
    IndexMap.wf_set!_some ha1.toBounded.dmap_wf hfs⟩,
    IndexMap.idx?_set!_le hfsz ha1.dmap_le hcorrect,
    IndexMap.idx?_set!_le hvsz ha1.vmap_le hhead, ha1.queue_ok⟩

/-- The reference witnesses the boundary guard: an interior src link forces an
interior dst link. -/
theorem link_guard {dm : IndexMap} {os od : OptIdx}
    (hhom : ∀ s, os.get? = Option.some s →
      ∃ t, od.get? = Option.some t ∧ dm.idx? s = Option.some t) :
    ¬(os.isSome && od.isNone) = true := by
  grind [OptIdx.isSome_eq, OptIdx.isNone_eq, Option.isSome_iff_exists]

/-- The reference makes the pushed link pair a correct in-bounds obligation --
exactly what `agrees_pushLink` wants. -/
theorem link_obligation {dm : IndexMap} {os od : OptIdx} {sSize dSize : Nat}
    (hhom : ∀ s, os.get? = Option.some s →
      ∃ t, od.get? = Option.some t ∧ dm.idx? s = Option.some t)
    (hsb : ∀ s, os.get? = Option.some s → s < sSize)
    (hdb : ∀ t, od.get? = Option.some t → t < dSize) :
    ∀ s t, os = OptIdx.some s → od = OptIdx.some t →
      s < sSize ∧ t < dSize ∧ dm.idx? s = Option.some t := by
  rintro s t rfl rfl
  obtain ⟨t', ht', hd⟩ := hhom s (OptIdx.get?_some s)
  obtain rfl : t = t' := by simpa using ht'
  grind [OptIdx.get?_some]

/-- **One step under a reference homomorphism**: from an `Agrees` state the
step never answers `none` (the reference witnesses every consistency check),
and a continuing step keeps `Agrees` and strictly drops `measure`.
Recursion-free; completeness is this lemma folded over the fuel. -/
theorem homStep_agrees {src dst : PseudoConfiguration}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat} {vm dm : IndexMap}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm)
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (ha : Agrees src dst vm dm q vmap dmap) :
    match homStep src dst degreeTest q vmap dmap with
    | .done r => r.isSome
    | .next q' vmap' dmap' =>
        Agrees src dst vm dm q' vmap' dmap' ∧ measure q' dmap' < measure q dmap := by
  unfold homStep
  rcases hpq : q.pop? with _ | ⟨packed, q1⟩ <;> simp only []
  · rfl
  · have hpk : Active q packed := active_head hpq
    have hbd := ha.toBounded.queued_bd packed hpk
    have hcorrect : dm.idx? packed.fst = Option.some packed.snd := ha.queue_ok packed hpk
    have hf : packed.fst < src.darts.size := hbd.1
    have hfs : packed.snd < dst.darts.size := hbd.2
    have hfsz : packed.fst < dmap.size := by
      simpa only [ha.toBounded.dmap_wf.size_eq] using hf
    have hagr1 : Agrees src dst vm dm q1 vmap dmap := agrees_pop ha hpq
    have hmeas1 : measure q1 dmap < measure q dmap := measure_pop_lt hpq
    cases hdd : dmap[packed.fst]! <;> simp only []
    · -- unmapped: expand -- the reference hom witnesses every check, so no `none`
      obtain ⟨hhead, hrev, hsucc, hpred⟩ := hom.2.1 packed.fst packed.snd hcorrect
      have hsrcD := dart_inBounds hsrc hf
      have hdstD := dart_inBounds hdst hfs
      have hhsz : src.darts[packed.fst]!.head < vmap.size := by
        simpa only [ha.toBounded.vmap_wf.size_eq] using hsrcD.head_lt
      have hfresh : dmap.idx? packed.fst = Option.none :=
        IndexMap.idx?_eq_none_of_not_isSome hfsz (by simp [hdd])
      -- head consistency: if `vmap[h]` is set it already agrees with the hom
      have hvhead : vmap[src.darts[packed.fst]!.head]!.isSome = true →
          vmap[src.darts[packed.fst]!.head]! = OptIdx.some dst.darts[packed.snd]!.head := by
        grind [Agrees, idx?_of_isSome, getElem!_eq_of_idx?]
      -- discharge the four `none` guards; the reference witnesses the two
      -- boundary guards (`link_guard`)
      rw [if_neg (by grind), if_neg (by have := hom.2.2 _ _ hhead; grind),
        if_neg (link_guard hsucc), if_neg (link_guard hpred)]
      have hbase := agrees_expand_base hagr1 hfsz hfs hhsz hcorrect hhead hdstD.head_lt
      have ha1 := agrees_push_pack hbase hpack hsrcD.rev_lt hdstD.rev_lt hrev
      have hunm := unmapped_set!_lt (v := packed.snd) hfsz hfresh
      refine ⟨agrees_pushLink (agrees_pushLink ha1 hpack
            (link_obligation hsucc hsrcD.succ_lt hdstD.succ_lt))
          hpack (link_obligation hpred hsrcD.pred_lt hdstD.pred_lt), ?_⟩
      grind [measure, Queue.live_push, live_pushLink_le, Queue.live_pop]
    · -- already mapped, and correctly (`hcorrect`)
      rename_i d
      have heqd : dm.idx? packed.fst = Option.some d :=
        ha.dmap_le _ _ (IndexMap.idx?_eq_of_getElem! hfsz hdd)
      rw [if_neg (by grind)]
      exact ⟨hagr1, hmeas1⟩

/-- **Completeness on the fuel driver**: given a reference homomorphism, from
any `Agrees` state with enough fuel, `homCoreGoImp` returns `some`. Ordinary
induction on fuel over `homStep_agrees`. -/
theorem homCoreGoImp_complete {src dst : PseudoConfiguration}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat} {vm dm : IndexMap}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    ∀ fuel q vmap dmap, Agrees src dst vm dm q vmap dmap → measure q dmap < fuel →
      ∃ r, homCoreGoImp src dst degreeTest fuel q vmap dmap = some r := by
  intro fuel
  induction fuel with
  | zero => grind
  | succ fuel ih =>
    intro q vmap dmap ha hm
    have h := homStep_agrees hsrc hdst hpack hom ha
    rw [homCoreGoImp]
    rcases heq : homStep src dst degreeTest q vmap dmap with r | ⟨q', vmap', dmap'⟩ <;>
      simp only []
    · grind [Option.isSome_iff_exists]
    · obtain ⟨ha', hlt⟩ : _ ∧ _ := by simpa only [heq] using h
      exact ih q' vmap' dmap' ha' (by grind)

/-- **Completeness of `homCore`**: if a rooted homomorphism `src → dst` exists,
the seeded BFS returns `some`. The seed state `Agrees` with the reference hom
(the root pair is queued and correct, the maps start empty), so `homCoreGoImp`
succeeds at enough fuel and the bridge transports it to `homCoreGo` = `homCore`. -/
theorem homCore_complete {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {vm dm : IndexMap} (hsrc : src.WF) (hdst : dst.WF)
    (hpack : dst.darts.size ≤ pairBase)
    (hdf : dartFrom < src.darts.size) (hdt : dartTo < dst.darts.size)
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    ∃ r, homCore src dartFrom dst dartTo degreeTest = some r := by
  obtain ⟨hxfst, hxsnd, hactive⟩ := seed_root dartFrom (src.darts.size * 3 + 1) hpack hdt
  have hagr : Agrees src dst vm dm
      ((Queue.emptyWithCapacity (src.darts.size * 3 + 1)).push (pack dartFrom dartTo))
      (Array.replicate src.n OptIdx.none) (Array.replicate src.darts.size OptIdx.none) := by
    refine ⟨⟨fun p hp => ?_,
      IndexMap.wf_replicate_none, IndexMap.wf_replicate_none⟩, ?_, ?_, fun p hp => ?_⟩
    · rw [hactive p hp]
      grind
    all_goals grind [IndexMap.idx?_replicate_none, IsRootedHom]
  obtain ⟨r, hr⟩ := homCoreGoImp_complete hsrc hdst hpack hom _ _ _ _ hagr (Nat.lt_succ_self _)
  exact ⟨r, homCoreGoImp_le _ _ _ _ _ hr⟩

/-- **`homomorphismExists` is complete**: if a rooted homomorphism exists, the
`.isSome` fast path reports it. With `homomorphismExists_sound`, this gives
`homomorphismExists = true ↔ ∃ hom` -- the equivalence the containment checks
rely on. -/
theorem homomorphismExists_complete {src dst : PseudoConfiguration}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    (hdf : dartFrom < src.darts.size) (hdt : dartTo < dst.darts.size)
    (h : ∃ vm dm, IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    homomorphismExists src dartFrom dst dartTo degreeTest = true := by
  grind [homomorphismExists, homCore_complete]

end PseudoConfiguration.HomState

end NearLinear4ct
