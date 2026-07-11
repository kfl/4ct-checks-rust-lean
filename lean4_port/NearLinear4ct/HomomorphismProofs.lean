import NearLinear4ct.PseudoConfiguration
import NearLinear4ct.MappingProofs
import NearLinear4ct.PseudoTriangulationProofs
import NearLinear4ct.UtilProofs

/-!
Machine-checked correctness of the homomorphism BFS
(`PseudoConfiguration.homCoreGo`, Appendix A.2), organised as three invariants
threaded through the BFS by per-step preservation:

* `Bounded`: structural well-formedness -- sizes and in-bounds -- yielding
  output well-formedness and feeding the termination measure.
* `Sound`: dart-local consistency (the paper's Sec. 9 homomorphism definition),
  yielding soundness of `homCore`/`homomorphismExists`.
* `Agrees`: agreement with a reference homomorphism, yielding completeness
  (no false negatives).

`homCoreGo` is a `partial_fixpoint`, so it exposes `homCoreGo.partial_correctness`
-- a partial-correctness (Scott) induction principle needing no termination
proof. `Bounded` and `Sound` ride on that directly; `Agrees` runs on a
fuel-based total twin (`homCoreGoImp`) with a termination bridge back to
`homCoreGo`, since completeness needs the BFS to actually return.
-/

namespace NearLinear4ct

-- The obligation type's members (`pack`, `pairBase`, `fst_pack`, ...) are used
-- throughout; the bare type `SmallNatPair` still appears in signatures. `OptIdx`
-- is deliberately *not* opened -- its `some`/`none` would collide with `Option`.
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

open NearLinear4ct

/-- Active (not-yet-popped) queue entries: an index `≥ head` holding `p`. -/
def Active (q : Queue SmallNatPair) (p : SmallNatPair) : Prop :=
  ∃ i, q.head ≤ i ∧ q.items[i]? = some p

/-- `pop` only shrinks the active set (`head` advances; `items` is untouched). -/
theorem active_pop {q : Queue SmallNatPair} {p : SmallNatPair}
    (h : Active q.pop!.2 p) : Active q p := by
  grind [Active, Queue.pop!]

/-- `push` adds exactly the new element to the active set. -/
theorem active_push {q : Queue SmallNatPair} {x p : SmallNatPair}
    (h : Active (q.push x) p) : Active q p ∨ p = x := by
  grind [Active, Queue.push]

/-- The just-popped element was active. -/
theorem active_head {q : Queue SmallNatPair} (h : q.isEmpty = false) :
    Active q q.pop!.1 := by
  refine ⟨q.head, Nat.le_refl _, ?_⟩
  grind [Queue.pop!, Queue.isEmpty, Array.getElem?_eq_getElem]

/-- **Structural invariant** (`Bounded` half of `HomState.WF`): sizes + all
indices in bounds. Enough for output-WF; no dart-local (semantic) content. -/
structure Bounded (src dst : PseudoConfiguration)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Prop where
  queue_wf   : q.head ≤ q.items.size
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

/-- `push` keeps `queue_wf`. -/
theorem queue_wf_push {q : Queue SmallNatPair} {x : SmallNatPair}
    (h : q.head ≤ q.items.size) : (q.push x).head ≤ (q.push x).items.size := by
  grind [Queue.push]

/-- Pushing an in-bounds element keeps `Bounded` (maps untouched). -/
theorem bounded_push {src dst : PseudoConfiguration}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {x : SmallNatPair}
    (hb : Bounded src dst q vmap dmap)
    (hx : x.fst < src.darts.size ∧ x.snd < dst.darts.size) :
    Bounded src dst (q.push x) vmap dmap := by
  grind [Bounded, queue_wf_push, active_push]

/-- An in-range interior pointer's `idx!` is bounded (bridges `isSome`/`get?`/`idx!`). -/
theorem idx!_lt_of_isSome {o : OptIdx} {D : Nat}
    (hbd : ∀ j, o.get? = Option.some j → j < D) (hs : o.isSome = true) : o.idx! < D := by
  grind [OptIdx.isSome_eq, OptIdx.idx!_of_get?_some, Option.isSome_iff_exists]

/-- From a passed boundary guard `!(os.isSome && od.isNone)` and `os.isSome`,
the target link is present. The shared `hbsucc`/`hbpred` derivation. -/
theorem dst_isSome_of_guard {os od : OptIdx} (hg : ¬(os.isSome && od.isNone) = true)
    (hs : os.isSome = true) : od.isSome = true := by
  grind [OptIdx.isSome, OptIdx.isNone]

/-- All three pushed obligations (`rev` unconditional, `succ`/`pred` under their
boundary guards) are in-bounds -- the bundle handed to grind in the expand case
(`homCoreGo_output_wf`/`homCoreGo_sound`). Takes the dart `InBounds` *structures*
directly, so its premises are concrete facts grind can match and it works as a
hint -- unlike a version abstracted over the link, whose `∀`-bound premises grind
won't instantiate. Composes `pack_bounded`/`idx!_lt_of_isSome`/`dst_isSome_of_guard`. -/
theorem push_bounds {src dst : PseudoConfiguration} {f fStar : Nat}
    (hsrcD : (src.darts[f]!).InBounds src.n src.darts.size)
    (hdstD : (dst.darts[fStar]!).InBounds dst.n dst.darts.size)
    (hpack : dst.darts.size ≤ pairBase)
    (hsg : ¬((src.darts[f]!).succ.isSome && (dst.darts[fStar]!).succ.isNone) = true)
    (hpg : ¬((src.darts[f]!).pred.isSome && (dst.darts[fStar]!).pred.isNone) = true) :
    ((pack (src.darts[f]!).rev (dst.darts[fStar]!).rev).fst < src.darts.size ∧
        (pack (src.darts[f]!).rev (dst.darts[fStar]!).rev).snd < dst.darts.size) ∧
      ((src.darts[f]!).succ.isSome = true →
        (pack (src.darts[f]!).succ.idx! (dst.darts[fStar]!).succ.idx!).fst < src.darts.size ∧
          (pack (src.darts[f]!).succ.idx! (dst.darts[fStar]!).succ.idx!).snd < dst.darts.size) ∧
      ((src.darts[f]!).pred.isSome = true →
        (pack (src.darts[f]!).pred.idx! (dst.darts[fStar]!).pred.idx!).fst < src.darts.size ∧
          (pack (src.darts[f]!).pred.idx! (dst.darts[fStar]!).pred.idx!).snd < dst.darts.size) :=
  ⟨pack_bounded hpack hsrcD.rev_lt hdstD.rev_lt,
    fun hs => pack_bounded hpack (idx!_lt_of_isSome hsrcD.succ_lt hs)
      (idx!_lt_of_isSome hdstD.succ_lt (dst_isSome_of_guard hsg hs)),
    fun hs => pack_bounded hpack (idx!_lt_of_isSome hsrcD.pred_lt hs)
      (idx!_lt_of_isSome hdstD.pred_lt (dst_isSome_of_guard hpg hs))⟩

/-- **Re-pop branch preservation**: popping (maps unchanged) keeps `Bounded`. -/
theorem bounded_pop {src dst : PseudoConfiguration}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (hb : Bounded src dst q vmap dmap) (hne : q.isEmpty = false) :
    Bounded src dst q.pop!.2 vmap dmap := by
  grind [Bounded, Queue.pop!, Queue.isEmpty, active_pop]

/-- The dart at an in-range index is `InBounds` (unfolding the `!`-read). The
shared `hsrcD`/`hdstD` step in every loop-body proof. -/
theorem dart_inBounds {c : PseudoConfiguration} (hwf : c.WF) {i : Nat}
    (h : i < c.darts.size) : (c.darts[i]!).InBounds c.n c.darts.size := by
  rw [getElem!_pos c.darts i h]; exact hwf.1 i h

/-- **Output well-formedness**: from a `Bounded` state, whenever `homCoreGo`
returns `some (vmap, dmap)`, both maps are well-formed `IndexMap`s. Proved by
`partial_fixpoint`'s partial-correctness principle (no termination needed):
`Bounded` is the loop invariant, preserved by the single per-step argument. -/
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
  split at hstep
  · -- base case: q.isEmpty, so r = (vmap, dmap)
    grind [OutputWF, Bounded]
  · -- q not empty: pop, then re-pop / expand
    rename_i hne'
    have hne : q.isEmpty = false := by simpa using hne'
    rcases hpop : q.pop! with ⟨packed, q1⟩
    have hfb := hb.queued_bd packed (by simpa only [hpop] using active_head hne)
    have hbpop : Bounded src dst q1 vmap dmap := by
      simpa only [hpop] using bounded_pop hb hne
    have hbase : Bounded src dst q1
        (vmap.set! (src.darts[packed.fst]!).head (OptIdx.some (dst.darts[packed.snd]!).head))
        (dmap.set! packed.fst (OptIdx.some packed.snd)) :=
      ⟨hbpop.queue_wf, hbpop.queued_bd,
        IndexMap.wf_set!_some hb.vmap_wf (dart_inBounds hdst hfb.2).head_lt,
        IndexMap.wf_set!_some hb.dmap_wf hfb.2⟩
    grind [bounded_push, push_bounds, OutputWF, Bounded, unpackPair, dart_inBounds]

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
  rcases hd with hdone | ⟨p, ha, _, _⟩
  · exact hdone
  · exact absurd ha (not_active_of_isEmpty h p)

/-- `push` only adds to the active set. -/
theorem active_push_mono {q : Queue SmallNatPair} {x p : SmallNatPair}
    (h : Active q p) : Active (q.push x) p := by
  obtain ⟨i, hi, hp⟩ := h
  exact ⟨i, hi, by grind [Queue.push, Array.getElem?_push_lt, Array.getElem?_eq_none]⟩

/-- The just-pushed element is active (given the queue is well-formed). -/
theorem active_push_self {q : Queue SmallNatPair} {x : SmallNatPair}
    (hqw : q.head ≤ q.items.size) : Active (q.push x) x := by
  exact ⟨q.items.size, hqw, by simp [Queue.push]⟩

/-- Popping either keeps `p` active or reveals it as the just-popped element. -/
theorem active_pop_cases {q : Queue SmallNatPair} {p : SmallNatPair}
    (hne : q.isEmpty = false) (h : Active q p) :
    Active q.pop!.2 p ∨ p = q.pop!.1 := by
  grind [Active, Queue.pop!, Queue.isEmpty]

/-- `DoneOrQueued` is monotone under `push` (the queue only grows). -/
theorem doneOrQueued_push {q : Queue SmallNatPair} {dmap : IndexMap} {g gStar : Nat}
    {x : SmallNatPair} (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued (q.push x) dmap g gStar := by
  grind [DoneOrQueued, Queued, active_push_mono]

/-- **Re-pop transport**: popping keeps `DoneOrQueued`, given the popped element
is already consistently mapped (so if it was the sole witness, it is now done). -/
theorem doneOrQueued_pop {q : Queue SmallNatPair} {dmap : IndexMap} {g gStar : Nat}
    (hne : q.isEmpty = false)
    (hdone : dmap.idx? (q.pop!.1).fst = Option.some (q.pop!.1).snd)
    (hd : DoneOrQueued q dmap g gStar) : DoneOrQueued q.pop!.2 dmap g gStar := by
  grind [DoneOrQueued, active_pop_cases, Queued]

/-- **Expand transport**: popping the fresh `(f, fStar)` and mapping it keeps
`DoneOrQueued`. A done witness `g ≠ f` survives the `set!`; the popped witness
becomes done via the fresh mapping. -/
theorem doneOrQueued_expand_pop {q : Queue SmallNatPair} {dmap : IndexMap}
    {g gStar f fStar : Nat} (hne : q.isEmpty = false) (hfsz : f < dmap.size)
    (hfresh : dmap.idx? f = Option.none)
    (hpf : (q.pop!.1).fst = f) (hps : (q.pop!.1).snd = fStar)
    (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued q.pop!.2 (dmap.set! f (OptIdx.some fStar)) g gStar := by
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
  intro s hs; obtain ⟨t, ht, hdq⟩ := hlp s hs; exact ⟨t, ht, htrans hdq⟩

/-- The fresh-dart (`g = f`) half of `succ_pending`/`pred_pending`: once `f` is
mapped and its `succ`/`pred` obligation pushed, that link is `LinkPending`. -/
theorem freshLink_pending {q' : Queue SmallNatPair} {dmap' : IndexMap} {os od : OptIdx}
    {D : Nat} (hpack : D ≤ pairBase) (hdb : ∀ j, od.get? = Option.some j → j < D)
    (hg : ¬(os.isSome && od.isNone) = true)
    (hactive : os.isSome = true → Active q' (pack os.idx! od.idx!)) :
    LinkPending q' dmap' os od := by
  intro s hs
  have hss : os.isSome = true := by simp [hs]
  have hds := dst_isSome_of_guard hg hss
  have hlt : od.idx! < pairBase := Nat.lt_of_lt_of_le (idx!_lt_of_isSome hdb hds) hpack
  obtain ⟨t, hts⟩ : ∃ t, od.get? = Option.some t :=
    Option.isSome_iff_exists.mp (OptIdx.isSome_eq _ ▸ hds)
  exact ⟨t, hts, Or.inr ⟨pack os.idx! od.idx!, hactive hss,
    (fst_pack _ _ hlt).trans (OptIdx.idx!_of_get?_some hs),
    (snd_pack _ _ hlt).trans (OptIdx.idx!_of_get?_some hts)⟩⟩

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
    IsRootedHom src dst degreeTest dartFrom dartTo vmap dmap :=
  ⟨done_of_isEmpty hq hs.root_pending,
    fun f fStar hf => ⟨hs.dart_head_ok f fStar hf, done_of_isEmpty hq (hs.rev_pending f fStar hf),
      (hs.succ_pending f fStar hf · · |>.imp fun _ ⟨w1, w2⟩ => ⟨w1, done_of_isEmpty hq w2⟩),
      (hs.pred_pending f fStar hf · · |>.imp fun _ ⟨w1, w2⟩ => ⟨w1, done_of_isEmpty hq w2⟩)⟩,
    hs.degree_ok⟩

/-- Discharge the re-pop consistency test: `¬(dv != some n)` means `dv = some n`. -/
theorem optIdx_eq_of_not_bne {dv : OptIdx} {n : Nat}
    (h : ¬(dv != OptIdx.some n) = true) : dv = OptIdx.some n := by
  simpa using h

/-- **Re-pop preservation** of `Sound`: popping an already-consistent element
keeps the invariant (maps unchanged; every pending clause transports by
`doneOrQueued_pop`). -/
theorem sound_pop {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap) (hne : q.isEmpty = false)
    (hdone : dmap.idx? (q.pop!.1).fst = Option.some (q.pop!.1).snd) :
    Sound src dst degreeTest dartFrom dartTo q.pop!.2 vmap dmap :=
  ⟨bounded_pop hs.toBounded hne, doneOrQueued_pop hne hdone hs.root_pending,
    hs.dart_head_ok, hs.degree_ok,
    (hs.rev_pending · · · |> doneOrQueued_pop hne hdone),
    (hs.succ_pending · · · |>.transport (doneOrQueued_pop hne hdone)),
    (hs.pred_pending · · · |>.transport (doneOrQueued_pop hne hdone))⟩

/-- **Soundness of `homCoreGo`**: from a `Sound` state, any `some (vmap, dmap)`
result is a genuine rooted homomorphism (`IsRootedHom`). The BFS decides the
paper's Sec. 9 predicate. Proved by `Sound`-preservation through
`.partial_correctness` -- base case = `isRootedHom_of_sound_isEmpty`, re-pop =
`sound_pop`, expand = the fresh mapping + pushes threaded through the pending
transporters. -/
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
  split at hstep
  · -- base case
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hstep)
    exact isRootedHom_of_sound_isEmpty hs (by assumption)
  · rename_i hne'
    have hne : q.isEmpty = false := by simpa using hne'
    rcases hpop : q.pop! with ⟨packed, q1⟩
    rw [hpop] at hstep
    simp only [unpackPair] at hstep
    have hpk : Active q packed := by simpa only [hpop] using active_head hne
    have hfb := hs.queued_bd packed hpk
    have hfsz : packed.fst < dmap.size := by rw [hs.dmap_wf.size_eq]; exact hfb.1
    have hpop1 : q.pop!.1 = packed := by rw [hpop]
    have hpop2 : q.pop!.2 = q1 := by rw [hpop]
    split at hstep
    · -- dv.isSome: already mapped; the consistency guard passes, then re-pop
      simp only [Option.ite_none_left_eq_some] at hstep
      obtain ⟨hcons, hstep⟩ := hstep
      have hdone : dmap.idx? (q.pop!.1).fst = Option.some (q.pop!.1).snd := by
        rw [hpop1]; exact IndexMap.idx?_eq_of_getElem! hfsz (optIdx_eq_of_not_bne hcons)
      exact ih q1 vmap dmap r hstep (hpop2 ▸ sound_pop hs hne hdone)
    · -- dv none: expand
      rename_i hdv
      have hfresh : dmap.idx? packed.fst = Option.none :=
        IndexMap.idx?_eq_none_of_not_isSome hfsz (by simpa using hdv)
      have hsrcD := dart_inBounds hsrc hfb.1
      have hdstD := dart_inBounds hdst hfb.2
      have hq1w : q1.head ≤ q1.items.size :=
        hpop2 ▸ (bounded_pop hs.toBounded hne).queue_wf
      have hpf : (q.pop!.1).fst = packed.fst := by rw [hpop1]
      have hps : (q.pop!.1).snd = packed.snd := by rw [hpop1]
      -- flatten the four early-return guards (vmap-conflict, degree, succ/pred
      -- boundary); on the success path each `else` is taken, so all pass
      simp only [Option.ite_none_left_eq_some] at hstep
      obtain ⟨hvvc, hdeg, hsg, hpg, hstep⟩ := hstep
      refine ih _ _ _ _ hstep ?_
      have hvsz : src.darts[packed.fst]!.head < vmap.size := by
        rw [hs.vmap_wf.size_eq]; exact hsrcD.head_lt
      have hvmap'_wf := IndexMap.wf_set!_some
        (i := src.darts[packed.fst]!.head) hs.vmap_wf hdstD.head_lt
      have hdmap'_wf := IndexMap.wf_set!_some (i := packed.fst) hs.dmap_wf hfb.2
      have hq1_qbd : ∀ p, Active q1 p →
          p.fst < src.darts.size ∧ p.snd < dst.darts.size :=
        hpop2 ▸ (bounded_pop hs.toBounded hne).queued_bd
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
        ⟨hq1w, hq1_qbd, hvmap'_wf, hdmap'_wf⟩
      have hexp : ∀ {g gStar}, DoneOrQueued q dmap g gStar →
          DoneOrQueued q1 (dmap.set! packed.fst (OptIdx.some packed.snd)) g gStar :=
        fun hdq => hpop2 ▸ doneOrQueued_expand_pop hne hfsz hfresh hpf hps hdq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- toBounded
        grind [bounded_push, push_bounds]
      · -- root_pending
        grind [doneOrQueued_push, hexp hs.root_pending]
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
          grind [active_push_self, active_push_mono, queue_wf_push]
        · grind [doneOrQueued_push,
            hexp (hs.rev_pending g gStar (IndexMap.idx?_set!_ne (Ne.symm hgf) ▸ hg))]
      · -- succ_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set!_self hfsz ▸ hg)).symm
          refine freshLink_pending hpack hdstD.succ_lt hsg (fun _ => ?_)
          grind [active_push_self, active_push_mono, queue_wf_push]
        · exact (hs.succ_pending g gStar (IndexMap.idx?_set!_ne (Ne.symm hgf) ▸ hg)).transport
            (fun hdq => by grind [doneOrQueued_push, hexp hdq])
      · -- pred_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set!_self hfsz ▸ hg)).symm
          refine freshLink_pending hpack hdstD.pred_lt hpg (fun _ => ?_)
          grind [active_push_self, active_push_mono, queue_wf_push]
        · exact (hs.pred_pending g gStar (IndexMap.idx?_set!_ne (Ne.symm hgf) ▸ hg)).transport
            (fun hdq => by grind [doneOrQueued_push, hexp hdq])

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
  refine ⟨⟨?_, ?_, IndexMap.wf_replicate_none, IndexMap.wf_replicate_none⟩,
    Or.inr ⟨pack dartFrom dartTo,
      active_push_self (by simp [Queue.emptyWithCapacity]), hxfst, hxsnd⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Queue.push, Queue.emptyWithCapacity]
  · intro p hp; grind
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
completeness -- no false negatives) requires a termination argument. We give a
fuel-indexed total copy `homCoreGoImp` and bridge it: whenever the fuel copy
succeeds, the partial fixpoint agrees. Completeness is then proved on the total
copy by ordinary induction. -/

/-- Fuel-based total copy of `homCoreGo` (identical body, `fuel` bounds the
recursion depth; `0` fuel = give up with `none`). -/
def homCoreGoImp (src dst : PseudoConfiguration) (degreeTest : Degree → Degree → Bool) :
    Nat → Queue SmallNatPair → IndexMap → IndexMap → Option (IndexMap × IndexMap)
  | 0, _, _, _ => none
  | fuel + 1, q, vmap, dmap =>
    if q.isEmpty then some (vmap, dmap)
    else
      let (packed, q) := q.pop!
      let (f, fStar) := packed.unpackPair
      let dv := dmap[f]!
      if dv.isSome then
        if dv != OptIdx.some fStar then none
        else homCoreGoImp src dst degreeTest fuel q vmap dmap
      else
        let dmap := dmap.set! f (OptIdx.some fStar)
        let srcD := src.darts[f]!
        let dstD := dst.darts[fStar]!
        let h := srcD.head
        let hStar := dstD.head
        let vv := vmap[h]!
        if vv.isSome && vv != OptIdx.some hStar then none
        else
          let vmap := vmap.set! h (OptIdx.some hStar)
          if !degreeTest (src.degrees[h]!) (dst.degrees[hStar]!) then none
          else if srcD.succ.isSome && dstD.succ.isNone then none
          else if srcD.pred.isSome && dstD.pred.isNone then none
          else
            let q := q.push (pack srcD.rev dstD.rev)
            let q := if srcD.succ.isSome then q.push (pack srcD.succ.idx! dstD.succ.idx!) else q
            let q := if srcD.pred.isSome then q.push (pack srcD.pred.idx! dstD.pred.idx!) else q
            homCoreGoImp src dst degreeTest fuel q vmap dmap

/-- **The termination bridge**: whenever the fuel copy returns `some r`, so does
the `partial_fixpoint` `homCoreGo` (with the same value). Lets completeness be
proved on the total `homCoreGoImp` and transported here. -/
theorem homCoreGoImp_le {src dst : PseudoConfiguration} {degreeTest : Degree → Degree → Bool} :
    ∀ fuel q vmap dmap r, homCoreGoImp src dst degreeTest fuel q vmap dmap = some r →
      homCoreGo src dst degreeTest q vmap dmap = some r := by
  intro fuel
  induction fuel with
  | zero => intro q vmap dmap r h; simp [homCoreGoImp] at h
  | succ fuel ih =>
    intro q vmap dmap r h
    simp only [homCoreGoImp] at h
    rw [homCoreGo.eq_def]
    grind

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
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h a List.mem_cons_self
    simp only [List.countP_cons]; grind

/-- Strict `countP` decrease: a weaker predicate with one strictly-dropped
element counts less. -/
private theorem countP_lt {α} (p q : α → Bool) (l : List α)
    (hle : ∀ x ∈ l, q x = true → p x = true)
    (x : α) (hx : x ∈ l) (hpx : p x = true) (hqx : q x = false) :
    l.countP q < l.countP p := by
  induction l with
  | nil => simp at hx
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
theorem measure_pop_lt {q : Queue SmallNatPair} {dmap : IndexMap} (h : q.isEmpty = false) :
    measure q.pop!.2 dmap < measure q dmap := by
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
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (ha : Agrees src dst vm dm q vmap dmap) (hne : q.isEmpty = false) :
    Agrees src dst vm dm q.pop!.2 vmap dmap := by
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

/-- Conditionally pushing a `pack a b`: only the taken branch need supply a
correct in-bounds obligation. Collapses the `if`-guarded succ/pred pushes into a
single `Agrees` step (no `split`). -/
theorem agrees_push_pack_if {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {cond : Bool} {a b : Nat}
    (ha : Agrees src dst vm dm q vmap dmap) (hpk : dst.darts.size ≤ pairBase)
    (hf : cond = true →
      a < src.darts.size ∧ b < dst.darts.size ∧ dm.idx? a = Option.some b) :
    Agrees src dst vm dm (if cond then q.push (pack a b) else q) vmap dmap := by
  grind [agrees_push_pack]

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
  exact ⟨⟨ha1.toBounded.queue_wf, ha1.toBounded.queued_bd,
    IndexMap.wf_set!_some ha1.toBounded.vmap_wf hdlt,
    IndexMap.wf_set!_some ha1.toBounded.dmap_wf hfs⟩,
    IndexMap.idx?_set!_le hfsz ha1.dmap_le hcorrect,
    IndexMap.idx?_set!_le hvsz ha1.vmap_le hhead, ha1.queue_ok⟩

/-- The single fact serving *both* the `succ` and `pred` expand cases: from an
optional source link that the reference hom maps, its target link is present,
both endpoints are in-bounds, and they agree. `.1` feeds the boundary
`none`-guard; `.2` is exactly the obligation `agrees_push_pack_if` wants. -/
theorem link_fact {dm : IndexMap} {os od : OptIdx} {sSize dSize : Nat}
    (hhom : ∀ s, os.get? = Option.some s →
      ∃ t, od.get? = Option.some t ∧ dm.idx? s = Option.some t)
    (hsb : ∀ s, os.get? = Option.some s → s < sSize)
    (hdb : ∀ t, od.get? = Option.some t → t < dSize)
    (his : os.isSome = true) :
    od.isSome = true ∧
      os.idx! < sSize ∧ od.idx! < dSize ∧ dm.idx? os.idx! = Option.some od.idx! := by
  rw [OptIdx.isSome_eq] at his
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp his
  obtain ⟨t, ht, hdt⟩ := hhom s hs
  rw [OptIdx.idx!_of_get?_some hs, OptIdx.idx!_of_get?_some ht]
  exact ⟨by rw [OptIdx.isSome_eq, ht]; rfl, hsb s hs, hdb t ht, hdt⟩

/-- **Completeness on the total copy**: given a reference homomorphism, from any
`Agrees` state with enough fuel, `homCoreGoImp` returns `some`. Proved by fuel
induction -- the reference witnesses every consistency check (so no `none`
branch fires) and each step drops `measure` (so the fuel suffices). -/
theorem homCoreGoImp_complete {src dst : PseudoConfiguration}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat} {vm dm : IndexMap}
    (hsrc : src.WF) (hdst : dst.WF) (hpack : dst.darts.size ≤ pairBase)
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    ∀ fuel q vmap dmap, Agrees src dst vm dm q vmap dmap → measure q dmap < fuel →
      ∃ r, homCoreGoImp src dst degreeTest fuel q vmap dmap = some r := by
  intro fuel
  induction fuel with
  | zero => intro q vmap dmap _ hm; exact absurd hm (by simp)
  | succ fuel ih =>
    intro q vmap dmap ha hm
    rw [homCoreGoImp]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne'
      have hne : q.isEmpty = false := by simpa using hne'
      rcases hpop : q.pop! with ⟨packed, q1⟩
      have hpk : Active q packed := by simpa only [hpop] using active_head hne
      have hbd := ha.toBounded.queued_bd packed hpk
      have hcorrect : dm.idx? packed.fst = Option.some packed.snd := ha.queue_ok packed hpk
      have hf : packed.fst < src.darts.size := hbd.1
      have hfs : packed.snd < dst.darts.size := hbd.2
      have hfsz : packed.fst < dmap.size := by rw [ha.toBounded.dmap_wf.size_eq]; exact hf
      have hmle : measure q dmap ≤ fuel := by omega
      have hq1e : q1 = q.pop!.2 := by rw [hpop]
      have hagr1 : Agrees src dst vm dm q1 vmap dmap := hq1e ▸ agrees_pop ha hne
      have hmeas1 : measure q1 dmap < fuel := by
        grind [measure_pop_lt]
      simp only [unpackPair]
      split
      · -- dv.isSome: the popped dart is already mapped, and correctly (`hcorrect`)
        rename_i hdvs
        have hd : dmap.idx? packed.fst = Option.some dmap[packed.fst]!.idx! := idx?_of_isSome hfsz hdvs
        have heq : dm.idx? packed.fst = Option.some dmap[packed.fst]!.idx! := ha.dmap_le _ _ hd
        rw [hcorrect] at heq
        rw [if_neg (by rw [getElem!_eq_of_idx? hd]; grind)]
        exact ih q1 vmap dmap hagr1 hmeas1
      · -- dv none: expand -- the reference hom witnesses every check, so no `none`
        rename_i hdvs
        obtain ⟨hhead, hrev, hsucc, hpred⟩ := hom.2.1 packed.fst packed.snd hcorrect
        have hsrcD := dart_inBounds hsrc hf
        have hdstD := dart_inBounds hdst hfs
        have hhsz : src.darts[packed.fst]!.head < vmap.size := by
          rw [ha.toBounded.vmap_wf.size_eq]; exact hsrcD.head_lt
        have hfresh : dmap.idx? packed.fst = Option.none :=
          IndexMap.idx?_eq_none_of_not_isSome hfsz hdvs
        -- head consistency: if `vmap[h]` is set it already agrees with the hom
        have hvhead : vmap[src.darts[packed.fst]!.head]!.isSome = true →
            vmap[src.darts[packed.fst]!.head]! = OptIdx.some dst.darts[packed.snd]!.head := by
          intro hs
          have := ha.vmap_le _ _ (idx?_of_isSome hhsz hs); rw [hhead] at this
          rw [getElem!_eq_of_idx? (idx?_of_isSome hhsz hs)]; grind
        -- `link_fact` bundles both expand cases: `.1` = target present (guards),
        -- `.2` = in-bounds + agree (the pushes). `hds`/`hdp` are the `.1` guards.
        have sfact := link_fact hsucc hsrcD.succ_lt hdstD.succ_lt
        have pfact := link_fact hpred hsrcD.pred_lt hdstD.pred_lt
        have hds := fun h => (sfact h).1
        have hdp := fun h => (pfact h).1
        -- discharge the four `none` guards
        rw [if_neg (by grind), if_neg (by have := hom.2.2 _ _ hhead; grind),
          if_neg (by grind [OptIdx.isSome, OptIdx.isNone]),
          if_neg (by grind [OptIdx.isSome, OptIdx.isNone])]
        have hbase := agrees_expand_base hagr1 hfsz hfs hhsz hcorrect hhead hdstD.head_lt
        have ha1 := agrees_push_pack hbase hpack hsrcD.rev_lt hdstD.rev_lt hrev
        have hunm := unmapped_set!_lt (v := packed.snd) hfsz hfresh
        refine ih _ _ _ ?_ ?_
        · exact agrees_push_pack_if (agrees_push_pack_if ha1 hpack (fun h => (sfact h).2))
            hpack (fun h => (pfact h).2)
        · simp only [measure, Queue.live] at hmeas1 ⊢
          split <;> split <;>
            simp only [Queue.push, Array.size_push] <;> omega

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
    refine ⟨⟨by simp [Queue.push, Queue.emptyWithCapacity], fun p hp => ?_,
      IndexMap.wf_replicate_none, IndexMap.wf_replicate_none⟩, ?_, ?_, fun p hp => ?_⟩
    · rw [hactive p hp]; exact ⟨by rw [hxfst]; exact hdf, by rw [hxsnd]; exact hdt⟩
    · grind [IndexMap.idx?_replicate_none]
    · grind [IndexMap.idx?_replicate_none]
    · rw [hactive p hp, hxfst, hxsnd]; exact hom.1
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
  obtain ⟨vm, dm, hom⟩ := h
  obtain ⟨r, hr⟩ := homCore_complete hsrc hdst hpack hdf hdt hom
  unfold homomorphismExists; rw [hr]; rfl

end PseudoConfiguration.HomState

end NearLinear4ct
