import NearLinear4ct.PseudoConfiguration
import NearLinear4ct.MappingProofs
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
* `Agrees`: agreement with a reference homomorphism (`homStep_agrees`),
  yielding completeness (no false negatives); the structural step theorem
  supplies the strict `measure` decrease independently.

The driver `homCoreGo` is a `partial_fixpoint`, so it exposes
`homCoreGo.partial_correctness` -- a partial-correctness (Scott) induction
principle needing no termination proof; `Bounded` and `Sound` lift through it
in a few lines each. Completeness needs the BFS to actually return, so
`Agrees` folds over `homCoreGoImp`, a fuel-bounded driver of the *same*
`homStep`; `homCoreGo_eq_imp` -- the unconditional totality theorem, riding
the strict `measure` decrease of every continuing step -- equates the two
drivers above the measure, `some` and `none` answers alike.

Both sides enter as `WFConfig` (`PseudoConfiguration.lean`): a configuration
bundled with its erased well-formedness and packability facts, so no lemma
threads `src.WF`/`dst.WF`/`darts.size ≤ pairBase` premises -- the facts are
read off the type (`WFConfig.wf`/`WFConfig.packable`). The per-call root-dart
bounds come from `homCore`'s guard on the soundness side (a `some` answer
means the guard passed), and stay as premises (`hdf`/`hdt`) on the
completeness side, which must show the guard passes.
-/

namespace NearLinear4ct

-- The obligation type's members (`pack`, `pairBase`, `fst_pack`, ...) are used
-- throughout; the bare type `SmallNatPair` still appears in signatures.
open SmallNatPair

namespace OptIdx

/-- Passing `homStep`'s map-conflict guard means the slot is either empty or
already contains the required image. -/
theorem eq_none_or_eq_some_of_not_conflict {dv : OptIdx} {n : Nat}
    (h : ¬(dv.isSome && dv != OptIdx.some n) = true) :
    dv = OptIdx.none ∨ dv = OptIdx.some n := by
  cases dv <;> grind [OptIdx.isSome, OptIdx.some]

/-- If every occupied slot has the required image, `homStep`'s map-conflict
guard cannot fire. -/
theorem not_conflict_of_eq_some_when_isSome {dv : OptIdx} {n : Nat}
    (h : dv.isSome = true → dv = OptIdx.some n) :
    ¬(dv.isSome && dv != OptIdx.some n) = true := by
  grind only

end OptIdx

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

/-- `idx?` view of a slot that passes `homStep`'s map-conflict guard. -/
theorem idx?_none_or_eq_some_of_not_conflict {m : IndexMap} {i n : Nat}
    (hi : i < m.size)
    (h : ¬(m[i]!.isSome && m[i]! != OptIdx.some n) = true) :
    m.idx? i = Option.none ∨ m.idx? i = Option.some n := by
  have hc := OptIdx.eq_none_or_eq_some_of_not_conflict h
  grind only [idx?_eq_of_getElem!, idx?_eq_none_of_not_isSome]

/-- The all-`none` replicate is unmapped everywhere. -/
theorem idx?_replicate_none {n i : Nat} :
    idx? (Array.replicate n OptIdx.none) i = Option.none := by
  grind [idx?, OptIdx.get?_none]

/-- Writing through the proof-carrying `set` is the `set!` the lemma library
speaks about (the bound makes `setIfInBounds` take its write branch). -/
theorem set_eq_set! {m : IndexMap} {i : Nat} {v : OptIdx}
    (h : i < m.size) : m.set i v h = m.set! i v := by
  grind [Array.set!, Array.setIfInBounds]

/-- `WF` through the proof-carrying write (`wf_set!_some` in the `set`
vocabulary the implementation uses). -/
theorem wf_set_some {m : IndexMap} {dom codom i v : Nat} {h : i < m.size}
    (hm : m.WF dom codom) (hv : v < codom) :
    IndexMap.WF (m.set i (OptIdx.some v) h) dom codom :=
  (set_eq_set! h).symm ▸ wf_set!_some hm hv

/-- `idx?` at the just-written index, `set` vocabulary. -/
theorem idx?_set_self {m : IndexMap} {i v : Nat} (h : i < m.size) :
    idx? (m.set i (OptIdx.some v) h) i = Option.some v :=
  (set_eq_set! h).symm ▸ idx?_set!_self h

/-- `idx?` at a different index, `set` vocabulary. -/
theorem idx?_set_ne {m : IndexMap} {i j v : Nat} {h : i < m.size} (hne : i ≠ j) :
    idx? (m.set i (OptIdx.some v) h) j = idx? m j :=
  (set_eq_set! h).symm ▸ idx?_set!_ne hne

/-- Restriction extension (`idx?_set!_le`), `set` vocabulary. -/
theorem idx?_set_le {m mref : IndexMap} {k v : Nat} (hk : k < m.size)
    (hle : ∀ i j, idx? m i = Option.some j → idx? mref i = Option.some j)
    (hnew : idx? mref k = Option.some v) :
    ∀ i j, idx? (m.set k (OptIdx.some v) hk) i = Option.some j →
      idx? mref i = Option.some j :=
  (set_eq_set! hk).symm ▸ idx?_set!_le hk hle hnew

/-- Read `idx?` off a proof-carrying read. -/
theorem idx?_eq_of_getElem {m : IndexMap} {i v : Nat} {h : i < m.size}
    (he : m[i]'h = OptIdx.some v) : idx? m i = Option.some v :=
  idx?_eq_of_getElem! h ((getElem!_pos m i h).trans he)

/-- Read an empty `idx?` slot off a proof-carrying read. -/
theorem idx?_eq_none_of_getElem {m : IndexMap} {i : Nat} {h : i < m.size}
    (he : m[i]'h = OptIdx.none) : idx? m i = Option.none :=
  idx?_eq_none_of_not_isSome h (by simp [(getElem!_pos m i h).trans he])

/-- The all-`none` replicate is a well-formed (empty) map. -/
theorem wf_replicate_none {n codom : Nat} :
    IndexMap.WF (Array.replicate n OptIdx.none) n codom := by
  grind [IndexMap.WF, IndexMap.Bounded, OptIdx.get?_none]

end IndexMap

namespace PseudoConfiguration.HomState

/-- The threaded worklist invariant covers every active (live) element. -/
theorem HomBounded.active {sD dD : Nat} {q : Queue SmallNatPair}
    (hb : HomBounded sD dD q) {p : SmallNatPair} (hp : q.Active p) :
    p.fst < sD ∧ p.snd < dD := by
  obtain ⟨i, -, hi⟩ := hp
  grind [HomBounded]

/-- **Structural invariant** (`Bounded` half of `HomState.WF`): sizes + all
indices in bounds. Enough for output-WF; no dart-local (semantic) content.
The queue clause is the executable layer's `HomBounded` -- one structural
invariant, no parallel versions; active-element bounds follow through
`HomBounded.active`, and the threaded size facts are `vmap_wf.size_eq`/
`dmap_wf.size_eq`. -/
structure Bounded (src dst : PseudoConfiguration)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Prop where
  queued_bd  : HomBounded src.darts.size dst.darts.size q
  vmap_wf    : IndexMap.WF vmap src.n dst.n
  dmap_wf    : IndexMap.WF dmap src.darts.size dst.darts.size

/-- The semantic structural invariant supplies the executable indexing
invariant; semantic step lemmas therefore need not thread a second proof. -/
theorem Bounded.toIndexSafe {src dst : WFConfig}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (hb : Bounded src dst q vmap dmap) : HomIndexSafe src dst q vmap dmap :=
  ⟨hb.queued_bd, hb.vmap_wf.size_eq, hb.dmap_wf.size_eq⟩

/-- The maps `homCoreGo` returns are well-formed `IndexMap`s. -/
def OutputWF (src dst : PseudoConfiguration) (r : IndexMap × IndexMap) : Prop :=
  IndexMap.WF r.1 src.n dst.n ∧ IndexMap.WF r.2 src.darts.size dst.darts.size

/-- A pushed `pack a b` decodes in bounds, given the dst side fits the pair base. -/
theorem pack_bounded {src dst : WFConfig} {a b : Nat}
    (ha : a < src.darts.size) (hb : b < dst.darts.size) :
    (pack a b).fst < src.darts.size ∧
      (pack a b).snd < dst.darts.size := by
  grind [WFConfig.packable]

/-- Pushing an in-bounds element keeps `Bounded` (maps untouched). -/
theorem bounded_push {src dst : PseudoConfiguration}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {x : SmallNatPair}
    (hb : Bounded src dst q vmap dmap)
    (hx : x.fst < src.darts.size ∧ x.snd < dst.darts.size) :
    Bounded src dst (q.push x) vmap dmap :=
  ⟨hb.queued_bd.push hx, hb.vmap_wf, hb.dmap_wf⟩

/-! `pushLink` is the expand step's conditional push, so the invariant
lemmas speak about it as one operation. Each lemma case-splits the two links;
the both-`some` arm is a plain `push`, every other arm is the identity. -/

/-- `pushLink` grows the live length by at most one. -/
theorem live_pushLink_le {q : Queue SmallNatPair} {os od : OptIdx} :
    (pushLink q os od).live ≤ q.live + 1 := by
  grind [pushLink.eq_def, Queue.live, Queue.push]

/-- `pushLink` on in-range links (the dart `InBounds` fields) keeps `Bounded`. -/
theorem bounded_pushLink {src dst : WFConfig}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {os od : OptIdx}
    (hb : Bounded src dst q vmap dmap)
    (hs : ∀ j, os.get? = Option.some j → j < src.darts.size)
    (hd : ∀ j, od.get? = Option.some j → j < dst.darts.size) :
    Bounded src dst (pushLink q os od) vmap dmap :=
  ⟨hb.queued_bd.pushLink dst.packable hs hd, hb.vmap_wf, hb.dmap_wf⟩

/-- **Re-pop branch preservation**: popping (maps unchanged) keeps `Bounded`. -/
theorem bounded_pop {src dst : PseudoConfiguration}
    {q q' : Queue SmallNatPair} {x : SmallNatPair} {vmap dmap : IndexMap}
    (hp : q.pop? = some (x, q')) (hb : Bounded src dst q vmap dmap) :
    Bounded src dst q' vmap dmap :=
  ⟨(hb.queued_bd.pop hp).2, hb.vmap_wf, hb.dmap_wf⟩

/-- **One step preserves `Bounded`**: a continuing step's state is `Bounded`,
and a `done` exit that answers `some` is well-formed output. Recursion-free --
the driver lemma `homCoreGo_output_wf` lifts it through the loop. -/
theorem homStep_bounded
    {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (hb : Bounded src dst q vmap dmap) :
    match homStep src dst degreeTest q vmap dmap hb.toIndexSafe with
    | .done r => ∀ p, r = some p → OutputWF src dst p
    | .next q' vmap' dmap' => Bounded src dst q' vmap' dmap' := by
  rcases hpq : q.pop? with _ | ⟨packed, q1⟩ <;> unfold homStep
  · -- base case: `pop?` exhausted, the maps are the answer
    grind [OutputWF, Bounded]
  · -- q not empty: pop, then re-pop / expand
    have hfb := (hb.queued_bd.pop hpq).1
    have hsrcD := src.wf.1 packed.fst hfb.1
    have hdstD := dst.wf.1 packed.snd hfb.2
    have hbase : Bounded src dst q1
        (vmap.set (src.darts[packed.fst]'hfb.1).head
          (OptIdx.some (dst.darts[packed.snd]'hfb.2).head)
          (hb.vmap_wf.size_eq.symm ▸ hsrcD.head_lt))
        (dmap.set packed.fst (OptIdx.some packed.snd)
          (hb.dmap_wf.size_eq.symm ▸ hfb.1)) :=
      ⟨(hb.queued_bd.pop hpq).2,
        IndexMap.wf_set_some hb.vmap_wf hdstD.head_lt,
        IndexMap.wf_set_some hb.dmap_wf hfb.2⟩
    -- `Bounded` through the three pushes, in order
    have hb1 := bounded_push hbase (pack_bounded hsrcD.rev_lt hdstD.rev_lt)
    have hb2 := bounded_pushLink hb1 hsrcD.succ_lt hdstD.succ_lt
    have hb3 := bounded_pushLink hb2 hsrcD.pred_lt hdstD.pred_lt
    grind [OutputWF, Bounded]

/-- **Output well-formedness**: whenever `homCoreGo` returns from a `Bounded`
state, both maps are well-formed `IndexMap`s. `homStep_bounded` lifted through
the driver by `partial_correctness` (no termination needed). -/
theorem homCoreGo_output_wf
    {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {r : IndexMap × IndexMap}
    (hb : Bounded src dst q vmap dmap)
    (hrun : homCoreGo src dst degreeTest q vmap dmap hb.toIndexSafe = some r) :
    OutputWF src dst r := by
  refine homCoreGo.partial_correctness src dst degreeTest
    (motive := fun q vmap dmap _hs r =>
      Bounded src dst q vmap dmap → OutputWF src dst r)
    ?step q vmap dmap hb.toIndexSafe r hrun hb
  intro rec ih q vmap dmap hs r hstep hb
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
  ∃ p, q.Active p ∧ p.fst = f ∧ p.snd = fStar

/-- Either already mapped consistently, or pending in the queue. -/
def DoneOrQueued (q : Queue SmallNatPair) (dmap : IndexMap) (f fStar : Nat) : Prop :=
  dmap.idx? f = Option.some fStar ∨ Queued q f fStar

/-- On an empty queue, `DoneOrQueued` collapses to `Done`. -/
theorem done_of_isEmpty {q : Queue SmallNatPair} {dmap : IndexMap} {f fStar : Nat}
    (h : q.isEmpty = true) (hd : DoneOrQueued q dmap f fStar) :
    dmap.idx? f = Option.some fStar := by
  grind [DoneOrQueued, Queued, Queue.not_active_of_isEmpty]

theorem active_pushLink_mono {q : Queue SmallNatPair} {os od : OptIdx} {p : SmallNatPair}
    (h : q.Active p) : (pushLink q os od).Active p := by
  grind [pushLink.eq_def, Queue.active_push_mono]

/-- The pair `pushLink` queues on interior links is active. -/
theorem active_pushLink_self {q : Queue SmallNatPair} {s t : Nat} :
    (pushLink q (OptIdx.some s) (OptIdx.some t)).Active (pack s t) :=
  Queue.active_push_self

/-- `DoneOrQueued` is monotone under `push` (the queue only grows). -/
theorem doneOrQueued_push {q : Queue SmallNatPair} {dmap : IndexMap} {g gStar : Nat}
    {x : SmallNatPair} (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued (q.push x) dmap g gStar := by
  grind [DoneOrQueued, Queued, Queue.active_push_mono]

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
  grind [DoneOrQueued, Queue.active_pop_cases, Queued]

/-- **Expand transport**: popping the fresh `(f, fStar)` and mapping it keeps
`DoneOrQueued`. A done witness `g ≠ f` survives the `set!`; the popped witness
becomes done via the fresh mapping. -/
theorem doneOrQueued_expand_pop {q q' : Queue SmallNatPair} {x : SmallNatPair}
    {dmap : IndexMap} {g gStar : Nat}
    (hp : q.pop? = some (x, q')) (hfsz : x.fst < dmap.size)
    (hfresh : dmap.idx? x.fst = Option.none)
    (hd : DoneOrQueued q dmap g gStar) :
    DoneOrQueued q' (dmap.set! x.fst (OptIdx.some x.snd)) g gStar := by
  grind [DoneOrQueued, Queued, Queue.active_pop_cases, IndexMap.idx?_set!_ne,
    IndexMap.idx?_set!_self]

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
    (hactive : ∀ s t, os = OptIdx.some s → od = OptIdx.some t → q'.Active (pack s t)) :
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
    {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat}
    {q q' : Queue SmallNatPair} {vmap dmap vmap' dmap' : IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hst : homStep src dst degreeTest q vmap dmap hs.toBounded.toIndexSafe =
      .next q' vmap' dmap') :
    Sound src dst degreeTest dartFrom dartTo q' vmap' dmap' := by
  unfold homStep at hst
  split at hst
  · grind
  · rename_i packed q1 heq
    have hfb := HomBounded.active hs.queued_bd (Queue.active_head heq)
    have hfsz : packed.fst < dmap.size := by
      simpa only [hs.dmap_wf.size_eq] using hfb.1
    -- move the state's reads to the spec's total-read (`!`) vocabulary once;
    -- the proof-carrying writes keep their `set` form (the `_set_` lemmas)
    simp only [← getElem!_pos] at hst
    split at hst
    · -- already mapped; the consistency guard passes, then re-pop
      rename_i d hdd
      simp only [ite_done_none_eq_next] at hst
      obtain ⟨hcons, hst⟩ := hst
      cases hst
      grind [sound_pop, IndexMap.idx?_eq_of_getElem]
    · -- unmapped: expand
      rename_i hdv
      have hfresh : dmap.idx? packed.fst = Option.none :=
        IndexMap.idx?_eq_none_of_not_isSome hfsz (by grind [OptIdx.isSome])
      have hsrcD := src.wf.1.read_inBounds hfb.1
      have hdstD := dst.wf.1.read_inBounds hfb.2
      -- flatten the four early-return guards (vmap-conflict, degree, succ/pred
      -- boundary); on the success path each `else` is taken, so all pass
      simp only [ite_done_none_eq_next] at hst
      obtain ⟨hvvc, hdeg, hsg, hpg, hst⟩ := hst
      cases hst
      have hvsz : src.darts[packed.fst]!.head < vmap.size := by
        simpa only [hs.vmap_wf.size_eq] using hsrcD.head_lt
      have hvv := IndexMap.idx?_none_or_eq_some_of_not_conflict hvsz hvvc
      have hbase : Bounded src dst q1
          (vmap.set src.darts[packed.fst]!.head
            (OptIdx.some dst.darts[packed.snd]!.head) hvsz)
          (dmap.set packed.fst (OptIdx.some packed.snd) hfsz) :=
        ⟨(bounded_pop heq hs.toBounded).queued_bd,
          IndexMap.wf_set_some hs.vmap_wf hdstD.head_lt,
          IndexMap.wf_set_some hs.dmap_wf hfb.2⟩
      have hexp : ∀ {g gStar}, DoneOrQueued q dmap g gStar →
          DoneOrQueued q1 (dmap.set packed.fst (OptIdx.some packed.snd) hfsz) g gStar :=
        fun hdq => (IndexMap.set_eq_set! hfsz).symm ▸
          doneOrQueued_expand_pop heq hfsz hfresh hdq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- toBounded: `Bounded` through the three pushes, in order
        exact bounded_pushLink (bounded_pushLink
            (bounded_push hbase (pack_bounded hsrcD.rev_lt hdstD.rev_lt))
            hsrcD.succ_lt hdstD.succ_lt)
          hsrcD.pred_lt hdstD.pred_lt
      · -- root_pending
        grind [doneOrQueued_push, doneOrQueued_pushLink, hexp hs.root_pending]
      · -- dart_head_ok
        grind [IndexMap.idx?_set_self, IndexMap.idx?_set_ne, hs.dart_head_ok]
      · -- degree_ok
        grind [IndexMap.idx?_set_self, IndexMap.idx?_set_ne, hs.degree_ok]
      · -- rev_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set_self hfsz ▸ hg)).symm
          refine Or.inr ⟨pack src.darts[packed.fst]!.rev
            dst.darts[packed.snd]!.rev, ?_,
            fst_pack _ _ (Nat.lt_of_lt_of_le hdstD.rev_lt dst.packable),
            snd_pack _ _ (Nat.lt_of_lt_of_le hdstD.rev_lt dst.packable)⟩
          grind [Queue.active_push_self, active_pushLink_mono]
        · grind [doneOrQueued_push, doneOrQueued_pushLink,
            hexp (hs.rev_pending g gStar (IndexMap.idx?_set_ne (Ne.symm hgf) ▸ hg))]
      · -- succ_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set_self hfsz ▸ hg)).symm
          refine freshLink_pending dst.packable hdstD.succ_lt hsg (fun s t hss hdd => ?_)
          grind [active_pushLink_self, active_pushLink_mono]
        · exact (hs.succ_pending g gStar (IndexMap.idx?_set_ne (Ne.symm hgf) ▸ hg)).transport
            (fun hdq => by grind [doneOrQueued_push, doneOrQueued_pushLink, hexp hdq])
      · -- pred_pending
        intro g gStar hg
        by_cases hgf : g = packed.fst
        · subst hgf
          obtain rfl : gStar = packed.snd :=
            (Option.some.inj (IndexMap.idx?_set_self hfsz ▸ hg)).symm
          refine freshLink_pending dst.packable hdstD.pred_lt hpg (fun s t hss hdd => ?_)
          grind [active_pushLink_self, active_pushLink_mono]
        · exact (hs.pred_pending g gStar (IndexMap.idx?_set_ne (Ne.symm hgf) ▸ hg)).transport
            (fun hdq => by grind [doneOrQueued_push, doneOrQueued_pushLink, hexp hdq])


/-- **A `some` answer from a `Sound` state is a homomorphism**: the step only
answers `some` at an exhausted queue, where `Sound` collapses to
`IsRootedHom`. -/
theorem homStep_done_sound
    {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    {p : IndexMap × IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hst : homStep src dst degreeTest q vmap dmap hs.toBounded.toIndexSafe =
      .done (some p)) :
    IsRootedHom src dst degreeTest dartFrom dartTo p.1 p.2 := by
  unfold homStep at hst
  split at hst
  · exact (Option.some.inj (HomNext.done.inj hst)) ▸
      isRootedHom_of_sound_isEmpty hs (by grind [Queue.pop?_none])
  · grind

/-- **Soundness of `homCoreGo`**: from a `Sound` state, any `some (vmap, dmap)`
result is a genuine rooted homomorphism (`IsRootedHom`) -- the BFS decides the
paper's Sec. 9 predicate. `homStep_next_sound`/`homStep_done_sound` lifted
through the driver by `partial_correctness`. -/
theorem homCoreGo_sound
    {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {r : IndexMap × IndexMap}
    (hs : Sound src dst degreeTest dartFrom dartTo q vmap dmap)
    (hrun : homCoreGo src dst degreeTest q vmap dmap hs.toBounded.toIndexSafe = some r) :
    IsRootedHom src dst degreeTest dartFrom dartTo r.1 r.2 := by
  refine homCoreGo.partial_correctness src dst degreeTest
    (motive := fun q vmap dmap _hix (vmapOut, dmapOut) =>
      Sound src dst degreeTest dartFrom dartTo q vmap dmap →
      IsRootedHom src dst degreeTest dartFrom dartTo vmapOut dmapOut)
    ?step q vmap dmap hs.toBounded.toIndexSafe r hrun hs
  intro rec ih q vmap dmap hix r hstep hs
  split at hstep
  · rename_i r' heq
    exact homStep_done_sound hs (heq.trans (congrArg HomNext.done hstep))
  · rename_i q' vmap' dmap' heq
    exact ih q' vmap' dmap' _ r hstep (homStep_next_sound hs heq)

/-- The seeded queue's only obligation is the root pair, and it unpacks to
`(dartFrom, dartTo)`. The shared setup of `homCore_sound`/`homCore_complete`. -/
theorem seed_root {dst : WFConfig} {dartTo : Nat} (dartFrom cap : Nat)
    (hdt : dartTo < dst.darts.size) :
    (pack dartFrom dartTo).fst = dartFrom ∧ (pack dartFrom dartTo).snd = dartTo ∧
    ∀ p, ((Queue.emptyWithCapacity cap).push (pack dartFrom dartTo)).Active p →
      p = pack dartFrom dartTo := by
  have hxb : dartTo < pairBase := Nat.lt_of_lt_of_le hdt dst.packable
  exact ⟨fst_pack dartFrom dartTo hxb, snd_pack dartFrom dartTo hxb,
    fun p hp => (Queue.active_push hp).resolve_left (Queue.not_active_emptyWithCapacity p)⟩

/-- **Soundness of `homCore`** (the seeded BFS, A.2): if it returns
`some (vmap, dmap)`, that is a genuine rooted homomorphism `src → dst`. The seed
state satisfies `Sound` (the root pair is queued; the maps start empty), so this
is `homCoreGo_sound` at the initial state. The root-dart guard supplies the
seed bounds, so no range premises remain. -/
theorem homCore_sound {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat}
    {r : IndexMap × IndexMap} (hrun : homCore src dartFrom dst dartTo degreeTest = some r) :
    IsRootedHom src dst degreeTest dartFrom dartTo r.1 r.2 := by
  revert hrun
  unfold homCore
  split
  · rename_i hguard
    intro hrun
    obtain ⟨hxfst, hxsnd, hactive⟩ := seed_root dartFrom (src.darts.size * 3 + 1) hguard.2
    refine homCoreGo_sound (r := r) ?_ hrun
    refine ⟨⟨HomBounded.push_pack dst.packable HomBounded.empty hguard.1 hguard.2,
      IndexMap.wf_replicate_none, IndexMap.wf_replicate_none⟩,
      Or.inr ⟨pack dartFrom dartTo, Queue.active_push_self, hxfst, hxsnd⟩,
      ?_, ?_, ?_, ?_, ?_⟩
    all_goals grind [IndexMap.idx?_replicate_none]
  · intro hrun
    exact nomatch hrun

/-- **`homomorphismExists` is sound**: if the `.isSome` fast path reports a
homomorphism, one genuinely exists. (The converse is `homomorphismExists_complete`.) -/
theorem homomorphismExists_sound {src dst : WFConfig}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat}
    (h : homomorphismExists src dartFrom dst dartTo degreeTest = true) :
    ∃ vmap dmap, IsRootedHom src dst degreeTest dartFrom dartTo vmap dmap := by
  obtain ⟨⟨vmap, dmap⟩, hr⟩ := Option.isSome_iff_exists.mp h
  exact ⟨vmap, dmap, homCore_sound hr⟩

/-! ### Completeness scaffolding: a fuel-based total twin of `homCoreGo`

`homCoreGo` is a `partial_fixpoint`, so proving it *returns* `some` (needed for
completeness -- no false negatives) requires a termination argument. The fuel
twin drives the same `homStep`; `homCoreGo_eq_imp` equates the two drivers
above the measure, and completeness is ordinary induction on fuel, stepped by
`homStep_agrees`. -/

/-- Fuel-bounded driver of `homStep` (`0` fuel = give up with `none`). -/
def homCoreGoImp (src dst : WFConfig) (degreeTest : Degree → Degree → Bool) :
    Nat → (q : Queue SmallNatPair) → (vmap dmap : IndexMap) →
      HomIndexSafe src dst q vmap dmap → Option (IndexMap × IndexMap)
  | 0, _, _, _, _ => none
  | fuel + 1, q, vmap, dmap, hs =>
    match hstep : homStep src dst degreeTest q vmap dmap hs with
    | .done r => r
    | .next q vmap dmap =>
      homCoreGoImp src dst degreeTest fuel q vmap dmap (homStep_next_safe hstep)


/-- The **completeness invariant**: the BFS state agrees with a fixed reference
homomorphism `(vm, dm)`. The built maps are restrictions of the reference, and
the queue holds only *correct* obligations (`dm.idx? f = some f★`). Under this,
the reference witnesses consistency at every step, so no `none` branch fires. -/
structure Agrees (src dst : PseudoConfiguration) (vm dm : IndexMap)
    (q : Queue SmallNatPair) (vmap dmap : IndexMap) : Prop where
  toBounded : Bounded src dst q vmap dmap
  dmap_le : ∀ f fStar, dmap.idx? f = Option.some fStar → dm.idx? f = Option.some fStar
  vmap_le : ∀ v vStar, vmap.idx? v = Option.some vStar → vm.idx? v = Option.some vStar
  queue_ok : ∀ p, q.Active p → dm.idx? p.fst = Option.some p.snd

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

/-- `unmapped_set!_lt` in the `set` vocabulary the implementation uses. -/
theorem unmapped_set_lt {dmap : IndexMap} {f v : Nat} (hf : f < dmap.size)
    (hnone : dmap.idx? f = Option.none) :
    unmapped (dmap.set f (OptIdx.some v) hf) < unmapped dmap :=
  (IndexMap.set_eq_set! hf).symm ▸ unmapped_set!_lt hf hnone

/-- **Re-pop measure decrease**: popping (maps unchanged) drops the measure. -/
theorem measure_pop_lt {q q' : Queue SmallNatPair} {x : SmallNatPair} {dmap : IndexMap}
    (hp : q.pop? = some (x, q')) : measure q' dmap < measure q dmap := by
  grind [Queue.live_pop, measure]

/-- **Every continuing step strictly drops `measure`**, unconditionally: a
re-pop shrinks the live queue with the maps untouched, and the expand arm's
proof-carrying read guarantees a fresh in-range write, so `unmapped` drops
(weighted ×4) against a net live growth of at most two. This is the
termination content of the BFS -- no reference homomorphism needed. -/
theorem homStep_next_measure {src dst : WFConfig}
    {degreeTest : Degree → Degree → Bool}
    {q q' : Queue SmallNatPair} {vmap dmap vmap' dmap' : IndexMap}
    {hs : HomIndexSafe src dst q vmap dmap}
    (hst : homStep src dst degreeTest q vmap dmap hs = .next q' vmap' dmap') :
    measure q' dmap' < measure q dmap := by
  unfold homStep at hst
  split at hst
  · exact nomatch hst
  · rename_i packed q1 hpq
    have hfsz : packed.fst < dmap.size :=
      hs.dmap_size.symm ▸ (hs.queue.pop hpq).1.1
    have hmeas1 := measure_pop_lt (dmap := dmap) hpq
    have hunm := fun (h : packed.fst < dmap.size)
        (hdd : dmap[packed.fst]'h = OptIdx.none) =>
      unmapped_set_lt (v := packed.snd) h (IndexMap.idx?_eq_none_of_getElem hdd)
    -- `splits` covers the `dmap` match and the four rejection guards;
    -- `OptIdx.none` unfolds so the match's raw-form arm feeds the read bridge
    grind (splits := 5) only [measure, OptIdx.none, !Queue.live_pop,
      !Queue.live_push, !live_pushLink_le]

/-- **`homCoreGo` is total**: above the measure, it agrees with the
fuel-bounded twin everywhere -- `some` and `none` answers alike -- so its
value is that of a structurally total function at computable fuel
(`measure q dmap + 1`). `homStep_next_measure` keeps the fuel ahead of the
recursion; fuel-irrelevance above the measure is immediate. This closes the
divergence question unconditionally: the indexing invariant is on the type,
so no well-formedness precondition remains. -/
theorem homCoreGo_eq_imp {src dst : WFConfig} {degreeTest : Degree → Degree → Bool} :
    ∀ fuel q vmap dmap hs, measure q dmap < fuel →
      homCoreGo src dst degreeTest q vmap dmap hs
        = homCoreGoImp src dst degreeTest fuel q vmap dmap hs := by
  intro fuel
  induction fuel <;> grind only [homCoreGo.eq_def, homCoreGoImp,
    → homStep_next_measure, → homStep_next_safe]

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
  grind [Agrees, bounded_pop, Queue.active_pop]

/-- Pushing an in-bounds, *correct* obligation keeps `Agrees`. -/
theorem agrees_push {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {x : SmallNatPair}
    (ha : Agrees src dst vm dm q vmap dmap)
    (hxb : x.fst < src.darts.size ∧ x.snd < dst.darts.size)
    (hxc : dm.idx? x.fst = Option.some x.snd) :
    Agrees src dst vm dm (q.push x) vmap dmap := by
  grind [Agrees, bounded_push, Queue.active_push]

/-- Pushing a `pack a b` of a correct in-bounds obligation keeps `Agrees`. -/
theorem agrees_push_pack {src dst : WFConfig} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {a b : Nat}
    (ha : Agrees src dst vm dm q vmap dmap)
    (hab : a < src.darts.size) (hbb : b < dst.darts.size) (hc : dm.idx? a = Option.some b) :
    Agrees src dst vm dm (q.push (pack a b)) vmap dmap := by
  grind [WFConfig.packable, agrees_push]

/-- `pushLink` keeps `Agrees`: when both links are interior, the queued pair
must be a correct in-bounds obligation of the reference. -/
theorem agrees_pushLink {src dst : WFConfig} {vm dm : IndexMap}
    {q : Queue SmallNatPair} {vmap dmap : IndexMap} {os od : OptIdx}
    (ha : Agrees src dst vm dm q vmap dmap)
    (hf : ∀ s t, os = OptIdx.some s → od = OptIdx.some t →
      s < src.darts.size ∧ t < dst.darts.size ∧ dm.idx? s = Option.some t) :
    Agrees src dst vm dm (pushLink q os od) vmap dmap := by
  cases os <;> cases od
  all_goals try exact ha
  obtain ⟨h1, h2, h3⟩ := hf _ _ rfl rfl
  exact agrees_push_pack ha h1 h2 h3

/-- The updated maps + queue after an expand still agree with the reference
(base case, before the ≤3 pushes). The head indices are abstract, so the
statement is vocabulary-neutral between `!` and proof-carrying reads. -/
theorem agrees_expand_base {src dst : PseudoConfiguration} {vm dm : IndexMap}
    {q1 : Queue SmallNatPair} {vmap dmap : IndexMap} {f fStar h hStar : Nat}
    (ha1 : Agrees src dst vm dm q1 vmap dmap)
    (hfsz : f < dmap.size) (hfs : fStar < dst.darts.size)
    (hvsz : h < vmap.size)
    (hcorrect : dm.idx? f = Option.some fStar)
    (hhead : vm.idx? h = Option.some hStar)
    (hdlt : hStar < dst.n) :
    Agrees src dst vm dm q1 (vmap.set h (OptIdx.some hStar) hvsz)
      (dmap.set f (OptIdx.some fStar) hfsz) := by
  exact ⟨⟨ha1.toBounded.queued_bd,
    IndexMap.wf_set_some ha1.toBounded.vmap_wf hdlt,
    IndexMap.wf_set_some ha1.toBounded.dmap_wf hfs⟩,
    IndexMap.idx?_set_le hfsz ha1.dmap_le hcorrect,
    IndexMap.idx?_set_le hvsz ha1.vmap_le hhead, ha1.queue_ok⟩

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

/-- The semantic content completeness needs from a step result: a final answer
is present, or the continuing state still agrees with the reference. Keeping
this match behind a named predicate lets `homStep_agrees` reason directly about
the computed result, without a dependent result equation; the independent
`homStep_next_measure` supplies termination. -/
def AgreesResult (src dst : PseudoConfiguration) (vm dm : IndexMap) : HomNext → Prop
  | .done r => r.isSome
  | .next q' vmap' dmap' => Agrees src dst vm dm q' vmap' dmap'

/-- **One step under a reference homomorphism**: from an `Agrees` state the
step never answers `none` (each early `done none` exit is refuted in place
by the reference's witness), and a continuing step keeps `Agrees`.
Recursion-free; completeness combines this semantic lemma with
`homStep_next_measure` while folding over the fuel. -/
theorem homStep_agrees {src dst : WFConfig}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat} {vm dm : IndexMap}
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm)
    {q : Queue SmallNatPair} {vmap dmap : IndexMap}
    (ha : Agrees src dst vm dm q vmap dmap) :
    AgreesResult src dst vm dm
      (homStep src dst degreeTest q vmap dmap ha.toBounded.toIndexSafe) := by
  unfold homStep
  split
  · -- `pop?` exhausted: the answer is `some (vmap, dmap)`
    rfl
  · rename_i packed q1 hpq
    have hpk : q.Active packed := Queue.active_head hpq
    have hbd := HomBounded.active ha.toBounded.queued_bd hpk
    have hcorrect : dm.idx? packed.fst = Option.some packed.snd := ha.queue_ok packed hpk
    have hf : packed.fst < src.darts.size := hbd.1
    have hfs : packed.snd < dst.darts.size := hbd.2
    have hfsz : packed.fst < dmap.size := by
      simpa only [ha.toBounded.dmap_wf.size_eq] using hf
    have hagr1 : Agrees src dst vm dm q1 vmap dmap := agrees_pop ha hpq
    -- move the state's reads to the spec's total-read (`!`) vocabulary once;
    -- the proof-carrying writes keep their `set` form (the `_set_` lemmas)
    simp only [← getElem!_pos]
    split
    · -- already mapped, and correctly (`hcorrect`)
      rename_i d hdd
      have heqd : dm.idx? packed.fst = Option.some d :=
        ha.dmap_le _ _ (IndexMap.idx?_eq_of_getElem! hfsz hdd)
      -- `heqd` and `hcorrect` decide the consistency guard, so `grind` needs
      -- no case split here (`splits` is a search budget, not an update count).
      grind (splits := 0) only [AgreesResult]
    · -- unmapped: expand -- the reference hom witnesses every check
      rename_i hdd
      obtain ⟨hhead, hrev, hsucc, hpred⟩ := hom.2.1 packed.fst packed.snd hcorrect
      have hsrcD := src.wf.1.read_inBounds hf
      have hdstD := dst.wf.1.read_inBounds hfs
      have hhsz : src.darts[packed.fst]!.head < vmap.size := by
        simpa only [ha.toBounded.vmap_wf.size_eq] using hsrcD.head_lt
      -- head consistency: if `vmap[h]` is set it already agrees with the hom
      have hvhead : vmap[src.darts[packed.fst]!.head]!.isSome = true →
          vmap[src.darts[packed.fst]!.head]! = OptIdx.some dst.darts[packed.snd]!.head := by
        grind [Agrees, idx?_of_isSome, getElem!_eq_of_idx?]
      have hheadGuard := OptIdx.not_conflict_of_eq_some_when_isSome hvhead
      have hdeg := hom.2.2 _ _ hhead
      have hsuccGuard := link_guard hsucc
      have hpredGuard := link_guard hpred
      have hbase := agrees_expand_base hagr1 hfsz hfs hhsz hcorrect
        hhead hdstD.head_lt
      have ha1 := agrees_push_pack hbase hsrcD.rev_lt hdstD.rev_lt hrev
      have hnext := agrees_pushLink (agrees_pushLink ha1
          (link_obligation hsucc hsrcD.succ_lt hdstD.succ_lt))
        (link_obligation hpred hsrcD.pred_lt hdstD.pred_lt)
      -- The four guard facts select the success path. `hdeg` simplifies its
      -- test directly; reducing the nested head/succ/pred conditionals still
      -- takes three proof-search case splits.
      grind (splits := 3) only [AgreesResult]

/-- **Completeness on the fuel driver**: given a reference homomorphism, from
any `Agrees` state with enough fuel, `homCoreGoImp` returns `some`. Ordinary
induction on fuel over `homStep_agrees`. -/
theorem homCoreGoImp_complete {src dst : WFConfig}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat} {vm dm : IndexMap}
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    ∀ fuel q vmap dmap hs, Agrees src dst vm dm q vmap dmap → measure q dmap < fuel →
      ∃ r, homCoreGoImp src dst degreeTest fuel q vmap dmap hs = some r := by
  intro fuel
  induction fuel with
  | zero => grind
  | succ fuel ih =>
    intro q vmap dmap hs ha hm
    have hstep := homStep_agrees hom ha
    rcases heq : homStep src dst degreeTest q vmap dmap hs
      with r | ⟨q', vmap', dmap'⟩
    · have h : r.isSome := by
        simpa only [AgreesResult, heq] using hstep
      grind [homCoreGoImp, Option.isSome_iff_exists]
    · have ha' : Agrees src dst vm dm q' vmap' dmap' := by
        simpa only [AgreesResult, heq] using hstep
      have hlt := homStep_next_measure heq
      obtain ⟨r', hr'⟩ := ih q' vmap' dmap' (homStep_next_safe heq) ha' (by grind)
      exact ⟨r', by grind [homCoreGoImp]⟩

/-- **Completeness of `homCore`**: if a rooted homomorphism `src → dst` exists,
the seeded BFS returns `some`. The seed state `Agrees` with the reference hom
(the root pair is queued and correct, the maps start empty), so `homCoreGoImp`
succeeds at enough fuel and `homCoreGo_eq_imp` transports it to
`homCoreGo` = `homCore`. -/
theorem homCore_complete {src dst : WFConfig} {degreeTest : Degree → Degree → Bool}
    {dartFrom dartTo : Nat} {vm dm : IndexMap}
    (hdf : dartFrom < src.darts.size) (hdt : dartTo < dst.darts.size)
    (hom : IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    ∃ r, homCore src dartFrom dst dartTo degreeTest = some r := by
  obtain ⟨hxfst, hxsnd, hactive⟩ := seed_root dartFrom (src.darts.size * 3 + 1) hdt
  have hagr : Agrees src dst vm dm
      ((Queue.emptyWithCapacity (src.darts.size * 3 + 1)).push (pack dartFrom dartTo))
      (Array.replicate src.n OptIdx.none) (Array.replicate src.darts.size OptIdx.none) := by
    refine ⟨⟨HomBounded.push_pack dst.packable HomBounded.empty hdf hdt,
      IndexMap.wf_replicate_none, IndexMap.wf_replicate_none⟩, ?_, ?_, fun p hp => ?_⟩
    all_goals grind [IndexMap.idx?_replicate_none, IsRootedHom]
  obtain ⟨r, hr⟩ := homCoreGoImp_complete hom _ _ _ _
    ⟨HomBounded.push_pack dst.packable HomBounded.empty hdf hdt,
      Array.size_replicate .., Array.size_replicate ..⟩ hagr (Nat.lt_succ_self _)
  refine ⟨r, ?_⟩
  unfold homCore
  rw [dif_pos ⟨hdf, hdt⟩]
  exact (homCoreGo_eq_imp _ _ _ _ _ (Nat.lt_succ_self _)).trans hr

/-- **`homomorphismExists` is complete**: if a rooted homomorphism exists, the
`.isSome` fast path reports it. With `homomorphismExists_sound`, this gives
`homomorphismExists = true ↔ ∃ hom` -- the equivalence the containment checks
rely on. -/
theorem homomorphismExists_complete {src dst : WFConfig}
    {degreeTest : Degree → Degree → Bool} {dartFrom dartTo : Nat}
    (hdf : dartFrom < src.darts.size) (hdt : dartTo < dst.darts.size)
    (h : ∃ vm dm, IsRootedHom src dst degreeTest dartFrom dartTo vm dm) :
    homomorphismExists src dartFrom dst dartTo degreeTest = true := by
  grind [homomorphismExists, homCore_complete]

end PseudoConfiguration.HomState

end NearLinear4ct
