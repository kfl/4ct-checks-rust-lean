/-!
A compact, **verified** pair of small naturals.

`SmallNatPair` packs `(f, s)` with `s < 2^32` into the single `Nat`
`f * 2^32 + s`. It is a single-field structure over `Nat`, so at runtime it
is represented **as a `Nat`** -- a pointer-tagged immediate while the pack
stays below `2^63` -- and `Array SmallNatPair` is a dense scalar array. By
contrast, `Array (Nat × Nat)` heap-allocates and reference-counts a pair
cell per element, and `UInt64` is no escape: Lean **boxes** `UInt64` in
polymorphic positions (`lean_box_uint64` allocates).

The encoding is **proved sound** below (`fst_pack`, `snd_pack`,
`pack_fst_snd`): under the precondition `s < 2^32`, `pack` carries exactly
the pair `(f, s)` -- so using it in the BFS kernel does not weaken the
code's meaning, mirroring `OptIdx`'s treatment of the `-1` sentinel.
-/

namespace NearLinear4ct

/-- A pair of small naturals packed into one pointer-tagged `Nat`
(`raw = f * 2^32 + s`). Precondition (unchecked, hot path): `snd < 2^32`;
for the value to stay a tagged scalar also keep `fst < 2^31`. Construct
with `SmallNatPair.pack`; read with `fst` / `snd`. -/
structure SmallNatPair where
  /-- Raw encoding: `f * 2^32 + s`. Prefer `pack`/`fst`/`snd`. -/
  raw : Nat
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace SmallNatPair

/-- `2^32`, hoisted into a def: `Nat` literals above the codegen's immediate
range compile to a `lean_cstr_to_nat` *string parse at every use site*;
`@[noinline]` keeps it evaluated once at module init (a plain `def` gets
constant-folded back into the use sites). -/
@[noinline] def pairBase : Nat := 4294967296

/-- Pack `(f, s)`, `s < 2^32` (`mul`/`add` have inline runtime fast paths;
zero allocation while the result stays below `2^63`). -/
@[inline] def pack (f s : Nat) : SmallNatPair := ⟨f * pairBase + s⟩

/-- First component (`raw >>> 32`; inline fast path, no allocation). -/
@[inline] def fst (p : SmallNatPair) : Nat := p.raw >>> 32

/-- Second component (`raw &&& (2^32 - 1)`; inline fast path, no allocation). -/
@[inline] def snd (p : SmallNatPair) : Nat := p.raw &&& 4294967295

/-- Both components. The `Nat × Nat` here is compile-time only *when the result
is immediately destructured* (`let (f, s) := p.unpackPair`): after inlining, the
pair ctor flows straight into the match and LCNF's case-of-constructor fusion
deletes it. (Contrast: an `Option (α × β)` returned across an `if` does **not**
fuse, because the ctor is not syntactically scrutinised at the match.) -/
@[inline] def unpackPair (p : SmallNatPair) : Nat × Nat := (p.fst, p.snd)

/-! ### Soundness: `pack` carries exactly the pair, given `snd < 2^32`.

The proofs rewrite with the variable-level `rfl` bridges below instead of
`simp only [pack, fst, snd]`: simp collapses all-`rfl` chains into a single
`rfl` certificate, whose kernel check unfolds `Nat.land` -> `Nat.bitwise`
(well-founded recursion) at *compound* arguments and deep-recurses on the
`2^32 - 1` literal. At variables the defeq stays one delta step and is
cheap; the instantiations are then ordinary congruence rewrites. -/

theorem raw_pack (f s : Nat) : (pack f s).raw = f * pairBase + s := rfl
theorem fst_eq_shift (p : SmallNatPair) : p.fst = p.raw >>> 32 := rfl
theorem snd_eq_land (p : SmallNatPair) : p.snd = p.raw &&& 4294967295 := rfl
theorem unpackPair_eq (p : SmallNatPair) : p.unpackPair = (p.fst, p.snd) := rfl

theorem fst_pack (f s : Nat) (h : s < 4294967296) : (pack f s).fst = f := by
  rw [fst_eq_shift, raw_pack, pairBase, Nat.shiftRight_eq_div_pow,
      (by simp : (2 : Nat) ^ 32 = 4294967296)]
  omega

theorem snd_pack (f s : Nat) (h : s < 4294967296) : (pack f s).snd = s := by
  rw [snd_eq_land, raw_pack, pairBase,
      (by simp : (4294967295 : Nat) = 2 ^ 32 - 1),
      Nat.and_two_pow_sub_one_eq_mod,
      (by simp : (2 : Nat) ^ 32 = 4294967296)]
  omega

theorem unpackPair_pack (f s : Nat) (h : s < 4294967296) :
    (pack f s).unpackPair = (f, s) := by
  rw [unpackPair_eq, fst_pack f s h, snd_pack f s h]

/-- Round-trip the other way: any `SmallNatPair` is the pack of its
components (unconditional -- the shift/mask decomposition of `raw`). -/
theorem pack_fst_snd (p : SmallNatPair) : pack p.fst p.snd = p := by
  have hraw : (pack p.fst p.snd).raw = p.raw := by
    rw [raw_pack, fst_eq_shift, snd_eq_land, pairBase, Nat.shiftRight_eq_div_pow,
        (by simp : (4294967295 : Nat) = 2 ^ 32 - 1),
        Nat.and_two_pow_sub_one_eq_mod,
        (by simp : (2 : Nat) ^ 32 = 4294967296)]
    omega
  obtain ⟨raw⟩ := p
  exact congrArg SmallNatPair.mk hraw

end SmallNatPair
end NearLinear4ct
