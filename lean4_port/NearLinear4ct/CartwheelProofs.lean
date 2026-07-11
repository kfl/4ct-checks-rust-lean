import NearLinear4ct.Cartwheel

/-!
Exactness of the port's `Nat` degree arithmetic.

`Degree.lower`/`upper` are `Nat`, so subtraction truncates at `0`. This module
proves each degree subtraction agrees with the paper's integer arithmetic:
the loaded-degree site (`refineNever`, gated at I/O), the literal site
(`deleteDegreeFromKTo9`), and the one deliberately-signed count
(`representativeDegree`).

Exactly one subtraction on a *loaded* degree exists in the port:
`CartWheel.refineNever` computes `(rule.degrees[vRule]!).lower - 1`
(A.9.19). The I/O gate
(`Configuration.assertDegreesValid`, called on every rule by `getRules`) aborts
unless each degree's lower bound is `≥ 1`; rule degrees are never written after
parsing, and `fixOutRules` only ever refines with rules from that gated array.
This module closes the remaining link by proof: on gate-valid degrees the
truncating `Nat` subtraction agrees with the paper's integer arithmetic, so no
further checks are needed at the refinement site.
-/

namespace NearLinear4ct

/-- The property `Configuration.assertDegreesValid` checks element-by-element,
aborting otherwise: every degree's lower bound is `≥ 1`. -/
def DegreesValid (degrees : Array Degree) : Prop :=
  ∀ i, i < degrees.size → 1 ≤ (degrees[i]!).lower

namespace CartWheel

/-- **The degree gate is sufficient for `refineNever`'s subtraction**: on
gate-valid degrees, the `Nat` computation `lower - 1` equals the paper's
integer `lower - 1` -- the truncation at `0` cannot fire. -/
theorem refineNever_sub_exact {rule : Rule} (hval : DegreesValid rule.degrees)
    {vRule : Nat} (h : vRule < rule.degrees.size) :
    (((rule.degrees[vRule]!).lower - 1 : Nat) : Int) =
      ((rule.degrees[vRule]!).lower : Int) - 1 := by
  grind [DegreesValid]

end CartWheel

namespace CombineCartwheel

/-- **The `k - 1` in `deleteDegreeFromKTo9` is exact**: for any `1 ≤ k` the
`Nat` subtraction agrees with the paper's integer arithmetic. Unlike
`refineNever`, `k` is never loaded data -- the only calls pass the literals `9`
and `8` (`checkDeg8`, `check7triangle`, `checkDeg7`), which discharge the
hypothesis on sight -- so there is no I/O gate to justify here; this records
that the truncation cannot fire for the values used. -/
theorem deleteDegreeFromKTo9_sub_exact {k : Nat} (h : 1 ≤ k) :
    ((k - 1 : Nat) : Int) = (k : Int) - 1 := by
  grind

end CombineCartwheel

/-- **The one deliberately-signed degree computation is equivalent to clamped
`Nat` arithmetic**: `representativeDegree`'s choice count is computed as
`((upper : Int) - lower + 1).toNat` so that an empty range (`upper < lower`)
yields `0` -- plain `Nat` `upper - lower + 1` would truncate to one spurious
choice. Unconditionally, that signed round-trip equals the reordered `Nat`
expression `upper + 1 - lower`, whose truncation clamps identically. The
executable keeps the signed form (it states the clamp explicitly and mirrors
the reference); this records that the `Int` detour is expression order, not
semantics. -/
theorem representativeDegree_count_exact (l u : Nat) :
    ((u : Int) - l + 1).toNat = u + 1 - l := by
  grind

end NearLinear4ct
