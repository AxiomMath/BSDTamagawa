/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildIZeroStarAtTwo
public import BSDTamagawa.GOTTable.WildRowStepsOneFiveAtTwo

/-!
# The `I₀*` loci together with the shallow loci in rows `t = 1` and `t = 2` at `p = 2`

In row `t = 1` the locus `one2Locus` of types `II` and non-split `IV` (mass `9/16`) and the
`(I₀*, 1)` locus (mass `1/32`) are disjoint; in row `t = 2` so are the type-`III` locus
`iii2LocusFull` (mass `1/4`) and the `(I₀*, 2)` locus (mass `1/32`). The shallow loci are cut out
modulo `8` and `4`, the `I₀*` loci modulo `16`, and disjointness is checked by reducing the eight
`I₀*` classes modulo `16` to the shallower modulus. We also record that the two `I₀*` loci are
measurable.

## Main results

* `WeierstrassCurve.disjoint_one2Locus_iZeroStarOne2Locus` and
  `WeierstrassCurve.disjoint_iii2LocusFull_iZeroStarTwo2Locus`: the two disjointness statements.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

/-! ### Disjointness of the deep loci from the shallow ones -/

set_option maxRecDepth 40000 in
/-- None of the eight `(I₀*, 1)` classes modulo `16` reduces into the `t = 1` residue set modulo
`8`. -/
theorem not_headResOneTwo_of_mem_headResiduesIZeroStarOne :
    ∀ c ∈ headResiduesIZeroStarOne,
      ¬ HeadResOneTwo (ZMod.cast c.1 : ZMod (2 ^ 3)) (ZMod.cast c.2 : ZMod (2 ^ 3)) := by
  decide

set_option maxRecDepth 40000 in
/-- None of the eight `(I₀*, 2)` classes modulo `16` reduces into the type-`III` residue set modulo
`4`. -/
theorem not_headResIIITwo_of_mem_headResiduesIZeroStarTwo :
    ∀ c ∈ headResiduesIZeroStarTwo,
      ¬ HeadResIIITwo (ZMod.cast c.1 : ZMod (2 ^ 2)) (ZMod.cast c.2 : ZMod (2 ^ 2)) := by
  decide

/-- **The locus `one2Locus` and the `(I₀*, 1)` locus are disjoint.** -/
theorem disjoint_one2Locus_iZeroStarOne2Locus : Disjoint one2Locus iZeroStarOne2Locus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := mem_one2Locus_iff.1 hx
  have h2 := mem_iZeroStarOne2Locus_iff.1 hx'
  rw [← PadicInt.cast_toZModPow 3 4 (by norm_num) x.1,
    ← PadicInt.cast_toZModPow 3 4 (by norm_num) x.2] at h1
  exact not_headResOneTwo_of_mem_headResiduesIZeroStarOne _ h2 h1

/-- **The type-`III` locus and the `(I₀*, 2)` locus are disjoint.** -/
theorem disjoint_iii2LocusFull_iZeroStarTwo2Locus :
    Disjoint iii2LocusFull iZeroStarTwo2Locus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := mem_iii2LocusFull_iff.1 hx
  have h2 := mem_iZeroStarTwo2Locus_iff.1 hx'
  rw [← PadicInt.cast_toZModPow 2 4 (by norm_num) x.1,
    ← PadicInt.cast_toZModPow 2 4 (by norm_num) x.2] at h1
  exact not_headResIIITwo_of_mem_headResiduesIZeroStarTwo _ h2 h1

/-! ### Measurability of the two deep loci -/

/-- The `(I₀*, 1)` locus is measurable. -/
theorem measurableSet_iZeroStarOne2Locus : MeasurableSet iZeroStarOne2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 4 headResiduesIZeroStarOne

/-- The `(I₀*, 2)` locus is measurable. -/
theorem measurableSet_iZeroStarTwo2Locus : MeasurableSet iZeroStarTwo2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 4 headResiduesIZeroStarTwo

end WeierstrassCurve

end
