/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeRootAtThree

/-!
# The mass of a half of Family A at `p = 3`

Family A has mass `2/729`, split evenly between Tamagawa number `2` and Tamagawa number `4`. This
file records that a half of the family has mass `1/729`; with the storey factor `59049/59048` such
a half contributes `1/729 · 59049/59048 = 81/59048` to the head density of its row.

## Main results

* `WeierstrassCurve.FamilyAThree.volume_half_locus`: a set `L` with `2 · μ L = μ locus` has mass
  `1/729`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

namespace FamilyAThree

/-! ### The mass of a half -/

/-- **A half of Family A has mass `1/729`.** If `2 · μ L = μ locus`, then `μ L = 1/729`. -/
theorem volume_half_locus {L : Set (ℤ_[3] × ℤ_[3])}
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) L
      = (volume : Measure (ℤ_[3] × ℤ_[3])) locus) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) L = 1 / 729 := by
  rw [volume_locus, show (2 : ℝ≥0∞) / 729 = 2 * (1 / 729) from by rw [mul_one_div]] at hhalf
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp hhalf

end FamilyAThree

end WeierstrassCurve

end
