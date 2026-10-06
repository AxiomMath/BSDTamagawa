/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowPrepAtThree
public import BSDTamagawa.GOTTable.WildRowLowerBoundThree
public import BSDTamagawa.GOTTable.FamilyAThreeDisjointAtThree

/-!
# The row `t = 4` of the `p = 3` head

The row `t = 4` of the `p = 3` column is filled by the `(I₀*, 4)` locus, the Tamagawa-`4` half of
Family A and a Family-B contribution of mass `2/3¹⁵`. Over the common denominator `3¹⁵ = 14348907`
their minimal-storey masses are

    (I₀*, 4)                         iZeroStarFour3Locus           1/2187     =    6561/14348907
    Family A, Tamagawa-4 half        FamilyAThree.part 4           1/729      =   19683/14348907
    Family B, row 4                                                                   2/14348907
                                                                  --------------------------------
                                                                                  26246/14348907

and `26246/14348907 · 59049/59048 = 1193/652212`. Family A lies where `a₆` is a unit and the
`(I₀*, 4)` locus where `81 ∣ a₆`, so the two are disjoint. The half of Family A enters under the
hypothesis `2 · μ(part 4) = μ(locus)`, and Family B as an abstract set.

## Main definitions

* `WeierstrassCurve.rowFourFull3Locus`: the `(I₀*, 4)` locus together with Family A's half.

## Main results

* `WeierstrassCurve.volume_rowFourFull3Locus`: `rowFourFull3Locus` has mass `4/2187` under the
  halving hypothesis.
* `WeierstrassCurve.row_four_close_at_three`: `1193/652212 ≤ δ_3(4)`, given the halving of Family A
  and a measurable set of mass `2/3¹⁵` inside the minimal part of the row and disjoint from
  `rowFourFull3Locus`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### The `(I₀*, 4)` locus together with Family A's half -/

/-- **The `(I₀*, 4)` locus together with the Tamagawa-`4` half of Family A.** -/
noncomputable def rowFourFull3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  iZeroStarFour3Locus ∪ FamilyAThree.part 4

/-- **The `(I₀*, 4)` locus is disjoint from Family A's half**, since it is disjoint from the whole
of Family A. -/
theorem disjoint_iZeroStarFour3Locus_part_four :
    Disjoint iZeroStarFour3Locus (FamilyAThree.part 4) :=
  FamilyAThree.disjoint_locus_IZeroStarFour.symm.mono_right (FamilyAThree.part_subset_locus 4)

/-- **With Family A's half the row has mass `1/2187 + 1/729 = 4/2187`**, under the halving
hypothesis. -/
theorem volume_rowFourFull3Locus
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 4)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowFourFull3Locus = 4 / 2187 := by
  rw [rowFourFull3Locus,
    measure_union disjoint_iZeroStarFour3Locus_part_four (FamilyAThree.measurableSet_part 4),
    volume_iZeroStarFour3Locus, FamilyAThree.volume_half_locus hhalf,
    show (1 : ℝ≥0∞) / 729 = 3 / 2187 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-- The set `rowFourFull3Locus` lies inside the minimal part `headMinimal 3 4` of the row. -/
theorem rowFourFull3Locus_subset_headMinimal : rowFourFull3Locus ⊆ headMinimal 3 4 :=
  Set.union_subset iZeroStarFour3Locus_subset_headMinimal (FamilyAThree.part_subset_headMinimal 4)

/-! ### The bound on the row -/

/-- **`1193/652212 ≤ δ_3(4)`**, given the halving of Family A and a measurable set `B` of mass
`2/3¹⁵` inside the minimal part of the row `t = 4` and disjoint from `rowFourFull3Locus`. -/
theorem row_four_close_at_three
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 4)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus)
    (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B) (hBsub : B ⊆ headMinimal 3 4)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 2 / 14348907)
    (hBdisj : Disjoint B rowFourFull3Locus) :
    (1193 : ℝ≥0∞) / 652212 ≤ δ 3 4 := by
  have hvol : (volume : Measure (ℤ_[3] × ℤ_[3])) (rowFourFull3Locus ∪ B)
      = 26246 / 14348907 := by
    rw [measure_union hBdisj.symm hB, volume_rowFourFull3Locus hhalf, hBvol,
      show (4 : ℝ≥0∞) / 2187 = 26244 / 14348907 from
        enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      ENNReal.div_add_div_same]
    norm_num
  refine le_trans (le_of_eq ?_)
    (le_δ_at_three_of_subset (Set.union_subset rowFourFull3Locus_subset_headMinimal hBsub))
  rw [hvol, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
