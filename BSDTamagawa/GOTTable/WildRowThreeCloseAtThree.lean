/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowPrepAtThree
public import BSDTamagawa.GOTTable.WildStarredUnitAtThree

/-!
# The row `t = 3` of the `p = 3` head

The row `t = 3` of the `p = 3` column is filled by three loci and a Family-B contribution. Over the
common denominator `3¹⁴ = 4782969` their minimal-storey masses are

    (IV, 3) split                    iv3Locus                      1/81       =   59049/4782969
    (IV*, 3), v₃(a₆) = 3             ivStarThreeUnit3Locus         2/6561     =    1458/4782969
    (IV*, 3), v₃(a₆) = 4             ivStarThree3Locus             1/6561     =     729/4782969
                                                                  --------------------------------
                                     rowThreeCore3Locus            28/2187    =   61236/4782969
    Family B, row 3                                                                   2/4782969
                                                                  --------------------------------
                                                                                  61238/4782969

and `61238/4782969 · 59049/59048 = 30619/2391444`. The Kodaira symbol separates the split `IV`
locus from the two `IV*` loci, and `3⁴ ∣ a₆` separates the two `IV*` loci from each other.

## Main definitions

* `WeierstrassCurve.rowThreeStarred3Locus`: the `IV*` block of the row.
* `WeierstrassCurve.rowThreeCore3Locus`: the split `IV` locus together with the `IV*` block.

## Main results

* `WeierstrassCurve.volume_rowThreeStarred3Locus`, `WeierstrassCurve.volume_rowThreeCore3Locus`:
  the masses `1/2187` and `28/2187`.
* `WeierstrassCurve.row_three_close_at_three`: `30619/2391444 ≤ δ_3(3)`, given a measurable set of
  mass `2/3¹⁴` inside the minimal part of the row and disjoint from `rowThreeCore3Locus`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### The two blocks of the row -/

/-- The starred block of row `t = 3`: `(IV*, 3)` at both depths of `a₆`. -/
noncomputable def rowThreeStarred3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  ivStarThreeUnit3Locus ∪ ivStarThree3Locus

/-- The union of the split `IV` locus and the `IV*` block of row `t = 3`. -/
noncomputable def rowThreeCore3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  iv3Locus ∪ rowThreeStarred3Locus

/-! ### Disjointness, measurability and mass -/

/-- **The split `IV` locus and the `IV*` block are disjoint**, by the symbol. -/
theorem disjoint_iv3Locus_rowThreeStarred3Locus : Disjoint iv3Locus rowThreeStarred3Locus :=
  RowsThree.disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iv3Locus_subset_stratFibre
    (Set.union_subset ivStarThreeUnit3Locus_subset_stratFibre ivStarThree3Locus_subset_stratFibre)

/-- The `IV*` block of row `t = 3` is measurable. -/
theorem measurableSet_rowThreeStarred3Locus : MeasurableSet rowThreeStarred3Locus :=
  measurableSet_ivStarThreeUnit3Locus.union measurableSet_ivStarThree3Locus

/-- **The `IV*` block has mass `2/6561 + 1/6561 = 1/2187`.** -/
theorem volume_rowThreeStarred3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowThreeStarred3Locus = 1 / 2187 := by
  rw [rowThreeStarred3Locus,
    measure_union disjoint_ivStarThreeUnit3Locus measurableSet_ivStarThree3Locus,
    volume_ivStarThreeUnit3Locus, volume_ivStarThree3Locus, ENNReal.div_add_div_same,
    show (2 : ℝ≥0∞) + 1 = 3 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The set `rowThreeCore3Locus` has mass `1/81 + 1/2187 = 28/2187`.** -/
theorem volume_rowThreeCore3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowThreeCore3Locus = 28 / 2187 := by
  rw [rowThreeCore3Locus,
    measure_union disjoint_iv3Locus_rowThreeStarred3Locus measurableSet_rowThreeStarred3Locus,
    volume_iv3Locus, show (3 : ℝ≥0∞) * (((3 : ℕ)) : ℝ≥0∞) ^ 3 = 81 by norm_num,
    volume_rowThreeStarred3Locus,
    show (1 : ℝ≥0∞) / 81 = 27 / 2187 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-! ### Inclusion in the minimal part of the row -/

/-- The `IV*` block of row `t = 3` lies in the minimal part `headMinimal 3 3` of the row. -/
theorem rowThreeStarred3Locus_subset_headMinimal : rowThreeStarred3Locus ⊆ headMinimal 3 3 :=
  Set.union_subset ivStarThreeUnit3Locus_subset_headMinimal ivStarThree3Locus_subset_headMinimal

/-- The set `rowThreeCore3Locus` lies in the minimal part `headMinimal 3 3` of the row. -/
theorem rowThreeCore3Locus_subset_headMinimal : rowThreeCore3Locus ⊆ headMinimal 3 3 :=
  Set.union_subset iv3Locus_subset_headMinimal rowThreeStarred3Locus_subset_headMinimal

/-! ### The bound on the row -/

/-- **`30619/2391444 ≤ δ_3(3)`**, given a measurable set `B` of mass `2/3¹⁴` inside the minimal
part of the row `t = 3` and disjoint from `rowThreeCore3Locus`. -/
theorem row_three_close_at_three (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B)
    (hBsub : B ⊆ headMinimal 3 3)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 2 / 4782969)
    (hBdisj : Disjoint B rowThreeCore3Locus) :
    (30619 : ℝ≥0∞) / 2391444 ≤ δ 3 3 := by
  have hvol : (volume : Measure (ℤ_[3] × ℤ_[3])) (rowThreeCore3Locus ∪ B)
      = 61238 / 4782969 := by
    rw [measure_union hBdisj.symm hB, volume_rowThreeCore3Locus, hBvol,
      show (28 : ℝ≥0∞) / 2187 = 61236 / 4782969 from
        enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      ENNReal.div_add_div_same]
    norm_num
  refine le_trans (le_of_eq ?_)
    (le_δ_at_three_of_subset (Set.union_subset rowThreeCore3Locus_subset_headMinimal hBsub))
  rw [hvol, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
