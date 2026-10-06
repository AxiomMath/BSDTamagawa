/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildMultiplicativeAtTwo
public import BSDTamagawa.GOTTable.WildStarredAtTwo

/-!
# The `t = 3` row at `p = 2`

Row `t = 3` of the `p = 2` head consists of three loci:

    locus                    stratum          mass      over 16384
    ------------------------------------------------------------------
    iv2Locus                 (IV, 3) split    1/16         1024
    ivStarThree2Locus        (IV*, 3)         1/128         128
    multSplitLocusTwo 2 3    (I₃, 3) split    1/16384         1
    ------------------------------------------------------------------
                                              1153/16384    1153

and `1153/16384 · 1024/1023 = 1153/16368`, which is the value of `δ_2(3)`. The split multiplicative
shell is cut out by `a₄ ≡ 5 (mod 16)`, whereas `a₄ ≡ 0, 3, 4, 7 (mod 8)` on the split `IV` locus
and `a₄ ≡ 0, 1, 8, 9 (mod 16)` on the `(IV*, 3)` locus, so the shell is disjoint from both.

## Main results

* `WeierstrassCurve.disjoint_iv2Locus_MultSplitLocusThree` and
  `WeierstrassCurve.disjoint_ivStarThree2Locus_MultSplitLocusThree`: the shell meets neither
  starred locus.
* `WeierstrassCurve.volume_rowThree_at_two`: the three loci together have mass `1153/16384`.
* `WeierstrassCurve.rowThree_subset_headMinimal`: they lie in the minimal part of the `t = 3` row.
* `WeierstrassCurve.elevenFiftyThree_div_le_δ_three_at_two`: `1153/16368 ≤ δ_2(3)`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

/-! ### The split multiplicative shell meets neither starred locus -/

/-- On the split `IV` locus `a₄ ≢ 5 (mod 8)`, which separates it from the split multiplicative
shell `a₄ ≡ 5 (mod 16)`. -/
theorem headResIVTwo_fst_ne_five : ∀ A E : ZMod (2 ^ 3), HeadResIVTwo A E → A ≠ 5 := by decide

/-- On the `(IV*, 3)` locus `a₄ ≡ 0, 1, 8, 9 (mod 16)`, never `5`. -/
theorem headResIVstarThreeTwo_fst_ne_five : ∀ A E : ZMod (2 ^ 5), HeadResIVstarThreeTwo A E →
    (ZMod.cast A : ZMod (2 ^ 4)) ≠ 5 := by decide

/-- **The split `IV` locus and the split multiplicative shell at level `3` are disjoint.** -/
theorem disjoint_iv2Locus_MultSplitLocusThree : Disjoint iv2Locus (multSplitLocusTwo 2 3) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  refine headResIVTwo_fst_ne_five _ _ (mem_iv2Locus_iff.1 hx) ?_
  rw [← PadicInt.cast_toZModPow 3 4 (by norm_num), (mem_multSplitLocusTwo_iff.1 hx').1]
  decide

/-- **The `(IV*, 3)` locus and the split multiplicative shell at level `3` are disjoint.** -/
theorem disjoint_ivStarThree2Locus_MultSplitLocusThree :
    Disjoint ivStarThree2Locus (multSplitLocusTwo 2 3) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  refine headResIVstarThreeTwo_fst_ne_five _ _ (mem_ivStarThree2Locus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num)]
  exact (mem_multSplitLocusTwo_iff.1 hx').1

/-- The union of the split `IV` locus and the `(IV*, 3)` locus is disjoint from the split
multiplicative shell at level `3`. -/
theorem disjoint_union_IVthree_MultSplitLocusThree :
    Disjoint (iv2Locus ∪ ivStarThree2Locus) (multSplitLocusTwo 2 3) :=
  Set.disjoint_union_left.2
    ⟨disjoint_iv2Locus_MultSplitLocusThree, disjoint_ivStarThree2Locus_MultSplitLocusThree⟩

/-! ### The mass of the whole row -/

/-- In `ℝ≥0∞`, `(2⁻¹)¹⁴ = 1/16384`. -/
theorem inv_pow_fourteen_eq_at_two : ((2 : ℝ≥0∞)⁻¹) ^ 14 = 1 / 16384 := by
  rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ 14 = 16384 by norm_num, ← one_div]

/-- **The three `t = 3` loci together have mass `9/128 + 2⁻¹⁴ = 1153/16384`.** -/
theorem volume_rowThree_at_two : (volume : Measure (ℤ_[2] × ℤ_[2]))
    (iv2Locus ∪ ivStarThree2Locus ∪ multSplitLocusTwo 2 3) = 1153 / 16384 := by
  rw [measure_union disjoint_union_IVthree_MultSplitLocusThree (measurableSet_multSplitLocusTwo 3),
    volume_union_IVthree_at_two, volume_multSplitLocusTwo_at_two, show 3 + 11 = 14 from rfl,
    inv_pow_fourteen_eq_at_two,
    show (9 : ℝ≥0∞) / 128 = 1152 / 16384 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-- **All three `t = 3` loci lie in the minimal part of the row.** -/
theorem rowThree_subset_headMinimal :
    iv2Locus ∪ ivStarThree2Locus ∪ multSplitLocusTwo 2 3 ⊆
      (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3)) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  Set.union_subset union_IVthree_subset_headMinimal
    (multSplitLocusTwo_subset_headMinimal rfl (by norm_num))

/-! ### The row bound -/

/-- **`1153/16368 ≤ δ_2(3)`.** The three loci have total mass `1153/16384`, and the storey factor
is `1024/1023`. -/
theorem elevenFiftyThree_div_le_δ_three_at_two : (1153 : ℝ≥0∞) / 16368 ≤ δ 2 3 := by
  have hmul : (1153 : ℝ≥0∞) / 16384 * (1024 / 1023) = 1180672 / 16760832 := by
    rw [enn_div_mul_div (by norm_num) (by norm_num)]; norm_num
  refine le_trans (le_of_eq ?_) (le_δ_at_two_of_subset rowThree_subset_headMinimal)
  rw [volume_rowThree_at_two, hmul]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve
