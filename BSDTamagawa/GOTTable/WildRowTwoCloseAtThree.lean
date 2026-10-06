/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowPrepAtThree
public import BSDTamagawa.GOTTable.WildStarredUnitAtThree

/-!
# The row `t = 2` of the `p = 3` head

The row `t = 2` of the `p = 3` column is filled by five loci, the Tamagawa-`2` half of Family A and
a Family-B contribution. Over the common denominator `6377292 = 4 · 3¹³` their minimal-storey
masses are

    (III, 2)                         iii3Locus                     2/27       =  472392/6377292
    (I₀*, 2), 9 ∣ a₄                 iZeroStarTwo3Locus            1/729      =    8748/6377292
    (I₀*, 2), v₃(a₄) = 1             IZeroStarUnitThree.Locus 1    2/729      =   17496/6377292
    (III*, 2), v₃(a₆) = 3            iiiStarUnit3Locus             4/19683    =    1296/6377292
    (III*, 2), v₃(a₆) ≥ 5            iiiStar3Locus                 2/19683    =     648/6377292
                                                                  --------------------------------
                                    rowTwoCore3Locus              515/6561   =  500580/6377292
    Family A, Tamagawa-2 half        FamilyAThree.part 2           1/729      =    8748/6377292
    Family B, row 2                                                                  17/6377292
                                                                  --------------------------------
                                                                                 509345/6377292

and `509345/6377292 · 59049/59048 = 509345/6377184`. Loci over distinct Kodaira symbols are
disjoint; in particular Family A, on which the symbol is `Iₘ*` with `m ≠ 0`, is disjoint from the
`(I₀*, 2)` cylinder of the same cell `v₃(a₄) = 1`, `a₆` a unit. The two `I₀*` loci are separated by
`9 ∣ a₄` against `v₃(a₄) = 1`, and the two `III*` loci by `3⁴ ∣ a₆`. The half of Family A enters
under the hypothesis `2 · μ(part 2) = μ(locus)`, and Family B as an abstract set.

## Main definitions

* `WeierstrassCurve.rowTwoIZeroStar3Locus`: the `I₀*` block of the row.
* `WeierstrassCurve.rowTwoStarred3Locus`: the `III*` block of the row.
* `WeierstrassCurve.rowTwoCore3Locus`: the union of `iii3Locus` and the two blocks.
* `WeierstrassCurve.rowTwoFull3Locus`: `rowTwoCore3Locus` together with Family A's half.

## Main results

* `WeierstrassCurve.volume_rowTwoCore3Locus`: `rowTwoCore3Locus` has mass `515/6561`.
* `WeierstrassCurve.volume_rowTwoFull3Locus`: `rowTwoFull3Locus` has mass `524/6561` under the
  halving hypothesis.
* `WeierstrassCurve.row_two_close_at_three`: `509345/6377184 ≤ δ_3(2)`, given the halving of Family
  A and a measurable set of mass `17/6377292` inside the minimal part of the row and disjoint from
  `rowTwoFull3Locus`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### The blocks of the row -/

/-- The `I₀*` block of row `t = 2`: the `9 ∣ a₄` locus and the `v₃(a₄) = 1` cylinder. -/
noncomputable def rowTwoIZeroStar3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  iZeroStarTwo3Locus ∪ IZeroStarUnitThree.locus 1

/-- The starred block of row `t = 2`: `(III*, 2)` at both depths of `a₆`. -/
noncomputable def rowTwoStarred3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  iiiStarUnit3Locus ∪ iiiStar3Locus

/-- The union of the `III` locus, the `I₀*` block and the `III*` block of row `t = 2`. -/
noncomputable def rowTwoCore3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  iii3Locus ∪ rowTwoIZeroStar3Locus ∪ rowTwoStarred3Locus

/-- **The set `rowTwoCore3Locus` together with the Tamagawa-`2` half of Family A.** -/
noncomputable def rowTwoFull3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  rowTwoCore3Locus ∪ FamilyAThree.part 2

/-! ### Each block's symbols -/

/-- The `I₀*` block of row `t = 2` lies in the stratum `(I₀*, 2)`. -/
theorem rowTwoIZeroStar3Locus_subset_stratFibre :
    rowTwoIZeroStar3Locus ⊆ stratFibre 3 (KodairaSymbol.I! 0, 2) :=
  Set.union_subset iZeroStarTwo3Locus_subset_stratFibre
    IZeroStarUnitThree.locus_one_subset_stratFibre

/-- The starred block of row `t = 2` lies in the stratum `(III*, 2)`. -/
theorem rowTwoStarred3Locus_subset_stratFibre :
    rowTwoStarred3Locus ⊆ stratFibre 3 (KodairaSymbol.III!, 2) :=
  Set.union_subset iiiStarUnit3Locus_subset_stratFibre iiiStar3Locus_subset_stratFibre

/-- Every point of `rowTwoCore3Locus` lies in a stratum `(κ, 2)` with `κ` one of `III`, `I₀*` and
`III*`. -/
theorem exists_symbol_of_mem_rowTwoCore3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ rowTwoCore3Locus) :
    ∃ κ, (κ = KodairaSymbol.III ∨ κ = KodairaSymbol.I! 0 ∨ κ = KodairaSymbol.III!) ∧
      x ∈ stratFibre 3 (κ, 2) := by
  rcases hx with (h | h) | h
  · exact ⟨KodairaSymbol.III, Or.inl rfl, iii3Locus_subset_stratFibre h⟩
  · exact ⟨_, Or.inr (Or.inl rfl), rowTwoIZeroStar3Locus_subset_stratFibre h⟩
  · exact ⟨_, Or.inr (Or.inr rfl), rowTwoStarred3Locus_subset_stratFibre h⟩

/-- Every point of the Tamagawa-`2` half of Family A lies in a stratum `(Iₘ*, 2)` with `m ≠ 0`. -/
theorem exists_symbol_of_mem_part_two {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ FamilyAThree.part 2) :
    ∃ κ, (∃ m : ℕ, m ≠ 0 ∧ κ = KodairaSymbol.I! m) ∧ x ∈ stratFibre 3 (κ, 2) := by
  obtain ⟨m, hm, h⟩ := FamilyAThree.exists_mem_stratFibre_of_mem_part hx
  exact ⟨KodairaSymbol.I! m, ⟨m, hm, rfl⟩, h⟩

/-! ### The blocks are pairwise disjoint -/

/-- The `III` locus is disjoint from the `I₀*` block of row `t = 2`. -/
theorem disjoint_iii3Locus_rowTwoIZeroStar3Locus : Disjoint iii3Locus rowTwoIZeroStar3Locus :=
  RowsThree.disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iii3Locus_subset_stratFibre rowTwoIZeroStar3Locus_subset_stratFibre

/-- The `III` locus is disjoint from the starred block of row `t = 2`. -/
theorem disjoint_iii3Locus_rowTwoStarred3Locus : Disjoint iii3Locus rowTwoStarred3Locus :=
  RowsThree.disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iii3Locus_subset_stratFibre rowTwoStarred3Locus_subset_stratFibre

/-- The `I₀*` block and the starred block of row `t = 2` are disjoint. -/
theorem disjoint_rowTwoIZeroStar3Locus_rowTwoStarred3Locus :
    Disjoint rowTwoIZeroStar3Locus rowTwoStarred3Locus :=
  RowsThree.disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    rowTwoIZeroStar3Locus_subset_stratFibre rowTwoStarred3Locus_subset_stratFibre

/-- **The set `rowTwoCore3Locus` is disjoint from Family A's half**: its symbols are `III`, `I₀*`
and `III*`, while Family A has symbol `Iₘ*` with `m ≠ 0`. -/
theorem disjoint_rowTwoCore3Locus_part_two : Disjoint rowTwoCore3Locus (FamilyAThree.part 2) :=
  RowsThree.disjoint_of_forall_stratFibre
    (by
      rintro κ (rfl | rfl | rfl) ⟨m, hm, h⟩
      · exact KodairaSymbol.noConfusion h
      · exact hm (KodairaSymbol.I!.inj h).symm
      · exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowTwoCore3Locus)
    fun _ => exists_symbol_of_mem_part_two

/-! ### Measurability and mass, block by block -/

/-- The `I₀*` block of row `t = 2` is measurable. -/
theorem measurableSet_rowTwoIZeroStar3Locus : MeasurableSet rowTwoIZeroStar3Locus :=
  measurableSet_iZeroStarTwo3Locus.union (IZeroStarUnitThree.measurableSet_locus 1)

/-- The starred block of row `t = 2` is measurable. -/
theorem measurableSet_rowTwoStarred3Locus : MeasurableSet rowTwoStarred3Locus :=
  measurableSet_iiiStarUnit3Locus.union measurableSet_iiiStar3Locus

/-- **The `I₀*` block has mass `1/729 + 2/729 = 1/243`.** -/
theorem volume_rowTwoIZeroStar3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowTwoIZeroStar3Locus = 1 / 243 := by
  rw [rowTwoIZeroStar3Locus,
    measure_union disjoint_iZeroStarTwo3Locus_locus_one (IZeroStarUnitThree.measurableSet_locus 1),
    volume_iZeroStarTwo3Locus,
    IZeroStarUnitThree.volume_locus_of_card IZeroStarUnitThree.card_residues_one,
    ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 2 = 3 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The `III*` block has mass `4/19683 + 2/19683 = 2/6561`.** -/
theorem volume_rowTwoStarred3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowTwoStarred3Locus = 2 / 6561 := by
  rw [rowTwoStarred3Locus, measure_union disjoint_iiiStarUnit3Locus measurableSet_iiiStar3Locus,
    volume_iiiStarUnit3Locus, volume_iiiStar3Locus, ENNReal.div_add_div_same,
    show (4 : ℝ≥0∞) + 2 = 6 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The set `rowTwoCore3Locus` has mass `515/6561`**, the total of `2/27`, `1/243` and
`2/6561`. -/
theorem volume_rowTwoCore3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowTwoCore3Locus = 515 / 6561 := by
  rw [rowTwoCore3Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_iii3Locus_rowTwoStarred3Locus,
          disjoint_rowTwoIZeroStar3Locus_rowTwoStarred3Locus⟩)
      measurableSet_rowTwoStarred3Locus,
    measure_union disjoint_iii3Locus_rowTwoIZeroStar3Locus measurableSet_rowTwoIZeroStar3Locus,
    volume_iii3Locus, six_mul_inv_pow_four_eq, volume_rowTwoIZeroStar3Locus,
    volume_rowTwoStarred3Locus,
    show (2 : ℝ≥0∞) / 27 = 486 / 6561 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 243 = 27 / 6561 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

/-- **With Family A's half the row has mass `515/6561 + 1/729 = 524/6561`**, under the halving
hypothesis. -/
theorem volume_rowTwoFull3Locus
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 2) =
      (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowTwoFull3Locus = 524 / 6561 := by
  rw [rowTwoFull3Locus,
    measure_union disjoint_rowTwoCore3Locus_part_two (FamilyAThree.measurableSet_part 2),
    volume_rowTwoCore3Locus, FamilyAThree.volume_half_locus hhalf,
    show (1 : ℝ≥0∞) / 729 = 9 / 6561 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-! ### Everything lies in the minimal part of the row -/

/-- The `I₀*` block lies in the minimal part of row `t = 2`. -/
theorem rowTwoIZeroStar3Locus_subset_headMinimal : rowTwoIZeroStar3Locus ⊆ headMinimal 3 2 :=
  Set.union_subset iZeroStarTwo3Locus_subset_headMinimal
    IZeroStarUnitThree.locus_one_subset_headMinimal

/-- The starred block lies in the minimal part of row `t = 2`. -/
theorem rowTwoStarred3Locus_subset_headMinimal : rowTwoStarred3Locus ⊆ headMinimal 3 2 :=
  Set.union_subset iiiStarUnit3Locus_subset_headMinimal iiiStar3Locus_subset_headMinimal

/-- The set `rowTwoCore3Locus` lies in the minimal part of row `t = 2`. -/
theorem rowTwoCore3Locus_subset_headMinimal : rowTwoCore3Locus ⊆ headMinimal 3 2 :=
  Set.union_subset
    (Set.union_subset iii3Locus_subset_headMinimal rowTwoIZeroStar3Locus_subset_headMinimal)
    rowTwoStarred3Locus_subset_headMinimal

/-- The set `rowTwoFull3Locus` lies in the minimal part of row `t = 2`. -/
theorem rowTwoFull3Locus_subset_headMinimal : rowTwoFull3Locus ⊆ headMinimal 3 2 :=
  Set.union_subset rowTwoCore3Locus_subset_headMinimal (FamilyAThree.part_subset_headMinimal 2)

/-! ### The bound on the row -/

/-- **`509345/6377184 ≤ δ_3(2)`**, given the halving of Family A and a measurable set `B` of mass
`17/6377292` inside the minimal part of the row `t = 2` and disjoint from `rowTwoFull3Locus`. -/
theorem row_two_close_at_three
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 2) =
      (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus)
    (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B) (hBsub : B ⊆ headMinimal 3 2)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 17 / 6377292)
    (hBdisj : Disjoint B rowTwoFull3Locus) :
    (509345 : ℝ≥0∞) / 6377184 ≤ δ 3 2 := by
  have hvol : (volume : Measure (ℤ_[3] × ℤ_[3])) (rowTwoFull3Locus ∪ B) =
      509345 / 6377292 := by
    rw [measure_union hBdisj.symm hB, volume_rowTwoFull3Locus hhalf, hBvol,
      show (524 : ℝ≥0∞) / 6561 = 509328 / 6377292 from
        enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      ENNReal.div_add_div_same]
    norm_num
  refine le_trans (le_of_eq ?_)
    (le_δ_at_three_of_subset (Set.union_subset rowTwoFull3Locus_subset_headMinimal hBsub))
  rw [hvol, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
