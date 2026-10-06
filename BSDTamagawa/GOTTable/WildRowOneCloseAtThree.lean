/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowPrepAtThree
public import BSDTamagawa.GOTTable.WildStarredUnitAtThree

/-!
# The row `t = 1` of the `p = 3` head

The row `t = 1` of the `p = 3` column is filled by seven loci and a Family-B contribution. Over the
common denominator `2125764 = 36 · 3¹⁰` their minimal-storey masses are

    I₀ ∪ II ∪ IV non-split          one3LocusFull                 73/81      = 1915704/2125764
    (I₀*, 1), 9 ∣ a₄                 iZeroStarOne3Locus            2/2187     =    1944/2125764
    (I₀*, 1), v₃(a₄) = 1             IZeroStarUnitThree.Locus 2    2/729      =    5832/2125764
    (IV*, 1), v₃(a₆) = 3             ivStarOneUnit3Locus           2/6561     =     648/2125764
    (IV*, 1), v₃(a₆) = 4             ivStarOne3Locus               1/6561     =     324/2125764
    (II*, 1), v₃(a₆) = 3             iiStarUnit3Locus              4/59049    =     144/2125764
    (II*, 1), v₃(a₆) = 5             iiStar3Locus                  2/59049    =      72/2125764
                                                                  --------------------------------
                                    rowOneCore3Locus           53466/59049 = 1924776/2125764
    Family B, row 1                                                                 65/2125764
                                                                  --------------------------------
                                                                                1924841/2125764

and `1924841/2125764 · 59049/59048 = 1924841/2125728`. Loci over distinct Kodaira symbols are
disjoint; the two `(I₀*, 1)` loci are separated by `9 ∣ a₄` against `v₃(a₄) = 1`, and the two `IV*`
and the two `II*` loci by `3⁴ ∣ a₆`.

## Main definitions

* `WeierstrassCurve.rowOneIZeroStar3Locus`: the `I₀*` block of the row.
* `WeierstrassCurve.rowOneStarred3Locus`: the `IV*` and `II*` block of the row.
* `WeierstrassCurve.rowOneCore3Locus`: the union of `one3LocusFull` and the two blocks.

## Main results

* `WeierstrassCurve.volume_rowOneIZeroStar3Locus`, `WeierstrassCurve.volume_rowOneStarred3Locus`,
  `WeierstrassCurve.volume_rowOneCore3Locus`: the masses `8/2187`, `33/59049` and `53466/59049`.
* `WeierstrassCurve.row_one_close_at_three`: `1924841/2125728 ≤ δ_3(1)`, given a measurable set of
  mass `65/2125764` inside the minimal part of the row and disjoint from `rowOneCore3Locus`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### The three blocks of the row -/

/-- The `I₀*` block of row `t = 1`: the `9 ∣ a₄` locus and the `v₃(a₄) = 1` cylinder. -/
noncomputable def rowOneIZeroStar3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  iZeroStarOne3Locus ∪ IZeroStarUnitThree.locus 2

/-- The starred block of row `t = 1`: `(IV*, 1)` and `(II*, 1)` at both depths of `a₆`. -/
noncomputable def rowOneStarred3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  (ivStarOneUnit3Locus ∪ ivStarOne3Locus) ∪ (iiStarUnit3Locus ∪ iiStar3Locus)

/-- The union of `one3LocusFull`, the `I₀*` block and the starred block of row `t = 1`. -/
noncomputable def rowOneCore3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  one3LocusFull ∪ rowOneIZeroStar3Locus ∪ rowOneStarred3Locus

/-! ### Each block's symbols -/

/-- A point of `one3LocusFull` lies in the fibre `(κ, 1)` for `κ` one of `I₀`, `II`, `IV`. -/
theorem exists_symbol_of_mem_one3LocusFull {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ one3LocusFull) :
    ∃ κ, (κ = KodairaSymbol.I 0 ∨ κ = KodairaSymbol.II ∨ κ = KodairaSymbol.IV) ∧
      x ∈ stratFibre 3 (κ, 1) := by
  rcases one3LocusFull_subset_stratFibre_triple hx with (h | h) | h
  · exact ⟨KodairaSymbol.I 0, Or.inl rfl, h⟩
  · exact ⟨KodairaSymbol.II, Or.inr (Or.inl rfl), h⟩
  · exact ⟨KodairaSymbol.IV, Or.inr (Or.inr rfl), h⟩

/-- A point of `rowOneIZeroStar3Locus` lies in the fibre `(I₀*, 1)`. -/
theorem exists_symbol_of_mem_rowOneIZeroStar3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ rowOneIZeroStar3Locus) :
    ∃ κ, κ = KodairaSymbol.I! 0 ∧ x ∈ stratFibre 3 (κ, 1) := by
  rcases hx with h | h
  · exact ⟨KodairaSymbol.I! 0, rfl, iZeroStarOne3Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I! 0, rfl, IZeroStarUnitThree.locus_two_subset_stratFibre h⟩

/-- A point of `rowOneStarred3Locus` lies in the fibre `(κ, 1)` for `κ` one of `IV*`, `II*`. -/
theorem exists_symbol_of_mem_rowOneStarred3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ rowOneStarred3Locus) :
    ∃ κ, (κ = KodairaSymbol.IV! ∨ κ = KodairaSymbol.II!) ∧ x ∈ stratFibre 3 (κ, 1) := by
  rcases hx with (h | h) | (h | h)
  · exact ⟨KodairaSymbol.IV!, Or.inl rfl, ivStarOneUnit3Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.IV!, Or.inl rfl, ivStarOne3Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.II!, Or.inr rfl, iiStarUnit3Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.II!, Or.inr rfl, iiStar3Locus_subset_stratFibre h⟩

/-! ### The blocks are pairwise disjoint -/

/-- `one3LocusFull` and `rowOneIZeroStar3Locus` are disjoint. -/
theorem disjoint_one3LocusFull_rowOneIZeroStar3Locus :
    Disjoint one3LocusFull rowOneIZeroStar3Locus :=
  RowsThree.disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl | rfl) h <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_one3LocusFull)
    fun _ => exists_symbol_of_mem_rowOneIZeroStar3Locus

/-- `one3LocusFull` and `rowOneStarred3Locus` are disjoint. -/
theorem disjoint_one3LocusFull_rowOneStarred3Locus :
    Disjoint one3LocusFull rowOneStarred3Locus :=
  RowsThree.disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl | rfl) (h | h) <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_one3LocusFull)
    fun _ => exists_symbol_of_mem_rowOneStarred3Locus

/-- `rowOneIZeroStar3Locus` and `rowOneStarred3Locus` are disjoint. -/
theorem disjoint_rowOneIZeroStar3Locus_rowOneStarred3Locus :
    Disjoint rowOneIZeroStar3Locus rowOneStarred3Locus :=
  RowsThree.disjoint_of_forall_stratFibre
    (by rintro κ rfl (h | h) <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowOneIZeroStar3Locus)
    fun _ => exists_symbol_of_mem_rowOneStarred3Locus

/-! ### Measurability and mass, block by block -/

/-- `rowOneIZeroStar3Locus` is measurable. -/
theorem measurableSet_rowOneIZeroStar3Locus : MeasurableSet rowOneIZeroStar3Locus :=
  measurableSet_iZeroStarOne3Locus.union (IZeroStarUnitThree.measurableSet_locus 2)

/-- `rowOneStarred3Locus` is measurable. -/
theorem measurableSet_rowOneStarred3Locus : MeasurableSet rowOneStarred3Locus :=
  (measurableSet_ivStarOneUnit3Locus.union measurableSet_ivStarOne3Locus).union
    (measurableSet_iiStarUnit3Locus.union measurableSet_iiStar3Locus)

/-- **The `I₀*` block has mass `2/2187 + 2/729 = 8/2187`.** -/
theorem volume_rowOneIZeroStar3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowOneIZeroStar3Locus = 8 / 2187 := by
  rw [rowOneIZeroStar3Locus,
    measure_union disjoint_iZeroStarOne3Locus_locus_two (IZeroStarUnitThree.measurableSet_locus 2),
    volume_iZeroStarOne3Locus,
    IZeroStarUnitThree.volume_locus_of_card IZeroStarUnitThree.card_residues_two,
    show (2 : ℝ≥0∞) / 729 = 6 / 2187 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-- **The starred block has mass `33/59049`**. -/
theorem volume_rowOneStarred3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowOneStarred3Locus = 33 / 59049 := by
  rw [rowOneStarred3Locus, volume_union_one_unit_at_three]

/-- **The set `rowOneCore3Locus` has mass `53466/59049`**, the total of `73/81`, `8/2187` and
`33/59049`. -/
theorem volume_rowOneCore3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowOneCore3Locus = 53466 / 59049 := by
  rw [rowOneCore3Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_one3LocusFull_rowOneStarred3Locus,
          disjoint_rowOneIZeroStar3Locus_rowOneStarred3Locus⟩)
      measurableSet_rowOneStarred3Locus,
    measure_union disjoint_one3LocusFull_rowOneIZeroStar3Locus measurableSet_rowOneIZeroStar3Locus,
    volume_one3LocusFull, volume_rowOneIZeroStar3Locus, volume_rowOneStarred3Locus,
    show (73 : ℝ≥0∞) / 81 = 53217 / 59049 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (8 : ℝ≥0∞) / 2187 = 216 / 59049 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

/-! ### Inclusion in the minimal part of the row -/

/-- `rowOneIZeroStar3Locus` lies in the minimal part `headMinimal 3 1` of row `t = 1`. -/
theorem rowOneIZeroStar3Locus_subset_headMinimal : rowOneIZeroStar3Locus ⊆ headMinimal 3 1 :=
  Set.union_subset iZeroStarOne3Locus_subset_headMinimal
    IZeroStarUnitThree.locus_two_subset_headMinimal

/-- `rowOneStarred3Locus` lies in the minimal part `headMinimal 3 1` of row `t = 1`. -/
theorem rowOneStarred3Locus_subset_headMinimal : rowOneStarred3Locus ⊆ headMinimal 3 1 :=
  Set.union_subset
    (Set.union_subset ivStarOneUnit3Locus_subset_headMinimal ivStarOne3Locus_subset_headMinimal)
    (Set.union_subset iiStarUnit3Locus_subset_headMinimal iiStar3Locus_subset_headMinimal)

/-- `rowOneCore3Locus` lies in the minimal part `headMinimal 3 1` of row `t = 1`. -/
theorem rowOneCore3Locus_subset_headMinimal : rowOneCore3Locus ⊆ headMinimal 3 1 :=
  Set.union_subset
    (Set.union_subset one3LocusFull_subset_headMinimal rowOneIZeroStar3Locus_subset_headMinimal)
    rowOneStarred3Locus_subset_headMinimal

/-! ### The bound on the row -/

/-- **`1924841/2125728 ≤ δ_3(1)`**, given a measurable set `B` of mass `65/2125764` inside the
minimal part of the row `t = 1` and disjoint from `rowOneCore3Locus`. -/
theorem row_one_close_at_three (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B)
    (hBsub : B ⊆ headMinimal 3 1)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 65 / 2125764)
    (hBdisj : Disjoint B rowOneCore3Locus) :
    (1924841 : ℝ≥0∞) / 2125728 ≤ δ 3 1 := by
  have hvol : (volume : Measure (ℤ_[3] × ℤ_[3])) (rowOneCore3Locus ∪ B)
      = 1924841 / 2125764 := by
    rw [measure_union hBdisj.symm hB, volume_rowOneCore3Locus, hBvol,
      show (53466 : ℝ≥0∞) / 59049 = 1924776 / 2125764 from
        enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      ENNReal.div_add_div_same]
    norm_num
  refine le_trans (le_of_eq ?_)
    (le_δ_at_three_of_subset (Set.union_subset rowOneCore3Locus_subset_headMinimal hBsub))
  rw [hvol, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
