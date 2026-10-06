/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildInStarEvenAtTwo
public import BSDTamagawa.GOTTable.WildInStarLowAtTwo
public import BSDTamagawa.GOTTable.WildMultiplicativeAtTwo

/-!
# Six loci of the `t = 4` row at `p = 2`

This file assembles six pairwise disjoint loci of the row `t = 4` of the `p = 2` head into one set,
shows that it lies in the minimal part of the row, and computes its mass. Masses are minimal-storey
masses, over the common denominator `32768`:

    locus                     stratum      mass       over 32768
    ------------------------------------------------------------
    iStarOneFourLocus         (I₁*, 4)     1/128            256
    iStarTwoFourLocus         (I₂*, 4)     1/512             64
    iStarThreeFourLocus       (I₃*, 4)     1/1024            32
    aStarTwoFourLocus         (I₂*, 4)     1/512             64
    iStarFourFourLocus        (I₄*, 4)     1/2048            16
    multSplitLocusTwo 2 4     (I₄, 4)      2⁻¹⁵               1
    ------------------------------------------------------------
                                           433/32768        433

Fourteen of the fifteen pairs lie in strata over distinct Kodaira symbols and are therefore
disjoint. The two loci with symbol `I₂*`, `iStarTwoFourLocus` and `aStarTwoFourLocus`, are
separated by `a₄` modulo `16`, which is `12` on the first and odd on the second.

## Main definitions

* `WeierstrassCurve.rowFourCore2Locus`: the union of the six loci.

## Main results

* `WeierstrassCurve.RowFour.mem_stratFibre_of_kodaira`: a point of the `t`-row whose Tate algorithm
  run has Kodaira symbol `κ` lies in the stratum over `(κ, t)`.
* `WeierstrassCurve.RowFour.disjoint_of_subset_stratFibre`: loci contained in strata over distinct
  Kodaira symbols are disjoint.
* `WeierstrassCurve.rowFourCore2Locus_subset_headMinimal`: the six loci lie in the minimal part
  of the `t = 4` row.
* `WeierstrassCurve.volume_rowFourCore2Locus`: the union has mass `433/32768`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Measurability -/

/-- The `(I₂*, 4)` locus `aStarTwoFourLocus` is measurable. -/
theorem measurableSet_aStarTwoFourLocus : MeasurableSet aStarTwoFourLocus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesAStarTwoFour

/-- The `(I₄*, 4)` locus is measurable. -/
theorem measurableSet_iStarFourFourLocus : MeasurableSet iStarFourFourLocus :=
  PadicInt.measurableSet_preimage_redPairPow 8 headResiduesIStarFourFour

namespace RowFour

/-! ### The strata containing the six loci -/

/-- A point of `⋃ κ', stratFibre 2 (κ', t)` whose Tate algorithm run has Kodaira symbol `κ` lies in
`stratFibre 2 (κ, t)`. -/
theorem mem_stratFibre_of_kodaira {t : ℕ} {κ : KodairaSymbol} {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ ⋃ κ' : KodairaSymbol, stratFibre 2 (κ', t))
    (hκ : ∀ hΔ : (ofShortNF x.1 x.2).Δ ≠ 0, (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = κ) :
    x ∈ stratFibre 2 (κ, t) := by
  obtain ⟨κ', hκ'⟩ := Set.mem_iUnion.1 hx
  have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ'
  have ht : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = t :=
    congrArg Prod.snd ((mem_stratFibre_iff hUp).1 hκ')
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext (hκ hUp) ht)

/-- **The `(I₁*, 4)` locus lies in the `(I₁*, 4)` stratum.** -/
theorem iStarOneFourLocus_subset_stratFibre :
    iStarOneFourLocus ⊆ stratFibre 2 (KodairaSymbol.I! 1, 4) := by
  intro x hx
  refine mem_stratFibre_of_kodaira (iStarOneFourLocus_subset_iUnion_stratFibre hx) fun hΔ => ?_
  rcases headResIStarOneFour_cases _ _ (mem_iStarOneFourLocus_iff.1 hx) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_odd_two h1 h2
    exact (run_eq_Istar_one_two_odd (p := 2) rfl (by norm_num) ha₄ ha₆ hΔ).1
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_even_two h1 h2
    exact (run_eq_Istar_one_two_even (p := 2) rfl (by norm_num) ha₄ ha₆ hΔ).1

/-- **The `(I₂*, 4)` locus `iStarTwoFourLocus` lies in the `(I₂*, 4)` stratum.** -/
theorem iStarTwoFourLocus_subset_stratFibre :
    iStarTwoFourLocus ⊆ stratFibre 2 (KodairaSymbol.I! 2, 4) := by
  intro x hx
  refine mem_stratFibre_of_kodaira (iStarTwoFourLocus_subset_iUnion_stratFibre hx) fun hΔ => ?_
  rcases headResIStarTwoFour_cases _ _ (mem_iStarTwoFourLocus_iff.1 hx) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨A, F, ha₄, ha₆, -⟩ := exists_params_istar_two_even (a₄ := x.1) (a₆ := x.2)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) h2)
    exact (run_eq_Istar_two_at_two (p := 2) rfl (by norm_num) (G := 0) (by ring) ha₄
      (by rw [ha₆]; ring) hΔ).1
  · obtain ⟨A, F, ha₄, ha₆, -⟩ := exists_params_istar_two_odd (a₄ := x.1) (a₆ := x.2)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
    exact (run_eq_Istar_two_at_two (p := 2) rfl (by norm_num) (G := 1) (by ring) ha₄
      (by rw [ha₆]; ring) hΔ).1

/-- **The `(I₃*, 4)` locus lies in the `(I₃*, 4)` stratum.** -/
theorem iStarThreeFourLocus_subset_stratFibre :
    iStarThreeFourLocus ⊆ stratFibre 2 (KodairaSymbol.I! 3, 4) := by
  intro x hx
  refine mem_stratFibre_of_kodaira (iStarThreeFourLocus_subset_iUnion_stratFibre hx) fun hΔ => ?_
  rcases headResIStarThreeFour_cases _ _ (mem_iStarThreeFourLocus_iff.1 hx) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 0) (ε := 0) (c₄ := 4) (c₆ := 0) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [sub_zero]))
    exact (run_eq_Istar_three_at_two (p := 2) rfl (by norm_num) (by norm_num) (by norm_num)
      ha₄ ha₆ hΔ).1
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 1) (ε := 0) (c₄ := 20) (c₆ := 0) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [sub_zero]))
    exact (run_eq_Istar_three_at_two (p := 2) rfl (by norm_num) (by norm_num) (by norm_num)
      ha₄ ha₆ hΔ).1
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 0) (ε := 1) (c₄ := 4) (c₆ := 32) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
    exact (run_eq_Istar_three_at_two (p := 2) rfl (by norm_num) (by norm_num) (by norm_num)
      ha₄ ha₆ hΔ).1
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 1) (ε := 1) (c₄ := 20) (c₆ := 32) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
    exact (run_eq_Istar_three_at_two (p := 2) rfl (by norm_num) (by norm_num) (by norm_num)
      ha₄ ha₆ hΔ).1

/-- **The `(I₂*, 4)` locus `aStarTwoFourLocus` lies in the `(I₂*, 4)` stratum.** -/
theorem aStarTwoFourLocus_subset_stratFibre :
    aStarTwoFourLocus ⊆ stratFibre 2 (KodairaSymbol.I! 2, 4) := by
  intro x hx
  refine mem_stratFibre_of_kodaira (aStarTwoFourLocus_subset_iUnion_stratFibre hx) fun hΔ => ?_
  rcases headResAStarTwoFour_cases _ _ (mem_aStarTwoFourLocus_iff.1 hx) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨A, F, ha₄, ha₆, -⟩ := exists_params_AStarTwoFive h1 h2
    exact (run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 2 * A ^ 2 + A) (by ring) hΔ).1
  · obtain ⟨A, F, ha₄, ha₆, -⟩ := exists_params_AStarTwoThirteen h1 h2
    exact (run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 1 + 3 * A + 2 * A ^ 2) (by ring) hΔ).1

/-- On the `(I₄*, 4)` residue set modulo `2⁸`, `a₄ ≡ 4` and `a₆ ≡ 16` modulo `32`. -/
theorem headResIStarFourFour_class : ∀ a e : ZMod (2 ^ 8), HeadResIStarFourFour a e →
    (ZMod.cast (a - 4) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast (e - 16) : ZMod (2 ^ 5)) = 0 := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨by decide, by decide⟩

/-- **The `(I₄*, 4)` locus lies in the `(I₄*, 4)` stratum.** -/
theorem iStarFourFourLocus_subset_stratFibre :
    iStarFourFourLocus ⊆ stratFibre 2 (KodairaSymbol.I! 4, 4) := by
  intro x hx
  refine mem_stratFibre_of_kodaira (iStarFourFourLocus_subset_iUnion_stratFibre hx) fun hΔ => ?_
  obtain ⟨h1, h2⟩ := headResIStarFourFour_class _ _ (mem_iStarFourFourLocus_iff.1 hx)
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.1 - 4 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 8) (by norm_num) (by rwa [map_sub, map_ofNat])
  obtain ⟨F, hF⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - 16 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 8) (by norm_num) (by rwa [map_sub, map_ofNat])
  rw [hcast] at hA hF
  obtain ⟨K, hK⟩ := exists_sq_add_self_eq_two_mul (p := 2) rfl hcast F
  obtain ⟨J, hJ⟩ := exists_sq_add_self_eq_two_mul (p := 2) rfl hcast (A + K)
  exact (run_eq_Istar_four_at_two (p := 2) rfl hcast (Z := A + K) (J := J)
    (by linear_combination hA) (by linear_combination hF) hK rfl hJ hΔ).1

/-- **The split multiplicative locus at level `4` lies in the `(I₄, 4)` stratum.** -/
theorem MultSplitFourLocus_subset_stratFibre :
    multSplitLocusTwo 2 4 ⊆ stratFibre 2 (KodairaSymbol.I 4, 4) := by
  intro x hx
  refine mem_stratFibre_of_kodaira
    (multSplitLocusTwo_subset_iUnion_stratFibre (p := 2) rfl (by norm_num) hx) fun hΔ => ?_
  exact (multTwo_run_eq_I_of_mem' (p := 2) rfl (by norm_num) hx hΔ).1

/-! ### Disjointness -/

/-- **Two loci lying in strata over distinct Kodaira symbols are disjoint.** -/
theorem disjoint_of_subset_stratFibre {κ κ' : KodairaSymbol} {c c' : ℕ}
    {L L' : Set (ℤ_[2] × ℤ_[2])} (h : κ ≠ κ') (hL : L ⊆ stratFibre 2 (κ, c))
    (hL' : L' ⊆ stratFibre 2 (κ', c')) : Disjoint L L' :=
  (disjoint_stratFibre_of_ne h c c').mono hL hL'

/-- The `(I₁*, 4)` locus and the `(I₂*, 4)` locus `iStarTwoFourLocus` are disjoint. -/
theorem disjoint_IStarOne_IStarTwo : Disjoint iStarOneFourLocus iStarTwoFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarOneFourLocus_subset_stratFibre iStarTwoFourLocus_subset_stratFibre

/-- The `(I₁*, 4)` locus and the `(I₃*, 4)` locus are disjoint. -/
theorem disjoint_IStarOne_IStarThree : Disjoint iStarOneFourLocus iStarThreeFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarOneFourLocus_subset_stratFibre iStarThreeFourLocus_subset_stratFibre

/-- The `(I₁*, 4)` locus and the `(I₂*, 4)` locus `aStarTwoFourLocus` are disjoint. -/
theorem disjoint_IStarOne_AStarTwo : Disjoint iStarOneFourLocus aStarTwoFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarOneFourLocus_subset_stratFibre aStarTwoFourLocus_subset_stratFibre

/-- The `(I₁*, 4)` locus and the `(I₄*, 4)` locus are disjoint. -/
theorem disjoint_IStarOne_IStarFour : Disjoint iStarOneFourLocus iStarFourFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarOneFourLocus_subset_stratFibre iStarFourFourLocus_subset_stratFibre

/-- The `(I₁*, 4)` locus and the split multiplicative locus at level `4` are disjoint. -/
theorem disjoint_IStarOne_MultSplit : Disjoint iStarOneFourLocus (multSplitLocusTwo 2 4) :=
  disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iStarOneFourLocus_subset_stratFibre MultSplitFourLocus_subset_stratFibre

/-- The `(I₂*, 4)` locus `iStarTwoFourLocus` and the `(I₃*, 4)` locus are disjoint. -/
theorem disjoint_IStarTwo_IStarThree : Disjoint iStarTwoFourLocus iStarThreeFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarTwoFourLocus_subset_stratFibre iStarThreeFourLocus_subset_stratFibre

/-- The `(I₂*, 4)` locus `iStarTwoFourLocus` and the `(I₄*, 4)` locus are disjoint. -/
theorem disjoint_IStarTwo_IStarFour : Disjoint iStarTwoFourLocus iStarFourFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarTwoFourLocus_subset_stratFibre iStarFourFourLocus_subset_stratFibre

/-- The `(I₂*, 4)` locus `iStarTwoFourLocus` and the split multiplicative locus at level `4` are
disjoint. -/
theorem disjoint_IStarTwo_MultSplit : Disjoint iStarTwoFourLocus (multSplitLocusTwo 2 4) :=
  disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iStarTwoFourLocus_subset_stratFibre MultSplitFourLocus_subset_stratFibre

/-- The `(I₃*, 4)` locus and the `(I₂*, 4)` locus `aStarTwoFourLocus` are disjoint. -/
theorem disjoint_IStarThree_AStarTwo : Disjoint iStarThreeFourLocus aStarTwoFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarThreeFourLocus_subset_stratFibre aStarTwoFourLocus_subset_stratFibre

/-- The `(I₃*, 4)` locus and the `(I₄*, 4)` locus are disjoint. -/
theorem disjoint_IStarThree_IStarFour : Disjoint iStarThreeFourLocus iStarFourFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    iStarThreeFourLocus_subset_stratFibre iStarFourFourLocus_subset_stratFibre

/-- The `(I₃*, 4)` locus and the split multiplicative locus at level `4` are disjoint. -/
theorem disjoint_IStarThree_MultSplit : Disjoint iStarThreeFourLocus (multSplitLocusTwo 2 4) :=
  disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iStarThreeFourLocus_subset_stratFibre MultSplitFourLocus_subset_stratFibre

/-- The `(I₂*, 4)` locus `aStarTwoFourLocus` and the `(I₄*, 4)` locus are disjoint. -/
theorem disjoint_AStarTwo_IStarFour : Disjoint aStarTwoFourLocus iStarFourFourLocus :=
  disjoint_of_subset_stratFibre (by intro h; injection h with h; omega)
    aStarTwoFourLocus_subset_stratFibre iStarFourFourLocus_subset_stratFibre

/-- The `(I₂*, 4)` locus `aStarTwoFourLocus` and the split multiplicative locus at level `4` are
disjoint. -/
theorem disjoint_AStarTwo_MultSplit : Disjoint aStarTwoFourLocus (multSplitLocusTwo 2 4) :=
  disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    aStarTwoFourLocus_subset_stratFibre MultSplitFourLocus_subset_stratFibre

/-- The `(I₄*, 4)` locus and the split multiplicative locus at level `4` are disjoint. -/
theorem disjoint_IStarFour_MultSplit : Disjoint iStarFourFourLocus (multSplitLocusTwo 2 4) :=
  disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    iStarFourFourLocus_subset_stratFibre MultSplitFourLocus_subset_stratFibre

set_option maxRecDepth 100000 in
/-- On the residue set `HeadResAStarTwoFour` modulo `2⁶`, the coefficient `a₄` is not `12` modulo
`16`. -/
theorem headResAStarTwoFour_fst_ne_twelve : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 12 := by decide

/-- **The two `I₂*` loci of the row are disjoint**, by `a₄` modulo `16`: it is `12` on
`iStarTwoFourLocus` and odd on `aStarTwoFourLocus`. -/
theorem disjoint_IStarTwo_AStarTwo : Disjoint iStarTwoFourLocus aStarTwoFourLocus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  refine headResAStarTwoFour_fst_ne_twelve _ _ (mem_aStarTwoFourLocus_iff.1 hx') ?_
  exact headResIStarTwoFour_fst _ _ (mem_iStarTwoFourLocus_iff.1 hx)

end RowFour

/-! ### The union of the six loci -/

/-- The union of six loci of the `t = 4` row of the `p = 2` head: the `(I₁*, 4)` locus, the two
`(I₂*, 4)` loci, the `(I₃*, 4)` locus, the `(I₄*, 4)` locus and the split multiplicative locus at
level `4`. -/
noncomputable def rowFourCore2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  iStarOneFourLocus ∪ iStarTwoFourLocus ∪ iStarThreeFourLocus ∪ aStarTwoFourLocus ∪
    iStarFourFourLocus ∪ multSplitLocusTwo 2 4

/-- **All six loci lie in the minimal part of the `t = 4` row.** -/
theorem rowFourCore2Locus_subset_headMinimal :
    rowFourCore2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowFourCore2Locus]
  refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (Set.union_subset iStarOneFourLocus_subset_headMinimal iStarTwoFourLocus_subset_headMinimal)
    iStarThreeFourLocus_subset_headMinimal) aStarTwoFourLocus_subset_headMinimal)
    iStarFourFourLocus_subset_headMinimal)
    (multSplitLocusTwo_subset_headMinimal (p := 2) rfl (by norm_num))

/-- `2⁻¹⁵ = 1/32768`. -/
theorem RowFour.inv_pow_fifteen_eq_at_two : ((2 : ℝ≥0∞)⁻¹) ^ (4 + 11) = 1 / 32768 := by
  rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ (4 + 11) = 32768 by norm_num, ← one_div]

/-- **The set `rowFourCore2Locus` has mass `433/32768`**, the total of `1/128`, `1/512`,
`1/1024`, `1/512`, `1/2048` and `2⁻¹⁵`. -/
theorem volume_rowFourCore2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowFourCore2Locus = 433 / 32768 := by
  rw [rowFourCore2Locus,
    measure_union (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
        ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
            ⟨RowFour.disjoint_IStarOne_MultSplit, RowFour.disjoint_IStarTwo_MultSplit⟩,
          RowFour.disjoint_IStarThree_MultSplit⟩, RowFour.disjoint_AStarTwo_MultSplit⟩,
        RowFour.disjoint_IStarFour_MultSplit⟩)
      (measurableSet_multSplitLocusTwo (p := 2) 4),
    measure_union (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
        ⟨Set.disjoint_union_left.2
            ⟨RowFour.disjoint_IStarOne_IStarFour, RowFour.disjoint_IStarTwo_IStarFour⟩,
          RowFour.disjoint_IStarThree_IStarFour⟩, RowFour.disjoint_AStarTwo_IStarFour⟩)
      measurableSet_iStarFourFourLocus,
    measure_union (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
        ⟨RowFour.disjoint_IStarOne_AStarTwo, RowFour.disjoint_IStarTwo_AStarTwo⟩,
      RowFour.disjoint_IStarThree_AStarTwo⟩) measurableSet_aStarTwoFourLocus,
    measure_union (Set.disjoint_union_left.2
        ⟨RowFour.disjoint_IStarOne_IStarThree, RowFour.disjoint_IStarTwo_IStarThree⟩)
      measurableSet_iStarThreeFourLocus,
    measure_union RowFour.disjoint_IStarOne_IStarTwo measurableSet_iStarTwoFourLocus,
    volume_iStarOneFourLocus, eight_mul_inv_pow_ten_eq, volume_iStarTwoFourLocus,
    volume_iStarThreeFourLocus, volume_aStarTwoFourLocus, eight_mul_inv_pow_twelve_eq_two,
    volume_iStarFourFourLocus, thirtyTwo_mul_inv_pow_sixteen_eq, volume_multSplitLocusTwo_at_two,
    RowFour.inv_pow_fifteen_eq_at_two,
    show (1 : ℝ≥0∞) / 128 = 256 / 32768 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 512 = 64 / 32768 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 1024 = 32 / 32768 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 2048 = 16 / 32768 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

end WeierstrassCurve

end
