/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildInStarEvenAtTwo
public import BSDTamagawa.GOTTable.WildInStarLowAtTwo
public import BSDTamagawa.GOTTable.WildRowOneCloseAtTwo

/-!
# Eleven loci of the row `t = 2` of the `p = 2` head

Eleven loci of the coefficient plane at `2` lie in the minimal part of the row `t = 2`. Over the
common denominator `24576` their minimal-storey masses are

    (III, 2)                     iii2LocusFull           1/4    = 6144/24576
    (I₀*, 2)                     iZeroStarTwo2Locus      1/32   =  768/24576
    (III*, 2) even half          iiiStar2Locus           1/256  =   96/24576
    (III*, 2) odd half           iiiStarOdd2Locus        1/256  =   96/24576
    (I₁*, 2)                     iStarOneTwoLocus        1/128  =  192/24576
    (I₂*, 2) `C` congruence      iStarTwoTwoLocus        1/512  =   48/24576
    (I₃*, 2)                     iStarThreeTwoLocus      1/1024 =   24/24576
    (I₂*, 2) `A` congruence      aStarTwoTwoLocus        1/512  =   48/24576
    (I₄*, 2)                     iStarFourTwoLocus       1/2048 =   12/24576
    (I₂, 2) split                multSplitLocusTwo 2 2   2⁻¹³   =    3/24576
    (Iₙ, 2) non-split, n even    the shells summed       1/6144 =    4/24576
                                                        ----------------------
                                                 total   7435/24576

and `7435/24576 · 1024/1023 = 7435/24552`. The value of `δ_2(2)` is `7495/24552`; the remaining
minimal mass `60/24576 = 5/2048` is carried by the `A` family of `Iₘ*` loci at the levels `m ≥ 3`
(mass `2⁻⁹` in this row) and the `B` family at the levels `m ≥ 5` (mass `2⁻¹¹`).

Loci lying in strata over distinct Kodaira symbols are disjoint, since `strat` is a function. Only
three pairs share a symbol: the two halves of `(III*, 2)`; the `C` and `A` congruence loci of
`(I₂*, 2)`, with `a₄ ≡ 12 (mod 16)` on `C` and `a₄ ≡ 5` or `13 (mod 16)` on `A`; and the split
`(I₂, 2)` locus and the non-split shell at level `2`, with `a₄ ≡ 5` against `a₄ ≡ 13 (mod 16)`. The
non-split shells are separated from one another by the level `v₂(Δ) - 12`.

## Main definitions

* `WeierstrassCurve.rowTwoSteps2Locus`, `WeierstrassCurve.rowTwoStarred2Locus`,
  `WeierstrassCurve.rowTwoInStar2Locus`, `WeierstrassCurve.rowTwoMult2Locus`: the four blocks of
  the row.
* `WeierstrassCurve.rowTwoCore2Locus`: their union.

## Main results

* `WeierstrassCurve.subset_stratFibre_of_kodairaSymbol_eq_at_two`: a locus lying in some stratum of
  the row, on which Tate's algorithm returns a fixed Kodaira symbol, lies in that symbol's stratum.
* `WeierstrassCurve.multNonSplitLocusTwo_subset_stratFibre_even`: the non-split shell at an even
  level lies in the `(Iₙ, 2)` stratum.
* `WeierstrassCurve.disjoint_iStarTwoTwoLocus_aStarTwoTwoLocus`: the `C` and `A` congruence loci of
  `(I₂*, 2)` are disjoint.
* `WeierstrassCurve.tsum_inv_pow_even_levels`: `∑_{j ≥ 0} 2^{-(2j+13)} = 2^{-13} · 4/3 = 1/6144`.
* `WeierstrassCurve.volume_rowTwoCore2Locus`: `rowTwoCore2Locus` has mass `7435/24576`.
* `WeierstrassCurve.rowTwoCore2Locus_subset_headMinimal`: it lies in the minimal part of the row.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Recovering a named stratum from a fixed Kodaira symbol -/

/-- **A locus in some stratum of the row, with a constant Kodaira symbol, lies in that symbol's
stratum.** -/
theorem subset_stratFibre_of_kodairaSymbol_eq_at_two {t : ℕ} {κ : KodairaSymbol}
    {L : Set (ℤ_[2] × ℤ_[2])} (hL : L ⊆ ⋃ κ' : KodairaSymbol, stratFibre 2 (κ', t))
    (hκ : ∀ x ∈ L, ∀ hΔ : (ofShortNF x.1 x.2).Δ ≠ 0, (TateAlgorithm.run
      (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = κ) :
    L ⊆ stratFibre 2 (κ, t) := by
  intro x hx
  obtain ⟨κ', hκ'⟩ := Set.mem_iUnion.1 (hL hx)
  have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ'
  have heq := congrArg Prod.fst ((mem_stratFibre_iff hUp).1 hκ')
  rw [strat] at heq
  exact heq.symm.trans (hκ x hx hUp) ▸ hκ'

/-! ### Measurability of the residue cylinders -/

/-- The even half of the `(III*, 2)` residue cylinder is measurable. -/
theorem measurableSet_iiiStar2Locus : MeasurableSet iiiStar2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResiduesIIIstarTwo

/-- The `(I₁*, 2)` residue cylinder is measurable. -/
theorem measurableSet_iStarOneTwoLocus : MeasurableSet iStarOneTwoLocus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResiduesIStarOneTwo

/-- The `A` congruence cylinder of `(I₂*, 2)` is measurable. -/
theorem measurableSet_aStarTwoTwoLocus : MeasurableSet aStarTwoTwoLocus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesAStarTwoTwo

/-- The `(I₄*, 2)` residue cylinder is measurable. -/
theorem measurableSet_iStarFourTwoLocus : MeasurableSet iStarFourTwoLocus :=
  PadicInt.measurableSet_preimage_redPairPow 8 headResiduesIStarFourTwo

/-! ### The Kodaira symbol on each of the five `Iₘ*` loci -/

/-- **The `(I₁*, 2)` locus answers `I₁*`.** -/
theorem iStarOneTwoLocus_run_kodairaSymbol {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarOneTwoLocus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 1 := by
  rcases headResIStarOneTwo_cases _ _ (mem_iStarOneTwoLocus_iff.1 hx) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_odd_two h1 h2
    exact (run_eq_Istar_one_two_odd (p := 2) rfl (by norm_num) ha₄ ha₆ hΔ).1
  · obtain ⟨A, E, ha₄, ha₆, -⟩ := exists_params_even_two h1 h2
    exact (run_eq_Istar_one_two_even (p := 2) rfl (by norm_num) ha₄ ha₆ hΔ).1

/-- **The `C` congruence locus of `(I₂*, 2)` answers `I₂*`.** -/
theorem iStarTwoTwoLocus_run_kodairaSymbol {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarTwoTwoLocus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 2 := by
  rcases headResIStarTwoTwo_cases _ _ (mem_iStarTwoTwoLocus_iff.1 hx) with
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

/-- **The `(I₃*, 2)` locus answers `I₃*`.** -/
theorem iStarThreeTwoLocus_run_kodairaSymbol {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarThreeTwoLocus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 3 := by
  rcases headResIStarThreeTwo_cases _ _ (mem_iStarThreeTwoLocus_iff.1 hx) with
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

/-- **The `A` congruence locus of `(I₂*, 2)` answers `I₂*`.** -/
theorem aStarTwoTwoLocus_run_kodairaSymbol {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTwoTwoLocus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 2 := by
  rcases headResAStarTwoTwo_cases _ _ (mem_aStarTwoTwoLocus_iff.1 hx) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨A, F, ha₄, ha₆, -⟩ := exists_params_AStarTwoFive h1 h2
    exact (run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 2 * A ^ 2 + A) (by ring) hΔ).1
  · obtain ⟨A, F, ha₄, ha₆, -⟩ := exists_params_AStarTwoThirteen h1 h2
    exact (run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 1 + 3 * A + 2 * A ^ 2) (by ring) hΔ).1

set_option maxRecDepth 4000 in
/-- On every `(I₄*, 2)` class `a₄ ≡ 4` and `a₆ ≡ 16` modulo `32`. -/
theorem headResIStarFourTwo_congr_mod_thirtyTwo : ∀ a e : ZMod (2 ^ 8), HeadResIStarFourTwo a e →
    (ZMod.cast (a - 4) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast (e - 16) : ZMod (2 ^ 5)) = 0 := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨by decide, by decide⟩

/-- **The `(I₄*, 2)` locus answers `I₄*`.** -/
theorem iStarFourTwoLocus_run_kodairaSymbol {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarFourTwoLocus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 4 := by
  obtain ⟨h1, h2⟩ :=
    headResIStarFourTwo_congr_mod_thirtyTwo _ _ (mem_iStarFourTwoLocus_iff.1 hx)
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.1 - 4 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 8) (by norm_num) (by rwa [map_sub, map_ofNat])
  obtain ⟨F, hF⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - 16 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 8) (by norm_num) (by rwa [map_sub, map_ofNat])
  have h32 : ((2 : ℕ) : ℤ_[2]) ^ 5 = 32 := by norm_num
  rw [h32] at hA hF
  obtain ⟨K, hK⟩ := exists_sq_add_self_eq_two_mul (p := 2) rfl (by norm_num) F
  obtain ⟨J, hJ⟩ := exists_sq_add_self_eq_two_mul (p := 2) rfl (by norm_num) (A + K)
  exact (run_eq_Istar_four_at_two (p := 2) rfl (by norm_num) (by linear_combination hA)
    (by linear_combination hF) hK rfl hJ hΔ).1

/-! ### Each of the eleven loci lies in a named stratum of the row -/

/-- **The full type-`III` locus lies in the `(III, 2)` stratum.** -/
theorem iii2LocusFull_subset_stratFibre : iii2LocusFull ⊆ stratFibre 2 (KodairaSymbol.III, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two iii2LocusFull_subset_iUnion_stratFibre
    fun _ hx hΔ => (run_eq_III_two_full (mem_iii2LocusFull_iff.1 hx) hΔ).1

/-- **The `(I₀*, 2)` locus lies in the `(I₀*, 2)` stratum.** -/
theorem iZeroStarTwo2Locus_subset_stratFibre :
    iZeroStarTwo2Locus ⊆ stratFibre 2 (KodairaSymbol.I! 0, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two iZeroStarTwo2Locus_subset_iUnion_stratFibre
    fun _ hx hΔ => (run_eq_I0star_two_two (mem_iZeroStarTwo2Locus_iff.1 hx) hΔ).1

/-- **The even half of the `(III*, 2)` locus lies in the `(III*, 2)` stratum.** -/
theorem iiiStar2Locus_subset_stratFibre :
    iiiStar2Locus ⊆ stratFibre 2 (KodairaSymbol.III!, 2) := by
  refine subset_stratFibre_of_kodairaSymbol_eq_at_two iiiStar2Locus_subset_iUnion_stratFibre
    fun x hx hΔ => ?_
  obtain ⟨-, hA, hE⟩ := headResIIIstarTwo_key _ _ (mem_iiiStar2Locus_iff.1 hx)
  obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 - 8 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) (by rwa [map_sub, map_ofNat])
  obtain ⟨E, hEv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.2 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) hE
  have h16 : ((2 : ℕ) : ℤ_[2]) ^ 4 = 16 := by norm_num
  rw [h16] at hAv hEv
  have ha₄ : x.1 = 8 + 16 * A := by linear_combination hAv
  exact (run_eq_IIIstarEven_two ha₄ hEv hΔ).1

/-- **The odd half of the `(III*, 2)` locus lies in the `(III*, 2)` stratum.** -/
theorem iiiStarOdd2Locus_subset_stratFibre :
    iiiStarOdd2Locus ⊆ stratFibre 2 (KodairaSymbol.III!, 2) := by
  refine subset_stratFibre_of_kodairaSymbol_eq_at_two iiiStarOdd2Locus_subset_iUnion_stratFibre
    fun x hx hΔ => ?_
  obtain ⟨A, E, -, hA, hE, -⟩ := exists_params_of_mem_iiiStarOdd2Locus hx
  exact (run_eq_IIIstarOdd_two hA hE hΔ).1

/-- **The `(I₁*, 2)` locus lies in the `(I₁*, 2)` stratum.** -/
theorem iStarOneTwoLocus_subset_stratFibre :
    iStarOneTwoLocus ⊆ stratFibre 2 (KodairaSymbol.I! 1, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two iStarOneTwoLocus_subset_iUnion_stratFibre
    fun _ hx hΔ => iStarOneTwoLocus_run_kodairaSymbol hx hΔ

/-- **The `C` congruence locus of `(I₂*, 2)` lies in the `(I₂*, 2)` stratum.** -/
theorem iStarTwoTwoLocus_subset_stratFibre :
    iStarTwoTwoLocus ⊆ stratFibre 2 (KodairaSymbol.I! 2, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two iStarTwoTwoLocus_subset_iUnion_stratFibre
    fun _ hx hΔ => iStarTwoTwoLocus_run_kodairaSymbol hx hΔ

/-- **The `(I₃*, 2)` locus lies in the `(I₃*, 2)` stratum.** -/
theorem iStarThreeTwoLocus_subset_stratFibre :
    iStarThreeTwoLocus ⊆ stratFibre 2 (KodairaSymbol.I! 3, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two iStarThreeTwoLocus_subset_iUnion_stratFibre
    fun _ hx hΔ => iStarThreeTwoLocus_run_kodairaSymbol hx hΔ

/-- **The `A` congruence locus of `(I₂*, 2)` lies in the `(I₂*, 2)` stratum.** -/
theorem aStarTwoTwoLocus_subset_stratFibre :
    aStarTwoTwoLocus ⊆ stratFibre 2 (KodairaSymbol.I! 2, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two aStarTwoTwoLocus_subset_iUnion_stratFibre
    fun _ hx hΔ => aStarTwoTwoLocus_run_kodairaSymbol hx hΔ

/-- **The `(I₄*, 2)` locus lies in the `(I₄*, 2)` stratum.** -/
theorem iStarFourTwoLocus_subset_stratFibre :
    iStarFourTwoLocus ⊆ stratFibre 2 (KodairaSymbol.I! 4, 2) :=
  subset_stratFibre_of_kodairaSymbol_eq_at_two iStarFourTwoLocus_subset_iUnion_stratFibre
    fun _ hx hΔ => iStarFourTwoLocus_run_kodairaSymbol hx hΔ

open scoped Classical in
/-- **The non-split multiplicative locus at an even level `n` lies in the `(Iₙ, 2)` stratum.** -/
theorem multNonSplitLocusTwo_subset_stratFibre_even {n : ℕ} (hn : 1 ≤ n) (heven : ¬ Odd n) :
    multNonSplitLocusTwo 2 n ⊆ stratFibre 2 (KodairaSymbol.I n, 2) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := multTwo_nonsplit_Δ_ne_zero_of_mem hx
  obtain ⟨hk, ht⟩ := multTwo_run_eq_I_of_mem_nonsplit' rfl hn hx hΔ
  rw [ite_eq_right heven] at ht
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

/-! ### The one pair the Kodaira symbol cannot separate

`iStarTwoTwoLocus` and `aStarTwoTwoLocus` both answer `I₂*`, being the two halves of that stratum
cut out by different congruences. On the first `a₄ ≡ 12 (mod 16)`; on the second `a₄` is `5` or
`13` modulo `16`, hence odd. -/

set_option maxRecDepth 100000 in
/-- On the `A` congruence locus of `(I₂*, 2)` the class of `a₄` modulo `16` is never `12`. -/
theorem headResAStarTwoTwo_fst_ne_twelve : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 12 := by decide

/-- **The `C` and `A` congruence loci of `(I₂*, 2)` are disjoint.** -/
theorem disjoint_iStarTwoTwoLocus_aStarTwoTwoLocus :
    Disjoint iStarTwoTwoLocus aStarTwoTwoLocus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := headResIStarTwoTwo_fst _ _ (mem_iStarTwoTwoLocus_iff.1 hx)
  refine headResAStarTwoTwo_fst_ne_twelve _ _ (mem_aStarTwoTwoLocus_iff.1 hx') ?_
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num)] at h1 ⊢
  exact h1

/-! ### The four blocks of the row -/

/-- The Steps-1-5 block of row `t = 2`: the full type-`III` locus and `(I₀*, 2)`. -/
noncomputable def rowTwoSteps2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  iii2LocusFull ∪ iZeroStarTwo2Locus

/-- The starred block of row `t = 2`: both halves of `(III*, 2)`. -/
noncomputable def rowTwoStarred2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  iiiStar2Locus ∪ iiiStarOdd2Locus

/-- The `Iₘ*` block of row `t = 2`: the levels `m = 1`, the two congruence halves of `m = 2`,
`m = 3` and `m = 4`. -/
noncomputable def rowTwoInStar2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  iStarOneTwoLocus ∪ iStarTwoTwoLocus ∪ iStarThreeTwoLocus ∪ aStarTwoTwoLocus ∪ iStarFourTwoLocus

/-- The multiplicative block of row `t = 2`: split `(I₂, 2)` and the non-split `Iₙ` shells at every
even level. -/
noncomputable def rowTwoMult2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  multSplitLocusTwo 2 2 ∪ ⋃ j : ℕ, multNonSplitLocusTwo 2 (2 * j + 2)

/-- A point of the Steps-1-5 block lies in the `(III, 2)` or the `(I₀*, 2)` stratum. -/
theorem exists_symbol_of_mem_rowTwoSteps2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ rowTwoSteps2Locus) :
    ∃ κ, (κ = KodairaSymbol.III ∨ κ = KodairaSymbol.I! 0) ∧ x ∈ stratFibre 2 (κ, 2) := by
  rcases hx with h | h
  · exact ⟨KodairaSymbol.III, Or.inl rfl, iii2LocusFull_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I! 0, Or.inr rfl, iZeroStarTwo2Locus_subset_stratFibre h⟩

/-- A point of the starred block lies in the `(III*, 2)` stratum. -/
theorem exists_symbol_of_mem_rowTwoStarred2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ rowTwoStarred2Locus) :
    ∃ κ, κ = KodairaSymbol.III! ∧ x ∈ stratFibre 2 (κ, 2) := by
  rcases hx with h | h
  · exact ⟨KodairaSymbol.III!, rfl, iiiStar2Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.III!, rfl, iiiStarOdd2Locus_subset_stratFibre h⟩

/-- A point of the `Iₘ*` block lies in an `(Iₘ*, 2)` stratum for some `m ≥ 1`. -/
theorem exists_symbol_of_mem_rowTwoInStar2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ rowTwoInStar2Locus) :
    ∃ κ, (∃ m : ℕ, κ = KodairaSymbol.I! (m + 1)) ∧ x ∈ stratFibre 2 (κ, 2) := by
  rcases hx with (((h | h) | h) | h) | h
  · exact ⟨KodairaSymbol.I! 1, ⟨0, rfl⟩, iStarOneTwoLocus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I! 2, ⟨1, rfl⟩, iStarTwoTwoLocus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I! 3, ⟨2, rfl⟩, iStarThreeTwoLocus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I! 2, ⟨1, rfl⟩, aStarTwoTwoLocus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I! 4, ⟨3, rfl⟩, iStarFourTwoLocus_subset_stratFibre h⟩

/-- A point of the multiplicative block lies in an `(Iₙ, 2)` stratum for some `n ≥ 2`. -/
theorem exists_symbol_of_mem_rowTwoMult2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ rowTwoMult2Locus) :
    ∃ κ, (∃ n : ℕ, κ = KodairaSymbol.I (n + 2)) ∧ x ∈ stratFibre 2 (κ, 2) := by
  rcases hx with h | h
  · exact ⟨KodairaSymbol.I 2, ⟨0, rfl⟩, multSplitLocusTwo_subset_stratFibre (by norm_num) h⟩
  · rcases Set.mem_iUnion.1 h with ⟨j, hj⟩
    exact ⟨KodairaSymbol.I (2 * j + 2), ⟨2 * j, rfl⟩,
      multNonSplitLocusTwo_subset_stratFibre_even (by omega) (by simp [Nat.odd_iff]) hj⟩

/-- The Steps-1-5 block and the starred block are disjoint. -/
theorem disjoint_rowTwoSteps2Locus_rowTwoStarred2Locus :
    Disjoint rowTwoSteps2Locus rowTwoStarred2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl) h <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowTwoSteps2Locus)
    fun _ => exists_symbol_of_mem_rowTwoStarred2Locus

/-- The Steps-1-5 block and the `Iₘ*` block are disjoint. -/
theorem disjoint_rowTwoSteps2Locus_rowTwoInStar2Locus :
    Disjoint rowTwoSteps2Locus rowTwoInStar2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl) ⟨m, h⟩ <;> [exact KodairaSymbol.noConfusion h;
      exact absurd (KodairaSymbol.I!.inj h) (by omega)])
    (fun _ => exists_symbol_of_mem_rowTwoSteps2Locus)
    fun _ => exists_symbol_of_mem_rowTwoInStar2Locus

/-- The Steps-1-5 block and the multiplicative block are disjoint. -/
theorem disjoint_rowTwoSteps2Locus_rowTwoMult2Locus :
    Disjoint rowTwoSteps2Locus rowTwoMult2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl) ⟨n, h⟩ <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowTwoSteps2Locus)
    fun _ => exists_symbol_of_mem_rowTwoMult2Locus

/-- The starred block and the `Iₘ*` block are disjoint. -/
theorem disjoint_rowTwoStarred2Locus_rowTwoInStar2Locus :
    Disjoint rowTwoStarred2Locus rowTwoInStar2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ rfl ⟨m, h⟩; exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowTwoStarred2Locus)
    fun _ => exists_symbol_of_mem_rowTwoInStar2Locus

/-- The starred block and the multiplicative block are disjoint. -/
theorem disjoint_rowTwoStarred2Locus_rowTwoMult2Locus :
    Disjoint rowTwoStarred2Locus rowTwoMult2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ rfl ⟨n, h⟩; exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowTwoStarred2Locus)
    fun _ => exists_symbol_of_mem_rowTwoMult2Locus

/-- The `Iₘ*` block and the multiplicative block are disjoint. -/
theorem disjoint_rowTwoInStar2Locus_rowTwoMult2Locus :
    Disjoint rowTwoInStar2Locus rowTwoMult2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ ⟨m, rfl⟩ ⟨n, h⟩; exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowTwoInStar2Locus)
    fun _ => exists_symbol_of_mem_rowTwoMult2Locus

/-! ### The `Iₘ*` block's internal disjointness

Four of the five loci answer distinct symbols; the two halves of `I₂*` are the pair separated by
the congruence above. -/

/-- The `(I₁*, 2)` locus and the `C` congruence locus of `(I₂*, 2)` are disjoint. -/
theorem disjoint_iStarOneTwoLocus_iStarTwoTwoLocus :
    Disjoint iStarOneTwoLocus iStarTwoTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarOneTwoLocus_subset_stratFibre iStarTwoTwoLocus_subset_stratFibre

/-- The `(I₁*, 2)` and `(I₃*, 2)` loci are disjoint. -/
theorem disjoint_iStarOneTwoLocus_iStarThreeTwoLocus :
    Disjoint iStarOneTwoLocus iStarThreeTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarOneTwoLocus_subset_stratFibre iStarThreeTwoLocus_subset_stratFibre

/-- The `(I₁*, 2)` locus and the `A` congruence locus of `(I₂*, 2)` are disjoint. -/
theorem disjoint_iStarOneTwoLocus_aStarTwoTwoLocus :
    Disjoint iStarOneTwoLocus aStarTwoTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarOneTwoLocus_subset_stratFibre aStarTwoTwoLocus_subset_stratFibre

/-- The `(I₁*, 2)` and `(I₄*, 2)` loci are disjoint. -/
theorem disjoint_iStarOneTwoLocus_iStarFourTwoLocus :
    Disjoint iStarOneTwoLocus iStarFourTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarOneTwoLocus_subset_stratFibre iStarFourTwoLocus_subset_stratFibre

/-- The `C` congruence locus of `(I₂*, 2)` and the `(I₄*, 2)` locus are disjoint. -/
theorem disjoint_iStarTwoTwoLocus_iStarFourTwoLocus :
    Disjoint iStarTwoTwoLocus iStarFourTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarTwoTwoLocus_subset_stratFibre iStarFourTwoLocus_subset_stratFibre

/-- The `(I₃*, 2)` locus and the `A` congruence locus of `(I₂*, 2)` are disjoint. -/
theorem disjoint_iStarThreeTwoLocus_aStarTwoTwoLocus :
    Disjoint iStarThreeTwoLocus aStarTwoTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarThreeTwoLocus_subset_stratFibre aStarTwoTwoLocus_subset_stratFibre

/-- The `(I₃*, 2)` and `(I₄*, 2)` loci are disjoint. -/
theorem disjoint_iStarThreeTwoLocus_iStarFourTwoLocus :
    Disjoint iStarThreeTwoLocus iStarFourTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    iStarThreeTwoLocus_subset_stratFibre iStarFourTwoLocus_subset_stratFibre

/-- The `A` congruence locus of `(I₂*, 2)` and the `(I₄*, 2)` locus are disjoint. -/
theorem disjoint_aStarTwoTwoLocus_iStarFourTwoLocus :
    Disjoint aStarTwoTwoLocus iStarFourTwoLocus :=
  disjoint_of_subset_stratFibre (fun h => absurd (KodairaSymbol.I!.inj h) (by omega))
    aStarTwoTwoLocus_subset_stratFibre iStarFourTwoLocus_subset_stratFibre

/-! ### The geometric sum over the even non-split levels -/

/-- **`∑_{j ≥ 0} 2^{-(2j+13)} = 1/6144`**: the total mass of the non-split `Iₙ` shells at even
levels, which is `2^{-13} · 4/3`. -/
theorem tsum_inv_pow_even_levels : ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (2 * j + 13) = 1 / 6144 := by
  have hterm : ∀ j : ℕ,
      ((2 : ℝ≥0∞)⁻¹) ^ (2 * j + 13) = ((2 : ℝ≥0∞)⁻¹) ^ 13 * ((4 : ℝ≥0∞)⁻¹) ^ j := fun j => by
    rw [pow_add, mul_comm, pow_mul,
      show ((2 : ℝ≥0∞)⁻¹) ^ 2 = (4 : ℝ≥0∞)⁻¹ from by rw [← ENNReal.inv_pow]; norm_num]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_inv_pow_quarter,
    show ((2 : ℝ≥0∞)⁻¹) ^ 13 = 1 / 8192 from by
      rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ 13 = 8192 by norm_num]
      exact (one_div _).symm,
    enn_div_mul_div (by norm_num) (by norm_num), show (1 : ℝ≥0∞) * 4 = 4 by norm_num,
    show (8192 : ℝ≥0∞) * 3 = 24576 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The even non-split shells have total mass `1/6144`.** -/
theorem volume_iUnion_multNonSplitLocusTwo_even :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (⋃ j : ℕ, multNonSplitLocusTwo 2 (2 * j + 2))
      = 1 / 6144 := by
  have hv : ∀ j : ℕ, (volume : Measure (ℤ_[2] × ℤ_[2])) (multNonSplitLocusTwo 2 (2 * j + 2))
      = ((2 : ℝ≥0∞)⁻¹) ^ (2 * j + 13) := fun j => by
    rw [volume_multNonSplitLocusTwo_at_two, show 2 * j + 2 + 11 = 2 * j + 13 from by omega]
  rw [measure_iUnion (fun i j hij => multTwo_disjoint_nonsplit (by omega))
      fun j => measurableSet_multNonSplitLocusTwo (p := 2) (2 * j + 2),
    tsum_congr hv, tsum_inv_pow_even_levels]

/-! ### Measurability and mass, block by block -/

/-- The starred block is measurable. -/
theorem measurableSet_rowTwoStarred2Locus : MeasurableSet rowTwoStarred2Locus :=
  measurableSet_iiiStar2Locus.union measurableSet_iiiStarOdd2Locus

/-- The `Iₘ*` block is measurable. -/
theorem measurableSet_rowTwoInStar2Locus : MeasurableSet rowTwoInStar2Locus :=
  (((measurableSet_iStarOneTwoLocus.union measurableSet_iStarTwoTwoLocus).union
    measurableSet_iStarThreeTwoLocus).union measurableSet_aStarTwoTwoLocus).union
    measurableSet_iStarFourTwoLocus

/-- The multiplicative block is measurable. -/
theorem measurableSet_rowTwoMult2Locus : MeasurableSet rowTwoMult2Locus :=
  (measurableSet_multSplitLocusTwo (p := 2) 2).union
    (MeasurableSet.iUnion fun j => measurableSet_multNonSplitLocusTwo (p := 2) (2 * j + 2))

/-- **The Steps-1-5 block has mass `1/4 + 1/32 = 9/32`.** -/
theorem volume_rowTwoSteps2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowTwoSteps2Locus = 9 / 32 := by
  rw [rowTwoSteps2Locus,
    measure_union disjoint_iii2LocusFull_iZeroStarTwo2Locus measurableSet_iZeroStarTwo2Locus,
    volume_iii2LocusFull, volume_iZeroStarTwo2Locus,
    show (1 : ℝ≥0∞) / 4 = 8 / 32 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-- **The starred block has mass `1/256 + 1/256 = 1/128`.** -/
theorem volume_rowTwoStarred2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowTwoStarred2Locus = 1 / 128 := by
  rw [rowTwoStarred2Locus,
    measure_union disjoint_iiiStar2Locus_iiiStarOdd2Locus measurableSet_iiiStarOdd2Locus,
    volume_iiiStar2Locus, four_mul_inv_pow_ten_eq, volume_iiiStarOdd2Locus,
    ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The `Iₘ*` block has mass `1/128 + 1/512 + 1/1024 + 1/512 + 1/2048 = 27/2048`.** -/
theorem volume_rowTwoInStar2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowTwoInStar2Locus = 27 / 2048 := by
  rw [rowTwoInStar2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨Set.disjoint_union_left.2
            ⟨Set.disjoint_union_left.2
                ⟨disjoint_iStarOneTwoLocus_iStarFourTwoLocus,
                  disjoint_iStarTwoTwoLocus_iStarFourTwoLocus⟩,
              disjoint_iStarThreeTwoLocus_iStarFourTwoLocus⟩,
          disjoint_aStarTwoTwoLocus_iStarFourTwoLocus⟩)
      measurableSet_iStarFourTwoLocus,
    measure_union (Set.disjoint_union_left.2
        ⟨Set.disjoint_union_left.2
            ⟨disjoint_iStarOneTwoLocus_aStarTwoTwoLocus,
              disjoint_iStarTwoTwoLocus_aStarTwoTwoLocus⟩,
          disjoint_iStarThreeTwoLocus_aStarTwoTwoLocus⟩)
      measurableSet_aStarTwoTwoLocus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_iStarOneTwoLocus_iStarThreeTwoLocus,
          disjoint_iStarTwoTwoLocus_iStarThreeTwoLocus⟩)
      measurableSet_iStarThreeTwoLocus,
    measure_union disjoint_iStarOneTwoLocus_iStarTwoTwoLocus measurableSet_iStarTwoTwoLocus,
    volume_iStarOneTwoLocus, eight_mul_inv_pow_ten_eq, volume_iStarTwoTwoLocus,
    volume_iStarThreeTwoLocus, volume_aStarTwoTwoLocus, eight_mul_inv_pow_twelve_eq_two,
    volume_iStarFourTwoLocus, thirtyTwo_mul_inv_pow_sixteen_eq,
    show (1 : ℝ≥0∞) / 128 = 16 / 2048 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 512 = 4 / 2048 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 1024 = 2 / 2048 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ENNReal.div_add_div_same]
  norm_num

/-- **The multiplicative block has mass `2⁻¹³ + 1/6144 = 7/24576`.** -/
theorem volume_rowTwoMult2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowTwoMult2Locus = 7 / 24576 := by
  rw [rowTwoMult2Locus,
    measure_union (Set.disjoint_iUnion_right.2 fun j =>
        disjoint_multSplitLocusTwo_multNonSplitLocusTwo 2 (2 * j + 2))
      (MeasurableSet.iUnion fun j => measurableSet_multNonSplitLocusTwo (p := 2) (2 * j + 2)),
    volume_multSplitLocusTwo_at_two, volume_iUnion_multNonSplitLocusTwo_even,
    show ((2 : ℝ≥0∞)⁻¹) ^ (2 + 11) = 1 / 8192 from by
      rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ (2 + 11) = 8192 by norm_num]
      exact (one_div _).symm,
    show (1 : ℝ≥0∞) / 8192 = 3 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 6144 = 4 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-! ### Each block lies in the minimal part of the row -/

/-- The Steps-1-5 block lies in the row `t = 2` and outside the image of `(a, b) ↦ (2⁴a, 2⁶b)`. -/
theorem rowTwoSteps2Locus_subset_headMinimal :
    rowTwoSteps2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowTwoSteps2Locus]
  exact Set.union_subset iii2LocusFull_subset_headMinimal iZeroStarTwo2Locus_subset_headMinimal

/-- The starred block lies in the row `t = 2` and outside the image of `(a, b) ↦ (2⁴a, 2⁶b)`. -/
theorem rowTwoStarred2Locus_subset_headMinimal :
    rowTwoStarred2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowTwoStarred2Locus]
  exact Set.union_subset iiiStar2Locus_subset_headMinimal iiiStarOdd2Locus_subset_headMinimal

/-- The `Iₘ*` block lies in the row `t = 2` and outside the image of `(a, b) ↦ (2⁴a, 2⁶b)`. -/
theorem rowTwoInStar2Locus_subset_headMinimal :
    rowTwoInStar2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowTwoInStar2Locus]
  exact Set.union_subset
    (Set.union_subset
      (Set.union_subset
        (Set.union_subset iStarOneTwoLocus_subset_headMinimal
          iStarTwoTwoLocus_subset_headMinimal)
        iStarThreeTwoLocus_subset_headMinimal)
      aStarTwoTwoLocus_subset_headMinimal)
    iStarFourTwoLocus_subset_headMinimal

/-- The multiplicative block lies in the row `t = 2` and outside the image of
`(a, b) ↦ (2⁴a, 2⁶b)`. -/
theorem rowTwoMult2Locus_subset_headMinimal :
    rowTwoMult2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowTwoMult2Locus]
  exact Set.union_subset (multSplitLocusTwo_subset_headMinimal (p := 2) rfl (by norm_num))
    (Set.iUnion_subset fun j =>
      multNonSplitLocusTwo_subset_headMinimal_even (p := 2) rfl (by omega)
        (by simp [Nat.odd_iff]))

/-! ### The union of the four blocks -/

/-- **Eleven loci of the `t = 2` row of the `p = 2` head, as one set.** Its four blocks are the
full type-`III` locus with `(I₀*, 2)`, both halves of `(III*, 2)`, the `Iₘ*` levels `m ≤ 4`, and
the multiplicative loci: split `(I₂, 2)` and the non-split `Iₙ` shells at every even level. -/
noncomputable def rowTwoCore2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  rowTwoSteps2Locus ∪ rowTwoStarred2Locus ∪ rowTwoInStar2Locus ∪ rowTwoMult2Locus

/-- The set `rowTwoCore2Locus` lies in the row `t = 2` and outside the image of
`(a, b) ↦ (2⁴a, 2⁶b)`. -/
theorem rowTwoCore2Locus_subset_headMinimal :
    rowTwoCore2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowTwoCore2Locus]
  exact Set.union_subset
    (Set.union_subset
      (Set.union_subset rowTwoSteps2Locus_subset_headMinimal
        rowTwoStarred2Locus_subset_headMinimal)
      rowTwoInStar2Locus_subset_headMinimal)
    rowTwoMult2Locus_subset_headMinimal

/-- **The mass of `rowTwoCore2Locus` is `7435/24576`**, the total of `9/32`, `1/128`, `27/2048`
and `7/24576`. -/
theorem volume_rowTwoCore2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowTwoCore2Locus = 7435 / 24576 := by
  rw [rowTwoCore2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨Set.disjoint_union_left.2
            ⟨disjoint_rowTwoSteps2Locus_rowTwoMult2Locus,
              disjoint_rowTwoStarred2Locus_rowTwoMult2Locus⟩,
          disjoint_rowTwoInStar2Locus_rowTwoMult2Locus⟩)
      measurableSet_rowTwoMult2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_rowTwoSteps2Locus_rowTwoInStar2Locus,
          disjoint_rowTwoStarred2Locus_rowTwoInStar2Locus⟩)
      measurableSet_rowTwoInStar2Locus,
    measure_union disjoint_rowTwoSteps2Locus_rowTwoStarred2Locus measurableSet_rowTwoStarred2Locus,
    volume_rowTwoSteps2Locus, volume_rowTwoStarred2Locus, volume_rowTwoInStar2Locus,
    volume_rowTwoMult2Locus,
    show (9 : ℝ≥0∞) / 32 = 6912 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 128 = 192 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (27 : ℝ≥0∞) / 2048 = 324 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

end WeierstrassCurve

end
