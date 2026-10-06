/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildMultiplicativeAtTwo
public import BSDTamagawa.GOTTable.WildRowAssemblyAtTwo
public import BSDTamagawa.GOTTable.WildStarredOddAtTwo

/-!
# The row `t = 1` of the `p = 2` head

The row `t = 1` of the `p = 2` column is filled by ten loci. Over the common denominator `12288`
their minimal-storey masses are

    (II, 1) ∪ (IV, 1) non-split  one2Locus               9/16   = 6912/12288
    (I₀*, 1)                     iZeroStarOne2Locus      1/32   =  384/12288
    (IV*, 1)                     ivStarOne2Locus         1/128  =   96/12288
    (II*, 1) even half           iiStar2Locus            1/512  =   24/12288
    (II*, 1) odd half            iiStarOdd2Locus         1/512  =   24/12288
    (I₀, 1) split quarter        good2Locus              1/2048 =    6/12288
    (I₀, 1) even family          goodEven2Locus          1/1024 =   12/12288
    (I₀, 1) mirror quarter       goodOdd2Locus           1/2048 =    6/12288
    (I₁, 1) split                multSplitLocusTwo 2 1   1/4096 =    3/12288
    (Iₙ, 1) non-split, n odd     the shells summed       1/3072 =    4/12288
                                                        ----------------------
                                                 total   7471/12288

and `7471/12288 · 1024/1023 = 7471/12276 = 241/396`, which is the value of `δ_2(1)`.

The `(I₀, 1)` mirror quarter, the odd half of `(II*, 1)` and the non-split `Iₙ` shells share the
residue class `(13, 14)` modulo `16`, and the shells are cut out by `v₂(Δ)` rather than by a deeper
congruence, so they are not separated by congruences. They are separated by the Kodaira symbol:
`strat` is a function, so loci lying in strata over distinct symbols are disjoint. The loci sharing
a symbol are separated by congruences: the two halves of `(II*, 1)` and the three pieces of
`(I₀, 1)`, and the split `(I₁, 1)` locus from the non-split shells by `a₄ ≡ 5` against `a₄ ≡ 13`
modulo `16`.

## Main definitions

* `WeierstrassCurve.rowOneSteps2Locus`, `WeierstrassCurve.rowOneStarred2Locus`,
  `WeierstrassCurve.rowOneGood2Locus`, `WeierstrassCurve.rowOneMult2Locus`: the four blocks of the
  row.
* `WeierstrassCurve.rowOne2Locus`: their union.

## Main results

* `WeierstrassCurve.one2Locus_subset_stratFibre_pair`,
  `WeierstrassCurve.iZeroStarOne2Locus_subset_stratFibre`,
  `WeierstrassCurve.iiStarOdd2Locus_subset_stratFibre`,
  `WeierstrassCurve.good2Locus_subset_stratFibre`,
  `WeierstrassCurve.goodEven2Locus_subset_stratFibre`,
  `WeierstrassCurve.goodOdd2Locus_subset_stratFibre`,
  `WeierstrassCurve.multSplitLocusTwo_subset_stratFibre` and
  `WeierstrassCurve.multNonSplitLocusTwo_subset_stratFibre_odd`: each locus lies in a stratum with
  a named Kodaira symbol.
* `WeierstrassCurve.disjoint_of_subset_stratFibre` and
  `WeierstrassCurve.disjoint_of_forall_stratFibre`: disjointness from the Kodaira symbol.
* `WeierstrassCurve.disjoint_multSplitLocusTwo_multNonSplitLocusTwo`: the split and non-split
  multiplicative loci are disjoint.
* `WeierstrassCurve.tsum_inv_pow_odd_levels`: the odd non-split shells total `2⁻¹² · 4/3 = 1/3072`.
* `WeierstrassCurve.volume_rowOne2Locus`: `rowOne2Locus` has mass `7471/12288`.
* `WeierstrassCurve.rowOne2Locus_subset_headMinimal`: `rowOne2Locus` lies in the minimal part of
  the row.
* `WeierstrassCurve.twoFortyOne_div_le_δ_one_at_two`: `241/396 ≤ δ_2(1)`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Naming the Kodaira symbol on each `t = 1` locus -/

/-- **The Steps-1-5 locus of row `t = 1` lies in the type-`II` stratum or the type-`IV` one.** -/
theorem one2Locus_subset_stratFibre_pair :
    one2Locus ⊆ stratFibre 2 (KodairaSymbol.II, 1) ∪ stratFibre 2 (KodairaSymbol.IV, 1) := by
  intro x hx
  have hA : HeadResOneTwo (PadicInt.toZModPow 3 x.1) (PadicInt.toZModPow 3 x.2) :=
    mem_one2Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_One_two hA
  rcases hA with hII | hIV
  · refine Or.inl ((mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 ?_)
    obtain ⟨hk, ht⟩ := run_eq_II_two (by
      rwa [PadicInt.cast_toZModPow 2 3 (by norm_num),
        PadicInt.cast_toZModPow 2 3 (by norm_num)] at hII) hΔ
    rw [strat]
    exact Prod.ext hk ht
  · refine Or.inr ((mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 ?_)
    obtain ⟨hk, ht⟩ := run_eq_IVns_two hIV hΔ
    rw [strat]
    exact Prod.ext hk ht

/-- **The `(I₀*, 1)` locus lies in the `(I₀*, 1)` stratum.** -/
theorem iZeroStarOne2Locus_subset_stratFibre :
    iZeroStarOne2Locus ⊆ stratFibre 2 (KodairaSymbol.I! 0, 1) := by
  intro x hx
  have hA : (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2) ∈ headResiduesIZeroStarOne :=
    mem_iZeroStarOne2Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
    ofShortNF_Δ_ne_zero_izeroStar (headResiduesIZeroStarOne_subset hA)
  obtain ⟨hk, ht⟩ := run_eq_I0star_one_two hA hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

/-- **The odd half of the `(II*, 1)` locus lies in the `(II*, 1)` stratum.** -/
theorem iiStarOdd2Locus_subset_stratFibre :
    iiStarOdd2Locus ⊆ stratFibre 2 (KodairaSymbol.II!, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_iiStarOdd2Locus hx
  obtain ⟨A, G, -, hA, hG, -⟩ := exists_params_of_mem_iiStarOdd2Locus hx
  obtain ⟨hk, ht⟩ := run_eq_IIstarOdd_two hA hG hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

/-- **The split-congruence quarter of the `(I₀, 1)` locus lies in the `(I₀, 1)` stratum.** -/
theorem good2Locus_subset_stratFibre : good2Locus ⊆ stratFibre 2 (KodairaSymbol.I 0, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_good2Locus hx
  obtain ⟨hk, ht⟩ := run_eq_I0_of_mem_good2Locus hx hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

/-- **The even family of the `(I₀, 1)` locus lies in the `(I₀, 1)` stratum.** -/
theorem goodEven2Locus_subset_stratFibre :
    goodEven2Locus ⊆ stratFibre 2 (KodairaSymbol.I 0, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_goodEven2Locus hx
  obtain ⟨A, G, hA, hG⟩ := exists_params_of_mem_goodEven2Locus hx
  obtain ⟨hk, ht⟩ := run_eq_I0_of_goodEven_two hA hG hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

/-- **The mirror quarter of the `(I₀, 1)` locus lies in the `(I₀, 1)` stratum.** -/
theorem goodOdd2Locus_subset_stratFibre : goodOdd2Locus ⊆ stratFibre 2 (KodairaSymbol.I 0, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_goodOdd2Locus hx
  obtain ⟨α, k, -, hα, hk, -⟩ := exists_params_of_mem_goodOdd2Locus hx
  obtain ⟨hkod, ht⟩ := run_eq_I0_of_goodOdd_two hα hk hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hkod ht)

/-- **The split multiplicative locus at level `n` lies in the `(Iₙ, n)` stratum.** -/
theorem multSplitLocusTwo_subset_stratFibre {n : ℕ} (hn : 1 ≤ n) :
    multSplitLocusTwo 2 n ⊆ stratFibre 2 (KodairaSymbol.I n, n) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := multTwo_Δ_ne_zero_of_mem hx
  obtain ⟨hk, ht⟩ := multTwo_run_eq_I_of_mem' rfl hn hx hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

open scoped Classical in
/-- **The non-split multiplicative locus at an odd level `n` lies in the `(Iₙ, 1)` stratum.** -/
theorem multNonSplitLocusTwo_subset_stratFibre_odd {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) :
    multNonSplitLocusTwo 2 n ⊆ stratFibre 2 (KodairaSymbol.I n, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := multTwo_nonsplit_Δ_ne_zero_of_mem hx
  obtain ⟨hk, ht⟩ := multTwo_run_eq_I_of_mem_nonsplit' rfl hn hx hΔ
  rw [ite_eq_left hodd] at ht
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

/-! ### Disjointness from the Kodaira symbol -/

/-- **Two loci lying in strata over distinct Kodaira symbols are disjoint.** -/
theorem disjoint_of_subset_stratFibre {κ κ' : KodairaSymbol} {c c' : ℕ}
    {L L' : Set (ℤ_[2] × ℤ_[2])} (h : κ ≠ κ') (hL : L ⊆ stratFibre 2 (κ, c))
    (hL' : L' ⊆ stratFibre 2 (κ', c')) : Disjoint L L' :=
  (disjoint_stratFibre_of_ne h c c').mono hL hL'

/-- **Two loci in a common row `t` are disjoint if no Kodaira symbol occurring on the first also
occurs on the second.** -/
theorem disjoint_of_forall_stratFibre {t : ℕ} {P Q : KodairaSymbol → Prop}
    {L L' : Set (ℤ_[2] × ℤ_[2])} (hPQ : ∀ κ, P κ → Q κ → False)
    (hL : ∀ x ∈ L, ∃ κ, P κ ∧ x ∈ stratFibre 2 (κ, t))
    (hL' : ∀ x ∈ L', ∃ κ, Q κ ∧ x ∈ stratFibre 2 (κ, t)) : Disjoint L L' := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨κ, hP, hκ⟩ := hL x hx
  obtain ⟨κ', hQ, hκ'⟩ := hL' x hx'
  have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ
  have hκκ : κ = κ' :=
    congrArg Prod.fst (((mem_stratFibre_iff hUp).1 hκ).symm.trans ((mem_stratFibre_iff hUp).1 hκ'))
  refine hPQ κ hP ?_
  rwa [hκκ]

/-- The `(IV*, 1)` locus and the odd half of the `(II*, 1)` locus are disjoint. -/
theorem disjoint_ivStarOne2Locus_iiStarOdd2Locus :
    Disjoint ivStarOne2Locus iiStarOdd2Locus :=
  disjoint_of_subset_stratFibre (fun h => KodairaSymbol.noConfusion h)
    ivStarOne2Locus_subset_stratFibre iiStarOdd2Locus_subset_stratFibre

/-- **The split and the non-split multiplicative loci are disjoint at every pair of levels**: `a₄`
is `5` modulo `16` on the one and `13` on the other. -/
theorem disjoint_multSplitLocusTwo_multNonSplitLocusTwo (n m : ℕ) :
    Disjoint (multSplitLocusTwo 2 n) (multNonSplitLocusTwo 2 m) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h5 : PadicInt.toZModPow 4 x.1 = (5 : ZMod (2 ^ 4)) := (mem_multSplitLocusTwo_iff.1 hx).1
  have h13 : PadicInt.toZModPow 4 x.1 = (13 : ZMod (2 ^ 4)) :=
    (mem_multNonSplitLocusTwo_iff.1 hx').1
  rw [h5] at h13
  exact absurd h13 (by decide)

/-! ### The four blocks of the row -/

/-- The Steps-1-5 block of row `t = 1`: type `II`, non-split type `IV`, and `(I₀*, 1)`. -/
noncomputable def rowOneSteps2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  one2Locus ∪ iZeroStarOne2Locus

/-- The starred block of row `t = 1`: `(IV*, 1)` and both halves of `(II*, 1)`. -/
noncomputable def rowOneStarred2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  ivStarOne2Locus ∪ iiStar2Locus ∪ iiStarOdd2Locus

/-- The good-reduction block of row `t = 1`: all of `(I₀, 1)`. -/
noncomputable def rowOneGood2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  good2Locus ∪ goodEven2Locus ∪ goodOdd2Locus

/-- The multiplicative block of row `t = 1`: split `(I₁, 1)` and the non-split `Iₙ` shells at every
odd level. -/
noncomputable def rowOneMult2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  multSplitLocusTwo 2 1 ∪ ⋃ j : ℕ, multNonSplitLocusTwo 2 (2 * j + 1)

/-- Every point of the Steps-1-5 block lies in a Tamagawa-number-`1` stratum of type `II`, `IV` or
`I₀*`. -/
theorem exists_symbol_of_mem_rowOneSteps2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ rowOneSteps2Locus) :
    ∃ κ, (κ = KodairaSymbol.II ∨ κ = KodairaSymbol.IV ∨ κ = KodairaSymbol.I! 0) ∧
      x ∈ stratFibre 2 (κ, 1) := by
  rcases hx with h | h
  · rcases one2Locus_subset_stratFibre_pair h with h' | h'
    · exact ⟨KodairaSymbol.II, Or.inl rfl, h'⟩
    · exact ⟨KodairaSymbol.IV, Or.inr (Or.inl rfl), h'⟩
  · exact ⟨KodairaSymbol.I! 0, Or.inr (Or.inr rfl), iZeroStarOne2Locus_subset_stratFibre h⟩

/-- Every point of the starred block lies in a Tamagawa-number-`1` stratum of type `IV*` or
`II*`. -/
theorem exists_symbol_of_mem_rowOneStarred2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ rowOneStarred2Locus) :
    ∃ κ, (κ = KodairaSymbol.IV! ∨ κ = KodairaSymbol.II!) ∧ x ∈ stratFibre 2 (κ, 1) := by
  rcases hx with (h | h) | h
  · exact ⟨KodairaSymbol.IV!, Or.inl rfl, ivStarOne2Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.II!, Or.inr rfl, iiStar2Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.II!, Or.inr rfl, iiStarOdd2Locus_subset_stratFibre h⟩

/-- Every point of the good-reduction block lies in the `(I₀, 1)` stratum. -/
theorem exists_symbol_of_mem_rowOneGood2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ rowOneGood2Locus) :
    ∃ κ, κ = KodairaSymbol.I 0 ∧ x ∈ stratFibre 2 (κ, 1) := by
  rcases hx with (h | h) | h
  · exact ⟨KodairaSymbol.I 0, rfl, good2Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I 0, rfl, goodEven2Locus_subset_stratFibre h⟩
  · exact ⟨KodairaSymbol.I 0, rfl, goodOdd2Locus_subset_stratFibre h⟩

/-- Every point of the multiplicative block lies in an `(Iₙ, 1)` stratum with `n ≥ 1`. -/
theorem exists_symbol_of_mem_rowOneMult2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ rowOneMult2Locus) :
    ∃ κ, (∃ n : ℕ, κ = KodairaSymbol.I (n + 1)) ∧ x ∈ stratFibre 2 (κ, 1) := by
  rcases hx with h | h
  · exact ⟨KodairaSymbol.I 1, ⟨0, rfl⟩, multSplitLocusTwo_subset_stratFibre le_rfl h⟩
  · rcases Set.mem_iUnion.1 h with ⟨j, hj⟩
    exact ⟨KodairaSymbol.I (2 * j + 1), ⟨2 * j, rfl⟩,
      multNonSplitLocusTwo_subset_stratFibre_odd (by omega) ⟨j, by omega⟩ hj⟩

/-- The Steps-1-5 block and the starred block are disjoint. -/
theorem disjoint_rowOneSteps2Locus_rowOneStarred2Locus :
    Disjoint rowOneSteps2Locus rowOneStarred2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl | rfl) (h | h) <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowOneSteps2Locus)
    fun _ => exists_symbol_of_mem_rowOneStarred2Locus

/-- The Steps-1-5 block and the good-reduction block are disjoint. -/
theorem disjoint_rowOneSteps2Locus_rowOneGood2Locus :
    Disjoint rowOneSteps2Locus rowOneGood2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl | rfl) h <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowOneSteps2Locus)
    fun _ => exists_symbol_of_mem_rowOneGood2Locus

/-- The Steps-1-5 block and the multiplicative block are disjoint. -/
theorem disjoint_rowOneSteps2Locus_rowOneMult2Locus :
    Disjoint rowOneSteps2Locus rowOneMult2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl | rfl) ⟨n, h⟩ <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowOneSteps2Locus)
    fun _ => exists_symbol_of_mem_rowOneMult2Locus

/-- The starred block and the good-reduction block are disjoint. -/
theorem disjoint_rowOneStarred2Locus_rowOneGood2Locus :
    Disjoint rowOneStarred2Locus rowOneGood2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl) h <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowOneStarred2Locus)
    fun _ => exists_symbol_of_mem_rowOneGood2Locus

/-- The starred block and the multiplicative block are disjoint. -/
theorem disjoint_rowOneStarred2Locus_rowOneMult2Locus :
    Disjoint rowOneStarred2Locus rowOneMult2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ (rfl | rfl) ⟨n, h⟩ <;> exact KodairaSymbol.noConfusion h)
    (fun _ => exists_symbol_of_mem_rowOneStarred2Locus)
    fun _ => exists_symbol_of_mem_rowOneMult2Locus

/-- The good-reduction block and the multiplicative block are disjoint. -/
theorem disjoint_rowOneGood2Locus_rowOneMult2Locus :
    Disjoint rowOneGood2Locus rowOneMult2Locus :=
  disjoint_of_forall_stratFibre
    (by rintro κ rfl ⟨n, h⟩; exact absurd (KodairaSymbol.I.inj h) (by omega))
    (fun _ => exists_symbol_of_mem_rowOneGood2Locus)
    fun _ => exists_symbol_of_mem_rowOneMult2Locus

/-! ### The geometric sum over the odd non-split levels -/

/-- `∑_{j ≥ 0} 4^{-j} = 4/3` in `ℝ≥0∞`. -/
theorem tsum_inv_pow_quarter : ∑' j : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ j = 4 / 3 := by
  have h1 : (1 : ℝ≥0∞) - (4 : ℝ≥0∞)⁻¹ = 3 / 4 := by
    refine ENNReal.sub_eq_of_eq_add (by simp) ?_
    rw [ENNReal.div_eq_inv_mul,
      show (4 : ℝ≥0∞)⁻¹ * 3 + (4 : ℝ≥0∞)⁻¹ = (4 : ℝ≥0∞)⁻¹ * 4 from by ring]
    exact (ENNReal.inv_mul_cancel (by norm_num) (by norm_num)).symm
  have h2 : ((3 : ℝ≥0∞) / 4)⁻¹ = 4 / 3 := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      inv_inv, ENNReal.div_eq_inv_mul]
    ring
  rw [ENNReal.tsum_geometric, h1, h2]

/-- **`∑_{j ≥ 0} 2^{-(2j+12)} = 1/3072`**: the total mass of the non-split `Iₙ` shells at odd
levels, which is `2^{-12} · 4/3`. -/
theorem tsum_inv_pow_odd_levels : ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (2 * j + 12) = 1 / 3072 := by
  have hterm : ∀ j : ℕ,
      ((2 : ℝ≥0∞)⁻¹) ^ (2 * j + 12) = ((2 : ℝ≥0∞)⁻¹) ^ 12 * ((4 : ℝ≥0∞)⁻¹) ^ j := fun j => by
    rw [pow_add, mul_comm, pow_mul,
      show ((2 : ℝ≥0∞)⁻¹) ^ 2 = (4 : ℝ≥0∞)⁻¹ from by rw [← ENNReal.inv_pow]; norm_num]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_inv_pow_quarter,
    show ((2 : ℝ≥0∞)⁻¹) ^ 12 = 1 / 4096 from by
      rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ 12 = 4096 by norm_num]
      exact (one_div _).symm,
    enn_div_mul_div (by norm_num) (by norm_num), show (1 : ℝ≥0∞) * 4 = 4 by norm_num,
    show (4096 : ℝ≥0∞) * 3 = 12288 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Measurability and mass, block by block -/

/-- The `(IV*, 1)` locus is measurable. -/
theorem measurableSet_ivStarOne2Locus : MeasurableSet ivStarOne2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResiduesIVstarOneTwo

/-- The starred block is measurable. -/
theorem measurableSet_rowOneStarred2Locus : MeasurableSet rowOneStarred2Locus :=
  (measurableSet_ivStarOne2Locus.union measurableSet_iiStar2Locus).union
    measurableSet_iiStarOdd2Locus

/-- The good-reduction block is measurable. -/
theorem measurableSet_rowOneGood2Locus : MeasurableSet rowOneGood2Locus :=
  (measurableSet_good2Locus.union measurableSet_goodEven2Locus).union measurableSet_goodOdd2Locus

/-- The multiplicative block is measurable. -/
theorem measurableSet_rowOneMult2Locus : MeasurableSet rowOneMult2Locus :=
  (measurableSet_multSplitLocusTwo (p := 2) 1).union
    (MeasurableSet.iUnion fun j => measurableSet_multNonSplitLocusTwo (p := 2) (2 * j + 1))

/-- **The Steps-1-5 block has mass `9/16 + 1/32 = 19/32`.** -/
theorem volume_rowOneSteps2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowOneSteps2Locus = 19 / 32 := by
  rw [rowOneSteps2Locus,
    measure_union disjoint_one2Locus_iZeroStarOne2Locus measurableSet_iZeroStarOne2Locus,
    volume_one2Locus, volume_iZeroStarOne2Locus,
    show (9 : ℝ≥0∞) / 16 = 18 / 32 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-- **The starred block has mass `1/128 + 1/512 + 1/512 = 3/256`.** -/
theorem volume_rowOneStarred2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowOneStarred2Locus = 3 / 256 := by
  rw [rowOneStarred2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_ivStarOne2Locus_iiStarOdd2Locus, disjoint_iiStar2Locus_iiStarOdd2Locus⟩)
      measurableSet_iiStarOdd2Locus,
    measure_union disjoint_ivStarOne2Locus_iiStar2Locus measurableSet_iiStar2Locus,
    volume_ivStarOne2Locus, eight_mul_inv_pow_ten_eq, volume_iiStar2Locus,
    eight_mul_inv_pow_twelve_eq, volume_iiStarOdd2Locus,
    show (1 : ℝ≥0∞) / 128 = 4 / 512 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    show (4 : ℝ≥0∞) + 1 + 1 = 6 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The good-reduction block has mass `1/2048 + 1/1024 + 1/2048 = 1/512`.** -/
theorem volume_rowOneGood2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowOneGood2Locus = 1 / 512 := by
  rw [rowOneGood2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_good2Locus_goodOdd2Locus, disjoint_goodEven2Locus_goodOdd2Locus⟩)
      measurableSet_goodOdd2Locus,
    measure_union disjoint_good2Locus_goodEven2Locus measurableSet_goodEven2Locus,
    volume_good2Locus, volume_goodEven2Locus, volume_goodOdd2Locus,
    show (1 : ℝ≥0∞) / 1024 = 2 / 2048 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    show (1 : ℝ≥0∞) + 2 + 1 = 4 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The odd non-split shells have total mass `1/3072`.** -/
theorem volume_iUnion_multNonSplitLocusTwo_odd :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (⋃ j : ℕ, multNonSplitLocusTwo 2 (2 * j + 1))
      = 1 / 3072 := by
  have hv : ∀ j : ℕ, (volume : Measure (ℤ_[2] × ℤ_[2])) (multNonSplitLocusTwo 2 (2 * j + 1))
      = ((2 : ℝ≥0∞)⁻¹) ^ (2 * j + 12) := fun j => by
    rw [volume_multNonSplitLocusTwo_at_two, show 2 * j + 1 + 11 = 2 * j + 12 from by omega]
  rw [measure_iUnion (fun i j hij => multTwo_disjoint_nonsplit (by omega))
      fun j => measurableSet_multNonSplitLocusTwo (p := 2) (2 * j + 1),
    tsum_congr hv, tsum_inv_pow_odd_levels]

/-- **The multiplicative block has mass `1/4096 + 1/3072 = 7/12288`.** -/
theorem volume_rowOneMult2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowOneMult2Locus = 7 / 12288 := by
  rw [rowOneMult2Locus,
    measure_union (Set.disjoint_iUnion_right.2 fun j =>
        disjoint_multSplitLocusTwo_multNonSplitLocusTwo 1 (2 * j + 1))
      (MeasurableSet.iUnion fun j => measurableSet_multNonSplitLocusTwo (p := 2) (2 * j + 1)),
    volume_multSplitLocusTwo_at_two, volume_iUnion_multNonSplitLocusTwo_odd,
    show ((2 : ℝ≥0∞)⁻¹) ^ (1 + 11) = 1 / 4096 from by
      rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ (1 + 11) = 4096 by norm_num]
      exact (one_div _).symm,
    show (1 : ℝ≥0∞) / 4096 = 3 / 12288 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 3072 = 4 / 12288 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-! ### Each block lies in the minimal part of the row -/

/-- The Steps-1-5 block lies in the union of the Tamagawa-number-`1` strata and outside the range
of `PadicInt.scaleProdByPPow 4 6`. -/
theorem rowOneSteps2Locus_subset_headMinimal :
    rowOneSteps2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowOneSteps2Locus]
  exact Set.union_subset one2Locus_subset_headMinimal iZeroStarOne2Locus_subset_headMinimal

/-- The starred block lies in the union of the Tamagawa-number-`1` strata and outside the range of
`PadicInt.scaleProdByPPow 4 6`. -/
theorem rowOneStarred2Locus_subset_headMinimal :
    rowOneStarred2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowOneStarred2Locus]
  exact Set.union_subset
    (Set.union_subset ivStarOne2Locus_subset_headMinimal iiStar2Locus_subset_headMinimal)
    iiStarOdd2Locus_subset_headMinimal

/-- The good-reduction block lies in the union of the Tamagawa-number-`1` strata and outside the
range of `PadicInt.scaleProdByPPow 4 6`. -/
theorem rowOneGood2Locus_subset_headMinimal :
    rowOneGood2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowOneGood2Locus]
  exact Set.union_subset
    (Set.union_subset good2Locus_subset_headMinimal goodEven2Locus_subset_headMinimal)
    goodOdd2Locus_subset_headMinimal

/-- The multiplicative block lies in the union of the Tamagawa-number-`1` strata and outside the
range of `PadicInt.scaleProdByPPow 4 6`. -/
theorem rowOneMult2Locus_subset_headMinimal :
    rowOneMult2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowOneMult2Locus]
  exact Set.union_subset (multSplitLocusTwo_subset_headMinimal (p := 2) rfl le_rfl)
    (Set.iUnion_subset fun j =>
      multNonSplitLocusTwo_subset_headMinimal_odd (p := 2) rfl (by omega) ⟨j, by omega⟩)

/-! ### The whole row -/

/-- **The `t = 1` row of the `p = 2` head, as one set.** Its four blocks are the Steps-1-5 loci
together with `(I₀*, 1)`, the starred loci `(IV*, 1)` and `(II*, 1)`, the whole of `(I₀, 1)`, and
the multiplicative loci: split `(I₁, 1)` and the non-split `Iₙ` shells at every odd level. -/
noncomputable def rowOne2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  rowOneSteps2Locus ∪ rowOneStarred2Locus ∪ rowOneGood2Locus ∪ rowOneMult2Locus

/-- The row `t = 1` locus lies in the union of the Tamagawa-number-`1` strata and outside the range
of `PadicInt.scaleProdByPPow 4 6`. -/
theorem rowOne2Locus_subset_headMinimal :
    rowOne2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowOne2Locus]
  exact Set.union_subset
    (Set.union_subset
      (Set.union_subset rowOneSteps2Locus_subset_headMinimal
        rowOneStarred2Locus_subset_headMinimal)
      rowOneGood2Locus_subset_headMinimal)
    rowOneMult2Locus_subset_headMinimal

/-- **The mass of the whole `t = 1` row is `7471/12288`**, the total of `19/32`, `3/256`, `1/512`
and `7/12288`. -/
theorem volume_rowOne2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowOne2Locus = 7471 / 12288 := by
  rw [rowOne2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨Set.disjoint_union_left.2
            ⟨disjoint_rowOneSteps2Locus_rowOneMult2Locus,
              disjoint_rowOneStarred2Locus_rowOneMult2Locus⟩,
          disjoint_rowOneGood2Locus_rowOneMult2Locus⟩)
      measurableSet_rowOneMult2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_rowOneSteps2Locus_rowOneGood2Locus,
          disjoint_rowOneStarred2Locus_rowOneGood2Locus⟩)
      measurableSet_rowOneGood2Locus,
    measure_union disjoint_rowOneSteps2Locus_rowOneStarred2Locus measurableSet_rowOneStarred2Locus,
    volume_rowOneSteps2Locus, volume_rowOneStarred2Locus, volume_rowOneGood2Locus,
    volume_rowOneMult2Locus,
    show (19 : ℝ≥0∞) / 32 = 7296 / 12288 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (3 : ℝ≥0∞) / 256 = 144 / 12288 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 512 = 24 / 12288 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

/-- **`241/396 ≤ δ_2(1)`.** The row's minimal mass is `7471/12288`, the storey factor is
`1024/1023`, and `7471/12288 · 1024/1023 = 7471/12276 = 241/396`. -/
theorem twoFortyOne_div_le_δ_one_at_two : (241 : ℝ≥0∞) / 396 ≤ δ 2 1 := by
  refine le_trans (le_of_eq ?_) (le_δ_at_two_of_subset rowOne2Locus_subset_headMinimal)
  rw [volume_rowOne2Locus, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
