/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.HeadDensityTwoFourCoupled
public import BSDTamagawa.GOTTable.InStarAdditivity
public import BSDTamagawa.GOTTable.InStarMassArithmetic
public import BSDTamagawa.GOTTable.WildStoreyFolding

/-!
# The total mass of the positively-indexed `Iₙ*` family

Let `σ_p` be the dilation `(a, b) ↦ (p⁴ a, p⁶ b)` of `ℤ_p²`. A set `A ⊆ ℤ_p²` is `σ_p`-stable when
`σ_p x ∈ A ↔ x ∈ A` for every `x`; every stratum of the Kodaira–Tamagawa stratification is stable
for `p ≥ 5`, and so is any union of strata. For a stable set the storey folding holds:

  `μ_p(A) = μ_p(A ∖ σ_p(ℤ_p²)) · (1 - p⁻¹⁰)⁻¹`.

Applied to the positively-indexed `Iₙ*` family over Tamagawa numbers `c ∈ {2, 4}`, this gives, with
`S_c := ∑_{n ≥ 1} δ_p((Iₙ*, c))`,

  `S₂ + S₄ = ofReal (gotInStarTwo p) + ofReal (gotInStarTwo p)`

for every prime `p ≥ 5`. Consequently the equality `S₂ = S₄` implies `HasGOTDensities p`.

## Main results

* `mem_stratFibre_scaleProdByPPow_iff`: a stratum is `σ_p`-stable.
* `mem_iUnion_scaleProdByPPow_iff`: a union of `σ_p`-stable sets is `σ_p`-stable.
* `volume_eq_volume_diff_mul_inv_one_sub`: the storey folding for a `σ_p`-stable set.
* `tsum_deltaP_InStar_two_add_tsum_deltaP_InStar_four`: `S₂ + S₄ = 2 · gotInStarTwo p`.
* `tsum_deltaP_InStar_two_eq_of_eq_four`: if `S₂ = S₄`, then `S₂ = gotInStarTwo p`.
* `hasGOTDensities_of_tsum_deltaP_InStar_eq`: if `S₂ = S₄`, then `HasGOTDensities p`.
-/

open MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-! ### Dilation-stability -/

/-- If the stratification is scale-invariant, then for every reduction datum `K` and every point
`x`, the dilate `σ_p x` lies in the stratum of `K` if and only if `x` does. -/
theorem mem_stratFibre_scaleProdByPPow_iff (h : StratScaleInvariant p) (K : ReductionData)
    (x : ℤ_[p] × ℤ_[p]) :
    PadicInt.scaleProdByPPow 4 6 x ∈ stratFibre p K ↔ x ∈ stratFibre p K := by
  constructor
  · intro hy
    have hyUp : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p := stratFibre_subset _ hy
    have hxUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_scaleProdByPPow_iff.1 hyUp
    exact (mem_stratFibre_iff hxUp).2 ((h x hxUp hyUp).symm.trans ((mem_stratFibre_iff hyUp).1 hy))
  · intro hx
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
    have hyUp : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p :=
      mem_nonsingularLocus_scaleProdByPPow_iff.2 hxUp
    exact (mem_stratFibre_iff hyUp).2 ((h x hxUp hyUp).trans ((mem_stratFibre_iff hxUp).1 hx))

/-- A union of `σ_p`-stable sets, indexed by an arbitrary `Sort`, is `σ_p`-stable. -/
theorem mem_iUnion_scaleProdByPPow_iff {ι : Sort*} {S : ι → Set (ℤ_[p] × ℤ_[p])}
    (h : ∀ i x, PadicInt.scaleProdByPPow 4 6 x ∈ S i ↔ x ∈ S i) (x : ℤ_[p] × ℤ_[p]) :
    PadicInt.scaleProdByPPow 4 6 x ∈ ⋃ i, S i ↔ x ∈ ⋃ i, S i := by
  simp only [Set.mem_iUnion, h]

/-- A `σ_p`-stable set meets `σ_p(ℤ_p²)` in exactly its own dilate. -/
theorem inter_range_scaleProdByPPow_eq_image {A : Set (ℤ_[p] × ℤ_[p])}
    (hA : ∀ x, PadicInt.scaleProdByPPow 4 6 x ∈ A ↔ x ∈ A) :
    A ∩ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = PadicInt.scaleProdByPPow 4 6 '' A := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hyA, x, rfl⟩
    exact ⟨x, (hA x).1 hyA, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨(hA x).2 hx, ⟨x, rfl⟩⟩

/-! ### The storey folding for a stable set -/

/-- **Storey folding.** For every `σ_p`-stable set `A ⊆ ℤ_p²`,

  `μ_p(A) = μ_p(A ∖ σ_p(ℤ_p²)) · (1 - p⁻¹⁰)⁻¹`. -/
theorem volume_eq_volume_diff_mul_inv_one_sub (hp : 2 ≤ p) {A : Set (ℤ_[p] × ℤ_[p])}
    (hA : ∀ x, PadicInt.scaleProdByPPow 4 6 x ∈ A ↔ x ∈ A) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) A
      = volume (A \ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have hz : (p : ℝ≥0∞) ^ (-(10 : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 10 := by
    rw [show (-(10 : ℤ)) = -((10 : ℕ) : ℤ) by norm_num]
    exact (PadicInt.measure_span_pPow (p := p) 10).symm.trans (PadicInt.measure_span_pPow' 10)
  have hinter : (volume : Measure (ℤ_[p] × ℤ_[p]))
      (A ∩ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = ((p : ℝ≥0∞)⁻¹) ^ 10 * volume A := by
    rw [inter_range_scaleProdByPPow_eq_image hA,
      PadicInt.measure_image_scaleProdByPPow_four_six, hz]
  have hfix : (volume : Measure (ℤ_[p] × ℤ_[p])) A = ((p : ℝ≥0∞)⁻¹) ^ 10 * volume A
      + volume (A \ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) := by
    rw [← hinter]
    exact (measure_inter_add_sdiff _
      (PadicInt.measurableEmbedding_scaleProdByPPow 4 6).measurableSet_range).symm
  exact enn_eq_mul_inv_one_sub_of_lt_one (enn_inv_pow_ten_lt_one hp) (measure_ne_top _ _) hfix

/-! ### The total mass of the family -/

/-- For every prime `p ≥ 5`, the masses `S_c := ∑_{n ≥ 1} δ_p((Iₙ*, c))` satisfy
`S₂ + S₄ = ofReal (gotInStarTwo p) + ofReal (gotInStarTwo p)`. -/
theorem tsum_deltaP_InStar_two_add_tsum_deltaP_InStar_four (hp : 5 ≤ p) :
    (∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2))
        + ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 4)
      = ENNReal.ofReal (gotInStarTwo p) + ENNReal.ofReal (gotInStarTwo p) := by
  have hstab : ∀ x : ℤ_[p] × ℤ_[p],
      PadicInt.scaleProdByPPow 4 6 x
          ∈ ⋃ m : ℕ, ⋃ c ∈ ({2, 4} : Set ℕ), stratFibre p (KodairaSymbol.I! (m + 1), c) ↔
        x ∈ ⋃ m : ℕ, ⋃ c ∈ ({2, 4} : Set ℕ), stratFibre p (KodairaSymbol.I! (m + 1), c) :=
    mem_iUnion_scaleProdByPPow_iff fun _ =>
      mem_iUnion_scaleProdByPPow_iff fun _ =>
        mem_iUnion_scaleProdByPPow_iff fun _ =>
          mem_stratFibre_scaleProdByPPow_iff (stratScaleInvariant_of_five_le hp) _
  have hfold := volume_eq_volume_diff_mul_inv_one_sub (p := p) (by omega) hstab
  rwa [volume_iUnion_stratFibre_Istar_pos_two_four,
    iUnion_stratFibre_Istar_pos_two_four_diff_range_eq hp,
    measure_inter_conull volume_compl_nonsingularLocus,
    volume_deepResidueLocus_doubleRootResidues_mul_storey hp] at hfold

/-- For every prime `p ≥ 5`, if the positively-indexed `Iₙ*` family has equal mass at Tamagawa
numbers `c = 2` and `c = 4`, then its mass at `c = 2` is `ofReal (gotInStarTwo p)`. -/
theorem tsum_deltaP_InStar_two_eq_of_eq_four (hp : 5 ≤ p)
    (hsym : (∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2))
      = ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 4)) :
    (∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2)) = ENNReal.ofReal (gotInStarTwo p) := by
  have h := tsum_deltaP_InStar_two_add_tsum_deltaP_InStar_four hp
  rw [← hsym, ← two_mul, ← two_mul] at h
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h

/-- For every prime `p ≥ 5`, if the positively-indexed `Iₙ*` family has equal mass at Tamagawa
numbers `c = 2` and `c = 4`, then `HasGOTDensities p` holds. -/
theorem hasGOTDensities_of_tsum_deltaP_InStar_eq (hp : 5 ≤ p)
    (hsym : (∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2))
      = ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 4)) :
    HasGOTDensities p :=
  (hasGOTDensities_iff_tsum_deltaP_InStar_two hp).2 (tsum_deltaP_InStar_two_eq_of_eq_four hp hsym)

end WeierstrassCurve
