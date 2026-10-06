/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.RunInvarianceAtTwo
public import BSDTamagawa.NumberTheory.SplitStoreyDescentTwo

/-!
# The tail law at `p = 2`

At the prime `p = 2` the local Tamagawa densities satisfy `δ₂(t) = (1/2046) · 2^{-t}`, that is
`δ₂(t) = 1/(2^{t+1} · 1023)`, for every `t ≥ 5`.

Scale invariance of the strata turns `δ₂(t)` into the solution of the fixed-point equation
`δ₂(t) = 2⁻¹⁰ δ₂(t) + μ₂(τ₂⁻¹((I_t, t)) ∖ σ₂(ℤ₂²))`, where `σ₂(a₄, a₆) = (2⁴a₄, 2⁶a₆)`, so
`δ₂(t) = (1 - 2⁻¹⁰)⁻¹ · μ₂(minimal storey)`. The minimal storey `τ₂⁻¹((I_t, t)) ∖ σ₂(ℤ₂²)` is
weighed exactly by Fubini: for `a₄` a unit its `a₆`-slice is the split locus `splitLevelSet`, and
for a non-unit `a₄` it is empty. Its mass is `2^{-(t+11)}`.

## Main results

* `setOf_mem_stratFibre_eq_splitLevelSet_of_eq_two`: for a unit `a₄` and `t ≥ 5`, the `a₆`-slice
  of the stratum `τ₂⁻¹((I_t, t))` is the split locus.
* `volume_stratFibre_diff_range_eq_two'`: `μ₂(τ₂⁻¹((I_t, t)) ∖ σ₂(ℤ₂²)) = 2^{-(t+11)}` for
  `t ≥ 5`.
* `δ_eq_ofReal_two_of_eq_two`, `δ_eq_inv_2046_mul_of_eq_two`: `δ₂(t) = (1/2046) · 2^{-t}` for
  `t ≥ 5`.
-/

open MeasureTheory

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### The mass of the minimal storey -/

/-- For `p = 2`, `a₄` a unit and `t ≥ 5`, the `a₆`-slice of the stratum `τ₂⁻¹((I_t, t))` is the
split locus `splitLevelSet 2 t a₄`. -/
theorem setOf_mem_stratFibre_eq_splitLevelSet_of_eq_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t)
    {a₄ : ℤ_[p]} (ha₄ : IsUnit a₄) :
    {a₆ : ℤ_[p] | (a₄, a₆) ∈ stratFibre p (KodairaSymbol.I t, t)} = splitLevelSet p t a₄ :=
  Set.Subset.antisymm (setOf_mem_stratFibre_subset_splitLevelSet_two hp2 ht ha₄)
    (fun _a₆ h => splitLevelSet_subset_preimage_stratFibre_two hp2
      (hasSplitStoreyDescent_of_eq_two hp2) ht ha₄ h)

/-- For `p = 2`, `t ≥ 5` and every `a₄`, the `a₆`-slice of `τ₂⁻¹((I_t, t)) ∖ σ₂(ℤ₂²)` has mass
`2⁻¹ · (1 - 2⁻¹) · 2^{-(t+5)}` if `a₄ ∈ minimalFstTwo 2` and `0` otherwise. -/
theorem volume_slice_stratFibre_diff_range_eq_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t)
    (a₄ : ℤ_[p]) :
    (volume : Measure ℤ_[p]) (Prod.mk a₄ ⁻¹' (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])))
      = (minimalFstTwo p).indicator
          (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 5))) a₄ := by
  by_cases ha₄ : IsUnit a₄
  · have hdrop : Prod.mk a₄ ⁻¹' (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = {a₆ : ℤ_[p] | (a₄, a₆) ∈ stratFibre p (KodairaSymbol.I t, t)} := by
      ext a₆
      exact ⟨fun h => h.1, fun h => ⟨h, notMem_range_of_isUnit_fst_two ha₄⟩⟩
    rw [hdrop, setOf_mem_stratFibre_eq_splitLevelSet_of_eq_two hp2 ht ha₄,
      volume_splitLevelSet_two hp2 ht ha₄]
  · have hempty : Prod.mk a₄ ⁻¹' (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = (∅ : Set ℤ_[p]) :=
      Set.eq_empty_iff_forall_notMem.2 fun _ hx =>
        ha₄ (isUnit_fst_of_mem_diff_two hp2 ht hx.1 hx.2)
    rw [hempty, measure_empty,
      Set.indicator_of_notMem (fun hc => ha₄ (isUnit_of_mem_minimalFstTwo hp2 hc))]

private theorem measurableSet_stratFibre_diff_split (t : ℕ) :
    MeasurableSet (stratFibre p (KodairaSymbol.I t, t) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :=
  (isOpen_stratFibre _).measurableSet.diff
    (PadicInt.measurableEmbedding_scaleProdByPPow 4 6).measurableSet_range

/-- For `p = 2` and every `t ≥ 5`,

  `μ₂(τ₂⁻¹((I_t, t)) ∖ σ₂(ℤ₂²)) = (1 - 2⁻¹) · 2^{-(t+10)}`.

The four powers of `2` are `2⁻⁴` for the class of `a₄`, `2⁻¹` for the rescaling `a₆ = 2b`,
`(1 - 2⁻¹)` for the surviving shell and `2^{-(t+5)}` for its level. -/
theorem volume_stratFibre_diff_range_eq_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 10) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_stratFibre_diff_split t),
    lintegral_congr (volume_slice_stratFibre_diff_range_eq_two hp2 ht),
    lintegral_indicator_const measurableSet_minimalFstTwo, volume_minimalFstTwo,
    ENNReal.inv_pow, show t + 10 = 4 + (1 + (t + 5)) by omega, pow_add, pow_add]
  ring

/-- For `p = 2` and every `t ≥ 5`, `μ₂(τ₂⁻¹((I_t, t)) ∖ σ₂(ℤ₂²)) = 2^{-(t+11)}`. -/
theorem volume_stratFibre_diff_range_eq_two' (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = ((p : ℝ≥0∞)⁻¹) ^ (t + 11) := by
  rw [volume_stratFibre_diff_range_eq_two hp2 ht, one_sub_inv_eq_inv_of_eq_two hp2,
    show t + 11 = 1 + (t + 10) by omega]
  ring

/-! ### The tail law at `p = 2` -/

/-- For `r < 1` in `ℝ≥0∞`, the unique finite solution of `x = rx + c` is `x = c(1 - r)⁻¹`. -/
private theorem eq_mul_inv_one_sub_split {r c x : ℝ≥0∞} (hr : r < 1) (hx : x ≠ ⊤)
    (hxe : x = r * x + c) : x = c * (1 - r)⁻¹ := by
  have hsub : x - r * x = c :=
    ENNReal.sub_eq_of_eq_add (ENNReal.mul_ne_top (ne_top_of_lt hr) hx) (by rwa [add_comm])
  have hmul : (1 - r) * x = c := by rw [ENNReal.sub_mul (fun _ _ => hx), one_mul, hsub]
  rw [← hmul, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel (tsub_pos_of_lt hr).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self), one_mul]

/-- `(p⁻¹)¹⁰ < 1`. -/
private theorem inv_pow_ten_lt_one_split : ((p : ℝ≥0∞)⁻¹) ^ 10 < 1 :=
  pow_lt_one₀ zero_le
    (ENNReal.inv_lt_one.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt)) (by norm_num)

/-- Under `StratScaleInvariant p`, for `t ≥ 5`, `δ_p(t)` is the mass of the minimal storey times
`(1 - p⁻¹⁰)⁻¹`. -/
private theorem δ_eq_mul_inv_storey_split (h : StratScaleInvariant p) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have hne : δ p t ≠ ⊤ := by rw [δ_eq_deltaP_I ht]; exact deltaP_ne_top p _
  refine eq_mul_inv_one_sub_split inv_pow_ten_lt_one_split hne ?_
  have h1 := δ_eq_inv_pow_mul_add h ht
  rwa [show (-(10 : ℤ)) = -((10 : ℕ) : ℤ) from by norm_num,
    PadicInt.zpow_neg_natCast_eq_inv_pow_two] at h1

/-- `1 - (2⁻¹)¹⁰` is `ENNReal.ofReal` of the positive real `1 - (2⁻¹)¹⁰`. -/
private theorem ofReal_one_sub_inv_pow_ten_split (hp2 : p = 2) :
    (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10 = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by subst hp2; norm_num
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinvE,
    ← ENNReal.ofReal_pow (by positivity)]

/-- `2^{-(t+11)} (1 - 2^{-10})⁻¹ = (1/(2 · 1023)) 2^{-t}`. -/
private theorem storey_mul_inv_eq_ofReal_split (hp2 : p = 2) (t : ℕ) :
    ((p : ℝ≥0∞)⁻¹) ^ (t + 11) * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      = ENNReal.ofReal (1 / (2 * 1023)) * ((p : ℝ≥0∞)⁻¹) ^ t := by
  rw [ofReal_one_sub_inv_pow_ten_split hp2]
  have hp0 : (0 : ℝ) < (p : ℝ) := by subst hp2; norm_num
  have hlt : ((p : ℝ)⁻¹) ^ 10 < 1 := by
    subst hp2
    rw [show ((2 : ℕ) : ℝ)⁻¹ = (2 : ℝ)⁻¹ from by norm_num]
    exact pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 := by linarith
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_inv_of_pos hpos, hinvE, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine congrArg ENNReal.ofReal ?_
  subst hp2
  rw [show ((2 : ℕ) : ℝ)⁻¹ = (2 : ℝ)⁻¹ from by norm_num, pow_add]
  field_simp
  ring

/-- For every `t ≥ 5`,

  `δ₂(t) = (1/(2 · 1023)) · 2^{-t}`,

that is `δ₂(t) = 1/(2^{t+1} · 1023)`; at `t = 5` it is `1/65472`. -/
theorem δ_eq_ofReal_two_of_eq_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = ENNReal.ofReal (1 / (2 * 1023)) * ((p : ℝ≥0∞)⁻¹) ^ t := by
  rw [δ_eq_mul_inv_storey_split (stratScaleInvariant_of_eq_two hp2) ht,
    volume_stratFibre_diff_range_eq_two' hp2 ht, storey_mul_inv_eq_ofReal_split hp2]

/-- `ENNReal.ofReal (1 / (2 * 1023))` equals the `ℝ≥0∞` literal `1 / 2046`. -/
theorem ofReal_inv_two_mul_eq : ENNReal.ofReal (1 / (2 * 1023)) = 1 / 2046 := by
  rw [show (2 : ℝ) * 1023 = 2046 by norm_num, one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat, one_div]

/-- For every `t ≥ 5`, `δ₂(t) = (1/2046) · 2^{-t}`. -/
theorem δ_eq_inv_2046_mul_of_eq_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = 1 / 2046 * ((p : ℝ≥0∞)⁻¹) ^ t := by
  rw [δ_eq_ofReal_two_of_eq_two hp2 ht, ofReal_inv_two_mul_eq]

end WeierstrassCurve
