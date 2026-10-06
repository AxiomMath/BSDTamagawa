/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.SplitMultiplicativeTail
public import BSDTamagawa.LocalDensity.SelfSimilarity
public import BSDTamagawa.LocalDensity.HeadDensityTwoBound

/-!
# The dilation `σ_p` of short models, and `c₄` at `p = 2, 3`

The dilation `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)` of the coefficient plane is the change of variables
`u = p` on short models: it multiplies the discriminant by `p¹²` and preserves the nonsingular
locus. If the reduction datum is
invariant under `σ_p` (`StratScaleInvariant p`), every reduction-datum stratum `F_K` satisfies
`F_K ∩ σ_p(ℤ_p²) = σ_p(F_K)`, so its non-minimal part carries `p⁻¹⁰` of its mass:
`δ_p(K) = p⁻¹⁰ δ_p(K) + μ_p(F_K ∖ σ_p(ℤ_p²))`.

At `p = 2` and `p = 3`, `c₄ = -48a₄` is divisible by `p` for every short model, so no short model
is nodal. We also record that `-4` and `-16` are units of `ℤ_p` at every odd prime.

## Main definitions

* `WeierstrassCurve.StratScaleInvariant`: the reduction datum is invariant under `σ_p`.

## Main results

* `WeierstrassCurve.ofShortNF_scale_Δ`: `Δ(ϖ⁴a₄, ϖ⁶a₆) = ϖ¹² Δ(a₄, a₆)`.
* `WeierstrassCurve.mem_nonsingularLocus_scaleProdByPPow_iff`: `σ_p` preserves the nonsingular
  locus.
* `WeierstrassCurve.deltaP_eq_inv_pow_mul_add`, `WeierstrassCurve.δ_eq_inv_pow_mul_add`: under
  `StratScaleInvariant p`, `δ_p(K) = p⁻¹⁰ δ_p(K) + μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²))`, and the same for
  `δ_p(t)` with `t ≥ 5`.
* `WeierstrassCurve.dvd_ofShortNF_c₄_of_eq_two_or_three`: at `p = 2, 3`, `p ∣ c₄` for every short
  model.

## Implementation notes

The relation `μ_p(F_K ∩ σ_p(ℤ_p²)) = p⁻¹⁰ μ_p(F_K)` holds within a single stratum; it does not
relate the datum `(I_t, t)` to `(I_{t+1}, t+1)`. All decompositions are stated additively, so no
truncated subtraction in `ℝ≥0∞` occurs.
-/

@[expose] public section

universe u

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

/-! ### The dilation `σ_p` on short models

Over an arbitrary commutative ring, the dilation `(a₄, a₆) ↦ (ϖ⁴a₄, ϖ⁶a₆)` multiplies the
discriminant by `ϖ¹²`. -/

/-- For the short model `y² = x³ + a₄x + a₆` over any commutative ring, replacing `(a₄, a₆)` by
`(ϖ⁴a₄, ϖ⁶a₆)` multiplies the discriminant by `ϖ¹²`. -/
theorem ofShortNF_scale_Δ {R : Type u} [CommRing R] (ϖ a₄ a₆ : R) :
    (ofShortNF (ϖ ^ 4 * a₄) (ϖ ^ 6 * a₆)).Δ = ϖ ^ 12 * (ofShortNF a₄ a₆).Δ := by
  rw [ofShortNF_Δ, ofShortNF_Δ]; ring

/-! ### `σ_p` on the coefficient plane

Here `σ_p` is `PadicInt.scaleProdByPPow 4 6`. -/

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-- `PadicInt.scaleProdByPPow m n` in coordinates: `(x, y) ↦ (pᵐ x, pⁿ y)`. -/
theorem _root_.PadicInt.scaleProdByPPow_apply (m n : ℕ) (x : ℤ_[p] × ℤ_[p]) :
    PadicInt.scaleProdByPPow m n x = ((p : ℤ_[p]) ^ m * x.1, (p : ℤ_[p]) ^ n * x.2) := rfl

/-- A pair lies in the range of `PadicInt.scaleProdByPPow m n` iff its first coordinate is
divisible by `pᵐ` and its second by `pⁿ`. -/
theorem _root_.PadicInt.mem_range_scaleProdByPPow_iff {m n : ℕ} {x : ℤ_[p] × ℤ_[p]} :
    x ∈ Set.range (PadicInt.scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) ↔
      (p : ℤ_[p]) ^ m ∣ x.1 ∧ (p : ℤ_[p]) ^ n ∣ x.2 := by
  rw [PadicInt.range_scaleProdByPPow, Set.mem_prod, PadicInt.range_scaleByPPow,
    PadicInt.range_scaleByPPow]
  exact and_congr Ideal.mem_span_singleton Ideal.mem_span_singleton

/-- `Δ(σ_p x) = p¹² Δ(x)` on the coefficient plane. -/
theorem Δ_scaleProdByPPow (x : ℤ_[p] × ℤ_[p]) :
    (ofShortNF (PadicInt.scaleProdByPPow 4 6 x).1 (PadicInt.scaleProdByPPow 4 6 x).2).Δ
      = (p : ℤ_[p]) ^ 12 * (ofShortNF x.1 x.2).Δ :=
  ofShortNF_scale_Δ _ _ _

/-- `σ_p x` is nonsingular iff `x` is: `σ_p x ∈ U_p ↔ x ∈ U_p`. -/
theorem mem_nonsingularLocus_scaleProdByPPow_iff {x : ℤ_[p] × ℤ_[p]} :
    PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p ↔ x ∈ nonsingularLocus p := by
  simp only [nonsingularLocus, Set.mem_ofPred_eq, Δ_scaleProdByPPow, ne_eq, mul_eq_zero,
    pow_eq_zero_iff (n := 12) (by norm_num), PadicInt.uniformizer_ne_zero, false_or]

/-! ### The `(1 - p⁻¹⁰)` decomposition of a stratum, under `τ_p ∘ σ_p = τ_p` -/

variable (p) in
/-- The reduction datum of a short model over `ℤ_p` is unchanged by the dilation
`σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)`: `τ_p ∘ σ_p = τ_p` on the nonsingular locus. (This holds because `σ_p`
is the change of variables `u = p`.) -/
def StratScaleInvariant : Prop :=
  ∀ (x : ℤ_[p] × ℤ_[p]) (hx : x ∈ nonsingularLocus p)
    (hσx : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p),
    strat p ⟨PadicInt.scaleProdByPPow 4 6 x, hσx⟩ = strat p ⟨x, hx⟩

/-- Under `StratScaleInvariant p`, the part of the stratum `τ_p⁻¹(K)` lying in the image of `σ_p`
is the dilate of the stratum: `τ_p⁻¹(K) ∩ σ_p(ℤ_p²) = σ_p(τ_p⁻¹(K))`. -/
theorem stratFibre_inter_range_eq_image (h : StratScaleInvariant p) (K : ReductionData) :
    stratFibre p K ∩ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = PadicInt.scaleProdByPPow 4 6 '' stratFibre p K := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hyK, x, rfl⟩
    have hyUp : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p := stratFibre_subset K hyK
    have hxUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_scaleProdByPPow_iff.1 hyUp
    exact ⟨x, (mem_stratFibre_iff hxUp).2
      (((h x hxUp hyUp).symm.trans ((mem_stratFibre_iff hyUp).1 hyK))), rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset K hx
    have hyUp : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p :=
      mem_nonsingularLocus_scaleProdByPPow_iff.2 hxUp
    exact ⟨(mem_stratFibre_iff hyUp).2
      ((h x hxUp hyUp).trans ((mem_stratFibre_iff hxUp).1 hx)), ⟨x, rfl⟩⟩

/-- Under `StratScaleInvariant p`, `μ_p(τ_p⁻¹(K) ∩ σ_p(ℤ_p²)) = p⁻¹⁰ μ_p(τ_p⁻¹(K))`. -/
theorem measure_stratFibre_inter_range (h : StratScaleInvariant p) (K : ReductionData) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p K ∩
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = (p : ℝ≥0∞) ^ (-(10 : ℤ)) * volume (stratFibre p K) := by
  rw [stratFibre_inter_range_eq_image h K, PadicInt.measure_image_scaleProdByPPow_four_six]

/-- Under `StratScaleInvariant p`, every reduction-datum density satisfies

  `δ_p(K) = p⁻¹⁰ δ_p(K) + μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²))`. -/
theorem deltaP_eq_inv_pow_mul_add (h : StratScaleInvariant p) (K : ReductionData) :
    deltaP p K = (p : ℝ≥0∞) ^ (-(10 : ℤ)) * deltaP p K
      + (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p K \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) := by
  rw [← volume_stratFibre K, ← measure_stratFibre_inter_range h K]
  exact (measure_inter_add_sdiff _
    (PadicInt.measurableEmbedding_scaleProdByPPow 4 6).measurableSet_range).symm

/-- Under `StratScaleInvariant p`, for `t ≥ 5`,

  `δ_p(t) = p⁻¹⁰ δ_p(t) + μ_p(τ_p⁻¹((I_t, t)) ∖ σ_p(ℤ_p²))`. -/
theorem δ_eq_inv_pow_mul_add (h : StratScaleInvariant p) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = (p : ℝ≥0∞) ^ (-(10 : ℤ)) * δ p t
      + (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) := by
  rw [δ_eq_deltaP_I ht]
  exact deltaP_eq_inv_pow_mul_add h _

/-! ### Units of `ℤ_p` at odd primes -/

/-- `-4` is a unit of `ℤ_[p]` at every odd prime. -/
theorem _root_.PadicInt.isUnit_neg_four (hp : Odd p) : IsUnit (-4 : ℤ_[p]) := by
  have h : IsUnit ((2 : ℤ_[p]) * 2) := (PadicInt.isUnit_two hp).mul (PadicInt.isUnit_two hp)
  simpa [show (2 : ℤ_[p]) * 2 = 4 by norm_num] using h.neg

/-- `-16` is a unit of `ℤ_[p]` at every odd prime. -/
theorem _root_.PadicInt.isUnit_neg_sixteen (hp : Odd p) : IsUnit (-16 : ℤ_[p]) := by
  have h4 : IsUnit (4 : ℤ_[p]) := by simpa using (PadicInt.isUnit_neg_four hp).neg
  simpa [show (4 : ℤ_[p]) * 4 = 16 by norm_num] using (h4.mul h4).neg

/-! ### No short model is nodal at `p = 2, 3` -/

/-- If the prime `p` divides `48`, then `p ∣ c₄` for every short model, since `c₄ = -48a₄`. -/
theorem dvd_ofShortNF_c₄_of_dvd_fortyEight (h : (p : ℤ_[p]) ∣ (48 : ℤ_[p])) (a₄ a₆ : ℤ_[p]) :
    (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ := by
  rw [ofShortNF_c₄]
  exact (dvd_neg.2 h).mul_right a₄

/-- At `p = 2` and `p = 3`, `p ∣ c₄` for every short model over `ℤ_p`. -/
theorem dvd_ofShortNF_c₄_of_eq_two_or_three (hp : p = 2 ∨ p = 3) (a₄ a₆ : ℤ_[p]) :
    (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
  dvd_ofShortNF_c₄_of_dvd_fortyEight
    (by rcases hp with rfl | rfl
        exacts [⟨24, by push_cast; ring⟩, ⟨16, by push_cast; ring⟩]) a₄ a₆

end WeierstrassCurve
