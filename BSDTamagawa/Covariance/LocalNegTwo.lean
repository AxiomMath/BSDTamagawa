/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.LocalNegTwoThree

/-!
# Negativity of the local covariance at `(ℓ, ℓ') = (2, ℓ')`, `ℓ' ≥ 5`

For a prime `p` and a prime `ℓ' ≥ 5`, the local covariance `C_p(2, ℓ')` is negative under
`HasTailConstantLaw p` and the head-sum lower bound `1/(2p²) ≤ A_{p,2}`. The cross-moment is at
most `α_p p^{-2ℓ'}/(1 - p^{-2ℓ'})²`, the product of the marginal moments is at least
`α_p p^{-2-ℓ'}/2`, and `2p^{2-ℓ'}/(1 - p^{-2ℓ'})² < 1`. The constant `α_p` cancels, so only
`α_p > 0` is used.

## Main results

* `WeierstrassCurve.two_mul_sq_mul_cube_lt`: `2 P² Y³ < (Y² - 1)²` for `Y ≥ 32` and `Y ≥ 8P²`.
* `WeierstrassCurve.localCov_two_prime_neg_of_inputs`: `C_p(2, ℓ') < 0` for a prime `ℓ' ≥ 5`, under
  the hypotheses above.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-- If `32 ≤ Y` and `8 P² ≤ Y`, then `2 P² Y³ < (Y² - 1)²`. -/
theorem two_mul_sq_mul_cube_lt {P Y : ℝ} (hY32 : 32 ≤ Y) (hY8 : 8 * P ^ 2 ≤ Y) :
    2 * P ^ 2 * Y ^ 3 < (Y ^ 2 - 1) ^ 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYsq : (1024 : ℝ) ≤ Y ^ 2 := by nlinarith
  have hfour : (1024 : ℝ) * Y ^ 2 ≤ Y ^ 4 := by nlinarith [sq_nonneg Y]
  have h1 : 2 * P ^ 2 * Y ^ 3 ≤ Y / 4 * Y ^ 3 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  have h2 : Y / 4 * Y ^ 3 < (Y ^ 2 - 1) ^ 2 := by nlinarith
  linarith

/-- For real `P ≥ 2` and `n ≥ 5`, `P ^ n` is at least `32` and at least `8 * P ^ 2`. -/
theorem thirtytwo_le_pow_and_eight_mul_sq_le {P : ℝ} (hP : 2 ≤ P) {n : ℕ} (hn : 5 ≤ n) :
    32 ≤ P ^ n ∧ 8 * P ^ 2 ≤ P ^ n := by
  have hmono : P ^ 5 ≤ P ^ n := pow_le_pow_right₀ (by linarith) hn
  refine ⟨le_trans ?_ hmono, le_trans ?_ hmono⟩
  · calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ P ^ 5 := two_pow_le_pow_of_two_le hP 5
  · calc 8 * P ^ 2 = 2 ^ 3 * P ^ 2 := by norm_num
      _ ≤ P ^ 3 * P ^ 2 := by gcongr
      _ = P ^ 5 := by ring

/-- Under `HasTailConstantLaw p` and `1/(2p²) ≤ A_{p,2}`, `C_p(2, ℓ') < 0` for every prime
`ℓ' ≥ 5`. -/
theorem localCov_two_prime_neg_of_inputs (h : HasTailConstantLaw p)
    (hA2 : 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2) {ℓ' : ℕ} (hℓ' : ℓ'.Prime) (hℓ'5 : 5 ≤ ℓ') :
    localCov p 2 ℓ' < 0 := by
  have hlaw := hasTailGeometricLaw_of_hasTailConstantLaw h
  obtain ⟨a, hgeom, hlt, hge, -, -⟩ := h
  have hne : (2 : ℕ) ≠ ℓ' := by omega
  set P : ℝ := (p : ℝ)
  set c : ℝ := a.toReal
  set Y : ℝ := P ^ ℓ' with hYdef
  have hP : (2 : ℝ) ≤ P := two_le_cast_prime
  have hc0 : 0 < c := toReal_tailConstant_pos hlt hge
  obtain ⟨hY32, hY8⟩ := thirtytwo_le_pow_and_eight_mul_sq_le (P := P) hP hℓ'5
  have hY0 : (0 : ℝ) < Y := by rw [hYdef]; positivity
  have hcross : crossValuationMoment p 2 ℓ' ≤ c * (Y ^ 2 / (Y ^ 2 - 1) ^ 2) := by
    rw [hYdef, ← pow_mul' P 2 ℓ']
    exact crossValuationMoment_le_crossBound hgeom Nat.prime_two hℓ' hne
  have hμ2 : 1 / (2 * P ^ 2) ≤ valuationMoment p 2 := inv_two_mul_sq_le_valuationMoment_two hlaw hA2
  have hμℓ : c / Y ≤ valuationMoment p ℓ' := tsum_le_valuationMoment_of_geom hlaw hgeom hℓ' hℓ'5
  have hprod : c / (2 * P ^ 2 * Y) ≤ valuationMoment p 2 * valuationMoment p ℓ' := by
    calc c / (2 * P ^ 2 * Y) = 1 / (2 * P ^ 2) * (c / Y) := by field_simp
      _ ≤ valuationMoment p 2 * valuationMoment p ℓ' :=
        mul_le_mul hμ2 hμℓ (by positivity) (le_trans (by positivity) hμ2)
  have hnum : c * (Y ^ 2 / (Y ^ 2 - 1) ^ 2) < c / (2 * P ^ 2 * Y) := by
    refine mul_div_sq_lt_div (by nlinarith) (by positivity) ?_
    calc 2 * P ^ 2 * Y * (c * Y ^ 2) = c * (2 * P ^ 2 * Y ^ 3) := by ring
      _ < c * (Y ^ 2 - 1) ^ 2 := mul_lt_mul_of_pos_left (two_mul_sq_mul_cube_lt hY32 hY8) hc0
  rw [localCov_neg_iff]
  exact (hcross.trans_lt hnum).trans_le hprod

/-- Under `HasLocalCovInputs p`, `C_p(2, ℓ') < 0` for every prime `ℓ' ≥ 5`. -/
theorem localCov_two_prime_neg (h : HasLocalCovInputs p) {ℓ' : ℕ} (hℓ' : ℓ'.Prime)
    (hℓ'5 : 5 ≤ ℓ') : localCov p 2 ℓ' < 0 :=
  localCov_two_prime_neg_of_inputs h.1 h.2.1 hℓ' hℓ'5

end WeierstrassCurve
