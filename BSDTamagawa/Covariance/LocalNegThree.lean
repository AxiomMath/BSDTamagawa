/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.LocalNegTwo

/-!
# Negativity of the local covariance at `(ℓ, ℓ') = (3, ℓ')`, `ℓ' ≥ 5`

For a prime `p` and a prime `ℓ' ≥ 5`, the local covariance `C_p(3, ℓ')` is negative under
`HasTailConstantLaw p` and the head-sum lower bound `1/(3p³) ≤ A_{p,3}`. The cross-moment is at
most `α_p p^{-3ℓ'}/(1 - p^{-3ℓ'})²`, the product of the marginal moments is at least
`α_p p^{-3-ℓ'}/3`, and `3p^{3-2ℓ'}/(1 - p^{-3ℓ'})² < 1`. The constant `α_p` cancels, so only
`α_p > 0` is used.

## Main results

* `WeierstrassCurve.three_mul_cube_mul_pow_four_lt`: `3 P³ Y⁴ < (Y³ - 1)²` for `Y ≥ 32` and
  `Y ≥ 4P³`.
* `WeierstrassCurve.localCov_three_prime_neg_of_inputs`: `C_p(3, ℓ') < 0` for a prime `ℓ' ≥ 5`,
  under the hypotheses above.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-- If `32 ≤ Y` and `4 P³ ≤ Y`, then `3 P³ Y⁴ < (Y³ - 1)²`. -/
theorem three_mul_cube_mul_pow_four_lt {P Y : ℝ} (hY32 : 32 ≤ Y) (hY4 : 4 * P ^ 3 ≤ Y) :
    3 * P ^ 3 * Y ^ 4 < (Y ^ 3 - 1) ^ 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYsq : (1024 : ℝ) ≤ Y ^ 2 := by nlinarith
  have h1 : 3 * P ^ 3 * Y ^ 4 ≤ 3 / 4 * Y * Y ^ 4 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  have hA : (0 : ℝ) < Y ^ 2 * (Y - 3 / 4) - 2 := by nlinarith
  have hB : (0 : ℝ) < Y ^ 3 := by positivity
  nlinarith [mul_pos hB hA]

/-- For real `P ≥ 2` and `n ≥ 5`, `4 P³ ≤ P^n`. -/
theorem four_mul_cube_le_pow {P : ℝ} (hP : 2 ≤ P) {n : ℕ} (hn : 5 ≤ n) :
    4 * P ^ 3 ≤ P ^ n :=
  calc 4 * P ^ 3 ≤ P ^ 2 * P ^ 3 := by gcongr; nlinarith
    _ = P ^ 5 := by ring
    _ ≤ P ^ n := pow_le_pow_right₀ (by linarith) hn

/-- Under `HasTailConstantLaw p` and `1/(3p³) ≤ A_{p,3}`, `C_p(3, ℓ') < 0` for every prime
`ℓ' ≥ 5`. -/
theorem localCov_three_prime_neg_of_inputs (h : HasTailConstantLaw p)
    (hA3 : 1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3) {ℓ' : ℕ} (hℓ' : ℓ'.Prime) (hℓ'5 : 5 ≤ ℓ') :
    localCov p 3 ℓ' < 0 := by
  have hlaw := hasTailGeometricLaw_of_hasTailConstantLaw (p := p) h
  obtain ⟨a, hgeom, hlt, hge, -, -⟩ := h
  have hne : (3 : ℕ) ≠ ℓ' := by omega
  set P : ℝ := (p : ℝ) with hPdef
  set c : ℝ := a.toReal with hcdef
  set Y : ℝ := P ^ ℓ' with hYdef
  have hP : (2 : ℝ) ≤ P := two_le_cast_prime
  have hP0 : (0 : ℝ) < P := by linarith
  have hc0 : 0 < c := toReal_tailConstant_pos hlt hge
  obtain ⟨hY32, -⟩ := thirtytwo_le_pow_and_eight_mul_sq_le (P := P) hP hℓ'5
  have hY4 : 4 * P ^ 3 ≤ Y := four_mul_cube_le_pow hP hℓ'5
  have hY0 : (0 : ℝ) < Y := by rw [hYdef]; positivity
  have hcross : crossValuationMoment p 3 ℓ' ≤ c * (Y ^ 3 / (Y ^ 3 - 1) ^ 2) := by
    rw [hYdef, ← pow_mul' P 3 ℓ']
    exact crossValuationMoment_le_crossBound hgeom Nat.prime_three hℓ' hne
  have hμ3 : 1 / (3 * P ^ 3) ≤ valuationMoment p 3 :=
    inv_three_mul_cube_le_valuationMoment_three hlaw hA3
  have hμℓ : c / Y ≤ valuationMoment p ℓ' := tsum_le_valuationMoment_of_geom hlaw hgeom hℓ' hℓ'5
  have hprod : c / (3 * P ^ 3 * Y) ≤ valuationMoment p 3 * valuationMoment p ℓ' :=
    calc c / (3 * P ^ 3 * Y) = 1 / (3 * P ^ 3) * (c / Y) := by field_simp
      _ ≤ _ := mul_le_mul hμ3 hμℓ (by positivity) (le_trans (by positivity) hμ3)
  have hnum : c * (Y ^ 3 / (Y ^ 3 - 1) ^ 2) < c / (3 * P ^ 3 * Y) := by
    refine mul_div_sq_lt_div
      (two_le_pow_of_two_le (show (2 : ℝ) ≤ Y by linarith) (by norm_num)) (by positivity) ?_
    calc 3 * P ^ 3 * Y * (c * Y ^ 3) = c * (3 * P ^ 3 * Y ^ 4) := by ring
      _ < c * (Y ^ 3 - 1) ^ 2 :=
        mul_lt_mul_of_pos_left (three_mul_cube_mul_pow_four_lt hY32 hY4) hc0
  rw [localCov_neg_iff]
  exact hcross.trans_lt (hnum.trans_le hprod)

/-- Under `HasLocalCovInputs p`, `C_p(3, ℓ') < 0` for every prime `ℓ' ≥ 5`. -/
theorem localCov_three_prime_neg (h : HasLocalCovInputs p) {ℓ' : ℕ} (hℓ' : ℓ'.Prime)
    (hℓ'5 : 5 ≤ ℓ') : localCov p 3 ℓ' < 0 :=
  localCov_three_prime_neg_of_inputs h.1 h.2.2 hℓ' hℓ'5

end WeierstrassCurve
