/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.LocalNegThree

/-!
# Negativity of the local covariance for `ℓ, ℓ' ≥ 5`

For a prime `p` and distinct primes `ℓ, ℓ' ≥ 5`, the local covariance `C_p(ℓ, ℓ')` is negative,
under the hypothesis `HasTailConstantLaw p` that `δ_p(t) = α_p p^{-t}` for `t ≥ 5` with
`1/88572 ≤ α_p < 1/2`. The cross-moment is at most `α_p p^{-ℓℓ'}/(1 - p^{-ℓℓ'})²`, one power of
`α_p`, while each marginal moment satisfies `μ_{p,r} ≥ α_p p^{-r}`, so the product of marginals is
at least `α_p² p^{-ℓ-ℓ'}`. The comparison thus reduces to the lower bound
`p^{-(ℓℓ' - ℓ - ℓ')}/(1 - p^{-ℓℓ'})² ≤ α_p`, which follows from `α_p ≥ 1/88572` and
`ℓℓ' - ℓ - ℓ' ≥ 23`. Combining with the cases where `2` or `3` is among `ℓ, ℓ'` gives
`C_p(ℓ, ℓ') < 0` for every pair of distinct primes.

## Main results

* `WeierstrassCurve.add_add_twentythree_le_mul`: `ℓ + ℓ' + 23 ≤ ℓℓ'` for distinct primes
  `ℓ, ℓ' ≥ 5`.
* `WeierstrassCurve.localCov_five_le_neg_of_inputs`: `C_p(ℓ, ℓ') < 0` for distinct primes
  `ℓ, ℓ' ≥ 5`, under `HasTailConstantLaw p`.
* `WeierstrassCurve.localCov_neg_of_inputs`: `C_p(ℓ, ℓ') < 0` for every pair of distinct primes,
  under `HasLocalCovInputs p`.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-- `x + y + 23 ≤ x y` for `5 ≤ x` and `7 ≤ y`, i.e. `(x-1)(y-1) ≥ 24`. -/
theorem add_add_twentythree_le_mul_aux {x y : ℕ} (hx : 5 ≤ x) (hy : 7 ≤ y) :
    x + y + 23 ≤ x * y := by
  obtain ⟨i, rfl⟩ : ∃ i, x = 5 + i := ⟨x - 5, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, y = 7 + j := ⟨y - 7, by omega⟩
  have hij : 0 ≤ i * j := Nat.zero_le _
  have hexp : (5 + i) * (7 + j) = 35 + 7 * i + 5 * j + i * j := by ring
  rw [hexp]
  linarith

/-- For distinct primes `ℓ, ℓ' ≥ 5`, `ℓ + ℓ' + 23 ≤ ℓℓ'`, i.e. `ℓℓ' - ℓ - ℓ' ≥ 23`, with equality
at `(5, 7)`. -/
theorem add_add_twentythree_le_mul {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ)
    (h5' : 5 ≤ ℓ') (hne : ℓ ≠ ℓ') : ℓ + ℓ' + 23 ≤ ℓ * ℓ' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h7 : 7 ≤ ℓ' := by
      rcases eq_or_ne ℓ' 6 with rfl | h6
      · exact absurd hℓ' (by decide)
      · omega
    exact add_add_twentythree_le_mul_aux h5 h7
  · have h7 : 7 ≤ ℓ := by
      rcases eq_or_ne ℓ 6 with rfl | h6
      · exact absurd hℓ (by decide)
      · omega
    have h := add_add_twentythree_le_mul_aux h5' h7
    rw [mul_comm]
    linarith

/-- If `1 ≤ W`, `2^{23} W ≤ Z` and `1/88572 ≤ c`, then `W · (c Z) < c² (Z-1)²`. -/
theorem mul_lt_sq_mul_sub_one_sq {Z W c : ℝ} (hW : 1 ≤ W) (hZW : 8388608 * W ≤ Z)
    (hc : 1 / 88572 ≤ c) : W * (c * Z) < c ^ 2 * (Z - 1) ^ 2 := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hstep : W < c * (Z - 2) := by
    linarith [mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ Z - 2 by linarith)]
  have h3 : W * (c * Z) < c * (Z - 2) * (c * Z) :=
    mul_lt_mul_of_pos_right hstep (mul_pos hc0 hZ0)
  have h4 : c * (Z - 2) * (c * Z) ≤ c ^ 2 * (Z - 1) ^ 2 := by nlinarith [sq_nonneg c]
  linarith

/-- Under `HasTailConstantLaw p`, `C_p(ℓ, ℓ') < 0` for distinct primes `ℓ, ℓ' ≥ 5`. -/
theorem localCov_five_le_neg_of_inputs (h : HasTailConstantLaw p) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ') (hne : ℓ ≠ ℓ') : localCov p ℓ ℓ' < 0 := by
  have hlaw := hasTailGeometricLaw_of_hasTailConstantLaw (p := p) h
  obtain ⟨a, hgeom, hlt, hge, -, -⟩ := h
  set P : ℝ := (p : ℝ) with hPdef
  set c : ℝ := a.toReal with hcdef
  have hP : (2 : ℝ) ≤ P := two_le_cast_prime
  have hP0 : (0 : ℝ) < P := by linarith
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hc0 : 0 < c := toReal_tailConstant_pos hlt hge
  have hc : 1 / 88572 ≤ c := inv_le_toReal_tailConstant hlt hge
  set Z : ℝ := P ^ (ℓ * ℓ') with hZdef
  set W : ℝ := P ^ (ℓ + ℓ') with hWdef
  have hexp : ℓ + ℓ' + 23 ≤ ℓ * ℓ' := add_add_twentythree_le_mul hℓ hℓ' h5 h5' hne
  obtain ⟨k, hk⟩ : ∃ k, ℓ * ℓ' = ℓ + ℓ' + k := ⟨ℓ * ℓ' - (ℓ + ℓ'), by omega⟩
  have hk23 : 23 ≤ k := by omega
  have hW1 : (1 : ℝ) ≤ W := one_le_pow₀ hP1
  have hpk : (8388608 : ℝ) ≤ P ^ k := by
    calc (8388608 : ℝ) = 2 ^ 23 := by norm_num
      _ ≤ P ^ 23 := two_pow_le_pow_of_two_le hP 23
      _ ≤ P ^ k := pow_le_pow_right₀ hP1 hk23
  have hZeq : Z = W * P ^ k := by rw [hZdef, hWdef, hk, pow_add]
  have hZW : 8388608 * W ≤ Z := by
    rw [hZeq, mul_comm]
    exact mul_le_mul_of_nonneg_left hpk (by linarith)
  have hZ2 : (2 : ℝ) ≤ Z := by linarith
  have hμ : c / P ^ ℓ ≤ valuationMoment p ℓ := tsum_le_valuationMoment_of_geom hlaw hgeom hℓ h5
  have hμ' : c / P ^ ℓ' ≤ valuationMoment p ℓ' := tsum_le_valuationMoment_of_geom hlaw hgeom hℓ' h5'
  rw [localCov_neg_iff]
  calc crossValuationMoment p ℓ ℓ' ≤ c * (Z / (Z - 1) ^ 2) :=
        crossValuationMoment_le_crossBound hgeom hℓ hℓ' hne
    _ < c ^ 2 / W := mul_div_sq_lt_div hZ2 (by linarith) (mul_lt_sq_mul_sub_one_sq hW1 hZW hc)
    _ = c / P ^ ℓ * (c / P ^ ℓ') := by
      rw [hWdef, pow_add]
      field_simp
    _ ≤ valuationMoment p ℓ * valuationMoment p ℓ' :=
      mul_le_mul hμ hμ' (by positivity) (le_trans (by positivity) hμ)

/-- Under `HasLocalCovInputs p`, `C_p(ℓ, ℓ') < 0` for distinct primes `ℓ, ℓ' ≥ 5`. -/
theorem localCov_five_le_neg (h : HasLocalCovInputs p) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ') (hne : ℓ ≠ ℓ') : localCov p ℓ ℓ' < 0 :=
  localCov_five_le_neg_of_inputs h.1 hℓ hℓ' h5 h5' hne

/-! ### All pairs of distinct primes -/

/-- Under `HasLocalCovInputs p`, `C_p(ℓ, ℓ') < 0` for every pair of distinct primes `ℓ ≠ ℓ'`. -/
theorem localCov_neg_of_inputs (h : HasLocalCovInputs p) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') : localCov p ℓ ℓ' < 0 := by
  rcases lt_or_gt_of_ne hne with hord | hord
  · rcases prime_eq_two_or_eq_three_or_five_le hℓ with rfl | rfl | h5
    · rcases prime_eq_two_or_eq_three_or_five_le hℓ' with rfl | rfl | h5'
      · exact absurd rfl hne
      · exact localCov_two_three_neg h
      · exact localCov_two_prime_neg h hℓ' h5'
    · rcases prime_eq_two_or_eq_three_or_five_le hℓ' with rfl | rfl | h5'
      · omega
      · exact absurd rfl hne
      · exact localCov_three_prime_neg h hℓ' h5'
    · exact localCov_five_le_neg h hℓ hℓ' h5 (by omega) hne
  · rw [localCov_comm]
    rcases prime_eq_two_or_eq_three_or_five_le hℓ' with rfl | rfl | h5'
    · rcases prime_eq_two_or_eq_three_or_five_le hℓ with rfl | rfl | h5
      · exact absurd rfl hne
      · exact localCov_two_three_neg h
      · exact localCov_two_prime_neg h hℓ h5
    · rcases prime_eq_two_or_eq_three_or_five_le hℓ with rfl | rfl | h5
      · omega
      · exact absurd rfl hne
      · exact localCov_three_prime_neg h hℓ h5
    · exact localCov_five_le_neg h hℓ' hℓ h5' (by omega) (Ne.symm hne)

end WeierstrassCurve
