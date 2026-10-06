/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.LocalCovInputsAtThree
public import BSDTamagawa.NumberTheory.RatioLawAtTwo

/-!
# `HasLocalCovInputs` at `p = 2`, and `Cov(v_ℓ, v_{ℓ'}) < 0`

This file shows that the hypothesis bundles `HasTailConstantLaw` and `HasLocalCovInputs` hold at
`p = 2`, with tail constant `a = α₂ = 1/2046`. Consequently the local covariance `C_2(ℓ, ℓ')` is
negative for every pair of distinct primes `ℓ ≠ ℓ'`. Together with `C_3(ℓ, ℓ') ≤ 0`, this makes the
covariance of the `ℓ`- and `ℓ'`-adic valuations of the Tamagawa product under the joint limiting
valuation law negative:

  `Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0`  for every pair of distinct primes `ℓ ≠ ℓ'`.

This is stated both on the index space `ℤ_{≥0}^{{ℓ,ℓ'}}` and on `ℤ_{≥0}²`.

## Main results

* `hasTailConstantLaw_two`: `HasTailConstantLaw 2`, with constant `a = 1/2046`.
* `hasLocalCovInputs_two`: `HasLocalCovInputs 2`.
* `localCov_neg_two`: `C_2(ℓ, ℓ') < 0` for distinct primes `ℓ` and `ℓ'`.
* `covariance_tamagawaValuation_neg`: `Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0` on `ℤ_{≥0}^{{ℓ,ℓ'}}`.
* `covariance_tamagawaValuation_prod_neg`: the same on `ℤ_{≥0}²`.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa BSDTamagawa.CovarianceFormula

variable {p : ℕ} [Fact p.Prime]

/-! ### The bundle at `p = 2` -/

/-- `HasTailConstantLaw 2` holds with constant `a = α₂ = 1/2046`; the upper bound `a ≤ 1/2046`
holds with equality. -/
theorem hasTailConstantLaw_two (hp2 : p = 2) : HasTailConstantLaw p := by
  refine ⟨1 / 2046, fun t ht => δ_eq_inv_2046_mul_of_eq_two hp2 ht, ?_, ?_, fun _ => le_rfl, ?_⟩
  · rw [one_div, one_div, ENNReal.inv_lt_inv]; norm_num
  · rw [one_div, one_div, ENNReal.inv_le_inv]; norm_num
  · intro h3; exact absurd (hp2.symm.trans h3) (by norm_num)

/-- `HasLocalCovInputs 2`: the tail-constant law at `2` together with the two head-sum lower
bounds. -/
theorem hasLocalCovInputs_two (hp2 : p = 2) : HasLocalCovInputs p :=
  ⟨hasTailConstantLaw_two hp2, headSum_lower_bounds_of_prime.1,
    headSum_lower_bounds_of_prime.2⟩

/-- `C_2(ℓ, ℓ') < 0` for every pair of distinct primes `ℓ` and `ℓ'`. -/
theorem localCov_neg_two (hp2 : p = 2) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') : localCov p ℓ ℓ' < 0 :=
  localCov_neg_of_inputs (hasLocalCovInputs_two hp2) hℓ hℓ' hne

/-! ### The covariance is negative -/

section CovarianceNeg

variable {ℓ ℓ' : ℕ}

/-- `C_2(ℓ, ℓ') ≤ 0` for every pair of distinct primes `ℓ` and `ℓ'`. -/
theorem localCov_nonpos_two (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    localCov 2 ℓ ℓ' ≤ 0 :=
  (localCov_neg_two (p := 2) rfl hℓ hℓ' hne).le

/-- `C_3(ℓ, ℓ') ≤ 0` for every pair of distinct primes `ℓ` and `ℓ'`. -/
theorem localCov_nonpos_three (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    localCov 3 ℓ ℓ' ≤ 0 :=
  (localCov_neg_three (p := 3) rfl hℓ hℓ' hne).le

/-- For every pair of distinct primes `ℓ ≠ ℓ'`,

  `Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0`.

The measure is the joint valuation law `P_{{ℓ,ℓ'}}` on `ℤ_{≥0}^{{ℓ,ℓ'}}` and the two random
variables are its `ℓ`- and `ℓ'`-coordinates, `valPairFst` and `valPairSnd`. -/
@[bsd_tamagawa "T057b"]
theorem covariance_tamagawaValuation_neg (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
        (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
        (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)) < 0 :=
  covariance_tamagawaValuation_neg_of_small_primes_nonpos (localCov_nonpos_two hℓ hℓ' hne)
    (localCov_nonpos_three hℓ hℓ' hne) hℓ hℓ' hne

/-- For every pair of distinct primes `ℓ ≠ ℓ'`, `Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0` on the index space
`ℤ_{≥0}²`: the two random variables are the coordinate projections and the measure is
`tamagawaValuationProdMeasure`, the joint valuation law with the `ℓ`-coordinate first. -/
@[bsd_tamagawa "T057b"]
theorem covariance_tamagawaValuation_prod_neg (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
        (tamagawaValuationProdMeasure ℓ ℓ' hne) < 0 :=
  covariance_tamagawaValuation_prod_neg_of_small_primes_nonpos (localCov_nonpos_two hℓ hℓ' hne)
    (localCov_nonpos_three hℓ hℓ' hne) hℓ hℓ' hne

end CovarianceNeg

end WeierstrassCurve
