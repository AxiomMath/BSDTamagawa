/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.RatioLawAtThree
public import BSDTamagawa.NumberTheory.SmallPrimeHeadBound
public import BSDTamagawa.Covariance.LocalNegLarge

/-!
# `HasLocalCovInputs 3`

This file shows that the hypothesis bundles `HasTailConstantLaw` and `HasLocalCovInputs` hold at
the prime `p = 3`:

* the tail identity `δ₃(t) = a · 3^{-t}` holds for `t ≥ 5` with `a = 1/88572`;
* the constant satisfies `a < 1/2` and `1/88572 ≤ a ≤ 1/88572`, the last two with equality;
* the two head-sum lower bounds hold.

Consequently `localCov 3 ℓ ℓ' < 0` for every pair of distinct primes `ℓ ≠ ℓ'`.

## Main results

* `hasTailConstantLaw_three`: `HasTailConstantLaw 3`, with constant `a = 1/88572`.
* `hasLocalCovInputs_three`: `HasLocalCovInputs 3`.
* `localCov_neg_three`: `localCov 3 ℓ ℓ' < 0` for distinct primes `ℓ` and `ℓ'`.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- `ENNReal.ofReal (1 / (3 * 29524))` equals the `ℝ≥0∞` literal `1 / 88572`. -/
theorem ofReal_inv_three_mul_eq : ENNReal.ofReal (1 / (3 * 29524)) = 1 / 88572 := by
  rw [show (3 : ℝ) * 29524 = 88572 by norm_num, one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat, one_div]

/-- `HasTailConstantLaw 3` holds with constant `a = 1/88572`, and both bounds on `a` hold with
equality. -/
theorem hasTailConstantLaw_three (hp3 : p = 3) : HasTailConstantLaw p := by
  refine ⟨1 / 88572, ?_, ?_, le_rfl, ?_, ?_⟩
  · intro t ht
    rw [δ_eq_ofReal_three_of_eq_three hp3 ht, ofReal_inv_three_mul_eq]
  · rw [one_div, one_div, ENNReal.inv_lt_inv]; norm_num
  · intro h2; exact absurd (hp3 ▸ h2) (by norm_num)
  · intro _; exact le_rfl

/-- `HasLocalCovInputs 3`: the tail-constant law at `3` together with the two head-sum lower
bounds. -/
theorem hasLocalCovInputs_three (hp3 : p = 3) : HasLocalCovInputs p :=
  ⟨hasTailConstantLaw_three hp3, headSum_lower_bounds_of_prime.1,
    headSum_lower_bounds_of_prime.2⟩

/-- `C₃(ℓ, ℓ') < 0` for every pair of distinct primes `ℓ` and `ℓ'`. -/
theorem localCov_neg_three (hp3 : p = 3) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') : localCov p ℓ ℓ' < 0 :=
  localCov_neg_of_inputs (hasLocalCovInputs_three hp3) hℓ hℓ' hne

end WeierstrassCurve
