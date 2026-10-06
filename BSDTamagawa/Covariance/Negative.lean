/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.Decay

/-!
# Negativity of the valuation covariance from the small primes

For distinct primes `ℓ ≠ ℓ'`, the covariance of `v_ℓ(Tam(E))` and `v_{ℓ'}(Tam(E))` under the
limiting joint valuation law equals the absolutely convergent series `∑_{q prime} C_q(ℓ, ℓ')`. At
every prime `q ≥ 5` the local covariance is strictly negative, so the covariance is negative as
soon as `C_2(ℓ, ℓ') ≤ 0` and `C_3(ℓ, ℓ') ≤ 0`.

## Main results

* `WeierstrassCurve.localCov_neg_of_five_le`: `C_q(ℓ, ℓ') < 0` for every prime `q ≥ 5`.
* `WeierstrassCurve.tsum_localCov_neg_of_small_primes_nonpos`: `∑_q C_q(ℓ, ℓ') < 0`, given
  `C_2(ℓ, ℓ') ≤ 0` and `C_3(ℓ, ℓ') ≤ 0`.
* `WeierstrassCurve.covariance_tamagawaValuation_neg_of_small_primes_nonpos`: under the same
  hypotheses, `Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0`.
* `WeierstrassCurve.covariance_tamagawaValuation_prod_neg_of_small_primes_nonpos`: the same
  statement for the law on `ℕ × ℕ`.
-/

@[expose] public section

namespace WeierstrassCurve

open ProbabilityTheory
open BSDTamagawa BSDTamagawa.CovarianceFormula

variable {ℓ ℓ' : ℕ}

/-! ### Negativity of `C_q(ℓ, ℓ')` at every prime `q ≥ 5` -/

/-- For distinct primes `ℓ ≠ ℓ'` and every prime `q ≥ 5`, `C_q(ℓ, ℓ') < 0`. -/
theorem localCov_neg_of_five_le {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') : localCov q ℓ ℓ' < 0 :=
  localCov_neg_of_inputs (hasLocalCovInputs_of_five_le hq) hℓ hℓ' hne

/-! ### Reduction to the primes `2` and `3` -/

/-- For distinct primes `ℓ ≠ ℓ'`, if `C_2(ℓ, ℓ') ≤ 0` and `C_3(ℓ, ℓ') ≤ 0`, then
`∑_{q prime} C_q(ℓ, ℓ') < 0`. -/
theorem tsum_localCov_neg_of_small_primes_nonpos (h2 : localCov 2 ℓ ℓ' ≤ 0)
    (h3 : localCov 3 ℓ ℓ' ≤ 0) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    (∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ') < 0 := by
  have hp5 : Nat.Prime 5 := by decide
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hnonpos : ∀ q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' ≤ 0 := by
    intro q
    rcases prime_eq_two_or_eq_three_or_five_le q.2 with hq | hq | hq
    · have hq' : q = ⟨2, Nat.prime_two⟩ := Subtype.ext hq
      subst hq'
      exact h2
    · have hq' : q = ⟨3, Nat.prime_three⟩ := Subtype.ext hq
      subst hq'
      exact h3
    · exact (@localCov_neg_of_five_le ℓ ℓ' (q : ℕ) ⟨q.2⟩ hq hℓ hℓ' hne).le
  have hstrict : @localCov 5 ⟨hp5⟩ ℓ ℓ' < 0 :=
    localCov_neg_of_five_le (q := 5) (by norm_num) hℓ hℓ' hne
  have hsum : Summable fun q : {n : ℕ // n.Prime} => -@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' :=
    (summable_localCov hℓ hℓ' hne).neg
  have hpos : 0 < ∑' q : {n : ℕ // n.Prime}, -@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' :=
    hsum.tsum_pos (fun q => neg_nonneg.2 (hnonpos q)) ⟨5, hp5⟩ (neg_pos.2 hstrict)
  rwa [tsum_neg, neg_pos] at hpos

/-- For distinct primes `ℓ ≠ ℓ'`, if `C_2(ℓ, ℓ') ≤ 0` and `C_3(ℓ, ℓ') ≤ 0`, then the covariance of
the `ℓ`- and `ℓ'`-coordinates under the joint valuation law `tamagawaValuationMeasure {ℓ, ℓ'}` is
negative. -/
theorem covariance_tamagawaValuation_neg_of_small_primes_nonpos (h2 : localCov 2 ℓ ℓ' ≤ 0)
    (h3 : localCov 3 ℓ ℓ' ≤ 0) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
        (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
        (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)) < 0 := by
  rw [(covariance_tamagawaValuation hℓ hℓ' hne).right]
  exact tsum_localCov_neg_of_small_primes_nonpos h2 h3 hℓ hℓ' hne

/-- For distinct primes `ℓ ≠ ℓ'`, if `C_2(ℓ, ℓ') ≤ 0` and `C_3(ℓ, ℓ') ≤ 0`, then the covariance of
the two coordinate projections of `ℕ × ℕ` under `tamagawaValuationProdMeasure ℓ ℓ' hne` is
negative. -/
theorem covariance_tamagawaValuation_prod_neg_of_small_primes_nonpos (h2 : localCov 2 ℓ ℓ' ≤ 0)
    (h3 : localCov 3 ℓ ℓ' ≤ 0) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
        (tamagawaValuationProdMeasure ℓ ℓ' hne) < 0 := by
  rw [(covariance_tamagawaValuation_prod hℓ hℓ' hne).right]
  exact tsum_localCov_neg_of_small_primes_nonpos h2 h3 hℓ hℓ' hne

end WeierstrassCurve
