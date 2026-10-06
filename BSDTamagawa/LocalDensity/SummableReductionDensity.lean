/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.PrimeSquareTail
public import BSDTamagawa.LocalDensity.StratumBound

/-!
# Summability of `δ_p(K)` over the primes

For a fixed nontrivial reduction stratum `K ∈ 𝒦 ∖ 𝒦₀`, where `𝒦₀ = {(I₀, 1), (I₁, 1)}`, the family
of its local masses across the primes is summable: `∑_{p prime} δ_p(K) < ∞`. Indeed `δ_p(K) ≤ 9/p²`
at every prime, and `∑_p p⁻²` converges.

## Main results

* `WeierstrassCurve.summable_stratumLocalMass`: the real-valued family `stratumLocalMass K`, equal
  to `(δ_p(K)).toReal` at a prime `p` and `0` elsewhere, is summable.
* `WeierstrassCurve.tsum_deltaP_prime_lt_top`: `∑_p δ_p(K) < ⊤` in `ℝ≥0∞`.

## Implementation notes

The sums range over `ℕ`, with summand `0` off the primes. In `ℝ≥0∞` every family is summable, so
there convergence is expressed as finiteness of the `tsum`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.PrimeSqTail

open scoped ENNReal

/-! ### The real-valued local mass of a stratum -/

/-- At a prime index the local mass of `K` is `(δ_p(K)).toReal`. -/
theorem stratumLocalMass_of_prime (K : ReductionData) (p : ℕ) [Fact p.Prime] :
    stratumLocalMass K p = (deltaP p K).toReal :=
  dite_eq_left Fact.out

/-- At a non-prime index the local mass of `K` is the neutral value `0`. -/
theorem stratumLocalMass_of_not_prime (K : ReductionData) {p : ℕ} (hp : ¬ p.Prime) :
    stratumLocalMass K p = 0 :=
  dite_eq_right hp

/-- Every local mass `stratumLocalMass K p` is nonnegative. -/
theorem stratumLocalMass_nonneg (K : ReductionData) (p : ℕ) : 0 ≤ stratumLocalMass K p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [stratumLocalMass_of_prime]
    exact ENNReal.toReal_nonneg
  · rw [stratumLocalMass_of_not_prime K hp]

/-! ### The termwise comparison with `9 · p⁻²` -/

/-- `(δ_p(K)).toReal ≤ 9/p²` for every prime `p` and every `K ∈ 𝒦 ∖ 𝒦₀`. -/
theorem deltaP_toReal_le_nine_div_sq (p : ℕ) [Fact p.Prime] {K : ReductionData}
    (hK : K ∉ (K0 : Set ReductionData)) : (deltaP p K).toReal ≤ 9 / (p : ℝ) ^ 2 := by
  have hpne : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  have hp0 : ((p : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using hpne)
  have hdiv : (9 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.div_ne_top (by norm_num) hp0
  have h := ENNReal.toReal_mono hdiv (deltaP_le_nine_div_sq p hK)
  rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at h

/-- For every `p : ℕ` and every `K ∈ 𝒦 ∖ 𝒦₀`, `stratumLocalMass K p ≤ 9 · primeSq p`. -/
theorem stratumLocalMass_le_primeSq {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData))
    (p : ℕ) : stratumLocalMass K p ≤ 9 * primeSq p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hps : primeSq p = 1 / (p : ℝ) ^ 2 := by rw [primeSq]; exact ite_eq_left hp
    rw [stratumLocalMass_of_prime, hps, mul_one_div]
    exact deltaP_toReal_le_nine_div_sq p hK
  · rw [stratumLocalMass_of_not_prime K hp, primeSq, ite_eq_right hp, mul_zero]

/-! ### Summability -/

/-- For every `K ∈ 𝒦 ∖ 𝒦₀` the family `(δ_p(K))_{p ∈ 𝒫}` of local masses is summable, in the
`ℝ`-valued form `Summable (stratumLocalMass K)`. -/
@[bsd_tamagawa "T040h"]
theorem summable_stratumLocalMass {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)) :
    Summable (stratumLocalMass K) :=
  Summable.of_nonneg_of_le (stratumLocalMass_nonneg K) (stratumLocalMass_le_primeSq hK)
    (summable_primeSq.mul_left 9)

/-- The `ℝ≥0∞`-valued local mass family is `ENNReal.ofReal` of the real one. -/
theorem dite_deltaP_eq_ofReal (K : ReductionData) (p : ℕ) :
    (if h : p.Prime then @deltaP p ⟨h⟩ K else 0) = ENNReal.ofReal (stratumLocalMass K p) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [dite_eq_left hp, stratumLocalMass_of_prime, ENNReal.ofReal_toReal (deltaP_ne_top p K)]
  · rw [dite_eq_right hp, stratumLocalMass_of_not_prime K hp, ENNReal.ofReal_zero]

/-- `∑_p δ_p(K) < ∞` in `ℝ≥0∞` for every `K ∈ 𝒦 ∖ 𝒦₀`, the sum being over the primes (the summand
is `0` at a non-prime index). -/
@[bsd_tamagawa "T040h"]
theorem tsum_deltaP_prime_lt_top {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)) :
    (∑' p : ℕ, if h : p.Prime then @deltaP p ⟨h⟩ K else 0) < ⊤ := by
  rw [tsum_congr (dite_deltaP_eq_ofReal K), ← ENNReal.ofReal_tsum_of_nonneg
    (stratumLocalMass_nonneg K) (summable_stratumLocalMass hK)]
  exact ENNReal.ofReal_lt_top

end WeierstrassCurve
