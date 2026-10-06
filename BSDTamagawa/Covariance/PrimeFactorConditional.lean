/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.FactorCount.MeanConditional
public import BSDTamagawa.Covariance.FormulaConditional

/-!
# Local covariance of `ω_Tam` and `Ω(Tam)`

The local factor at a prime `p` of the bivariate generating function of `ω_Tam(E)` and `Ω(Tam(E))`
is `g_p(u, w) = ∑_{t ≥ 1} δ_p(t) u^{ω_{Tam,t}} w^{Ω(t)}`, where `ω_{Tam,t}` is `0` at `t = 1` and
`1` at `t ≥ 2`. Since `Ω(1) = 0` and `δ_p` has total mass `1`, at every prime

  `∑_t δ_p(t) ω_{Tam,t} Ω(t) - (∑_t δ_p(t) ω_{Tam,t})(∑_t δ_p(t) Ω(t)) = δ_p(1) ∑_t δ_p(t) Ω(t)`.

This file also introduces the summands `δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)` of the series of local
covariances, and shows that each is nonnegative and at most `∑_t δ_p(t) Ω(t)`.

## Main definitions

* `BSDTamagawa.PrimeFactorCovariance.omegaIndicator`: the local exponent `ω_{Tam,t}`.
* `BSDTamagawa.PrimeFactorCovariance.crossExp`: the mixed exponent `t ↦ ω_{Tam,t} Ω(t)`.
* `BSDTamagawa.PrimeFactorCovariance.localCovOmega`: the local covariance of `ω_{Tam,·}` and `Ω`
  against `δ_p`.
* `BSDTamagawa.PrimeFactorCovariance.covSeriesTerm`: the summand `δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)`.

## Main results

* `BSDTamagawa.PrimeFactorCovariance.localCovOmega_of_prime`: the local covariance identity.
-/

@[expose] public section

namespace BSDTamagawa.PrimeFactorCovariance

open Set MeasureTheory ProbabilityTheory
open WeierstrassCurve BSDTamagawa.ValuationMean BSDTamagawa.FactorCountMean

open scoped ENNReal

/-! ### The two local exponents -/

/-- The local exponent `ω_{Tam,t}` of `ω_Tam`: `0` for `t ≤ 1` and `1` otherwise. -/
def omegaIndicator : ℕ → ℕ := fun t => if t ≤ 1 then 0 else 1

/-- `ω_{Tam,t} = 0` for `t ≤ 1`. -/
theorem omegaIndicator_of_le_one {t : ℕ} (ht : t ≤ 1) : omegaIndicator t = 0 := ite_eq_left ht

/-- `ω_{Tam,t} = 1` for `t ≥ 2`. -/
theorem omegaIndicator_of_two_le {t : ℕ} (ht : 2 ≤ t) : omegaIndicator t = 1 :=
  ite_eq_right (by omega)

/-- `Ω(t) = 0` for `t ≤ 1`: both `0` and `1` are products of no primes. -/
theorem omegaExp_eq_zero_of_le_one {t : ℕ} (ht : t ≤ 1) : omegaExp t = 0 := by
  interval_cases t <;> simp [omegaExp]

/-- `2^{Ω(t)} ≤ max 1 t`. -/
theorem two_pow_omegaExp_le (t : ℕ) : 2 ^ omegaExp t ≤ max 1 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [omegaExp]
  · exact (FirstMoment.two_pow_cardFactors_le ht).trans (le_max_right 1 t)

/-- The mixed exponent `t ↦ ω_{Tam,t} Ω(t)`. -/
def crossExp : ℕ → ℕ := fun t => omegaIndicator t * omegaExp t

/-- The mixed exponent `ω_{Tam,t} Ω(t)` equals `Ω(t)`, since `Ω(t) = 0` for `t ≤ 1`. -/
theorem crossExp_eq_omegaExp : crossExp = omegaExp := by
  funext t
  rcases le_or_gt t 1 with h | h
  · rw [crossExp, omegaIndicator_of_le_one h, omegaExp_eq_zero_of_le_one h, Nat.mul_zero]
  · rw [crossExp, omegaIndicator_of_two_le h, one_mul]

/-! ### The local covariance of `ω_{Tam,·}` and `Ω` against `δ_p` -/

/-- The local covariance `E_{δ_p}[ω_{Tam,·} Ω] - E_{δ_p}[ω_{Tam,·}] E_{δ_p}[Ω]`, in `ℝ`; it is `0`
off the primes. -/
noncomputable def localCovOmega (p : ℕ) : ℝ :=
  eulerMoment crossExp p - eulerMoment omegaIndicator p * eulerMoment omegaExp p

/-- The cross moment is the `Ω`-moment, by `crossExp_eq_omegaExp`. -/
theorem eulerMoment_crossExp (p : ℕ) : eulerMoment crossExp p = eulerMoment omegaExp p := by
  rw [crossExp_eq_omegaExp]

/-- The family `t ↦ δ_p(t) ω_{Tam,t}` is summable. -/
theorem summable_toReal_δ_mul_omegaIndicator (p : ℕ) [Fact p.Prime] :
    Summable fun t : ℕ => (δ p t).toReal * (omegaIndicator t : ℝ) := by
  refine Summable.of_nonneg_of_le
    (fun t => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (fun t => ?_)
    (hasSum_toReal_δ p).summable
  rcases le_or_gt t 1 with h | h
  · rw [omegaIndicator_of_le_one h]
    simp
  · rw [omegaIndicator_of_two_le h]
    simp

/-- At a prime `p`, `∑_{t ≥ 1} δ_p(t) ω_{Tam,t} = 1 - δ_p(1)`. -/
theorem eulerMoment_omegaIndicator_of_prime (p : ℕ) [Fact p.Prime] :
    eulerMoment omegaIndicator p = 1 - (δ p 1).toReal := by
  have hf : HasSum (fun t : ℕ => (δ p t).toReal) 1 := hasSum_toReal_δ p
  have hg := (summable_toReal_δ_mul_omegaIndicator p).sum_add_tsum_nat_add 2
  have h2 := hf.summable.sum_add_tsum_nat_add 2
  have hhead : (∑ i ∈ Finset.range 2, (δ p i).toReal * (omegaIndicator i : ℝ)) = 0 := by
    simp [Finset.sum_range_succ, omegaIndicator]
  have hfhead : (∑ i ∈ Finset.range 2, (δ p i).toReal) = (δ p 1).toReal := by
    simp [Finset.sum_range_succ, δ_zero p]
  have htail : (∑' i : ℕ, (δ p (i + 2)).toReal * (omegaIndicator (i + 2) : ℝ))
      = ∑' i : ℕ, (δ p (i + 2)).toReal :=
    tsum_congr fun i => by rw [omegaIndicator_of_two_le (by omega), Nat.cast_one, mul_one]
  rw [hhead, zero_add, htail] at hg
  rw [hfhead, hf.tsum_eq] at h2
  rw [eulerMoment_of_prime, ← hg]
  linarith

/-- At every prime `p`,

  `∑_t δ_p(t) ω_{Tam,t} Ω(t) - (∑_t δ_p(t) ω_{Tam,t})(∑_t δ_p(t) Ω(t)) = δ_p(1) ∑_t δ_p(t) Ω(t)`.
-/
theorem localCovOmega_of_prime (p : ℕ) [Fact p.Prime] :
    localCovOmega p = (δ p 1).toReal * eulerMoment omegaExp p := by
  rw [localCovOmega, eulerMoment_crossExp, eulerMoment_omegaIndicator_of_prime]
  ring

/-- Off the primes every moment is `0`, hence so is the local covariance. -/
theorem localCovOmega_of_not_prime {p : ℕ} (hp : ¬ p.Prime) : localCovOmega p = 0 := by
  simp [localCovOmega, eulerMoment_of_not_prime hp]

/-! ### The series `∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)` -/

/-- The summand `δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)` at a prime `p`, and `0` off the primes. -/
noncomputable def covSeriesTerm (p : ℕ) : ℝ :=
  if h : p.Prime then
    (@δ p ⟨h⟩ 1).toReal
      * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
  else 0

/-- `localCovOmega p = covSeriesTerm p` for every `p`. -/
theorem localCovOmega_eq_covSeriesTerm (p : ℕ) : localCovOmega p = covSeriesTerm p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [localCovOmega_of_prime, covSeriesTerm, dite_eq_left hp, eulerMoment_of_prime]
    exact congrArg _ (tsum_congr fun t => by rw [omegaExp_apply])
  · rw [localCovOmega_of_not_prime hp, covSeriesTerm, dite_eq_right hp]

/-- Every summand is nonnegative: a mass times a sum of nonnegative terms. -/
theorem covSeriesTerm_nonneg (p : ℕ) : 0 ≤ covSeriesTerm p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [covSeriesTerm, dite_eq_left hp]
    exact mul_nonneg ENNReal.toReal_nonneg
      (tsum_nonneg fun t => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
  · rw [covSeriesTerm, dite_eq_right hp]

/-- `δ_p(1) ∑_t δ_p(t) Ω(t) ≤ ∑_t δ_p(t) Ω(t)`. -/
theorem covSeriesTerm_le (p : ℕ) : covSeriesTerm p ≤ eulerMoment omegaExp p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [covSeriesTerm, dite_eq_left hp, eulerMoment_of_prime]
    exact mul_le_of_le_one_left
      (tsum_nonneg fun t => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
      (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (δ_le_one (p := p) 1))
  · rw [covSeriesTerm, dite_eq_right hp, eulerMoment_of_not_prime hp]

/-! ### The local factor of `Ω` at a prime -/

/-- At a prime `q`, `primeFactor omegaExp q w = eulerFactor omegaExp q w`, both being
`∑_t δ_q(t) w^{Ω(t)}`. -/
theorem primeFactor_eq_eulerFactor (q : {n : ℕ // n.Prime}) (w : ℝ) :
    primeFactor omegaExp q w = eulerFactor omegaExp (q : ℕ) w := by
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [eulerFactor_of_prime]
  rfl

end BSDTamagawa.PrimeFactorCovariance
