/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.PrimeCount.SecondDerivative
public import BSDTamagawa.Analysis.PGFSecondDeriv
public import BSDTamagawa.PrimeCount.LawProbability

/-!
# The distribution of `ω(Tam)`: limiting density, Euler product and moments

The density `π_r = lim_{X → ∞} #{E : Ht(E) ≤ X, ω_Tam(E) = r} / N(X)` exists, its generating
function is the Euler product `∏_{p ∈ 𝒫}(δ_p(1) + (1 - δ_p(1))u)` on all of `ℂ`, that product
converges absolutely and locally uniformly, and, letting `P` be the probability measure on `ℤ_{≥0}`
with `P({r}) = π_r`,

  `𝔼_P[ω_Tam(E)] = ∑_{p ∈ 𝒫} (1 - δ_p(1))`,  `Var_P(ω_Tam(E)) = ∑_{p ∈ 𝒫} δ_p(1)(1 - δ_p(1))`,

both sums converging absolutely. The moments are read off from the first two left derivatives of
the generating function at `u = 1`.

## Main definitions

* `WeierstrassCurve.tamagawaOmegaPMF`: the limiting law `P` as a `PMF ℕ`.

## Main results

* `WeierstrassCurve.tamagawaOmegaPMF_toMeasure`: `tamagawaOmegaPMF.toMeasure` is the limiting law
  `tamagawaOmegaMeasure`.
* `WeierstrassCurve.integral_natCast_tamagawaOmegaMeasure`: `𝔼_P[ω_Tam] = ∑_{p ∈ 𝒫}(1 - δ_p(1))`.
* `WeierstrassCurve.variance_natCast_tamagawaOmegaMeasure`:
  `Var_P(ω_Tam) = ∑_{p ∈ 𝒫} δ_p(1)(1 - δ_p(1))`.
* `WeierstrassCurve.summable_one_sub_δ_one`, `WeierstrassCurve.summable_δ_one_mul_one_sub_δ_one`:
  the two series converge absolutely.
* `WeierstrassCurve.tendsto_tamagawaOmegaCount_div_integralShortNFCount`: existence of `π_r`.
* `WeierstrassCurve.tsum_tamagawaOmegaDensity_mul_pow_eq_tprod_primes`: the generating-function
  identity on `ℂ`.
* `WeierstrassCurve.multipliable_and_hasProdLocallyUniformly_tamagawaOmegaEulerFactor`: absolute
  and locally uniform convergence of the Euler product.

## Implementation notes

Sums and products over the primes are written over `p : ℕ` with the summand `0` (respectively the
factor `1`) at a non-prime index. Neither moment statement assumes integrability of `ω_Tam` or
summability of the second factorial moment; both follow from the existence of the one-sided
derivatives.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory ProbabilityTheory Set
open BSDTamagawa

/-! ### `P` as a `PMF ℕ` -/

/-- **The limiting law `P` as a `PMF ℕ`.** The masses are the limiting densities `π_r`, coerced by
`ENNReal.ofReal`. -/
noncomputable def tamagawaOmegaPMF : PMF ℕ :=
  ⟨fun r : ℕ => ENNReal.ofReal (tamagawaOmegaDensity r), by
    have h : ∑' r : ℕ, ENNReal.ofReal (tamagawaOmegaDensity r) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => (tamagawaOmegaDensity_mem_Icc r).1)
          summable_tamagawaOmegaDensity, tsum_tamagawaOmegaDensity_eq_one, ENNReal.ofReal_one]
    exact h ▸ ENNReal.summable.hasSum⟩

/-- The mass `tamagawaOmegaPMF` puts at `r` is `ENNReal.ofReal (π_r)`. -/
theorem tamagawaOmegaPMF_apply (r : ℕ) :
    tamagawaOmegaPMF r = ENNReal.ofReal (tamagawaOmegaDensity r) := rfl

/-- The mass at `r`, read back in `ℝ`, is the density `π_r`. -/
theorem toReal_tamagawaOmegaPMF_apply (k : ℕ) :
    (tamagawaOmegaPMF k).toReal = tamagawaOmegaDensity k := by
  rw [tamagawaOmegaPMF_apply, ENNReal.toReal_ofReal (tamagawaOmegaDensity_mem_Icc k).1]

/-- `k ↦ (tamagawaOmegaPMF k).toReal` is the function `k ↦ π_k`. -/
theorem toReal_tamagawaOmegaPMF :
    (fun k : ℕ => (tamagawaOmegaPMF k).toReal) = tamagawaOmegaDensity :=
  funext toReal_tamagawaOmegaPMF_apply

/-- **The `PMF` and the measure are the same law.** `tamagawaOmegaPMF.toMeasure` is the limiting
law `P`. -/
theorem tamagawaOmegaPMF_toMeasure : tamagawaOmegaPMF.toMeasure = tamagawaOmegaMeasure := by
  rw [tamagawaOmegaMeasure]
  conv_lhs => rw [← Measure.sum_smul_dirac tamagawaOmegaPMF.toMeasure]
  simp_rw [tamagawaOmegaPMF.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  rfl

/-! ### The derivatives of the probability generating function at `u = 1` -/

/-- The probability generating function of `tamagawaOmegaPMF` is differentiable at `u = 1` from the
left with derivative `∑_p a_p`, `a_p = 1 - δ_p(1)`. -/
theorem hasDerivWithinAt_pgf_toReal_tamagawaOmegaPMF :
    HasDerivWithinAt (PGFMean.pgf fun k : ℕ => (tamagawaOmegaPMF k).toReal)
      (∑' p : ℕ, tamagawaLocalTailMass p) (Iio 1) 1 := by
  rw [toReal_tamagawaOmegaPMF]
  exact hasDerivWithinAt_pgf_tamagawaOmegaDensity

/-- The first derivative of the probability generating function of `tamagawaOmegaPMF`, taken within
`Set.Iic 1`, is differentiable at `u = 1` from the left, with value
`F''(1) = (∑_p a_p)² - ∑_p a_p²`. -/
theorem hasDerivWithinAt_derivWithin_pgf_toReal_tamagawaOmegaPMF :
    HasDerivWithinAt (derivWithin (PGFMean.pgf fun k : ℕ => (tamagawaOmegaPMF k).toReal) (Iic 1))
      ((∑' p : ℕ, tamagawaLocalTailMass p) ^ 2 - ∑' p : ℕ, tamagawaLocalTailMass p ^ 2)
      (Iio 1) 1 := by
  rw [toReal_tamagawaOmegaPMF]
  exact hasDerivWithinAt_derivWithin_pgf_tamagawaOmegaDensity

/-- **`ω_Tam` is `P`-integrable.** -/
theorem integrable_natCast_tamagawaOmegaMeasure :
    Integrable (fun n : ℕ => (n : ℝ)) tamagawaOmegaMeasure := by
  rw [← tamagawaOmegaPMF_toMeasure]
  exact BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt tamagawaOmegaPMF
    hasDerivWithinAt_pgf_toReal_tamagawaOmegaPMF

/-! ### The mean -/

/-- **The mean, in terms of the local tail masses.** `𝔼_P[ω_Tam] = ∑' p, a_p` with `a_p` the local
tail mass. -/
theorem integral_natCast_tamagawaOmegaMeasure_tailMass :
    ∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure = ∑' p : ℕ, tamagawaLocalTailMass p := by
  rw [← tamagawaOmegaPMF_toMeasure,
    ← PGFVariance.pgfDeriv_eq_mean tamagawaOmegaPMF
      (tamagawaOmegaPMF_toMeasure ▸ integrable_natCast_tamagawaOmegaMeasure), PGFVariance.pgfDeriv]
  simp_rw [toReal_tamagawaOmegaPMF_apply]
  exact (PGFMean.main_theorem tamagawaOmegaDensity (fun r => (tamagawaOmegaDensity_mem_Icc r).1)
    hasSum_tamagawaOmegaDensity_one _ hasDerivWithinAt_pgf_tamagawaOmegaDensity).2

/-- The expectation of `ω_Tam` under its limiting law `P` is

  `𝔼_P[ω_Tam(E)] = ∑_{p ∈ 𝒫} (1 - δ_p(1))`,

with `δ_p(1)` the scalar local density. The random variable is the identity coordinate
`fun n : ℕ => (n : ℝ)` on `ℤ_{≥0} = ℕ`, and the expectation is the Bochner integral against `P`. -/
@[bsd_tamagawa "T041"]
theorem integral_natCast_tamagawaOmegaMeasure :
    ∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure
      = ∑' p : ℕ, if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0 :=
  integral_natCast_tamagawaOmegaMeasure_tailMass

/-! ### The variance -/

/-- The variance summand `δ_p(1)(1 - δ_p(1))` is `a_p(1 - a_p)`, at every index. -/
theorem dite_δ_one_mul_one_sub_δ_one_eq (p : ℕ) :
    (if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal) else 0)
      = tamagawaLocalTailMass p * (1 - tamagawaLocalTailMass p) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [dite_eq_left hp, tamagawaLocalTailMass_of_prime]
    ring
  · rw [dite_eq_right hp, tamagawaLocalTailMass_of_not_prime hp]
    ring

/-- The variance series converges absolutely: `∑_{p ∈ 𝒫} δ_p(1)(1 - δ_p(1)) < ∞`. -/
@[bsd_tamagawa "T041"]
theorem summable_δ_one_mul_one_sub_δ_one :
    Summable fun p : ℕ => if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal)
      else 0 := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) summable_tamagawaLocalTailMass
  · rw [dite_δ_one_mul_one_sub_δ_one_eq]
    exact mul_nonneg (tamagawaLocalTailMass_nonneg p)
      (by linarith [tamagawaLocalTailMass_le_one p])
  · rw [dite_δ_one_mul_one_sub_δ_one_eq]
    nlinarith [tamagawaLocalTailMass_nonneg p, tamagawaLocalTailMass_le_one p]

/-- **The variance, in terms of the local tail masses.** `Var_P(ω_Tam) = ∑' p, a_p(1 - a_p)`. -/
theorem variance_natCast_tamagawaOmegaMeasure_tailMass :
    variance (fun n : ℕ => (n : ℝ)) tamagawaOmegaMeasure
      = ∑' p : ℕ, tamagawaLocalTailMass p * (1 - tamagawaLocalTailMass p) := by
  rw [← tamagawaOmegaPMF_toMeasure,
    BSDTamagawa.PGFSecondDeriv.variance_eq_of_hasDerivWithinAt_derivWithin' tamagawaOmegaPMF
      hasDerivWithinAt_pgf_toReal_tamagawaOmegaPMF
      hasDerivWithinAt_derivWithin_pgf_toReal_tamagawaOmegaPMF]
  have hsub : ∑' p : ℕ, tamagawaLocalTailMass p * (1 - tamagawaLocalTailMass p)
      = (∑' p : ℕ, tamagawaLocalTailMass p) - ∑' p : ℕ, tamagawaLocalTailMass p ^ 2 := by
    rw [← summable_tamagawaLocalTailMass.tsum_sub summable_tamagawaLocalTailMass_sq]
    exact tsum_congr fun p => by ring
  rw [hsub]
  ring

/-- The variance of `ω_Tam` under its limiting law `P` is

  `Var_P(ω_Tam(E)) = ∑_{p ∈ 𝒫} δ_p(1)(1 - δ_p(1))`,

with `δ_p(1)` the scalar local density, the random variable the identity coordinate
`fun n : ℕ => (n : ℝ)` on `ℤ_{≥0} = ℕ`, and `Var` Mathlib's `ProbabilityTheory.variance` against
`P`. -/
@[bsd_tamagawa "T041"]
theorem variance_natCast_tamagawaOmegaMeasure :
    variance (fun n : ℕ => (n : ℝ)) tamagawaOmegaMeasure
      = ∑' p : ℕ, if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal) else 0 := by
  rw [variance_natCast_tamagawaOmegaMeasure_tailMass]
  exact (tsum_congr dite_δ_one_mul_one_sub_δ_one_eq).symm

/-! ### Existence of `π_r` -/

/-- For each `r ≥ 0` the density `π_r` is the limit of the proportion of pairs `(a₄, a₆) ∈ ℤ²`
whose short Weierstrass model is nonsingular, of naive height at most `X`, and has `ω_Tam = r`,
among all `N(X)` nonsingular pairs of height at most `X`. -/
@[bsd_tamagawa "T041"]
theorem tendsto_tamagawaOmegaCount_div_integralShortNFCount (r : ℕ) :
    Filter.Tendsto (fun X : ℝ =>
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          tamagawaOmega q.1 q.2 = r}.ncard : ℝ) / integralShortNFCount X)
      Filter.atTop (nhds (tamagawaOmegaDensity r)) :=
  tendsto_tamagawaOmegaProportion_tamagawaOmegaDensity r

/-! ### The generating function and its Euler product -/

/-- `∑_{r ≥ 0} π_r u^r = ∏_{p ∈ 𝒫} (δ_p(1) + (1 - δ_p(1))u)` for every `u ∈ ℂ`. The product is `∏'`
over `p : ℕ` with the non-prime factors equal to `1`. -/
@[bsd_tamagawa "T041"]
theorem tsum_tamagawaOmegaDensity_mul_pow_eq_tprod_primes (u : ℂ) :
    (∑' r : ℕ, ((tamagawaOmegaDensity r : ℝ) : ℂ) * u ^ r)
      = ∏' p : ℕ, (if h : p.Prime then
          ((@δ p ⟨h⟩ 1).toReal : ℂ) + (1 - ((@δ p ⟨h⟩ 1).toReal : ℂ)) * u else 1) :=
  tsum_tamagawaOmegaDensity_mul_pow u

/-- The mean series converges absolutely: `∑_{p ∈ 𝒫} (1 - δ_p(1)) < ∞`. -/
@[bsd_tamagawa "T041"]
theorem summable_one_sub_δ_one :
    Summable fun p : ℕ => if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0 :=
  summable_tamagawaLocalTailMass

/-- The Euler product converges absolutely at every `u ∈ ℂ` (`Multipliable`) and locally uniformly
on `ℂ`. -/
@[bsd_tamagawa "T041"]
theorem multipliable_and_hasProdLocallyUniformly_tamagawaOmegaEulerFactor :
    (∀ u : ℂ, Multipliable fun p : ℕ => tamagawaOmegaEulerFactor p u) ∧
      HasProdLocallyUniformly tamagawaOmegaEulerFactor
        (fun u => ∏' p : ℕ, tamagawaOmegaEulerFactor p u) :=
  ⟨multipliable_tamagawaOmegaEulerFactor, hasProdLocallyUniformly_tamagawaOmegaEulerFactor⟩

end WeierstrassCurve
