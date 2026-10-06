/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.Mean
public import BSDTamagawa.FactorCount.PrimeCountLeConditional
public import BSDTamagawa.PrimeCount.Moments

/-!
# The mean of `Ω(Tam(E))`

With `P_Ω` the limiting law of `Ω(Tam(E))`, the number of prime factors of the Tamagawa product
counted with multiplicity,

`𝔼_{P_Ω}[Ω(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t) < ∞`,

and this mean dominates the mean of the Tamagawa prime count `ω_Tam(E)` under its limiting law.
These are the statements of `BSDTamagawa.FactorCountMean` and `BSDTamagawa.PrimeCountLeFactorCount`
with the geometric tail law hypothesis removed.

## Main results

* `WeierstrassCurve.summable_tsum_δ_mul_cardFactors`: the double series
  `∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t)` converges.
* `WeierstrassCurve.integral_natCast_cardFactorsTamagawaMeasure_val`: the mean of `Ω(Tam(E))` is
  that double series.
* `WeierstrassCurve.cardFactors_mean`: the two together.
* `WeierstrassCurve.omegaTamMean_le_cardFactors_mean`: `𝔼[ω_Tam(E)] ≤ 𝔼[Ω(Tam(E))] < ∞`.
-/

@[expose] public section

namespace BSDTamagawa.FactorCountMeanUnconditional

open Set MeasureTheory WeierstrassCurve BSDTamagawa.ValuationMean
  BSDTamagawa.ValuationMeanUnconditional
open BSDTamagawa.FactorCountMean

open scoped ENNReal

/-! ### The log-derivative package at the `Ω`-weighted family -/

/-- The Euler factors, moments, bounds and window of the `Ω`-weighted family satisfy the hypotheses
`LogDerivProduct.ProdHyp`. -/
theorem prodHyp_omegaExp' :
    LogDerivProduct.ProdHyp (eulerFactor omegaExp) (eulerMoment omegaExp) (eulerSup omegaExp)
      (eulerEta omegaExp) :=
  prodHyp_eulerFactor' omegaExp_cast_le two_pow_omegaExp_cast_le
    fun q _ hq => tsum_δ_mul_cardFactors_le q hq

/-- On the window, the coerced real product `LogDerivProduct.prodG` is the Euler product
`∏'_p h_p(0, w, ())` at `Π = ∅`, `s = 0`. -/
theorem ofReal_prodG_omegaExp' {w : ℝ} (hw : w ∈ Icc (1 - eulerEta omegaExp) 1) :
    ((LogDerivProduct.prodG (eulerFactor omegaExp) w : ℝ) : ℂ)
      = ∏' p : ℕ, scalarLocalFactor ∅ p 0 (w : ℂ) (fun _ => 0) := by
  have hmap := (LogDerivProduct.hasProd_prodG prodHyp_omegaExp' hw).map Complex.ofRealHom
    Complex.continuous_ofReal
  refine ((hmap.congr_fun fun p => ?_).tprod_eq).symm
  simpa using (ofReal_eulerFactor_eq_scalarLocalFactor p (abs_le_one_of_mem_window hw)).symm

/-- On the window, the generating function `PGFMean.pgf ρ` equals the real product
`LogDerivProduct.prodG`. -/
theorem pgf_eq_prodG_omegaExp' {w : ℝ} (hw : w ∈ Icc (1 - eulerEta omegaExp) 1) :
    PGFMean.pgf cardFactorsTamagawaDensity w = LogDerivProduct.prodG (eulerFactor omegaExp) w :=
  Complex.ofReal_inj.mp
    ((ofReal_pgf_cardFactorsTamagawaDensity (abs_le_one_of_mem_window hw)).trans
      (ofReal_prodG_omegaExp' hw).symm)

/-- The generating function of `ρ` has left derivative `∑_p ∑_t δ_p(t) Ω(t)` at `w = 1`. -/
theorem hasDerivWithinAt_pgf_cardFactorsTamagawaDensity' :
    HasDerivWithinAt (PGFMean.pgf cardFactorsTamagawaDensity)
      (∑' p : ℕ, eulerMoment omegaExp p) (Iio 1) 1 := by
  have hη := eulerEta_pos omegaExp
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG prodHyp_omegaExp'
  rw [tsum_deriv_eulerFactor' omegaExp_cast_le two_pow_omegaExp_cast_le] at hprod
  refine hprod.congr_of_eventuallyEq ?_ (pgf_eq_prodG_omegaExp' ⟨by linarith, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show 1 - eulerEta omegaExp < 1 by linarith)] with x hx
  exact pgf_eq_prodG_omegaExp' ⟨hx.1.le, hx.2.le⟩

/-- The identity coordinate `n ↦ n` is `P_Ω`-integrable. -/
theorem integrable_natCast_cardFactorsTamagawaMeasure' :
    Integrable (fun n : ℕ => (n : ℝ)) cardFactorsTamagawaMeasure := by
  rw [← cardFactorsPMF_toMeasure]
  exact BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt cardFactorsPMF
    (by rw [toReal_cardFactorsPMF]; exact hasDerivWithinAt_pgf_cardFactorsTamagawaDensity')

/-- The mean of `Ω(Tam(E))` under `P_Ω` is `∑_p ∑_t δ_p(t) Ω(t)`. -/
theorem integral_natCast_cardFactorsTamagawaMeasure' :
    ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure = ∑' p : ℕ, eulerMoment omegaExp p := by
  rw [← cardFactorsPMF_toMeasure, ← PGFVariance.pgfDeriv_eq_mean cardFactorsPMF
      (cardFactorsPMF_toMeasure ▸ integrable_natCast_cardFactorsTamagawaMeasure'),
    PGFVariance.pgfDeriv]
  simp_rw [toReal_cardFactorsPMF_apply]
  exact (PGFMean.main_theorem cardFactorsTamagawaDensity cardFactorsTamagawaDensity_nonneg
    hasSum_cardFactorsTamagawaDensity _
    hasDerivWithinAt_pgf_cardFactorsTamagawaDensity').2

/-! ### The termwise comparison with `ω_Tam` -/

/-- At a prime `p`, `1 - δ_p(1) ≤ ∑_{t ≥ 1} δ_p(t) Ω(t)`. -/
theorem one_sub_δ_one_le_moment' {p : ℕ} [Fact p.Prime] :
    1 - (δ p 1).toReal ≤ eulerMoment omegaExp p := by
  have HM := massFamily_δ (p := p) omegaExp_cast_le two_pow_omegaExp_cast_le
  have hupd : HasSum (Function.update (fun t : ℕ => (δ p t).toReal) 1 0)
      (1 - (δ p 1).toReal) := by
    have hu := (hasSum_toReal_δ p).update 1 0
    rw [show (0 : ℝ) - (δ p 1).toReal + 1 = 1 - (δ p 1).toReal by ring] at hu
    exact hu
  have hle : ∀ t : ℕ, Function.update (fun t : ℕ => (δ p t).toReal) 1 0 t
      ≤ (δ p t).toReal * ((omegaExp t : ℕ) : ℝ) := by
    intro t
    rcases eq_or_ne t 1 with rfl | h1
    · simp [omegaExp]
    · rw [Function.update_of_ne h1]
      rcases eq_or_ne t 0 with rfl | h0
      · rw [δ_zero]
        simp
      · have hΩ : (1 : ℝ) ≤ ((omegaExp t : ℕ) : ℝ) := by
          exact_mod_cast BSDTamagawa.PrimeCountLeFactorCount.one_le_cardFactors (t := t) (by omega)
        nlinarith [ENNReal.toReal_nonneg (a := δ p t)]
  calc 1 - (δ p 1).toReal
      = ∑' t : ℕ, Function.update (fun t : ℕ => (δ p t).toReal) 1 0 t := hupd.tsum_eq.symm
    _ ≤ ∑' t : ℕ, (δ p t).toReal * ((omegaExp t : ℕ) : ℝ) :=
        hupd.summable.tsum_le_tsum hle (summable_moment HM)
    _ = eulerMoment omegaExp p := (eulerMoment_of_prime omegaExp p).symm

/-- For every `p : ℕ`, the local tail mass `1 - δ_p(1)` is at most `∑_{t ≥ 1} δ_p(t) Ω(t)` (both
are `0` off the primes). -/
theorem tamagawaLocalTailMass_le_eulerMoment' (p : ℕ) :
    tamagawaLocalTailMass p ≤ eulerMoment omegaExp p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTailMass_of_prime]
    exact one_sub_δ_one_le_moment'
  · rw [tamagawaLocalTailMass_of_not_prime hp, eulerMoment_of_not_prime hp]

/-- The mean of `ω_Tam(E)` under its limiting law is at most the mean of `Ω(Tam(E))` under
`P_Ω`. -/
theorem integral_natCast_le' :
    ∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure ≤ ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure := by
  rw [integral_natCast_tamagawaOmegaMeasure_tailMass,
    integral_natCast_cardFactorsTamagawaMeasure']
  exact summable_tamagawaLocalTailMass.tsum_le_tsum tamagawaLocalTailMass_le_eulerMoment'
    (summable_eulerMoment (k := omegaExp) fun q _ hq => tsum_δ_mul_cardFactors_le q hq)

end BSDTamagawa.FactorCountMeanUnconditional

namespace WeierstrassCurve

open BSDTamagawa.ValuationMean BSDTamagawa.FactorCountMean BSDTamagawa.FactorCountMeanUnconditional
  MeasureTheory

/-- The double series `∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t)` converges; all its terms being nonnegative,
the convergence is absolute. -/
theorem summable_tsum_δ_mul_cardFactors :
    Summable fun p : ℕ => if h : p.Prime then
      ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  summable_eulerMoment (k := omegaExp) fun q _ hq =>
    BSDTamagawa.ValuationMeanUnconditional.tsum_δ_mul_cardFactors_le q hq

/-- With `P_Ω` the limiting law of `Ω(Tam(E))` on `ℤ_{≥0} = ℕ`,

  `𝔼_{P_Ω}[Ω(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t)`,

the random variable being the identity coordinate `fun n : ℕ => (n : ℝ)`. -/
theorem integral_natCast_cardFactorsTamagawaMeasure_val :
    ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
      = ∑' p : ℕ, if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  BSDTamagawa.FactorCountMeanUnconditional.integral_natCast_cardFactorsTamagawaMeasure'

/-- With `P` the probability measure on `ℤ_{≥0}` with `P({b}) = ρ_b`,

  `𝔼_P[Ω(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t) < ∞`:

the double series converges and the mean is its value. -/
@[bsd_tamagawa "T046b"]
theorem cardFactors_mean :
    (Summable fun p : ℕ => if h : p.Prime then
        ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0) ∧
      ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
        = ∑' p : ℕ, if h : p.Prime then
            ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  ⟨summable_tsum_δ_mul_cardFactors, integral_natCast_cardFactorsTamagawaMeasure_val⟩

/-- With `P` the limiting law of `ω_Tam(E)` and `P'` the limiting law of `Ω(Tam(E))`,

  `𝔼_P[ω_Tam(E)] ≤ 𝔼_{P'}[Ω(Tam(E))] < ∞`,

where the right-hand mean is the convergent double series `∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t)`. Both
expectations are integrals of the identity coordinate `fun n : ℕ => (n : ℝ)` on `ℤ_{≥0} = ℕ`. -/
@[bsd_tamagawa "T046c"]
theorem omegaTamMean_le_cardFactors_mean :
    (∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure ≤ ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure) ∧
      (Summable fun p : ℕ => if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0) ∧
        ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
          = ∑' p : ℕ, if h : p.Prime then
              ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  ⟨integral_natCast_le', summable_tsum_δ_mul_cardFactors,
    integral_natCast_cardFactorsTamagawaMeasure_val⟩

end WeierstrassCurve
