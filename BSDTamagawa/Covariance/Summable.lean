/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.Mean
public import BSDTamagawa.Covariance.Formula
public import BSDTamagawa.Covariance.PrimeFactorConditional

/-!
# Convergence of the covariance series of `ω_Tam` and `Ω(Tam)`, and the variance of `Ω(Tam)`

The series `∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)` converges absolutely. Through the Euler product
`∏_p ∑_t δ_p(t) w^{Ω(t)}` for the probability generating function of `Ω(Tam(E))`, the law
`cardFactorsPMF` of `Ω(Tam(E))` is square integrable with

  `Var(Ω(Tam(E))) = ∑_p ( ∑_t δ_p(t) Ω(t)² - (∑_t δ_p(t) Ω(t))² )`,

and so is the limiting law `P_Ω`.

## Main results

* `WeierstrassCurve.summable_abs_δ_one_mul_tsum_δ_mul_cardFactors`:
  `∑_p |δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)| < ∞`.
* `BSDTamagawa.PrimeFactorCovarianceUnconditional.variance_cardFactorsPMF'`: the variance formula
  above, against `cardFactorsPMF`.
* `WeierstrassCurve.memLp_two_natCast_cardFactorsTamagawaMeasure`: `Ω(Tam(E))` is square integrable
  under `P_Ω`.
-/

@[expose] public section

namespace BSDTamagawa.PrimeFactorCovarianceUnconditional

open Set MeasureTheory ProbabilityTheory
open WeierstrassCurve BSDTamagawa.ValuationMean BSDTamagawa.ValuationMeanUnconditional
open BSDTamagawa.FactorCountMean BSDTamagawa.CovarianceFormula BSDTamagawa.PrimeFactorCovariance

/-- The series `∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)` is summable. -/
theorem summable_covSeriesTerm' : Summable covSeriesTerm :=
  Summable.of_nonneg_of_le covSeriesTerm_nonneg covSeriesTerm_le
    (summable_eulerMoment (k := omegaExp) fun q _ hq => tsum_δ_mul_cardFactors_le q hq)

/-- On `[1 - windowRadius omegaExp, 1]` the probability generating function of `Ω(Tam(E))` equals
the Euler product `∏_p ∑_t δ_p(t) w^{Ω(t)}`. -/
theorem pgf_eq_prodG_primeFactor' {w : ℝ} (hw : w ∈ Icc (1 - windowRadius omegaExp) 1) :
    PGFMean.pgf cardFactorsTamagawaDensity w = LogDerivProduct.prodG (primeFactor omegaExp) w := by
  have hη : windowRadius omegaExp ≤ 1 := min_le_left _ _
  have habs : |w| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hw.1], hw.2⟩
  have hnorm : ‖(w : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hmap := (LogDerivProduct.hasProd_prodG (prodHyp_primeFactor' two_pow_omegaExp_le) hw).map
    Complex.ofRealHom Complex.continuous_ofReal
  have hfac : ∀ q : {n : ℕ // n.Prime},
      (Complex.ofRealHom (primeFactor omegaExp q w))
        = ∑' t : ℕ, ((@δ (q : ℕ) ⟨q.2⟩ t).toReal : ℂ)
            * (w : ℂ) ^ ArithmeticFunction.cardFactors t := by
    intro q
    have : Fact (q : ℕ).Prime := ⟨q.2⟩
    rw [primeFactor_eq_eulerFactor]
    exact ofReal_eulerFactor_of_prime (q : ℕ) omegaExp habs
  have hprod := (hmap.congr_fun fun q => (hfac q).symm).tprod_eq
  have hleft := ofReal_pgf_cardFactorsTamagawaDensity habs
  refine Complex.ofReal_inj.mp ?_
  rw [hleft, ← tprod_cardFactorsEulerFactor_primes hnorm (fun _ => 0)]
  exact hprod

/-- `Var(Ω(Tam(E))) = ∑_{p prime} (S_p - m_p²)` against `cardFactorsPMF`, with
`m_p = ∑_t δ_p(t) Ω(t)` and `S_p = ∑_t δ_p(t) Ω(t)²`. -/
theorem variance_cardFactorsPMF' :
    variance (fun n : ℕ => (n : ℝ)) cardFactorsPMF.toMeasure
      = ∑' q : {n : ℕ // n.Prime},
          (primeMoment2 omegaExp q - primeMoment1 omegaExp q ^ 2) := by
  refine variance_of_pgf' two_pow_omegaExp_le fun w hw => ?_
  rw [toReal_cardFactorsPMF]
  exact pgf_eq_prodG_primeFactor' hw

/-- `Ω(Tam(E))` is square integrable against `cardFactorsPMF`. -/
theorem memLp_two_cardFactorsPMF' :
    MemLp (fun n : ℕ => (n : ℝ)) 2 cardFactorsPMF.toMeasure := by
  refine memLp_two_of_pgf' two_pow_omegaExp_le fun w hw => ?_
  rw [toReal_cardFactorsPMF]
  exact pgf_eq_prodG_primeFactor' hw

end BSDTamagawa.PrimeFactorCovarianceUnconditional

namespace WeierstrassCurve

open MeasureTheory ProbabilityTheory
open BSDTamagawa.ValuationMean BSDTamagawa.FactorCountMean BSDTamagawa.PrimeFactorCovariance
open BSDTamagawa.PrimeFactorCovarianceUnconditional

/-- The series `∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)` converges absolutely:

  `∑_{p prime} |δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)| < ∞`. -/
theorem summable_abs_δ_one_mul_tsum_δ_mul_cardFactors :
    Summable fun p : ℕ => |if h : p.Prime then
      (@δ p ⟨h⟩ 1).toReal
        * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
      else 0| :=
  summable_covSeriesTerm'.congr fun p => (abs_of_nonneg (covSeriesTerm_nonneg p)).symm

/-- `Ω(Tam(E))` is square integrable under its limiting law `P_Ω`. -/
theorem memLp_two_natCast_cardFactorsTamagawaMeasure :
    MemLp (fun n : ℕ => (n : ℝ)) 2 cardFactorsTamagawaMeasure := by
  rw [← cardFactorsPMF_toMeasure]
  exact memLp_two_cardFactorsPMF'

end WeierstrassCurve
