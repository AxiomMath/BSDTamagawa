/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.MeanConditional
public import BSDTamagawa.FactorCount.Density
public import BSDTamagawa.FactorCount.LawProbability

/-!
# Ingredients for the mean of `Ω(Tam(E))`, granted the geometric tail law

Let `P = P_Ω` be the limiting law of `Ω(Tam(E))`, the number of prime factors of the Tamagawa
product counted with multiplicity. Granted the geometric tail law `HasTailGeometricLaw q` at every
prime `q`, one expects

`𝔼_P[Ω(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t) < ∞`.

That identity is not proved here; this file sets up ingredients for it. The mean is the left
derivative at `w = 1` of the generating function `∑_b ρ_b w^b`, and for `|w| ≤ 1` this file
identifies that generating function with the scalar Euler product at `Π = ∅`, whose coerced local
factors are the real Euler factors `∑_t δ_p(t) w^{Ω(t)}`. It also packages `P_Ω` as a `PMF ℕ`.

## Main definitions

* `BSDTamagawa.FactorCountMean.omegaExp`: the exponent function `t ↦ Ω(t)`.
* `BSDTamagawa.FactorCountMean.cardFactorsPMF`: the law `P_Ω` as a `PMF ℕ`.

## Main results

* `BSDTamagawa.FactorCountMean.cardFactorsPMF_toMeasure`: the measure of `cardFactorsPMF` is `P_Ω`.
-/

@[expose] public section

namespace BSDTamagawa.FactorCountMean

open Set MeasureTheory WeierstrassCurve BSDTamagawa.ValuationMean

open scoped ENNReal

/-! ### The exponent `Ω` -/

/-- The exponent function `t ↦ Ω(t)`, the number of prime factors of `t` counted with
multiplicity. -/
def omegaExp : ℕ → ℕ := ArithmeticFunction.cardFactors

/-- `omegaExp` unfolded. -/
theorem omegaExp_apply (t : ℕ) : omegaExp t = ArithmeticFunction.cardFactors t := rfl

/-- `Ω(t) ≤ t + 1`, in the `omegaExp` spelling. -/
theorem omegaExp_cast_le : ∀ t, ((omegaExp t : ℕ) : ℝ) ≤ (t : ℝ) + 1 := cardFactors_cast_le

/-- `2^{Ω(t)} ≤ t + 1`, in the `omegaExp` spelling. -/
theorem two_pow_omegaExp_cast_le : ∀ t, (2 : ℝ) ^ (omegaExp t) ≤ (t : ℝ) + 1 :=
  two_pow_cardFactors_cast_le

/-! ### The real Euler product and the complex one -/

/-- For `|w| ≤ 1`, the coerced real Euler factor `∑_t δ_p(t) w^{Ω(t)}` is the scalar local factor
`h_p(0, w, ())` at `Π = ∅`, `s = 0`. -/
theorem ofReal_eulerFactor_eq_scalarLocalFactor (p : ℕ) {w : ℝ} (hw : |w| ≤ 1) :
    ((eulerFactor omegaExp p w : ℝ) : ℂ) = scalarLocalFactor ∅ p 0 (w : ℂ) (fun _ => 0) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [ofReal_eulerFactor_of_prime p _ hw, scalarLocalFactor_empty_zero_of_prime]
    exact tsum_congr fun t => by rw [omegaExp_apply]
  · rw [eulerFactor_of_not_prime hp, scalarLocalFactor_of_not_prime hp]
    norm_num

/-! ### The densities `ρ_b` as a probability mass function -/

/-- The densities `ρ_b` have total mass `1`, as a `HasSum`. -/
theorem hasSum_cardFactorsTamagawaDensity : HasSum cardFactorsTamagawaDensity 1 :=
  tsum_cardFactorsTamagawaDensity_eq_one ▸ summable_cardFactorsTamagawaDensity.hasSum

/-- The real generating series `∑_b ρ_b w^b` converges absolutely for `|w| ≤ 1`. -/
theorem summable_cardFactorsTamagawaDensity_mul_pow {w : ℝ} (hw : |w| ≤ 1) :
    Summable fun b : ℕ => cardFactorsTamagawaDensity b * w ^ b := by
  refine Summable.of_norm_bounded (g := cardFactorsTamagawaDensity)
    summable_cardFactorsTamagawaDensity fun b => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cardFactorsTamagawaDensity_nonneg b), abs_pow]
  exact mul_le_of_le_one_right (cardFactorsTamagawaDensity_nonneg b) (pow_le_one₀ (abs_nonneg w) hw)

/-- For `|w| ≤ 1`, the coerced real generating function `PGFMean.pgf ρ w` is the Euler product
`∏'_p h_p(0, w, ())`. -/
theorem ofReal_pgf_cardFactorsTamagawaDensity {w : ℝ} (hw : |w| ≤ 1) :
    ((PGFMean.pgf cardFactorsTamagawaDensity w : ℝ) : ℂ)
      = ∏' p : ℕ, scalarLocalFactor ∅ p 0 (w : ℂ) (fun _ => 0) := by
  rw [← tsum_cardFactorsTamagawaDensity_mul_pow (w := (w : ℂ)) (by simpa using hw)]
  have hreal : HasSum (fun b : ℕ => cardFactorsTamagawaDensity b * w ^ b)
      (PGFMean.pgf cardFactorsTamagawaDensity w) := by
    rw [PGFMean.pgf]
    exact (summable_cardFactorsTamagawaDensity_mul_pow hw).hasSum
  refine ((Complex.hasSum_ofReal.mpr hreal).tsum_eq).symm.trans ?_
  exact tsum_congr fun b => by push_cast; ring

/-- The law `P_Ω` as a `PMF ℕ`, with mass `ENNReal.ofReal ρ_b` at `b`. -/
noncomputable def cardFactorsPMF : PMF ℕ :=
  ⟨fun b : ℕ => ENNReal.ofReal (cardFactorsTamagawaDensity b), by
    have h : ∑' b : ℕ, ENNReal.ofReal (cardFactorsTamagawaDensity b) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg cardFactorsTamagawaDensity_nonneg
        summable_cardFactorsTamagawaDensity, tsum_cardFactorsTamagawaDensity_eq_one,
        ENNReal.ofReal_one]
    exact h ▸ ENNReal.summable.hasSum⟩

/-- The mass at `b`, read back in `ℝ`, is the density `ρ_b` itself. -/
theorem toReal_cardFactorsPMF_apply (b : ℕ) :
    (cardFactorsPMF b).toReal = cardFactorsTamagawaDensity b :=
  ENNReal.toReal_ofReal (cardFactorsTamagawaDensity_nonneg b)

/-- `toReal_cardFactorsPMF_apply` as an equality of functions. -/
theorem toReal_cardFactorsPMF :
    (fun b : ℕ => (cardFactorsPMF b).toReal) = cardFactorsTamagawaDensity :=
  funext toReal_cardFactorsPMF_apply

/-- The measure of `cardFactorsPMF` is `P_Ω = ∑_b ρ_b δ_b`. -/
theorem cardFactorsPMF_toMeasure : cardFactorsPMF.toMeasure = cardFactorsTamagawaMeasure := by
  rw [cardFactorsTamagawaMeasure]
  conv_lhs => rw [← Measure.sum_smul_dirac cardFactorsPMF.toMeasure]
  simp_rw [cardFactorsPMF.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  rfl

end BSDTamagawa.FactorCountMean
