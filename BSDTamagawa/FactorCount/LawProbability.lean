/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.DirichletSeries
public import BSDTamagawa.FactorCount.GeneratingFunctionIdentity
public import BSDTamagawa.FactorCount.Law

/-!
# `P_Ω` is a probability measure

Let `ρ_b` be the limiting frequency of curves `E` with `Ω(Tam(E)) = b`, where `Ω(Tam(E))` is the
number of prime factors of the Tamagawa product counted with multiplicity, and let
`P_Ω = ∑_{b ≥ 0} ρ_b δ_b` be the corresponding measure on `ℕ`. Then `ρ_b ≥ 0` for every `b` and
`∑_{b ≥ 0} ρ_b = 1`, so that `P_Ω` is a probability measure.

## Main results

* `WeierstrassCurve.cardFactorsTamagawaDensity_nonneg`: `ρ_b ≥ 0` for every `b`.
* `WeierstrassCurve.summable_cardFactorsTamagawaDensity`: the family `b ↦ ρ_b` is summable.
* `WeierstrassCurve.tsum_cardFactorsTamagawaDensity_eq_one`: `∑_{b ≥ 0} ρ_b = 1`.
* `WeierstrassCurve.cardFactorsTamagawaMeasure_singleton_toReal`: `(P_Ω {b}).toReal = ρ_b`.
* `WeierstrassCurve.isProbabilityMeasure_cardFactorsTamagawaMeasure`: `P_Ω` is a probability
  measure.

## Implementation notes

The total mass is obtained by evaluating the generating-function identity
`∑_b ρ_b w^b = ∏_p h_p(0, w, ())`, valid on the closed unit disc, at the boundary point `w = 1`.
There the left-hand side is `∑_b ρ_b`, and each local factor `h_p(0, 1, ())` equals the total mass
`∑_{t ≥ 1} δ_p(t) = 1` of the scalar local density, so the Euler product `∏'` is that of the
constant family `1`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-- The density `ρ_b` is nonnegative for every `b ≥ 0`. -/
@[bsd_tamagawa "T046g"]
theorem cardFactorsTamagawaDensity_nonneg (b : ℕ) : 0 ≤ cardFactorsTamagawaDensity b :=
  (hasPolydiscExpansion_cardFactorsTamagawaDensity.1 b).1

/-- The family of densities `b ↦ ρ_b` is summable. -/
theorem summable_cardFactorsTamagawaDensity :
    Summable fun b : ℕ => cardFactorsTamagawaDensity b :=
  hasPolydiscExpansion_cardFactorsTamagawaDensity.2.1

/-- The densities have total mass `∑_{b ≥ 0} ρ_b = 1`. -/
@[bsd_tamagawa "T046g"]
theorem tsum_cardFactorsTamagawaDensity_eq_one :
    ∑' b : ℕ, cardFactorsTamagawaDensity b = 1 := by
  have h := tsum_cardFactorsTamagawaDensity_mul_pow (w := 1) (by simp)
  rw [tprod_scalarLocalFactor_empty_one_zero (fun _ => 0),
    tsum_congr fun b : ℕ => by rw [one_pow, mul_one], ← Complex.ofReal_tsum] at h
  exact_mod_cast h

/-- For every `b ≥ 0`, the real mass `(P_Ω {b}).toReal` of the singleton `{b}` equals `ρ_b`. -/
@[bsd_tamagawa "T046g"]
theorem cardFactorsTamagawaMeasure_singleton_toReal (b : ℕ) :
    (cardFactorsTamagawaMeasure {b}).toReal = cardFactorsTamagawaDensity b := by
  rw [cardFactorsTamagawaMeasure_singleton,
    ENNReal.toReal_ofReal (cardFactorsTamagawaDensity_nonneg b)]

/-- The measure `P_Ω = ∑_{b ≥ 0} ρ_b δ_b` on `ℕ` is a probability measure. -/
@[bsd_tamagawa "T046g"]
instance isProbabilityMeasure_cardFactorsTamagawaMeasure :
    IsProbabilityMeasure cardFactorsTamagawaMeasure := by
  constructor
  rw [cardFactorsTamagawaMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg cardFactorsTamagawaDensity_nonneg
      summable_cardFactorsTamagawaDensity,
    tsum_cardFactorsTamagawaDensity_eq_one, ENNReal.ofReal_one]

end WeierstrassCurve
