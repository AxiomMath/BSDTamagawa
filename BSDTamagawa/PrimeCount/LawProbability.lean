/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.PrimeCount.Law
public import BSDTamagawa.PrimeCount.GeneratingFunctionIdentity

/-!
# `P` is a probability measure

The limiting law `P = ∑_{r ≥ 0} π_r δ_r` of the Tamagawa exponent `ω_Tam` is a probability measure:
the limiting densities `π_r` are nonnegative and `∑_{r ≥ 0} π_r = 1`.

## Main results

* `WeierstrassCurve.tamagawaOmegaEulerProduct_one`: the Euler product satisfies `F(1) = 1`.
* `WeierstrassCurve.tsum_tamagawaOmegaDensity_eq_one`: `∑_{r ≥ 0} π_r = 1`.
* `WeierstrassCurve.tamagawaOmegaMeasure_singleton_toReal`: `(P {r}).toReal = π_r` for every
  `r ≥ 0`.
* `WeierstrassCurve.isProbabilityMeasure_tamagawaOmegaMeasure`: `P` is a probability measure.

The total mass is obtained by evaluating the identity `∑_{r ≥ 0} π_r u^r = F(u)` at `u = 1`, where
every local factor equals `1`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-! ### The Euler product at `u = 1` -/

/-- For every index `p : ℕ`, the local factor of the Euler product `F` at `u = 1` is
`δ_p(1) + (1 - δ_p(1))·1 = 1`. -/
@[simp]
theorem tamagawaOmegaEulerFactor_one (p : ℕ) : tamagawaOmegaEulerFactor p 1 = 1 := by
  rw [tamagawaOmegaEulerFactor_eq_one_add]
  simp

/-- The Euler product satisfies `F(1) = 1`. -/
@[simp]
theorem tamagawaOmegaEulerProduct_one : tamagawaOmegaEulerProduct 1 = 1 := by
  rw [tamagawaOmegaEulerProduct, tprod_congr tamagawaOmegaEulerFactor_one, tprod_one]

/-! ### The total mass -/

/-- The limiting densities `π_r` have sum `1`. -/
theorem hasSum_tamagawaOmegaDensity_one : HasSum (fun r : ℕ => tamagawaOmegaDensity r) 1 := by
  have h := hasSum_tamagawaOmegaDensity_mul_pow 1
  rw [tamagawaOmegaEulerProduct_one] at h
  rw [← Complex.hasSum_ofReal, Complex.ofReal_one]
  exact h.congr_fun fun r => by simp

/-- The limiting densities `π_r` are summable. -/
theorem summable_tamagawaOmegaDensity : Summable fun r : ℕ => tamagawaOmegaDensity r :=
  hasSum_tamagawaOmegaDensity_one.summable

/-- The limiting densities satisfy `∑_{r ≥ 0} π_r = 1`. -/
@[bsd_tamagawa "T041m"]
theorem tsum_tamagawaOmegaDensity_eq_one : ∑' r : ℕ, tamagawaOmegaDensity r = 1 :=
  hasSum_tamagawaOmegaDensity_one.tsum_eq

/-! ### The measure -/

/-- For every `r ≥ 0`, the mass of `P` at `r` recovers the density: `(P({r})).toReal = π_r`. -/
@[bsd_tamagawa "T041m"]
theorem tamagawaOmegaMeasure_singleton_toReal (r : ℕ) :
    (tamagawaOmegaMeasure {r}).toReal = tamagawaOmegaDensity r := by
  rw [tamagawaOmegaMeasure_singleton, ENNReal.toReal_ofReal (tamagawaOmegaDensity_mem_Icc r).1]

/-- The limiting law `P = ∑_{r ≥ 0} π_r δ_r` is a probability measure on `ℤ_{≥0}`. -/
@[bsd_tamagawa "T041m"]
instance isProbabilityMeasure_tamagawaOmegaMeasure : IsProbabilityMeasure tamagawaOmegaMeasure := by
  constructor
  rw [tamagawaOmegaMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => (tamagawaOmegaDensity_mem_Icc r).1)
      summable_tamagawaOmegaDensity,
    tsum_tamagawaOmegaDensity_eq_one, ENNReal.ofReal_one]

end WeierstrassCurve
