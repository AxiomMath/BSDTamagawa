/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.ReductionCount.JointLaw
public import BSDTamagawa.ReductionCount.GeneratingFunctionIdentity

/-!
# The joint law `P_Λ` is a probability measure

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. The joint law `P_Λ = ∑_𝐫 π_Λ(𝐫) δ_𝐫` is a
probability measure: the joint densities `π_Λ(𝐫)` are nonnegative and
`∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫) = 1`. The total mass is obtained by evaluating the generating-function
identity `∑_𝐫 π_Λ(𝐫) 𝐮^𝐫 = F_Λ(𝐮)` at `𝐮 = 𝟏`, where every local factor of `F_Λ` equals `1`.

## Main results

* `WeierstrassCurve.jointReductionOmegaEulerProduct_one`: `F_Λ(𝟏) = 1`.
* `WeierstrassCurve.tsum_jointReductionOmegaDensity_eq_one`: the total mass is `1`.
* `WeierstrassCurve.jointReductionOmegaMeasure_singleton_toReal`: `(P_Λ {𝐫}).toReal = π_Λ(𝐫)`.
* `WeierstrassCurve.isProbabilityMeasure_jointReductionOmegaMeasure`: `P_Λ` is a probability
  measure.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory
open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

variable {Λ : Finset ReductionData}

/-! ### The joint Euler product at `𝐮 = 𝟏` -/

/-- For every index `p : ℕ`, the local factor of `F_Λ` at `𝐮 = 𝟏` is
`1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K)·1 = 1`. -/
theorem jointReductionOmegaEulerFactor_one (Λ : Finset ReductionData) (p : ℕ) :
    jointReductionOmegaEulerFactor Λ p (fun _ => 1) = 1 := by
  rw [jointReductionOmegaEulerFactor_eq_one_add]
  simp

/-- The joint Euler product at the constant vector `𝟏` is `F_Λ(𝟏) = 1`. -/
theorem jointReductionOmegaEulerProduct_one (Λ : Finset ReductionData) :
    jointReductionOmegaEulerProduct Λ (fun _ => 1) = 1 := by
  rw [jointReductionOmegaEulerProduct, tprod_congr (jointReductionOmegaEulerFactor_one Λ),
    tprod_one]

/-! ### The total mass -/

/-- The joint densities `π_Λ(𝐫)` have sum `1`, as a `HasSum`. -/
theorem hasSum_jointReductionOmegaDensity_one (hΛ : Admissible Λ) :
    HasSum (fun r : Λ → ℕ => jointReductionOmegaDensity Λ r) 1 := by
  have h := hasSum_jointReductionOmegaDensity_multiMonomial hΛ fun _ => 1
  rw [jointReductionOmegaEulerProduct_one] at h
  rw [← Complex.hasSum_ofReal, Complex.ofReal_one]
  exact h.congr_fun fun r => by simp [multiMonomial]

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. The joint densities have total mass
exactly `1`:

`∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫) = 1`. -/
@[bsd_tamagawa "T040p"]
theorem tsum_jointReductionOmegaDensity_eq_one (hΛ : Admissible Λ) :
    ∑' r : Λ → ℕ, jointReductionOmegaDensity Λ r = 1 :=
  (hasSum_jointReductionOmegaDensity_one hΛ).tsum_eq

/-! ### The measure -/

/-- `(P_Λ({𝐫})).toReal = π_Λ(𝐫)` for every multi-index `𝐫 ∈ ℤ_{≥0}^Λ`; equivalently, since
`P_Λ({𝐫}) = ENNReal.ofReal (π_Λ(𝐫))`, the density `π_Λ(𝐫)` is nonnegative. -/
@[bsd_tamagawa "T040p"]
theorem jointReductionOmegaMeasure_singleton_toReal (hΛ : Admissible Λ) (r : Λ → ℕ) :
    (jointReductionOmegaMeasure Λ {r}).toReal = jointReductionOmegaDensity Λ r := by
  rw [jointReductionOmegaMeasure_singleton,
    ENNReal.toReal_ofReal (jointReductionOmegaDensity_nonneg hΛ r)]

/-- For a finite set `Λ ⊆ 𝒦 ∖ 𝒦₀` of local reduction data, the joint law `P_Λ = ∑_𝐫 π_Λ(𝐫) δ_𝐫` is
a probability measure on `ℤ_{≥0}^Λ`. -/
@[bsd_tamagawa "T040p"]
theorem isProbabilityMeasure_jointReductionOmegaMeasure (hΛ : Admissible Λ) :
    IsProbabilityMeasure (jointReductionOmegaMeasure Λ) := by
  constructor
  rw [jointReductionOmegaMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (jointReductionOmegaDensity_nonneg hΛ)
      (summable_jointReductionOmegaDensity hΛ),
    tsum_jointReductionOmegaDensity_eq_one hΛ, ENNReal.ofReal_one]

end WeierstrassCurve
