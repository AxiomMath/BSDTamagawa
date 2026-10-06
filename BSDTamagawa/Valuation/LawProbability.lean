/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.GeneratingFunctionIdentity
public import BSDTamagawa.Valuation.JointLaw

/-!
# `P_Π` is a probability measure

Let `Π` be a finite set of primes. The joint valuation law `P_Π = ∑_𝐣 Q_Π(𝐣) δ_𝐣` is a probability
measure: the joint valuation densities `Q_Π(𝐣)` are nonnegative and

`∑_{𝐣 ∈ ℤ_{≥0}^Π} Q_Π(𝐣) = 1`.

## Main results

* `WeierstrassCurve.scalarLocalFactor_zero_one_one_of_prime`: the scalar local factor satisfies
  `h_p(0, 1, 𝟏) = ∑_{t ≥ 1} δ_p(t) = 1` at every prime `p`.
* `WeierstrassCurve.tprod_scalarLocalFactor_zero_one_one`: the scalar Euler product
  `∏_p h_p(0, 1, 𝟏)` equals `1`.
* `WeierstrassCurve.tsum_tamagawaValuationDensity_eq_one`: the joint valuation densities have total
  mass `1`.
* `WeierstrassCurve.tamagawaValuationMeasure_singleton_toReal`: `(P_Π {𝐣}).toReal = Q_Π(𝐣)` for
  every multi-index `𝐣`.
* `WeierstrassCurve.isProbabilityMeasure_tamagawaValuationMeasure`: `P_Π` is a probability measure.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory
open BSDTamagawa.MultiIndex

/-! ### The scalar Euler product at `s = 0`, `w = 1`, `𝐳 = 𝟏` -/

/-- The scalar weight is identically `1` at `s = 0`, `w = 1`, `𝐳 = 𝟏`: for every `t : ℕ`, including
`t = 0`,

`ψ_{0, 1, 𝟏}(t) = 1^{Ω(t)} (∏_{ℓ ∈ Π} 1^{v_ℓ(t)}) t^{-0} = 1`. -/
theorem scalarWeight_zero_one_one (P : Finset ℕ) (t : ℕ) :
    scalarWeight P 0 1 (fun _ => 1) t = 1 := by
  simp [scalarWeight, multiMonomial]

/-- At a prime `p`, the scalar local factor at `s = 0`, `w = 1`, `𝐳 = 𝟏` equals `1`:

`h_p(0, 1, 𝟏) = ∑_{t ≥ 1} δ_p(t) = 1`. -/
theorem scalarLocalFactor_zero_one_one_of_prime (P : Finset ℕ) (p : ℕ) [Fact p.Prime] :
    scalarLocalFactor P p 0 1 (fun _ => 1) = 1 := by
  have hne : ∀ t : ℕ, δ p t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (by simp [tsum_δ]) (ENNReal.le_tsum t)
  have hreal : ∑' t : ℕ, (δ p t).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hne, tsum_δ, ENNReal.toReal_one]
  rw [scalarLocalFactor_eq_tsum_of_prime,
    tsum_congr fun t : ℕ => by rw [scalarWeight_zero_one_one, mul_one],
    ← Complex.ofReal_tsum, hreal, Complex.ofReal_one]

/-- The scalar Euler product at `s = 0`, `w = 1`, `𝐳 = 𝟏` equals `1`:
`∏'_p h_p(0, 1, 𝟏) = 1`. -/
theorem tprod_scalarLocalFactor_zero_one_one (P : Finset ℕ) :
    ∏' p : ℕ, scalarLocalFactor P p 0 1 (fun _ => 1) = 1 := by
  rw [tprod_congr fun p : ℕ => ?_, tprod_one]
  by_cases hp : p.Prime
  · exact @scalarLocalFactor_zero_one_one_of_prime P p ⟨hp⟩
  · exact scalarLocalFactor_of_not_prime hp 0 1 _

/-! ### The total mass -/

/-- Let `Π` be a finite set of primes. The joint valuation densities sum to `1`:

`∑_{𝐣 ∈ ℤ_{≥0}^Π} Q_Π(𝐣) = 1`. -/
@[bsd_tamagawa "T044h"]
theorem tsum_tamagawaValuationDensity_eq_one (P : Finset ℕ) (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) :
    ∑' g : P → ℕ, tamagawaValuationDensity P g = 1 := by
  have h := tsum_tamagawaValuationDensity_mul_multiMonomial P hP
    (z := fun _ : P => (1 : ℂ)) fun _ => by simp
  rw [tprod_scalarLocalFactor_zero_one_one P,
    tsum_congr fun g : P → ℕ => (by simp [multiMonomial] :
      ((tamagawaValuationDensity P g : ℝ) : ℂ) * multiMonomial g (fun _ => 1)
        = ((tamagawaValuationDensity P g : ℝ) : ℂ)),
    ← Complex.ofReal_tsum] at h
  exact_mod_cast h

/-! ### The measure -/

/-- Let `Π` be a finite set of primes. For every multi-index `𝐣 ∈ ℤ_{≥0}^Π`, the mass of `P_Π` at
`𝐣` is the joint valuation density: `(P_Π {𝐣}).toReal = Q_Π(𝐣)`. -/
@[bsd_tamagawa "T044h"]
theorem tamagawaValuationMeasure_singleton_toReal (P : Finset ℕ) (hP : ∀ ℓ ∈ P, Nat.Prime ℓ)
    (j : P → ℕ) :
    (tamagawaValuationMeasure P {j}).toReal = tamagawaValuationDensity P j := by
  rw [tamagawaValuationMeasure_singleton,
    ENNReal.toReal_ofReal ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 j).1]

/-- For a finite set of primes `Π`, the joint valuation law `P_Π = ∑_𝐣 Q_Π(𝐣) δ_𝐣` is a probability
measure on `ℤ_{≥0}^Π`. -/
@[bsd_tamagawa "T044h"]
theorem isProbabilityMeasure_tamagawaValuationMeasure (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) : IsProbabilityMeasure (tamagawaValuationMeasure P) := by
  constructor
  rw [tamagawaValuationMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun g => ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 g).1)
      (hasPolydiscExpansion_tamagawaValuationDensity P hP).2.1,
    tsum_tamagawaValuationDensity_eq_one P hP, ENNReal.ofReal_one]

end WeierstrassCurve
