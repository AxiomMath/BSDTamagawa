/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.EulerProductHypothesis
public import BSDTamagawa.Moments.MultipliableConditional

/-!
# The Dirichlet series of the Tamagawa density at real exponents

This file collects three facts about the limiting Tamagawa density `P_Tam` and its Dirichlet
series `∑_m P_Tam(m) m^{-s}` at a real exponent `s = -x`: the density vanishes at `0`, the Euler
factor at `-x` is the moment local factor `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x`, and each term
`P_Tam(m) m^x` is real.

## Main results

* `WeierstrassCurve.tamagawaDensity_zero`: `P_Tam(0) = 0`.
* `WeierstrassCurve.tamagawaEulerFactor_neg`: the Euler factor at the exponent `-x` is `G_p(x)`.
* `WeierstrassCurve.ofReal_tamagawaDensity_mul_natCast_cpow`: the terms of the Dirichlet series at
  a real exponent are real.
-/

@[expose] public section

namespace WeierstrassCurve

/-! ### `P_Tam(0) = 0` -/

/-- `P_Tam(0) = 0`: the Tamagawa product is positive, so the fibre over `0` is empty at every
height bound. -/
theorem tamagawaDensity_zero : tamagawaDensity 0 = 0 :=
  tamagawaDensity_eq_of_tendsto
    (by
      rw [show tamagawaProportion 0 = fun _ : ℝ => (0 : ℝ) from funext tamagawaProportion_zero]
      exact tendsto_const_nhds)

/-! ### The Euler factor and the moment local factor -/

/-- The Euler factor of the Tamagawa density at the real exponent `-x` is the moment local factor
`G_p(x)`; both are `∑_{t ≥ 1} δ_p(t) t^{x}`. -/
theorem tamagawaEulerFactor_neg (p : {q : ℕ // q.Prime}) (x : ℝ) :
    tamagawaEulerFactor p (-((x : ℝ) : ℂ)) = momentLocalFactor (p : ℕ) x := by
  have : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  rw [tamagawaEulerFactor, momentLocalFactor_of_prime]
  refine tsum_congr fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp [δ_zero]
  · rw [ite_eq_right ht, neg_neg]

/-- For every `m : ℕ` and real `x`, the `ℂ`-valued term `P_Tam(m) m^{x}` (with `cpow`) is the
coercion of the `ℝ`-valued term `P_Tam(m) m^{x}` (with `rpow`). -/
theorem ofReal_tamagawaDensity_mul_natCast_cpow (m : ℕ) (x : ℝ) :
    (tamagawaDensity m : ℂ) * (m : ℂ) ^ ((x : ℝ) : ℂ)
      = ((tamagawaDensity m * (m : ℝ) ^ x : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast]

end WeierstrassCurve
