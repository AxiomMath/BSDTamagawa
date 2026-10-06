/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarLocalFactor

/-!
# The moment local factor

For a prime `p` and a real number `x`, the moment local factor is `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x`,
the scalar local densities `δ_p(t)` summed against `t^x`. It is the scalar local factor
`h_p(-x, 1, ())` at the empty parameter set, `w = 1` and `s = -x`, where the scalar weight
degenerates to `1^{Ω(t)} · 1 · t^{-(-x)} = t^x`. The definition
`WeierstrassCurve.momentLocalFactor` lives in `BSDTamagawa.Defs`.

## Main results

* `WeierstrassCurve.momentLocalFactor_of_prime`: at a prime, `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x`.
* `WeierstrassCurve.momentLocalFactor_of_not_prime`: at a non-prime index, `G_p(x) = 1`.

## Implementation notes

The value is `ℂ`-valued, with `x` entering through `(t : ℂ) ^ ((x : ℝ) : ℂ)`. The `t = 0` term is
excluded explicitly: at `x = 0` Mathlib's convention `0^0 = 1` would otherwise add `δ_p(0)`, which
vanishes anyway. The sum is the total `tsum`, so no convergence is asserted by the definition. For
`x > 0` the exponent `s = -x` has negative real part, so `G_p(x)` lies outside the polydisc on
which the scalar local factor is estimated.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- At a prime index the moment local factor is `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x`. -/
@[bsd_tamagawa "T059d"]
lemma momentLocalFactor_of_prime (p : ℕ) [Fact p.Prime] (x : ℝ) :
    momentLocalFactor p x =
      ∑' t : ℕ, if t = 0 then 0 else ((δ p t).toReal : ℂ) * (t : ℂ) ^ (x : ℂ) := by
  rw [momentLocalFactor, scalarLocalFactor_of_prime]
  refine tsum_congr fun t => ?_
  split
  · rfl
  · rw [scalarWeight]
    simp [multiMonomial]

/-- At a non-prime index the moment local factor is the neutral value `1`. -/
lemma momentLocalFactor_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (x : ℝ) :
    momentLocalFactor p x = 1 :=
  scalarLocalFactor_of_not_prime hp _ _ _

end WeierstrassCurve
