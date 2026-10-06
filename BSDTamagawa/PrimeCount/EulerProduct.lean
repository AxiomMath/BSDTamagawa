/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The Euler product `F(u)`

For `u ∈ ℂ`, `F(u) := ∏_p (δ_p(1) + (1 - δ_p(1)) u)`, the product over all primes of the affine
local factors built from the scalar local densities `δ_p(1)`. The local factor
`WeierstrassCurve.tamagawaOmegaEulerFactor` is defined in `BSDTamagawa.Defs`.

## Main definitions

* `WeierstrassCurve.tamagawaOmegaEulerProduct`: the Euler product `F(u)`.

## Implementation notes

The product is the topological infinite product `tprod` (`∏'`), not `finprod`: the multiplicative
support of the local factors is infinite for every `u ≠ 1`, so `finprod` would be identically `1`.
At a non-prime index the local factor is `1`, so `∏' p : ℕ` is a product over the primes. The
density `δ_p(1) ∈ [0, 1]` is coerced to `ℂ` inside the local factor, and the complementary factor
`1 - δ_p(1)` is computed in `ℂ`, not in `ℝ≥0∞`.
-/

@[expose] public section

namespace WeierstrassCurve

/-- At a prime index the local factor is `δ_p(1) + (1 - δ_p(1)) u`. -/
lemma tamagawaOmegaEulerFactor_of_prime (p : ℕ) [Fact p.Prime] (u : ℂ) :
    tamagawaOmegaEulerFactor p u =
      ((δ p 1).toReal : ℂ) + (1 - ((δ p 1).toReal : ℂ)) * u :=
  dite_eq_left Fact.out

/-- At a non-prime index the local factor is the neutral value `1`. -/
lemma tamagawaOmegaEulerFactor_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (u : ℂ) :
    tamagawaOmegaEulerFactor p u = 1 :=
  dite_eq_right hp

/-- The Euler product `F(u) := ∏_p (δ_p(1) + (1 - δ_p(1)) u)` for `u : ℂ`, the product over all
primes of the affine local factors built from the scalar local densities `δ_p(1)`. -/
@[bsd_tamagawa "T041b"]
noncomputable def tamagawaOmegaEulerProduct (u : ℂ) : ℂ :=
  ∏' p : ℕ, tamagawaOmegaEulerFactor p u

end WeierstrassCurve
