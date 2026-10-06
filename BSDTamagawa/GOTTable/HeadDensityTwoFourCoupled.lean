/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityIZeroStarOne

/-!
# The `p ≥ 5` column of `HasGOTDensities` as one identity

At a prime `p ≥ 5` the head densities `δ_p(1)` and `δ_p(3)` equal their Griffin–Ono–Tsai values,
and the head densities `δ_p(0), …, δ_p(4)` have the same total as the table values, so the `t = 2`
and `t = 4` clauses of `HasGOTDensities p` are coupled. This file records the consequence that
`HasGOTDensities p` is equivalent to the single identity
`∑_{n ≥ 1} δ_p((Iₙ*, 2)) = gotInStarTwo p`.

## Main results

* `WeierstrassCurve.hasGOTDensities_iff_tsum_deltaP_InStar_two`: `HasGOTDensities p` holds exactly
  when `∑_{n ≥ 1} δ_p((Iₙ*, 2)) = gotInStarTwo p`.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound

variable {p : ℕ} [Fact p.Prime]

/-! ### The coupling of `t = 2` and `t = 4` -/

/-- **The whole `p ≥ 5` column of `HasGOTDensities`, as an `iff` on one quantity**:

  `HasGOTDensities p ↔ ∑_{n ≥ 1} δ_p((Iₙ*, 2)) = ENNReal.ofReal (gotInStarTwo p)`.

The `p ≥ 5` column holds exactly when the mass of the non-split `Iₙ*` family equals
`gotInStarTwo p`. -/
theorem hasGOTDensities_iff_tsum_deltaP_InStar_two (hp : 5 ≤ p) :
    HasGOTDensities p ↔
      ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2) = ENNReal.ofReal (gotInStarTwo p) :=
  ⟨fun h => (δ_two_eq_ofReal_gotδ_iff_InStar hp).1 (h 2), hasGOTDensities_of_InStar hp⟩

end WeierstrassCurve
