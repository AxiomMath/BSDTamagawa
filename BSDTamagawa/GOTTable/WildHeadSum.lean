/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityByDifference

/-!
# The exact head total

For every prime `p`, the four head values of the Tamagawa density satisfy
`δ_p(1) + δ_p(2) + δ_p(3) + δ_p(4) = gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4`, the complement of
the geometric tail mass. As a consequence, `HasGOTDensities p` follows from the three head values
`t = 1, 2, 3`.

## Main results

* `δ_headSum_eq_ofReal_gotδ_headSum`: the four head values of `δ p` total the corresponding four
  table values.
* `hasGOTDensities_of_one_two_three`: `HasGOTDensities p` follows from the three head values
  `t = 1, 2, 3`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*, Quart. J. Math.
  72 (2021).
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

/-! ### The exact head total -/

variable {p : ℕ} [Fact p.Prime]

/-- At every prime `p`, `δ p 1 + δ p 2 + δ p 3 + δ p 4` equals
`ENNReal.ofReal (gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4)`. -/
theorem δ_headSum_eq_ofReal_gotδ_headSum :
    δ p 1 + δ p 2 + δ p 3 + δ p 4
      = ENNReal.ofReal (gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4) := by
  have hprime : p.Prime := Fact.out
  have hnn : ∀ t : ℕ, (0 : ℝ) ≤ gotδ p t := fun _ => gotδ_nonneg hprime
  have key := δ_head_sum_eq_gotδ_head_sum (p := p)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, δ_zero, gotδ_zero,
    ENNReal.ofReal_zero, zero_add] at key
  rw [key, ← ENNReal.ofReal_add (hnn 1) (hnn 2),
    ← ENNReal.ofReal_add (add_nonneg (hnn 1) (hnn 2)) (hnn 3),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hnn 1) (hnn 2)) (hnn 3)) (hnn 4)]

/-! ### `HasGOTDensities` from `t = 1, 2, 3` -/

/-- At every prime `p`, if `δ p t = ENNReal.ofReal (gotδ p t)` for `t = 1, 2, 3`, then
`HasGOTDensities p` holds. -/
theorem hasGOTDensities_of_one_two_three
    (h1 : δ p 1 = ENNReal.ofReal (gotδ p 1)) (h2 : δ p 2 = ENNReal.ofReal (gotδ p 2))
    (h3 : δ p 3 = ENNReal.ofReal (gotδ p 3)) :
    HasGOTDensities p :=
  hasGOTDensities_of_three_heads h2 h3 (δ_four_eq_ofReal_gotδ_of_one_two_three h1 h2 h3)

end WeierstrassCurve
