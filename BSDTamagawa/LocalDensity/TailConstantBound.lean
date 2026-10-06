/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.ExplicitTailConstant

/-!
# Conditional bounds on the tail constant `α_p`

For a prime `p`, the tail constant `α_p = p⁵ δ_p(5)` of `WeierstrassCurve.α` satisfies

`α_p < 1/2`  and  `α_p ≥ 1/88572`,

for `p ≥ 5`, granted the scale invariance `WeierstrassCurve.StratScaleInvariant p`, i.e.
`τ_p ∘ σ_p = τ_p` for the dilation `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)`: under that hypothesis `α_p` equals
the closed-form constant `gotα p`, which satisfies both bounds.

## Main results

* `WeierstrassCurve.α_eq_ofReal_gotα_of_stratScaleInvariant`: given `StratScaleInvariant p` and
  `5 ≤ p`, `α_p = gotα p`.
* `WeierstrassCurve.α_bounds_of_stratScaleInvariant`: given `StratScaleInvariant p` and `5 ≤ p`,
  `α_p < 1/2` and `1/88572 ≤ α_p`.

## Implementation notes

The bounds are stated in `ℝ≥0∞` without subtraction: each comparison is transported through
`ENNReal.ofReal` from the corresponding inequality for the real number `gotα p`.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The two `ℝ≥0∞` numerals -/

/-- `ENNReal.ofReal (1/2) = 1/2`. -/
theorem ofReal_one_div_two : ENNReal.ofReal ((1 : ℝ) / 2) = 1 / 2 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-- `ENNReal.ofReal (1/88572) = 1/88572`. -/
theorem ofReal_one_div_88572 : ENNReal.ofReal ((1 : ℝ) / 88572) = 1 / 88572 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-! ### Bounds from `StratScaleInvariant` -/

/-- If `p ≥ 5` and `StratScaleInvariant p` holds, then `α_p = gotα p`, the closed form
`p⁸(p-1)²/(2(p¹⁰-1))`. -/
theorem α_eq_ofReal_gotα_of_stratScaleInvariant (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    α p = ENNReal.ofReal (gotα p) := by
  rw [α_eq_tailConstant_of_stratScaleInvariant hp h, tailConstant_eq_ofReal_gotα hp]

/-- If `p ≥ 5` and `StratScaleInvariant p` holds, then `α_p < 1/2`. -/
theorem α_lt_half_of_stratScaleInvariant (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    α p < 1 / 2 := by
  rw [α_eq_ofReal_gotα_of_stratScaleInvariant hp h, ← ofReal_one_div_two]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (gotα_lt_half (Fact.out : p.Prime))

/-- If `p ≥ 5` and `StratScaleInvariant p` holds, then `1/88572 ≤ α_p`. -/
theorem inv_88572_le_α_of_stratScaleInvariant (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    1 / 88572 ≤ α p := by
  rw [α_eq_ofReal_gotα_of_stratScaleInvariant hp h, ← ofReal_one_div_88572]
  exact ENNReal.ofReal_le_ofReal (inv_88572_le_gotα (Fact.out : p.Prime))

/-- If `p ≥ 5` and `StratScaleInvariant p` holds, then `α_p < 1/2` and `1/88572 ≤ α_p`. -/
theorem α_bounds_of_stratScaleInvariant (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    α p < 1 / 2 ∧ 1 / 88572 ≤ α p :=
  ⟨α_lt_half_of_stratScaleInvariant hp h, inv_88572_le_α_of_stratScaleInvariant hp h⟩

end WeierstrassCurve
