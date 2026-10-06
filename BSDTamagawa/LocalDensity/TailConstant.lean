/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.SplitMultiplicativeTail

/-!
# The tail constant `α_p`

For a prime `p`, let `δ_p(t)` be the scalar local density: the measure of the set of nonsingular
short Weierstrass models over `ℤ_p` whose local Tamagawa number is `t`. The tail constant is
`α_p := p⁵ δ_p(5)`, normalised so that the geometric tail law reads `δ_p(t) = α_p p^{-t}` for
`t ≥ 5`. This file defines `α_p` and records that `p⁵` is a nonzero, finite element of `ℝ≥0∞`.

## Main definitions

* `WeierstrassCurve.α`: the tail constant `α_p := p⁵ δ_p(5)`.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The tail constant -/

variable (p) in
/-- The tail constant `α_p := p⁵ δ_p(5)`. -/
noncomputable def α : ℝ≥0∞ := (p : ℝ≥0∞) ^ 5 * δ p 5

/-- `p ^ 5` is a nonzero, finite element of `ℝ≥0∞`. -/
theorem pow_five_ne_zero_and_ne_top :
    (p : ℝ≥0∞) ^ 5 ≠ 0 ∧ (p : ℝ≥0∞) ^ 5 ≠ ⊤ := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    simpa using (Fact.out : p.Prime).pos.ne'
  exact ⟨pow_ne_zero 5 hp0, by simp⟩

end WeierstrassCurve
