/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.RunInvarianceAtThree
public import BSDTamagawa.NumberTheory.TailConstantThree

/-!
# The geometric tail and the tail constant at `p = 3`

At the prime `p = 3` the local Tamagawa densities have the geometric tail
`δ₃(t) = 1/(3^{t+1} · 29524)` for every `t ≥ 5`, and the tail constant is `α₃ = 1/(3 · 29524)`.
These follow from the conditional versions in `TailConstantThree` together with the scale
invariance `stratScaleInvariant_three`.

## Main results

* `δ_eq_ofReal_three_of_eq_three`: `δ₃(t) = (1/(3 · 29524)) · 3^{-t}` for `t ≥ 5`.
* `α_eq_ofReal_three_of_eq_three`: `α₃ = 1/(3 · 29524)`.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- For every `t ≥ 5`, `δ₃(t) = (1/(3 · 29524)) · 3^{-t}`, that is,
`δ₃(t) = 1/(3^{t+1} · 29524)`. -/
theorem δ_eq_ofReal_three_of_eq_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = ENNReal.ofReal (1 / (3 * 29524)) * ((p : ℝ≥0∞)⁻¹) ^ t :=
  δ_eq_ofReal_three hp3 (stratScaleInvariant_three hp3) ht

/-- The tail constant at `p = 3` is `α₃ = 1/(3 · 29524)`. -/
theorem α_eq_ofReal_three_of_eq_three (hp3 : p = 3) :
    α p = ENNReal.ofReal (1 / (3 * 29524)) :=
  α_eq_ofReal_three hp3 (stratScaleInvariant_three hp3)

end WeierstrassCurve
