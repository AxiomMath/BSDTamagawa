/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The measure `P_Ω` on `ℤ_{≥0}`

`P_Ω := ∑_{b ≥ 0} ρ_b δ_b` is the measure on `ℤ_{≥0} = ℕ` with mass `ρ_b` at `b`, where `δ_b` is
the Dirac mass at `b` and `ρ_b` is the limiting density of `Ω(Tam(E))`. It is
`WeierstrassCurve.cardFactorsTamagawaMeasure`, defined in `BSDTamagawa.Defs` as a
`MeasureTheory.Measure.sum` with coefficients `ENNReal.ofReal ρ_b`.

## Main results

* `WeierstrassCurve.cardFactorsTamagawaMeasure_singleton`: `P_Ω({b}) = ENNReal.ofReal ρ_b`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-- `P_Ω({b}) = ρ_b` for every `b ≥ 0`, in the `ℝ≥0∞`-coerced form `ENNReal.ofReal (ρ_b)`. -/
@[bsd_tamagawa "T046h"]
lemma cardFactorsTamagawaMeasure_singleton (b : ℕ) :
    cardFactorsTamagawaMeasure {b} = ENNReal.ofReal (cardFactorsTamagawaDensity b) := by
  rw [cardFactorsTamagawaMeasure, Measure.sum_apply _ (measurableSet_singleton b),
    tsum_eq_single b fun c hc => by simp [Measure.dirac_apply' _ (measurableSet_singleton b), hc]]
  simp

end WeierstrassCurve
