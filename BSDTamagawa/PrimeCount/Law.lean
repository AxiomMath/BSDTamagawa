/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The limiting law `P` of `ω(Tam)` on `ℤ_{≥0}`

The limiting law `P := ∑_{r ≥ 0} π_r δ_r` (`WeierstrassCurve.tamagawaOmegaMeasure`, defined in
`BSDTamagawa.Defs`) is the measure on `ℕ` with mass `π_r` at `r`, where `δ_r` is the Dirac mass at
`r` and `π_r` is the limiting density of curves whose Tamagawa product has exactly `r` distinct
prime factors. Equivalently `P({r}) = π_r` for every `r ≥ 0`.

## Main results

* `WeierstrassCurve.tamagawaOmegaMeasure_singleton`: `P({r}) = ENNReal.ofReal π_r`.

## Implementation notes

The countable sum of measures is `MeasureTheory.Measure.sum`, and the mass at `r` is
`ENNReal.ofReal π_r`, which is faithful since `π_r ≥ 0`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-- `P({r}) = π_r` for every `r ≥ 0`, in the `ℝ≥0∞`-coerced form `ENNReal.ofReal (π_r)`. -/
@[bsd_tamagawa "T041d"]
lemma tamagawaOmegaMeasure_singleton (r : ℕ) :
    tamagawaOmegaMeasure {r} = ENNReal.ofReal (tamagawaOmegaDensity r) := by
  rw [tamagawaOmegaMeasure, Measure.sum_apply _ (measurableSet_singleton r),
    tsum_eq_single r fun c hc => by simp [Measure.dirac_apply' _ (measurableSet_singleton r), hc]]
  simp

end WeierstrassCurve
