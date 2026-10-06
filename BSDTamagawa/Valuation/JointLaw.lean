/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The joint valuation law `P_Π` on `ℤ_{≥0}^Π`

For a finite set of primes `Π`, the joint valuation law of the Tamagawa product is the measure

`P_Π := ∑_{𝐣 ∈ ℤ_{≥0}^Π} Q_Π(𝐣) δ_𝐣`

on `ℤ_{≥0}^Π`, where `δ_𝐣` is the Dirac mass at `𝐣` and `Q_Π(𝐣)` is the limiting joint valuation
density. Equivalently, `P_Π({𝐣}) = Q_Π(𝐣)` for every `𝐣`. The measure
`tamagawaValuationMeasure` is defined in `BSDTamagawa.Defs`.

## Main results

* `WeierstrassCurve.tamagawaValuationMeasure_singleton`: `P_Π({𝐣}) = ENNReal.ofReal (Q_Π(𝐣))`.

## Implementation notes

The multi-index space `ℤ_{≥0}^Π` is `↥Π → ℕ` with the product σ-algebra, in which every singleton
is measurable. The mass at `𝐣` is `ENNReal.ofReal (Q_Π(𝐣))`, which is faithful because
`Q_Π(𝐣) ≥ 0`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-- `P_Π({𝐣}) = Q_Π(𝐣)` for every multi-index `𝐣 ∈ ℤ_{≥0}^Π`, in the form
`ENNReal.ofReal (Q_Π(𝐣))`, the masses of a measure lying in `ℝ≥0∞`. -/
@[bsd_tamagawa "T044i"]
lemma tamagawaValuationMeasure_singleton (P : Finset ℕ) (j : P → ℕ) :
    tamagawaValuationMeasure P {j} = ENNReal.ofReal (tamagawaValuationDensity P j) := by
  rw [tamagawaValuationMeasure, Measure.sum_apply _ (measurableSet_singleton j),
    tsum_eq_single j fun c hc => by
      simp [Measure.dirac_apply' _ (measurableSet_singleton j), hc]]
  simp

end WeierstrassCurve
