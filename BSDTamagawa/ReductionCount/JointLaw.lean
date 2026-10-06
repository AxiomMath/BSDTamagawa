/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The joint law `P_Λ` on `ℤ_{≥0}^Λ`

For a finite set `Λ` of local reduction data, the joint law is the measure
`P_Λ := ∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫) δ_𝐫` on `ℤ_{≥0}^Λ = ↥Λ → ℕ`, where `δ_𝐫` is the Dirac mass at `𝐫`
and `π_Λ(𝐫)` is the limiting joint density. It is defined in `BSDTamagawa.Defs` as
`WeierstrassCurve.jointReductionOmegaMeasure`, using `MeasureTheory.Measure.sum` and the masses
`ENNReal.ofReal (π_Λ(𝐫))`.

## Main results

* `WeierstrassCurve.jointReductionOmegaMeasure_singleton`: `P_Λ({𝐫}) = π_Λ(𝐫)`, in the form
  `ENNReal.ofReal (π_Λ(𝐫))`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-- `P_Λ({𝐫}) = ENNReal.ofReal (π_Λ(𝐫))` for every multi-index `𝐫 ∈ ℤ_{≥0}^Λ`. -/
@[bsd_tamagawa "T040g"]
lemma jointReductionOmegaMeasure_singleton (Λ : Finset (KodairaSymbol × ℕ))
    (r : Λ → ℕ) :
    jointReductionOmegaMeasure Λ {r} = ENNReal.ofReal (jointReductionOmegaDensity Λ r) := by
  rw [jointReductionOmegaMeasure, Measure.sum_apply _ (measurableSet_singleton r),
    tsum_eq_single r fun c hc => by
      simp [Measure.dirac_apply' _ (measurableSet_singleton r), hc]]
  simp

end WeierstrassCurve
