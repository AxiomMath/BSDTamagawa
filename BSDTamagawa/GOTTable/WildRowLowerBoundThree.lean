/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowLowerBound

/-!
# Lower bounds on a head row at `p = 3` from minimal loci

By `δ_eq_volume_diff_mul_at_three`,

    `δ_3(t) = μ_3((⋃ κ, stratFibre 3 (κ, t)) ∖ range σ_3) · 59049/59048`

with `σ_3 = PadicInt.scaleProdByPPow 4 6`. Hence any set inside this minimal part of the `t`-fibre
contributes its mass, times the storey factor `59049/59048`, to `δ_3(t)`. This file states this for
one locus.

## Main results

* `WeierstrassCurve.subset_headMinimal_at_three`: a locus in one stratum avoiding the dilates lies
  in the minimal part of its row.
* `WeierstrassCurve.le_δ_at_three_of_subset`: the row bound for one locus.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-! ### The minimal part of a head row at `p = 3` -/

/-- **A locus lying in one stratum and avoiding the dilates lies in the minimal part of its
row.** -/
theorem subset_headMinimal_at_three {t : ℕ} {κ : KodairaSymbol} {L : Set (ℤ_[3] × ℤ_[3])}
    (hstrat : L ⊆ stratFibre 3 (κ, t))
    (hmin : ∀ x ∈ L, x ∉ Set.range
      (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3])) :
    L ⊆ (⋃ κ' : KodairaSymbol, stratFibre 3 (κ', t)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  fun x hx => ⟨Set.mem_iUnion.2 ⟨κ, hstrat hx⟩, hmin x hx⟩

/-! ### The row bound for one locus -/

/-- **One locus.** A subset of the minimal part of the `t`-fibre contributes its mass, times the
storey factor, to `δ_3(t)`. The set `L` need not be measurable. -/
theorem le_δ_at_three_of_subset {t : ℕ} {L : Set (ℤ_[3] × ℤ_[3])}
    (hL : L ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, t)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3])) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) L * (59049 / 59048) ≤ δ 3 t := by
  rw [δ_eq_volume_diff_mul_at_three t]
  gcongr

end WeierstrassCurve

end
