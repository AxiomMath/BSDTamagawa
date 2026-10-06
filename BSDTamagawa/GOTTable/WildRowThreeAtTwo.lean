/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowLowerBound

/-!
# The split `IV` locus at `p = 2` lies in the minimal part of the `t = 3` row

The split `IV` locus `iv2Locus` consists of the four residue classes
`(a₄, a₆) ≡ (0,1), (4,1), (3,5), (7,1)` modulo `8`, of mass `4 · 2⁻⁶ = 1/16`. It lies in the
`t = 3` row, and since `a₆` is odd on it while a dilate `σ_2(x)` has `2⁶ ∣ a₆`, it lies in the
minimal part of that row.

## Main results

* `WeierstrassCurve.notMem_range_of_mem_iv2Locus`: no point of the locus is a dilate.
* `WeierstrassCurve.iv2Locus_subset_headMinimal`: the locus lies in the minimal part of the `t = 3`
  row, `(⋃ κ, stratFibre 2 (κ, 3)) ∖ σ_2(ℤ_2²)`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

/-! ### The split `IV` locus is minimal -/

/-- **No point of the split `IV` locus at `2` is a dilate.** On the locus `a₆` is odd
(`headResIVTwo_odd`), whereas `PadicInt.mem_range_scaleProdByPPow_iff` makes `2⁶ ∣ a₆`
necessary. -/
theorem notMem_range_of_mem_iv2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iv2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun hdvd => ?_
  refine headResIVTwo_odd _ _ (mem_iv2Locus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 1 3 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
  exact dvd_trans (dvd_pow_self ((2 : ℕ) : ℤ_[2]) (by norm_num)) hdvd

/-- **The split `IV` locus at `2` lies in the minimal part of the `t = 3` row.** -/
theorem iv2Locus_subset_headMinimal :
    iv2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨iv2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iv2Locus hx⟩

end WeierstrassCurve

end
