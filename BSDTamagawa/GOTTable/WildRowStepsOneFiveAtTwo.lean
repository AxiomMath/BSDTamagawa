/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityWildIVNonSplit

/-!
# The Steps 1–5 loci of the `t = 1` and `t = 2` rows at `p = 2`

Steps 1–5 of Tate's algorithm decide loci of the `t = 1` and `t = 2` rows at `2`: the merged
`t = 1` locus of types `II` and non-split `IV`, and the type-`III` locus, with `t = 2`.
A `(2⁴, 2⁶)`-dilate has `4 ∣ a₄` and `4 ∣ a₆`, so its class modulo `4` is `(0, 0)`; since `(0, 0)`
lies on neither locus, each locus lies in the minimal part of its fibre.

## Main results

* `WeierstrassCurve.notMem_range_scaleProdByPPow_of_toZModPow_ne_zero`: a pair whose class modulo
  `2ᵏ` is not `(0, 0)`, for any `k ≤ 4`, is not a dilate.
* `WeierstrassCurve.one2Locus_subset_headMinimal`,
  `WeierstrassCurve.iii2LocusFull_subset_headMinimal`: the merged `t = 1` locus and the type-`III`
  locus lie in the minimal parts of their fibres.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Minimality from a shallow residue class

A `(2⁴, 2⁶)`-dilate has `2⁴ ∣ a₄` and `2⁶ ∣ a₆`. Both exponents are at least `k` for any `k ≤ 4`,
so the class of a dilate modulo `2ᵏ` is `(0, 0)`. -/

/-- **A pair whose class modulo `2ᵏ` is not `(0, 0)` is not a dilate**, for any `k ≤ 4`. -/
theorem notMem_range_scaleProdByPPow_of_toZModPow_ne_zero {k : ℕ} (hk : k ≤ 4)
    {x : ℤ_[2] × ℤ_[2]} (h : ¬ (PadicInt.toZModPow k x.1 = 0 ∧ PadicInt.toZModPow k x.2 = 0)) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine fun hx => h ?_
  obtain ⟨h4, h6⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hx
  refine ⟨?_, ?_⟩
  · rw [← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    exact (pow_dvd_pow ((2 : ℕ) : ℤ_[2]) hk).trans h4
  · rw [← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    exact (pow_dvd_pow ((2 : ℕ) : ℤ_[2]) (hk.trans (by norm_num))).trans h6

/-! ### Each locus lies in the minimal part of its row -/

/-- The zero class modulo `4` is not a type-`III` class. -/
theorem not_headResIIITwo_zero : ¬ HeadResIIITwo 0 0 := by decide

/-- The zero class modulo `8` is on neither `t = 1` cell. -/
theorem not_headResOneTwo_zero : ¬ HeadResOneTwo 0 0 := by decide

/-- **The merged locus `II ∪ IV`-non-split at `2` lies in the minimal part of the `t = 1` row.**
-/
theorem one2Locus_subset_headMinimal :
    one2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine fun x hx => ⟨one2Locus_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero (k := 3) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_one2Locus_iff.1 hx
  rw [h1, h2] at h
  exact not_headResOneTwo_zero h

/-- **The full type-`III` locus at `2` lies in the minimal part of the `t = 2` row.** -/
theorem iii2LocusFull_subset_headMinimal :
    iii2LocusFull ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine fun x hx => ⟨iii2LocusFull_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero (k := 2) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_iii2LocusFull_iff.1 hx
  rw [h1, h2] at h
  exact not_headResIIITwo_zero h

end WeierstrassCurve

end
