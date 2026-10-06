/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityWildIVNonSplit

/-!
# The Steps 1–5 loci of the `p = 3` column lie in the minimal part

Steps 1–5 of Tate's algorithm at `3` decide good reduction, type `II` and non-split type `IV`, all
with `t = 1`; type `III`, with `t = 2`; and split type `IV`, with `t = 3`. A `(3⁴, 3⁶)`-dilate has
`9 ∣ a₄` and `9 ∣ a₆`, so its class modulo `9` is `(0, 0)`, which lies on none of these loci. This
file shows that the merged `t = 1` locus, the type-`III` locus and the split type-`IV` locus each
lie in the minimal part of their row, that is, in their stratum and outside the range of the
dilation.

## Main results

* `WeierstrassCurve.notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three`: a pair whose class
  modulo `3ᵏ` is not `(0, 0)`, for any `k ≤ 4`, is not a dilate.
* `WeierstrassCurve.one3LocusFull_subset_headMinimal`,
  `WeierstrassCurve.iii3Locus_subset_headMinimal` and
  `WeierstrassCurve.iv3Locus_subset_headMinimal`: each locus lies in the minimal part of its row.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Minimality from a shallow residue class

A `(3⁴, 3⁶)`-dilate has `3⁴ ∣ a₄` and `3⁶ ∣ a₆`. Both exponents are at least `k` for any `k ≤ 4`,
so the class of a dilate modulo `3ᵏ` is `(0, 0)`. -/

/-- **A pair whose class modulo `3ᵏ` is not `(0, 0)` is not a dilate**, for any `k ≤ 4`. -/
theorem notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three {k : ℕ} (hk : k ≤ 4)
    {x : ℤ_[3] × ℤ_[3]}
    (h : ¬ (PadicInt.toZModPow k x.1 = 0 ∧ PadicInt.toZModPow k x.2 = 0)) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun hx => h ?_
  obtain ⟨h4, h6⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hx
  refine ⟨?_, ?_⟩
  · rw [← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    exact (pow_dvd_pow ((3 : ℕ) : ℤ_[3]) hk).trans h4
  · rw [← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    exact (pow_dvd_pow ((3 : ℕ) : ℤ_[3]) (hk.trans (by norm_num))).trans h6

/-! ### Each locus lies in the minimal part of its row -/

/-- The zero class modulo `9` is not a type-`III` class. -/
theorem not_headResThree_zero : ¬ HeadResThree 0 0 := by decide

/-- The zero class modulo `27` is not a split `IV` class. -/
theorem not_headResIVThree_zero : ¬ HeadResIVThree 0 0 := by decide

/-- The zero class modulo `27` is on no `t = 1` cell: `a₄` is not a unit and `9 ∤ a₆` fails. -/
theorem not_headResOneThreeFull_zero : ¬ HeadResOneThreeFull 0 0 := by decide

/-- **The merged `t = 1` locus `I₀ ∪ II ∪ IV`-non-split lies in the minimal part of the `t = 1`
row.** -/
theorem one3LocusFull_subset_headMinimal :
    one3LocusFull ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun x hx => ⟨one3LocusFull_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three (k := 3) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_one3LocusFull_iff.1 hx
  rw [h1, h2] at h
  exact not_headResOneThreeFull_zero h

/-- **The type-`III` locus at `3` lies in the minimal part of the `t = 2` row.** -/
theorem iii3Locus_subset_headMinimal :
    iii3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun x hx => ⟨iii3Locus_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three (k := 2) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_iii3Locus_iff.1 hx
  rw [h1, h2] at h
  exact not_headResThree_zero h

/-- **The split `IV` locus at `3` lies in the minimal part of the `t = 3` row.** -/
theorem iv3Locus_subset_headMinimal :
    iv3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 3)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun x hx => ⟨iv3Locus_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three (k := 3) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_iv3Locus_iff.1 hx
  rw [h1, h2] at h
  exact not_headResIVThree_zero h

end WeierstrassCurve

end
