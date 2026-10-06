/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeRowAtThree

/-!
# Family A is disjoint from the `(I₀*, 4)` locus at `p = 3`

The Family A locus at `p = 3` (the `Iₘ*` strata with `m ≥ 1`) is disjoint from the `(I₀*, 4)` locus
`iZeroStarFour3Locus = {a₄ ≡ 18, 45, 72 (mod 81)} × {81 ∣ a₆}`: on Family A, `a₆` is a unit, while
`3 ∣ a₆` on the other locus.

## Main results

* `WeierstrassCurve.FamilyAThree.dvd_of_toZModPow_eq_zero`: vanishing of a residue at any positive
  depth gives divisibility by `3`.
* `WeierstrassCurve.FamilyAThree.disjoint_locus_IZeroStarFour`: Family A is disjoint from the
  `(I₀*, 4)` locus.
-/

open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

namespace FamilyAThree

/-! ### A residue fact -/

/-- Vanishing of the residue at any positive depth gives divisibility by `3`. -/
theorem dvd_of_toZModPow_eq_zero {n : ℕ} (hn : 1 ≤ n) {y : ℤ_[3]}
    (h : PadicInt.toZModPow n y = 0) : ((3 : ℕ) : ℤ_[3]) ∣ y := by
  refine dvd_trans ?_ (PadicInt.pow_dvd_iff_toZModPow_eq_zero.2 h)
  simpa using pow_dvd_pow ((3 : ℕ) : ℤ_[3]) hn

/-! ### Row `t = 4`: disjoint from the `(I₀*, 4)` locus

`a₆` is a unit on Family A and `81 ∣ a₆` on the other, so one residue at depth `1` separates them
and `a₄` is never consulted. -/

/-- **Family A is disjoint from the `(I₀*, 4)` locus.** -/
theorem disjoint_locus_IZeroStarFour : Disjoint locus iZeroStarFour3Locus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨-, -, -, h₆, -⟩ := exists_form_of_mem_locus hx
  exact h₆ (dvd_of_toZModPow_eq_zero (by norm_num)
    (mem_iZeroStarFour3Locus_iff.1 hx').2)

end FamilyAThree

end WeierstrassCurve

end
