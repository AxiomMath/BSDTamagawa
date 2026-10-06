/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyBThreeAtThree
public import BSDTamagawa.GOTTable.FamilyBThreeMeasureAtThree

/-!
# Family B at `p = 3`: the forward run meets the measure side

On the Family B cylinder at `p = 3`, Tate's algorithm makes one non-minimal descent and then
returns a multiplicative reduction type whose Tamagawa number is determined by the level and the
residue of `β`; that is, the hypothesis `ForwardRun` holds. Hence the four Family B row sets lie in
the minimal parts of their rows `t = 1, …, 4`.

## Main results

* `WeierstrassCurve.FamilyBThree.cyl_eq_locus`: the cylinders `cyl` and `locus` are equal.
* `WeierstrassCurve.FamilyBThree.forwardRun`: the hypothesis `ForwardRun` holds.
* `WeierstrassCurve.FamilyBThree.rowOne_subset_headMinimal`,
  `WeierstrassCurve.FamilyBThree.rowTwo_subset_headMinimal`,
  `WeierstrassCurve.FamilyBThree.rowThree_subset_headMinimal`,
  `WeierstrassCurve.FamilyBThree.rowFour_subset_headMinimal`: the Family B row sets lie in the
  minimal parts of their rows.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

namespace FamilyBThree

/-- The cylinder `cyl` of the measure computation equals the cylinder `locus` of the forward
run. -/
theorem cyl_eq_locus : cyl = locus := rfl

/-- Tate's algorithm on the Family B cylinder satisfies the forward-run hypothesis `ForwardRun`. -/
theorem forwardRun : ForwardRun where
  run_eq_I_zero_of_level_zero := by
    intro x hΔ hx α β h₄ h₆ hlev
    exact run_eq_I_zero_of_level_zero hΔ hx h₄ h₆ hlev
  run_eq_I_of_split := by
    intro x hΔ hx α β h₄ h₆ n hn hlev hlev' hs
    exact run_eq_I_of_split hΔ hx h₄ h₆ hn hlev hlev' hs
  run_eq_I_of_nonsplit := by
    intro x hΔ hx α β h₄ h₆ n hn hlev hlev' hs
    exact run_eq_I_of_nonsplit hΔ hx h₄ h₆ hn hlev hlev' hs

/-- Family B's row `t = 1` set lies in the minimal part of the `1`-row at `p = 3`. -/
theorem rowOne_subset_headMinimal : rowOneFamilyB ⊆ headMinimal 1 :=
  rowOneFamilyB_subset_headMinimal forwardRun

/-- Family B's row `t = 2` set lies in the minimal part of the `2`-row at `p = 3`. -/
theorem rowTwo_subset_headMinimal : rowTwoFamilyB ⊆ headMinimal 2 :=
  rowTwoFamilyB_subset_headMinimal forwardRun

/-- Family B's row `t = 3` set lies in the minimal part of the `3`-row at `p = 3`. -/
theorem rowThree_subset_headMinimal : rowThreeFamilyB ⊆ headMinimal 3 :=
  rowThreeFamilyB_subset_headMinimal forwardRun

/-- Family B's row `t = 4` set lies in the minimal part of the `4`-row at `p = 3`. -/
theorem rowFour_subset_headMinimal : rowFourFamilyB ⊆ headMinimal 4 :=
  rowFourFamilyB_subset_headMinimal forwardRun

end FamilyBThree

end WeierstrassCurve

end
