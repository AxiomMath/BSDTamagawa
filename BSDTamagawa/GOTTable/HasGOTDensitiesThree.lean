/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildFamilyBCellAtThree
public import BSDTamagawa.GOTTable.FamilyAThreeCloseAtThree
public import BSDTamagawa.GOTTable.FamilyBThreeCloseAtThree

/-!
# The Griffin–Ono–Tsai table at `p = 3`

The Tamagawa densities at `p = 3` agree with the `p = 3` column of the Griffin–Ono–Tsai table, with
three corrected head values. The four Family B row sets lie in the Family B cell.

## Main results

* `WeierstrassCurve.FamilyBThree.cyl_subset_familyBCell`: the Family B cylinder lies in the Family
  B cell.
* `WeierstrassCurve.FamilyBThree.rowOneFamilyB_subset_cell`,
  `WeierstrassCurve.FamilyBThree.rowTwoFamilyB_subset_cell`,
  `WeierstrassCurve.FamilyBThree.rowThreeFamilyB_subset_cell`,
  `WeierstrassCurve.FamilyBThree.rowFourFamilyB_subset_cell`: each Family B row set lies in the
  Family B cell.
* `WeierstrassCurve.hasGOTDensities_three`: `HasGOTDensities 3`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

namespace FamilyBThree

/-- **The Family B cylinder lies in the Family B cell.** -/
theorem cyl_subset_familyBCell : cyl ⊆ familyBCell := by
  intro x hx
  obtain ⟨α, β, h1, h2, hα, hβ, h27⟩ := exists_form_of_mem_locus (cyl_eq_locus ▸ hx)
  exact ⟨α, β, by rw [h1]; norm_num, by rw [h2]; norm_num, hα, hβ, h27⟩

/-- Family B's row `t = 1` set lies in the Family B cell. -/
theorem rowOneFamilyB_subset_cell : rowOneFamilyB ⊆ familyBCell := by
  refine Set.union_subset (Set.union_subset ?_ ?_) ?_
  · exact (shell_subset_cyl 0).trans cyl_subset_familyBCell
  · exact Set.iUnion_subset fun j =>
      ((nonSplitShell_subset_shell _).trans (shell_subset_cyl _)).trans cyl_subset_familyBCell
  · exact ((splitShell_subset_shell _).trans (shell_subset_cyl _)).trans cyl_subset_familyBCell

/-- Family B's row `t = 2` set lies in the Family B cell. -/
theorem rowTwoFamilyB_subset_cell : rowTwoFamilyB ⊆ familyBCell := by
  refine Set.union_subset ?_ ?_
  · exact Set.iUnion_subset fun j =>
      ((nonSplitShell_subset_shell _).trans (shell_subset_cyl _)).trans cyl_subset_familyBCell
  · exact ((splitShell_subset_shell _).trans (shell_subset_cyl _)).trans cyl_subset_familyBCell

/-- Family B's row `t = 3` set lies in the Family B cell. -/
theorem rowThreeFamilyB_subset_cell : rowThreeFamilyB ⊆ familyBCell :=
  ((splitShell_subset_shell _).trans (shell_subset_cyl _)).trans cyl_subset_familyBCell

/-- Family B's row `t = 4` set lies in the Family B cell. -/
theorem rowFourFamilyB_subset_cell : rowFourFamilyB ⊆ familyBCell :=
  ((splitShell_subset_shell _).trans (shell_subset_cyl _)).trans cyl_subset_familyBCell

end FamilyBThree

/-- **The `p = 3` column of the Griffin–Ono–Tsai table holds**, with the three corrected head
values `δ_3(1) = 1924841/2125728`, `δ_3(2) = 509345/6377184`, `δ_3(3) = 30619/2391444`, the printed
`δ_3(4) = 1193/652212`, and the geometric tail. -/
theorem hasGOTDensities_three : HasGOTDensities 3 :=
  hasGOTDensities_three_of_cell FamilyAThree.two_mul_volume_part_two
    FamilyAThree.two_mul_volume_part_four
    FamilyBThree.rowOneFamilyB FamilyBThree.rowTwoFamilyB FamilyBThree.rowThreeFamilyB
    FamilyBThree.rowFourFamilyB
    FamilyBThree.measurableSet_rowOneFamilyB FamilyBThree.rowOne_subset_headMinimal
    FamilyBThree.volume_rowOneFamilyB FamilyBThree.rowOneFamilyB_subset_cell
    FamilyBThree.measurableSet_rowTwoFamilyB FamilyBThree.rowTwo_subset_headMinimal
    FamilyBThree.volume_rowTwoFamilyB FamilyBThree.rowTwoFamilyB_subset_cell
    FamilyBThree.measurableSet_rowThreeFamilyB FamilyBThree.rowThree_subset_headMinimal
    FamilyBThree.volume_rowThreeFamilyB FamilyBThree.rowThreeFamilyB_subset_cell
    FamilyBThree.measurableSet_rowFourFamilyB FamilyBThree.rowFour_subset_headMinimal
    FamilyBThree.volume_rowFourFamilyB FamilyBThree.rowFourFamilyB_subset_cell

end WeierstrassCurve

end
