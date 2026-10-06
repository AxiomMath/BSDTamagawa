/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeRowAtThree

/-!
# The two parts of Family A lie in the minimal parts of the rows `t = 2` and `t = 4`

The Tamagawa-`t` part of Family A at `p = 3` is

  `FamilyAThree.part t := {x | ∃ h : Δ(x) ≠ 0, x ∈ locus ∧ tamagawaNumber (run … h) = t}`.

It lies in the minimal part (outside the `(3⁴, 3⁶)`-dilates) of the union over Kodaira symbols of
the strata with Tamagawa number `t`, and on the nonsingular locus the parts with `t = 2` and
`t = 4` cover. The nonsingularity witness is carried inside the set because `locus` contains
singular points: `(α, a₆) = (−1, 2)` has `4α³ + a₆² = 0`.

## Main definitions

* `WeierstrassCurve.FamilyAThree.part`: the Tamagawa-`t` part of the nonsingular locus.

## Main results

* `WeierstrassCurve.FamilyAThree.part_subset_locus`: `part t` lies in `locus`.
* `WeierstrassCurve.FamilyAThree.part_subset_headMinimal`: `part t` lies in the minimal part of the
  `t`-row.
* `WeierstrassCurve.FamilyAThree.disjoint_part`: distinct Tamagawa numbers give disjoint parts.
* `WeierstrassCurve.FamilyAThree.part_two_union_part_four`: on the nonsingular locus the two parts
  cover.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

namespace FamilyAThree

/-! ### The Tamagawa-`t` part of the nonsingular locus -/

open scoped Classical in
/-- **The Tamagawa-`t` part of Family A**: the nonsingular points of `locus` at which Tate's
algorithm reports Tamagawa number `t`. -/
noncomputable def part (t : ℕ) : Set (ℤ_[3] × ℤ_[3]) :=
  {x | ∃ h : (ofShortNF x.1 x.2).Δ ≠ 0, x ∈ locus ∧
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero h).tamagawaNumber = t}

/-- The Tamagawa-`t` part of Family A is contained in the cylinder `locus`. -/
theorem part_subset_locus (t : ℕ) : part t ⊆ locus := fun _ hx => hx.2.1

/-! ### The parts lie in the minimal part of their rows -/

open scoped Classical in
/-- The Tamagawa-`t` part of Family A lies in the minimal part of the `t`-row. -/
theorem part_subset_headMinimal (t : ℕ) :
    part t ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, t)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  rintro x ⟨hΔ, hx, ht⟩
  refine ⟨?_, locus_subset_notMem_range x hx⟩
  obtain ⟨m, hm, hks⟩ := exists_kodairaSymbol_eq_Istar_of_mem_locus hΔ hx
  refine Set.mem_iUnion.2
    ⟨KodairaSymbol.I! m, (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_⟩
  rw [strat]
  exact Prod.ext hks ht

/-! ### The two parts are disjoint and, on the nonsingular locus, cover -/

/-- Parts of Family A with distinct Tamagawa numbers are disjoint. -/
theorem disjoint_part {s t : ℕ} (hst : s ≠ t) : Disjoint (part s) (part t) := by
  rw [Set.disjoint_left]
  rintro x ⟨hΔ, -, hs⟩ ⟨hΔ', -, ht⟩
  exact hst (hs.symm.trans ht)

open scoped Classical in
/-- **On the nonsingular part of the locus the two halves cover**: `locus ∩ nonsingularLocus 3` is
the union of the Tamagawa-`2` and Tamagawa-`4` parts. -/
theorem part_two_union_part_four : locus ∩ nonsingularLocus 3 = part 2 ∪ part 4 := by
  refine Set.Subset.antisymm (fun x ⟨hx, hUp⟩ => ?_) ?_
  · have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := hUp
    rcases tamagawaNumber_eq_two_or_four_of_mem_locus hΔ hx with h2 | h4
    · exact Or.inl ⟨hΔ, hx, h2⟩
    · exact Or.inr ⟨hΔ, hx, h4⟩
  · rintro x (⟨hΔ, hx, -⟩ | ⟨hΔ, hx, -⟩) <;> exact ⟨hx, hΔ⟩

end FamilyAThree

end WeierstrassCurve

end
