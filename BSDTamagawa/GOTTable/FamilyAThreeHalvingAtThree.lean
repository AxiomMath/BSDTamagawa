/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeAtThree

/-!
# Fibrewise reflections of the coefficient plane preserve mass

Two measurable subsets of `ℤ_[p] × ℤ_[p]` whose `a₄`-fibres are exchanged by a reflection
`a₆ ↦ c − a₆` have the same Haar mass, where the reflection point `c` may depend on `a₄`
arbitrarily (no measurability of `a₄ ↦ c` is required). These are the measure-theoretic inputs for
showing that, in the `Iₘ*` family at `p = 3`, half the mass carries Tamagawa number `2` and half
carries `4`.

## Main results

* `WeierstrassCurve.FamilyAThree.volume_reflect_preimage`: a reflection `y ↦ c − y` of `ℤ_[p]`
  preserves the mass of any measurable set.
* `WeierstrassCurve.FamilyAThree.volume_eq_of_reflect`: if the reflection `y ↦ c − y` pulls `T`
  back to `S`, then `S` and `T` have equal mass.
* `WeierstrassCurve.FamilyAThree.volume_eq_of_slice_volume_eq`: two measurable sets of the plane
  with equally massive `a₄`-fibres have equal mass.
* `WeierstrassCurve.FamilyAThree.volume_eq_of_fibrewise_reflect`: two measurable subsets of the
  plane whose `a₄`-fibres are exchanged by a reflection have equal mass.
* `WeierstrassCurve.FamilyAThree.two_mul_volume_eq_of_two_fibrewise_reflects`:
  `2 · μ (L₁ ∪ L₂) = μ S` for a set `S` split into two pieces, each halved by its own reflection.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

namespace FamilyAThree

/-! ### One fibre: a reflection preserves Haar measure -/

/-- **A reflection of `ℤ_[p]` preserves mass.** `y ↦ c − y` is negation followed by translation,
and `volume` is invariant under both. -/
theorem volume_reflect_preimage (c : ℤ_[p]) {T : Set ℤ_[p]} (hT : MeasurableSet T) :
    (volume : Measure ℤ_[p]) ((fun y => c - y) ⁻¹' T) = (volume : Measure ℤ_[p]) T :=
  (Measure.measurePreserving_sub_left volume c).measure_preimage hT.nullMeasurableSet

/-- The fibre form: if the reflection `y ↦ c − y` carries `S` onto `T` — i.e. `S` is the preimage
of `T` — then `S` and `T` have the same mass. -/
theorem volume_eq_of_reflect {c : ℤ_[p]} {S T : Set ℤ_[p]} (hT : MeasurableSet T)
    (hST : (fun y => c - y) ⁻¹' T = S) :
    (volume : Measure ℤ_[p]) S = (volume : Measure ℤ_[p]) T := by
  rw [← hST]
  exact volume_reflect_preimage c hT

/-! ### The plane: equal fibres give equal mass -/

/-- **Two measurable subsets of the plane with equally massive `a₄`-fibres have equal mass.** -/
theorem volume_eq_of_slice_volume_eq {L L' : Set (ℤ_[p] × ℤ_[p])} (hL : MeasurableSet L)
    (hL' : MeasurableSet L')
    (hslice : ∀ a : ℤ_[p], (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' L) =
      (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' L')) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) L = (volume : Measure (ℤ_[p] × ℤ_[p])) L' := by
  rw [Measure.volume_eq_prod, Measure.prod_apply hL, Measure.prod_apply hL']
  exact lintegral_congr hslice

/-! ### Fibrewise reflections -/

/-- If every `a₄`-fibre of `L` is the preimage of the corresponding fibre of `L'` under a
reflection `y ↦ c − y`, with the reflection point allowed to depend on `a₄` in any way, then `L`
and `L'` have the same mass. -/
theorem volume_eq_of_fibrewise_reflect {L L' : Set (ℤ_[p] × ℤ_[p])} (hL : MeasurableSet L)
    (hL' : MeasurableSet L')
    (hrefl : ∀ a : ℤ_[p], ∃ c : ℤ_[p],
      (fun y => c - y) ⁻¹' (Prod.mk a ⁻¹' L') = Prod.mk a ⁻¹' L) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) L = (volume : Measure (ℤ_[p] × ℤ_[p])) L' := by
  refine volume_eq_of_slice_volume_eq hL hL' fun a => ?_
  obtain ⟨c, hc⟩ := hrefl a
  exact volume_eq_of_reflect (hL'.preimage measurable_prodMk_left) hc

/-! ### Two reflections, one per piece -/

/-- **A set split into two pieces, each halved by its own reflection.** If `S` is partitioned into
`L₁ ⊔ L₁'` on one piece and `L₂ ⊔ L₂'` on the other, with the `a₄`-fibres of `Lᵢ` and `Lᵢ'`
exchanged by a reflection whose point may differ between the two pieces as well as between fibres,
then `2 · μ (L₁ ∪ L₂) = μ S`. -/
theorem two_mul_volume_eq_of_two_fibrewise_reflects {S L₁ L₁' L₂ L₂' : Set (ℤ_[p] × ℤ_[p])}
    (h₁ : MeasurableSet L₁) (h₁' : MeasurableSet L₁') (h₂ : MeasurableSet L₂)
    (h₂' : MeasurableSet L₂') (hcover : S = (L₁ ∪ L₂) ∪ (L₁' ∪ L₂'))
    (hdisj : Disjoint (L₁ ∪ L₂) (L₁' ∪ L₂')) (hd : Disjoint L₁ L₂) (hd' : Disjoint L₁' L₂')
    (hr₁ : ∀ a : ℤ_[p], ∃ c : ℤ_[p],
      (fun y => c - y) ⁻¹' (Prod.mk a ⁻¹' L₁') = Prod.mk a ⁻¹' L₁)
    (hr₂ : ∀ a : ℤ_[p], ∃ c : ℤ_[p],
      (fun y => c - y) ⁻¹' (Prod.mk a ⁻¹' L₂') = Prod.mk a ⁻¹' L₂) :
    2 * (volume : Measure (ℤ_[p] × ℤ_[p])) (L₁ ∪ L₂) =
      (volume : Measure (ℤ_[p] × ℤ_[p])) S := by
  have hhalf : (volume : Measure (ℤ_[p] × ℤ_[p])) (L₁ ∪ L₂) =
      (volume : Measure (ℤ_[p] × ℤ_[p])) (L₁' ∪ L₂') := by
    rw [measure_union hd h₂, measure_union hd' h₂',
      volume_eq_of_fibrewise_reflect h₁ h₁' hr₁, volume_eq_of_fibrewise_reflect h₂ h₂' hr₂]
  rw [hcover, measure_union hdisj (h₁'.union h₂'), ← hhalf, two_mul]

end FamilyAThree

end WeierstrassCurve

end
