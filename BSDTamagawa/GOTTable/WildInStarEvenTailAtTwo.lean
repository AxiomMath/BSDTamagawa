/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarTamagawaTwoFour
public import BSDTamagawa.GOTTable.WildInStarLowAtTwo

/-!
# The deep `Iₘ*` cylinder `a₄ ≡ 20`, `a₆ ≡ 16 (mod 32)` at `p = 2`, and its two Tamagawa halves

A single residue cylinder of the coefficient plane at `2` whose every nonsingular point is `Iₘ*`
for some `m ≥ 1` with Tamagawa number `2` or `4`, split into its two Tamagawa halves.

The cylinder is

    `bStarTailLocus = {(a₄, a₆) : a₄ ≡ 20 (mod 32), a₆ ≡ 16 (mod 32)}`,

the `PadicInt.redPairPow 2 5` preimage of the one-element `Finset {(20, 16)}`, of mass
`1 · 2⁻¹⁰ = 1/1024`. It lies inside `a₄ ≡ 4 (mod 8)`, `a₆ ≡ 0 (mod 16)`: with `a₄ = 4 + 8A₀` for
`A₀ = 2 + 4A` and `a₆ = 16B` for `B = 1 + 2F`, Steps 1–5 succeed, Step 6's cubic has a double but
not a triple root, and Step 7 enters its subprocedure.

The cylinder is cut by the stratification itself,

    `bStarTailTwoLocus  = bStarTailLocus ∩ ⋃ κ, stratFibre 2 (κ, 2)`
    `bStarTailFourLocus = bStarTailLocus ∩ ⋃ κ, stratFibre 2 (κ, 4)`,

so each lies inside the minimal part of its row, minimality being `16 ∤ a₄`. They are disjoint, and
they exhaust the cylinder off the singular locus `{Δ = 0}`, which is null.

Hence the two masses total exactly `1/1024`. Under the hypothesis `BStarTailFlip` that the two
halves have equal mass, each half has mass `1/2048`.

## Main definitions

* `WeierstrassCurve.bStarTailLocus`: the cylinder `a₄ ≡ 20`, `a₆ ≡ 16 (mod 32)`.
* `WeierstrassCurve.bStarTailTwoLocus`, `WeierstrassCurve.bStarTailFourLocus`: its points with
  Tamagawa number `2`, resp. `4`.
* `WeierstrassCurve.BStarTailFlip`: the two halves have equal mass.

## Main results

* `WeierstrassCurve.volume_bStarTailLocus`: the cylinder has mass `1/1024`.
* `WeierstrassCurve.bstarTail_exists_kodairaSymbol_and_tamagawaNumber`: at a nonsingular point of
  the cylinder, Tate's algorithm returns `(Iₘ*, c)` with `m ≠ 0` and `c ∈ {2, 4}`.
* `WeierstrassCurve.notMem_range_of_mem_bStarTailLocus`: points of the cylinder are minimal.
* `WeierstrassCurve.bstarTail_mass_split`: `μ(L₂) + μ(L₄) = 1/1024`.
* `WeierstrassCurve.bstarTail_volume_eq_of_flip`: under `BStarTailFlip`, each half has mass
  `1/2048`.

## Implementation notes

The Kodaira index is not computed: both `∃ m ≠ 0, κ = Iₘ*` and `c ∈ {2, 4}` hold uniformly in the
number of loop turns of Step 7's subprocedure.

The halves are exchanged by the level-dependent translation `(a₄, a₆) ↦ (a₄, a₆ + 2^(m+3))` on the
shell where the symbol is `Iₘ*`; no level-independent translation exchanges them, since the bit of
`a₆` at index `m + 3` is the one the subprocedure's exit test reads while every lower bit steers
the trajectory.
-/

open CommRing Ideal MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-! ### The one residue class modulo `32` -/

/-- **The residue condition cutting out the deep `Iₘ*` cylinder at `2`**: the single class
`a₄ ≡ 20`, `a₆ ≡ 16` modulo `32`. -/
abbrev BStarTailHeadRes (a e : ZMod (2 ^ 5)) : Prop := a = 20 ∧ e = 16

/-- The one class modulo `32`, as a `Finset`. -/
def bstarTailHeadResidues : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) := {(20, 16)}

/-- The residue set `bstarTailHeadResidues` has exactly one element. -/
theorem card_bstarTailHeadResidues : bstarTailHeadResidues.card = 1 := by decide

/-- A residue pair lies in `bstarTailHeadResidues` exactly when it is the class `(20, 16)`. -/
theorem mem_bstarTailHeadResidues_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ bstarTailHeadResidues ↔ BStarTailHeadRes c.1 c.2 := by
  simp [bstarTailHeadResidues, Prod.ext_iff]

/-- On the class `a₄ ≡ 20 (mod 32)` the coefficient `a₄` reduces to `4` modulo `16`. -/
theorem bstarTailHeadRes_cast_ne_zero : ∀ a e : ZMod (2 ^ 5), BStarTailHeadRes a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

/-! ### The cylinder, its mass and its parametrisation -/

/-- The deep `Iₘ*` cylinder at `2`: the one residue class `(20, 16)` modulo `32`. -/
noncomputable def bStarTailLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (bstarTailHeadResidues : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- A point lies in `bStarTailLocus` exactly when `a₄ ≡ 20` and `a₆ ≡ 16` modulo `32`. -/
theorem mem_bStarTailLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ bStarTailLocus ↔
      BStarTailHeadRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [bStarTailLocus, mem_preimage, Finset.mem_coe, mem_bstarTailHeadResidues_iff,
    PadicInt.redPairPow]

/-- The cylinder `bStarTailLocus` is measurable. -/
theorem measurableSet_bStarTailLocus : MeasurableSet bStarTailLocus :=
  PadicInt.measurableSet_preimage_redPairPow 5 bstarTailHeadResidues

/-- **The mass of the cylinder is `1 · 2⁻¹⁰ = 1/1024`.** -/
theorem volume_bStarTailLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailLocus = 1 / 1024 := by
  rw [bStarTailLocus, PadicInt.volume_preimage_redPairPow, card_bstarTailHeadResidues,
    show ((1 : ℕ) : ℝ≥0∞) = 1 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num, one_mul,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 5) = 1024 by norm_num, ← one_div]

/-- **The cylinder's points, parametrised.** Every point of the cylinder has
`a₄ = 4 + 8(2 + 4A)` and `a₆ = 16(1 + 2F)` for some `A F : ℤ_[2]`. -/
theorem bstarTail_exists_params {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ bStarTailLocus) :
    ∃ A F : ℤ_[2], x.1 = 4 + 8 * (2 + 4 * A) ∧ x.2 = 16 * (1 + 2 * F) := by
  obtain ⟨h1, h2⟩ := mem_bStarTailLocus_iff.1 hx
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.1 - 20 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, h1, map_ofNat, sub_self]
  obtain ⟨F, hF⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - 16 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, h2, map_ofNat, sub_self]
  rw [show ((2 : ℕ) : ℤ_[2]) ^ 5 = 32 by norm_num] at hA hF
  exact ⟨A, F, by linear_combination hA, by linear_combination hF⟩

/-! ### The forward run, uniformly in the level -/

open scoped Classical in
/-- **On a nonsingular point of the cylinder, Tate's algorithm at `2` answers `(Iₘ*, c)` with
`m ≠ 0` and `c ∈ {2, 4}`.** -/
theorem bstarTail_exists_kodairaSymbol_and_tamagawaNumber {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ bStarTailLocus) (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (∃ m, m ≠ 0 ∧ (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m) ∧
      ((TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 ∨
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 4) := by
  obtain ⟨A, F, ha₄, ha₆⟩ := bstarTail_exists_params hx
  obtain ⟨V, ν, σ, μ, h5, hdbl, hntr, -⟩ :=
    exists_step7_entry_even_two (p := 2) (a₄ := x.1) (a₆ := x.2) (A₀ := 2 + 4 * A)
      (B := 1 + 2 * F) rfl (by norm_num) ha₄ ha₆
  have h6 : Step6.run ((2 : ℕ) : ℤ_[2]) (ofShortNF x.1 x.2)
      = Except.ok (Step6.translate ((2 : ℕ) : ℤ_[2]) V) := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_left hdbl
  obtain ⟨out, h7, m, hm, hκ⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hntr
  have hrun := TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ
    (step11_error_of_step7 hΔ h7)
  exact ⟨⟨m, hm, by rw [hrun]; exact hκ⟩,
    by rw [hrun]; exact Step7.run_error_tamagawaNumber_eq_two_or_four hΔ h6 hntr h7⟩

/-- **No point of the cylinder is a `(2⁴, 2⁶)`-dilate**: no point of `bStarTailLocus` lies in the
image of `(a₄, a₆) ↦ (2⁴a₄, 2⁶a₆)`. -/
theorem notMem_range_of_mem_bStarTailLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ bStarTailLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine bstarTailHeadRes_cast_ne_zero _ _ (mem_bStarTailLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-! ### The two Tamagawa halves -/

/-- The `c = 2` half of the deep cylinder: its points whose Tamagawa number is `2`. -/
noncomputable def bStarTailTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  bStarTailLocus ∩ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)

/-- The `c = 4` half of the deep cylinder: its points whose Tamagawa number is `4`. -/
noncomputable def bStarTailFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  bStarTailLocus ∩ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)

/-- A row `⋃ κ, stratFibre 2 (κ, t)` of the stratification at `2` is measurable. -/
theorem measurableSet_iUnion_stratFibre_at_two (t : ℕ) :
    MeasurableSet (⋃ κ : KodairaSymbol, stratFibre 2 (κ, t)) :=
  MeasurableSet.iUnion fun κ => (isOpen_stratFibre (p := 2) (κ, t)).measurableSet

/-- The `c = 2` half `bStarTailTwoLocus` is measurable. -/
theorem measurableSet_bStarTailTwoLocus : MeasurableSet bStarTailTwoLocus :=
  measurableSet_bStarTailLocus.inter (measurableSet_iUnion_stratFibre_at_two 2)

/-- The `c = 4` half `bStarTailFourLocus` is measurable. -/
theorem measurableSet_bStarTailFourLocus : MeasurableSet bStarTailFourLocus :=
  measurableSet_bStarTailLocus.inter (measurableSet_iUnion_stratFibre_at_two 4)

/-- **The `c = 2` half lies in the minimal part of the row `t = 2`.** -/
theorem bStarTailTwoLocus_subset_headMinimal :
    bStarTailTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨hx.2, notMem_range_of_mem_bStarTailLocus hx.1⟩

/-- **The `c = 4` half lies in the minimal part of the row `t = 4`.** -/
theorem bStarTailFourLocus_subset_headMinimal :
    bStarTailFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨hx.2, notMem_range_of_mem_bStarTailLocus hx.1⟩

/-- **The two halves are disjoint.** -/
theorem disjoint_bStarTailTwoLocus_bStarTailFourLocus :
    Disjoint bStarTailTwoLocus bStarTailFourLocus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨κ, h2⟩ := Set.mem_iUnion.1 hx.2
  obtain ⟨κ', h4⟩ := Set.mem_iUnion.1 hx'.2
  have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ h2
  have e2 := (mem_stratFibre_iff hUp).1 h2
  have e4 := (mem_stratFibre_iff hUp).1 h4
  rw [e4] at e2
  exact absurd (congrArg Prod.snd e2) (by decide : (4 : ℕ) ≠ 2)

/-- **The two halves exhaust the cylinder off the singular locus**: every nonsingular point of
`bStarTailLocus` lies in `bStarTailTwoLocus` or `bStarTailFourLocus`. -/
theorem bStarTailLocus_inter_nonsingularLocus_subset_union :
    bStarTailLocus ∩ nonsingularLocus 2 ⊆ bStarTailTwoLocus ∪ bStarTailFourLocus := by
  intro x hx
  obtain ⟨hxc, hUp⟩ := hx
  obtain ⟨⟨m, -, hκ⟩, hc⟩ := bstarTail_exists_kodairaSymbol_and_tamagawaNumber hxc hUp
  rcases hc with h | h
  · exact Or.inl ⟨hxc, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m,
      (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ h)⟩⟩
  · exact Or.inr ⟨hxc, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m,
      (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ h)⟩⟩

/-! ### The mass split -/

/-- **The two halves carry the cylinder's whole mass between them**: `μ(L₂) + μ(L₄) = 1/1024`. -/
theorem bstarTail_mass_split :
    (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailTwoLocus
        + (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailFourLocus = 1 / 1024 := by
  rw [← measure_union disjoint_bStarTailTwoLocus_bStarTailFourLocus
    measurableSet_bStarTailFourLocus, ← volume_bStarTailLocus]
  refine le_antisymm (measure_mono (Set.union_subset (fun _ hx => hx.1) fun _ hx => hx.1)) ?_
  have hsub :
      bStarTailLocus ⊆ (bStarTailTwoLocus ∪ bStarTailFourLocus) ∪ (nonsingularLocus 2)ᶜ := by
    intro x hx
    by_cases hUp : x ∈ nonsingularLocus 2
    · exact Or.inl (bStarTailLocus_inter_nonsingularLocus_subset_union ⟨hx, hUp⟩)
    · exact Or.inr hUp
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) (le_of_eq ?_))
  rw [volume_compl_nonsingularLocus, add_zero]

/-! ### The mass of each half, from the flip -/

/-- **The flip**: the two Tamagawa halves of the cylinder have equal mass. -/
def BStarTailFlip : Prop :=
  (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailTwoLocus
    = (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailFourLocus

/-- **Each half has mass `2⁻¹¹ = 1/2048`**, given the flip. -/
theorem bstarTail_volume_eq_of_flip (hflip : BStarTailFlip) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailTwoLocus = 1 / 2048 ∧
      (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailFourLocus = 1 / 2048 := by
  unfold BStarTailFlip at hflip
  have hsum := bstarTail_mass_split
  rw [← hflip, ← two_mul] at hsum
  have h : (volume : Measure (ℤ_[2] × ℤ_[2])) bStarTailTwoLocus = 1 / 2048 := by
    refine (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).1 ?_
    rw [hsum, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      show (2048 : ℝ≥0∞) = 2 * 1024 by norm_num,
      ENNReal.mul_inv (by norm_num) (by norm_num), mul_one, mul_one, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact ⟨h, hflip ▸ h⟩

end WeierstrassCurve

end
