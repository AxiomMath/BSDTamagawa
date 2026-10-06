/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildStarredRunAtTwo
public import BSDTamagawa.GOTTable.WildRowThreeAtTwo

/-!
# The starred strata `IV*`, `III*` and `II*` at `p = 2`

Four residue loci of the coefficient plane at `2`, all inside the triple-root region of Tate's
algorithm, lie in the minimal part (outside the range of `σ_2`) of the strata with a given Tamagawa
number `t`:

    (IV*,  3)   8 classes mod 32,  mass 1/128   -> t = 3   (the whole stratum)
    (IV*,  1)   8 classes mod 32,  mass 1/128   -> t = 1   (the whole stratum)
    (III*, 2)   4 classes mod 32,  mass 1/256   -> t = 2   (half the stratum)
    (II*,  1)   8 classes mod 64,  mass 1/512   -> t = 1   (half the stratum)

Explicitly

    (IV*, 3) : (0,4), (8,4), (16,4), (24,4), (1,6), (9,14), (17,22), (25,30)     (mod 32)
    (IV*, 1) : (0,20), (8,20), (16,20), (24,20), (1,22), (9,30), (17,6), (25,14) (mod 32)
    (III*,2) : (8,0), (24,0), (8,16), (24,16)                                    (mod 32)
    (II*, 1) : a₄ ≡ 0 (mod 16) and a₆ ≡ 32 or 48 (mod 64)

They are covered by four parametrised families:

    IV*   even   a₄ = 8A,       a₆ = 4 + 16F        Tamagawa 3 / 1 as F is even / odd
    IV*   odd    a₄ = 1 + 8A,   a₆ = 6 + 8A + 16F   Tamagawa 3 / 1 as F is even / odd
    III*         a₄ = 8 + 16A,  a₆ = 16E
    II*          a₄ = 16A,      a₆ = 16G            with G ≡ 2 or 3 (mod 4)

On each family the cubic of Step 6 has a triple root, and the strata are separated by the parity
of the translation parameter handed to Step 8: when it is `2W` with `W` odd, the quadratic of
Step 8 has no double root and the symbol is `IV*`, with Tamagawa number `3` exactly when that
quadratic splits; when `W` is even, Step 9 answers `III*` or Step 10 answers `II*`.

## Main results

* `WeierstrassCurve.volume_ivStarThree2Locus`, `WeierstrassCurve.volume_ivStarOne2Locus`,
  `WeierstrassCurve.volume_iiiStar2Locus`, `WeierstrassCurve.volume_iiStar2Locus`: the masses
  `1/128`, `1/128`, `1/256`, `1/512` of the four loci.
* `WeierstrassCurve.ivStarOne2Locus_subset_stratFibre`,
  `WeierstrassCurve.iiStar2Locus_subset_stratFibre`: the two `t = 1` loci lie in the strata
  `(IV*, 1)` and `(II*, 1)`.
* `WeierstrassCurve.ivStarThree2Locus_subset_headMinimal`,
  `WeierstrassCurve.ivStarOne2Locus_subset_headMinimal`,
  `WeierstrassCurve.iiiStar2Locus_subset_headMinimal`,
  `WeierstrassCurve.iiStar2Locus_subset_headMinimal`: each locus lies in the minimal part of the
  strata over its Tamagawa number.
* `WeierstrassCurve.volume_union_IVthree_at_two`,
  `WeierstrassCurve.union_IVthree_subset_headMinimal`: the `(IV*, 3)` locus and the split `IV`
  locus of `WildRowThreeAtTwo` together have mass `9/128` and lie in the minimal part of the
  `t = 3` strata.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

/-! ### The two loci, their masses, and their minimality -/

/-- **The residue condition cutting out the `(IV*, 3)` locus at `2`**: the eight classes
`(a₄, a₆) ≡ (0,4), (8,4), (16,4), (24,4), (1,6), (9,14), (17,22), (25,30)` modulo `32`. -/
abbrev HeadResIVstarThreeTwo (A E : ZMod (2 ^ 5)) : Prop :=
  (A = 0 ∧ E = 4) ∨ (A = 8 ∧ E = 4) ∨ (A = 16 ∧ E = 4) ∨ (A = 24 ∧ E = 4) ∨
    (A = 1 ∧ E = 6) ∨ (A = 9 ∧ E = 14) ∨ (A = 17 ∧ E = 22) ∨ (A = 25 ∧ E = 30)

/-- **The residue condition cutting out the `(IV*, 1)` locus at `2`**: the eight classes
`(a₄, a₆) ≡ (0,20), (8,20), (16,20), (24,20), (1,22), (9,30), (17,6), (25,14)` modulo `32`. -/
abbrev HeadResIVstarOneTwo (A E : ZMod (2 ^ 5)) : Prop :=
  (A = 0 ∧ E = 20) ∨ (A = 8 ∧ E = 20) ∨ (A = 16 ∧ E = 20) ∨ (A = 24 ∧ E = 20) ∨
    (A = 1 ∧ E = 22) ∨ (A = 9 ∧ E = 30) ∨ (A = 17 ∧ E = 6) ∨ (A = 25 ∧ E = 14)

/-- The eight residue pairs of `HeadResIVstarThreeTwo`, as a `Finset`. -/
def headResiduesIVstarThreeTwo : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(0, 4), (8, 4), (16, 4), (24, 4), (1, 6), (9, 14), (17, 22), (25, 30)}

/-- The eight residue pairs of `HeadResIVstarOneTwo`, as a `Finset`. -/
def headResiduesIVstarOneTwo : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(0, 20), (8, 20), (16, 20), (24, 20), (1, 22), (9, 30), (17, 6), (25, 14)}

/-- `headResiduesIVstarThreeTwo` has eight elements. -/
theorem card_headResiduesIVstarThreeTwo : headResiduesIVstarThreeTwo.card = 8 := by decide

/-- `headResiduesIVstarOneTwo` has eight elements. -/
theorem card_headResiduesIVstarOneTwo : headResiduesIVstarOneTwo.card = 8 := by decide

/-- Membership in `headResiduesIVstarThreeTwo` is the condition `HeadResIVstarThreeTwo`. -/
theorem mem_headResiduesIVstarThreeTwo_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ headResiduesIVstarThreeTwo ↔ HeadResIVstarThreeTwo c.1 c.2 := by
  simp [headResiduesIVstarThreeTwo, Prod.ext_iff]

/-- Membership in `headResiduesIVstarOneTwo` is the condition `HeadResIVstarOneTwo`. -/
theorem mem_headResiduesIVstarOneTwo_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ headResiduesIVstarOneTwo ↔ HeadResIVstarOneTwo c.1 c.2 := by
  simp [headResiduesIVstarOneTwo, Prod.ext_iff]

/-- **The residue arithmetic of the `(IV*, 3)` locus.** On each of the eight classes `a₆` is `4` or
`6` modulo `8` — never `0`, which is the minimality — and the pair sits in one of the two
parametrised families with `F` **even**: `8 ∣ a₄` and `32 ∣ a₆ - 4`, or `a₄ ≡ 1 (mod 8)` and
`32 ∣ a₆ - a₄ - 5`. -/
theorem headResIVstarThreeTwo_key : ∀ A E : ZMod (2 ^ 5), HeadResIVstarThreeTwo A E →
    (ZMod.cast E : ZMod (2 ^ 3)) ≠ 0 ∧
      (((ZMod.cast A : ZMod (2 ^ 3)) = 0 ∧ E - 4 = 0) ∨
        ((ZMod.cast (A - 1) : ZMod (2 ^ 3)) = 0 ∧ E - A - 5 = 0)) := by decide

/-- **The residue arithmetic of the `(IV*, 1)` locus.** The same two families, now with `F`
**odd**: `16 ∣ a₆ - 4` but `32 ∤ a₆ - 4`, respectively `16 ∣ a₆ - a₄ - 5` but
`32 ∤ a₆ - a₄ - 5`. -/
theorem headResIVstarOneTwo_key : ∀ A E : ZMod (2 ^ 5), HeadResIVstarOneTwo A E →
    (ZMod.cast E : ZMod (2 ^ 3)) ≠ 0 ∧
      (((ZMod.cast A : ZMod (2 ^ 3)) = 0 ∧ (ZMod.cast (E - 4) : ZMod (2 ^ 4)) = 0 ∧ E - 4 ≠ 0) ∨
        ((ZMod.cast (A - 1) : ZMod (2 ^ 3)) = 0 ∧
          (ZMod.cast (E - A - 5) : ZMod (2 ^ 4)) = 0 ∧ E - A - 5 ≠ 0)) := by decide

/-- The **`(IV*, 3)` locus** of the coefficient plane at `2`: eight residue classes modulo `32`. -/
noncomputable def ivStarThree2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (headResiduesIVstarThreeTwo : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- The **`(IV*, 1)` locus** of the coefficient plane at `2`: eight residue classes modulo `32`. -/
noncomputable def ivStarOne2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (headResiduesIVstarOneTwo : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- A pair lies in `ivStarThree2Locus` iff its residues modulo `32` satisfy
`HeadResIVstarThreeTwo`. -/
theorem mem_ivStarThree2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ ivStarThree2Locus ↔
      HeadResIVstarThreeTwo (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [ivStarThree2Locus, mem_preimage, Finset.mem_coe, mem_headResiduesIVstarThreeTwo_iff,
    PadicInt.redPairPow]

/-- A pair lies in `ivStarOne2Locus` iff its residues modulo `32` satisfy
`HeadResIVstarOneTwo`. -/
theorem mem_ivStarOne2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ ivStarOne2Locus ↔
      HeadResIVstarOneTwo (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [ivStarOne2Locus, mem_preimage, Finset.mem_coe, mem_headResiduesIVstarOneTwo_iff,
    PadicInt.redPairPow]

/-- **The mass of the `(IV*, 3)` locus at `2` is `8/1024 = 1/128`.** -/
theorem volume_ivStarThree2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) ivStarThree2Locus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 10 := by
  rw [ivStarThree2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIVstarThreeTwo]
  norm_num

/-- **The mass of the `(IV*, 1)` locus at `2` is `8/1024 = 1/128`.** -/
theorem volume_ivStarOne2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) ivStarOne2Locus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 10 := by
  rw [ivStarOne2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIVstarOneTwo]
  norm_num

/-- The `(IV*, 3)` locus at `2` is measurable. -/
theorem measurableSet_ivStarThree2Locus : MeasurableSet ivStarThree2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResiduesIVstarThreeTwo

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction in
/-- **The `(IV*, 3)` locus at `2` lies in the strata over `t = 3`.** -/
theorem ivStarThree2Locus_subset_iUnion_stratFibre :
    ivStarThree2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3) := by
  intro x hx
  obtain ⟨-, hcase⟩ := headResIVstarThreeTwo_key _ _ (mem_ivStarThree2Locus_iff.1 hx)
  have hF : ∀ G : ℤ_[2], ((2 : ℕ) : ℤ_[2]) ∣ 2 * G := fun G => ⟨G, by norm_num⟩
  rcases hcase with ⟨hA, hE⟩ | ⟨hA, hE⟩
  · obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ x.1 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 3 5 (by norm_num)]
      exact hA
    obtain ⟨G, hGv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - 4 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
      exact sub_eq_zero_of_eq (by linear_combination hE)
    have ha₄ : x.1 = 8 * A := by rw [hAv]; norm_num
    have ha₆ : x.2 = 4 + 16 * (2 * G) := by
      have h : x.2 - 4 = 32 * G := by rw [hGv]; norm_num
      linear_combination h
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_IVstarEven ha₄ ha₆
    obtain ⟨hk, h3, -⟩ := run_eq_IVstarEven_two ha₄ ha₆ hΔ
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.IV!,
      (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2
        (by rw [strat]; exact Prod.ext hk (h3 (hF G)))⟩
  · obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ x.1 - 1 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 3 5 (by norm_num),
        map_sub, map_one]
      exact hA
    obtain ⟨G, hGv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - x.1 - 5 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_sub, map_ofNat]
      exact sub_eq_zero_of_eq (by linear_combination hE)
    have ha₄ : x.1 = 1 + 8 * A := by
      have h : x.1 - 1 = 8 * A := by rw [hAv]; norm_num
      linear_combination h
    have ha₆ : x.2 = 6 + 8 * A + 16 * (2 * G) := by
      have h : x.2 - x.1 - 5 = 32 * G := by rw [hGv]; norm_num
      linear_combination h + ha₄
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_IVstarOdd ha₄ ha₆
    obtain ⟨hk, h3, -⟩ := run_eq_IVstarOdd_two ha₄ ha₆ hΔ
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.IV!,
      (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2
        (by rw [strat]; exact Prod.ext hk (h3 (hF G)))⟩

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction in
/-- **The `(IV*, 1)` locus at `2` lies in the `(IV*, 1)` stratum.** -/
theorem ivStarOne2Locus_subset_stratFibre :
    ivStarOne2Locus ⊆ stratFibre 2 (KodairaSymbol.IV!, 1) := by
  intro x hx
  obtain ⟨-, hcase⟩ := headResIVstarOneTwo_key _ _ (mem_ivStarOne2Locus_iff.1 hx)
  rcases hcase with ⟨hA, hE16, hE32⟩ | ⟨hA, hE16, hE32⟩
  · obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ x.1 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 3 5 (by norm_num)]
      exact hA
    obtain ⟨F, hFv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.2 - 4 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 5 (by norm_num),
        map_sub, map_ofNat]
      exact hE16
    have h32 : ¬ ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - 4 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
      exact fun hc => hE32 (by linear_combination hc)
    have ha₄ : x.1 = 8 * A := by rw [hAv]; norm_num
    have ha₆ : x.2 = 4 + 16 * F := by
      have h : x.2 - 4 = 16 * F := by rw [hFv]; norm_num
      linear_combination h
    have hFodd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ F := by
      rintro ⟨G, hG⟩
      exact h32 ⟨G, by rw [hFv, hG]; norm_num; ring⟩
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_IVstarEven ha₄ ha₆
    obtain ⟨hk, -, h1⟩ := run_eq_IVstarEven_two ha₄ ha₆ hΔ
    exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2
      (by rw [strat]; exact Prod.ext hk (h1 hFodd))
  · obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ x.1 - 1 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 3 5 (by norm_num),
        map_sub, map_one]
      exact hA
    obtain ⟨F, hFv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.2 - x.1 - 5 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 5 (by norm_num),
        map_sub, map_sub, map_ofNat]
      exact hE16
    have h32 : ¬ ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - x.1 - 5 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_sub, map_ofNat]
      exact fun hc => hE32 (by linear_combination hc)
    have ha₄ : x.1 = 1 + 8 * A := by
      have h : x.1 - 1 = 8 * A := by rw [hAv]; norm_num
      linear_combination h
    have ha₆ : x.2 = 6 + 8 * A + 16 * F := by
      have h : x.2 - x.1 - 5 = 16 * F := by rw [hFv]; norm_num
      linear_combination h + ha₄
    have hFodd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ F := by
      rintro ⟨G, hG⟩
      exact h32 ⟨G, by rw [hFv, hG]; norm_num; ring⟩
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_IVstarOdd ha₄ ha₆
    obtain ⟨hk, -, h1⟩ := run_eq_IVstarOdd_two ha₄ ha₆ hΔ
    exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2
      (by rw [strat]; exact Prod.ext hk (h1 hFodd))

open BSDTamagawa.LocalConstancy in
/-- **The `(IV*, 1)` locus at `2` lies in the strata over `t = 1`.** -/
theorem ivStarOne2Locus_subset_iUnion_stratFibre :
    ivStarOne2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) :=
  fun _ hx => Set.mem_iUnion.2 ⟨_, ivStarOne2Locus_subset_stratFibre hx⟩

/-- **No point of the `(IV*, 3)` locus at `2` is a dilate.** On the locus `a₆` is `4` or `6` modulo
`8`, whereas `PadicInt.mem_range_scaleProdByPPow_iff` makes `2⁶ ∣ a₆` necessary. -/
theorem notMem_range_of_mem_ivStarThree2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ ivStarThree2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun hdvd => ?_
  refine (headResIVstarThreeTwo_key _ _ (mem_ivStarThree2Locus_iff.1 hx)).1 ?_
  rw [PadicInt.cast_toZModPow 3 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact dvd_trans (pow_dvd_pow ((2 : ℕ) : ℤ_[2]) (by norm_num)) hdvd

/-- **No point of the `(IV*, 1)` locus at `2` is a dilate**, for the same reason. -/
theorem notMem_range_of_mem_ivStarOne2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ ivStarOne2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun hdvd => ?_
  refine (headResIVstarOneTwo_key _ _ (mem_ivStarOne2Locus_iff.1 hx)).1 ?_
  rw [PadicInt.cast_toZModPow 3 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact dvd_trans (pow_dvd_pow ((2 : ℕ) : ℤ_[2]) (by norm_num)) hdvd

/-- **The `(IV*, 3)` locus at `2` lies in the minimal part of the `t = 3` row.** -/
theorem ivStarThree2Locus_subset_headMinimal :
    ivStarThree2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨ivStarThree2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_ivStarThree2Locus hx⟩

/-- **The `(IV*, 1)` locus at `2` lies in the minimal part of the `t = 1` row.** -/
theorem ivStarOne2Locus_subset_headMinimal :
    ivStarOne2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨ivStarOne2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_ivStarOne2Locus hx⟩

/-! ### The `(IV*, 3)` locus together with the split `IV` locus -/

/-- On the `(IV*, 3)` locus `a₆` is even. -/
theorem headResIVstarThreeTwo_even : ∀ A E : ZMod (2 ^ 5), HeadResIVstarThreeTwo A E →
    (ZMod.cast E : ZMod (2 ^ 1)) = 0 := by decide

/-- **The `(IV*, 3)` locus and the split `IV` locus of `WildRowThreeAtTwo` are disjoint**: `a₆` is
odd on the latter (`headResIVTwo_odd`) and even on the former. -/
theorem disjoint_iv2Locus_ivStarThree2Locus : Disjoint iv2Locus ivStarThree2Locus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  refine headResIVTwo_odd _ _ (mem_iv2Locus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 1 3 (by norm_num), ← PadicInt.cast_toZModPow 1 5 (by norm_num)]
  exact headResIVstarThreeTwo_even _ _ (mem_ivStarThree2Locus_iff.1 hx')

/-- **The two `t = 3` loci together have mass `1/16 + 1/128 = 9/128`.** -/
theorem volume_union_IVthree_at_two :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (iv2Locus ∪ ivStarThree2Locus) = 9 / 128 := by
  rw [measure_union disjoint_iv2Locus_ivStarThree2Locus measurableSet_ivStarThree2Locus,
    volume_iv2Locus, volume_ivStarThree2Locus, four_mul_inv_pow_six_eq, eight_mul_inv_pow_ten_eq,
    show (1 : ℝ≥0∞) / 16 = 8 / 128 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same]
  norm_num

/-- **Both `t = 3` loci lie in the minimal part of the row.** -/
theorem union_IVthree_subset_headMinimal :
    iv2Locus ∪ ivStarThree2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  Set.union_subset iv2Locus_subset_headMinimal ivStarThree2Locus_subset_headMinimal

/-! ### The `III*` locus at `t = 2` -/

/-- **The residue condition cutting out the even half of the `(III*, 2)` locus at `2`**: the four
classes `(a₄, a₆) ≡ (8,0), (24,0), (8,16), (24,16)` modulo `32`, i.e. `a₄ ≡ 8 (mod 16)` and
`a₆ ≡ 0 (mod 16)`. -/
abbrev HeadResIIIstarTwo (A E : ZMod (2 ^ 5)) : Prop :=
  (A = 8 ∧ E = 0) ∨ (A = 24 ∧ E = 0) ∨ (A = 8 ∧ E = 16) ∨ (A = 24 ∧ E = 16)

/-- The four residue pairs of `HeadResIIIstarTwo`, as a `Finset`. -/
def headResiduesIIIstarTwo : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(8, 0), (24, 0), (8, 16), (24, 16)}

/-- `headResiduesIIIstarTwo` has four elements. -/
theorem card_headResiduesIIIstarTwo : headResiduesIIIstarTwo.card = 4 := by decide

/-- Membership in `headResiduesIIIstarTwo` is the condition `HeadResIIIstarTwo`. -/
theorem mem_headResiduesIIIstarTwo_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ headResiduesIIIstarTwo ↔ HeadResIIIstarTwo c.1 c.2 := by
  simp [headResiduesIIIstarTwo, Prod.ext_iff]

/-- **The residue arithmetic of the `III*` locus.** On each class `a₄` is `8` modulo `16` — so
`2⁴ ∤ a₄`, which is the minimality — and `a₆` is `0` modulo `16`. -/
theorem headResIIIstarTwo_key : ∀ A E : ZMod (2 ^ 5), HeadResIIIstarTwo A E →
    (ZMod.cast A : ZMod (2 ^ 4)) ≠ 0 ∧ (ZMod.cast (A - 8) : ZMod (2 ^ 4)) = 0 ∧
      (ZMod.cast E : ZMod (2 ^ 4)) = 0 := by decide

/-- The even half of the **`(III*, 2)` locus** at `2`: four residue classes modulo `32`. -/
noncomputable def iiiStar2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (headResiduesIIIstarTwo : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- A pair lies in `iiiStar2Locus` iff its residues modulo `32` satisfy `HeadResIIIstarTwo`. -/
theorem mem_iiiStar2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iiiStar2Locus ↔
      HeadResIIIstarTwo (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [iiiStar2Locus, mem_preimage, Finset.mem_coe, mem_headResiduesIIIstarTwo_iff,
    PadicInt.redPairPow]

/-- **The mass of this `III*` locus at `2` is `4/1024 = 1/256`.** -/
theorem volume_iiiStar2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iiiStar2Locus = 4 * ((2 : ℝ≥0∞)⁻¹) ^ 10 := by
  rw [iiiStar2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIIIstarTwo]
  norm_num

/-- `4 · 2⁻¹⁰ = 4/1024 = 1/256`. -/
theorem four_mul_inv_pow_ten_eq : (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 10 = 1 / 256 := by
  rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 10 = 1024 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction in
/-- **This `III*` locus at `2` lies in the strata over `t = 2`.** -/
theorem iiiStar2Locus_subset_iUnion_stratFibre :
    iiiStar2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  obtain ⟨-, hA, hE⟩ := headResIIIstarTwo_key _ _ (mem_iiiStar2Locus_iff.1 hx)
  obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 - 8 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 5 (by norm_num),
      map_sub, map_ofNat]
    exact hA
  obtain ⟨E, hEv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 5 (by norm_num)]
    exact hE
  have ha₄ : x.1 = 8 + 16 * A := by
    have h : x.1 - 8 = 16 * A := by rw [hAv]; norm_num
    linear_combination h
  have ha₆ : x.2 = 16 * E := by rw [hEv]; norm_num
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_IIIstarEven ha₄ ha₆
  obtain ⟨hk, ht⟩ := run_eq_IIIstarEven_two ha₄ ha₆ hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.III!,
    (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **No point of this `III*` locus at `2` is a dilate.** On the locus `a₄` is `8` modulo `16`,
whereas `PadicInt.mem_range_scaleProdByPPow_iff` makes `2⁴ ∣ a₄` necessary. -/
theorem notMem_range_of_mem_iiiStar2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiiStar2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine (headResIIIstarTwo_key _ _ (mem_iiiStar2Locus_iff.1 hx)).1 ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- **This `III*` locus at `2` lies in the minimal part of the `t = 2` row.** -/
theorem iiiStar2Locus_subset_headMinimal :
    iiiStar2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨iiiStar2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iiiStar2Locus hx⟩

/-! ### The `II*` locus at `t = 1` -/

/-- **The residue condition cutting out the even half of the `(II*, 1)` locus at `2`**: the eight
classes with `a₄ ≡ 0 (mod 16)` and `a₆ ≡ 32` or `48 (mod 64)`. -/
abbrev HeadResIIstarTwo (A E : ZMod (2 ^ 6)) : Prop :=
  (A = 0 ∧ E = 32) ∨ (A = 16 ∧ E = 32) ∨ (A = 32 ∧ E = 32) ∨ (A = 48 ∧ E = 32) ∨
    (A = 0 ∧ E = 48) ∨ (A = 16 ∧ E = 48) ∨ (A = 32 ∧ E = 48) ∨ (A = 48 ∧ E = 48)

/-- The eight residue pairs of `HeadResIIstarTwo`, as a `Finset`. -/
def headResiduesIIstarTwo : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(0, 32), (16, 32), (32, 32), (48, 32), (0, 48), (16, 48), (32, 48), (48, 48)}

/-- `headResiduesIIstarTwo` has eight elements. -/
theorem card_headResiduesIIstarTwo : headResiduesIIstarTwo.card = 8 := by decide

/-- Membership in `headResiduesIIstarTwo` is the condition `HeadResIIstarTwo`. -/
theorem mem_headResiduesIIstarTwo_iff {c : ZMod (2 ^ 6) × ZMod (2 ^ 6)} :
    c ∈ headResiduesIIstarTwo ↔ HeadResIIstarTwo c.1 c.2 := by
  simp [headResiduesIIstarTwo, Prod.ext_iff]

/-- **The residue arithmetic of the `II*` locus.** `16 ∣ a₄` and `16 ∣ a₆`, while `a₆` is neither
`0` nor `16` modulo `64` — the first of those is the minimality and both together say that
`G = a₆/16` is `2` or `3` modulo `4`. -/
theorem headResIIstarTwo_key : ∀ A E : ZMod (2 ^ 6), HeadResIIstarTwo A E →
    (ZMod.cast A : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast E : ZMod (2 ^ 4)) = 0 ∧
      E ≠ 0 ∧ E - 16 ≠ 0 := by
  have hA : ∀ A : ZMod (2 ^ 6), A = 0 ∨ A = 16 ∨ A = 32 ∨ A = 48 →
      (ZMod.cast A : ZMod (2 ^ 4)) = 0 := by decide
  have hE : ∀ E : ZMod (2 ^ 6), E = 32 ∨ E = 48 →
      (ZMod.cast E : ZMod (2 ^ 4)) = 0 ∧ E ≠ 0 ∧ E - 16 ≠ 0 := by decide
  rintro A E h
  exact ⟨hA A (by tauto), hE E (by tauto)⟩

/-- The even half of the **`(II*, 1)` locus** at `2`: eight residue classes modulo `64`. -/
noncomputable def iiStar2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesIIstarTwo : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- A pair lies in `iiStar2Locus` iff its residues modulo `64` satisfy `HeadResIIstarTwo`. -/
theorem mem_iiStar2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iiStar2Locus ↔ HeadResIIstarTwo (PadicInt.toZModPow 6 x.1) (PadicInt.toZModPow 6 x.2) := by
  rw [iiStar2Locus, mem_preimage, Finset.mem_coe, mem_headResiduesIIstarTwo_iff,
    PadicInt.redPairPow]

/-- **The mass of this `II*` locus at `2` is `8/4096 = 1/512`.** -/
theorem volume_iiStar2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iiStar2Locus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 12 := by
  rw [iiStar2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIIstarTwo]
  norm_num

/-- The `II*` locus at `2` is measurable. -/
theorem measurableSet_iiStar2Locus : MeasurableSet iiStar2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesIIstarTwo

/-- `8 · 2⁻¹² = 8/4096 = 1/512`. -/
theorem eight_mul_inv_pow_twelve_eq : (8 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 12 = 1 / 512 := by
  rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 12 = 4096 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction in
/-- **This `II*` locus at `2` lies in the `(II*, 1)` stratum.** -/
theorem iiStar2Locus_subset_stratFibre :
    iiStar2Locus ⊆ stratFibre 2 (KodairaSymbol.II!, 1) := by
  intro x hx
  obtain ⟨hA, hE, hE0, hE16⟩ := headResIIstarTwo_key _ _ (mem_iiStar2Locus_iff.1 hx)
  obtain ⟨A, hAv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 6 (by norm_num)]
    exact hA
  obtain ⟨G, hGv⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 6 (by norm_num)]
    exact hE
  have ha₄ : x.1 = 16 * A := by rw [hAv]; norm_num
  have ha₆ : x.2 = 16 * G := by rw [hGv]; norm_num
  have h64 : ¬ ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ x.2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero]; exact hE0
  have h64' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ x.2 - 16 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
    exact hE16
  have hG : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ G := by
    rintro ⟨k, hk⟩
    exact h64 ⟨k, by rw [ha₆, hk, show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]; ring⟩
  have hG' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ (G - 1) := by
    rintro ⟨k, hk⟩
    exact h64' ⟨k, by
      rw [ha₆, show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]
      rw [show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num] at hk
      linear_combination 16 * hk⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_IIstarEven ha₄ ha₆ hG
  obtain ⟨hk, ht⟩ := run_eq_IIstarEven_two ha₄ ha₆ hG hG' hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 2)).2 (by rw [strat]; exact Prod.ext hk ht)

open BSDTamagawa.LocalConstancy in
/-- **This `II*` locus at `2` lies in the strata over `t = 1`.** -/
theorem iiStar2Locus_subset_iUnion_stratFibre :
    iiStar2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) :=
  fun _ hx => Set.mem_iUnion.2 ⟨_, iiStar2Locus_subset_stratFibre hx⟩

/-- **No point of this `II*` locus at `2` is a dilate.** On the locus `a₆` is `32` or `48` modulo
`64`, whereas `PadicInt.mem_range_scaleProdByPPow_iff` makes `2⁶ ∣ a₆` necessary. -/
theorem notMem_range_of_mem_iiStar2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiStar2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun hdvd => ?_
  refine (headResIIstarTwo_key _ _ (mem_iiStar2Locus_iff.1 hx)).2.2.1 ?_
  rw [← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- **This `II*` locus at `2` lies in the minimal part of the `t = 1` row.** -/
theorem iiStar2Locus_subset_headMinimal :
    iiStar2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨iiStar2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iiStar2Locus hx⟩

/-- **The `(IV*, 1)` and `II*` loci at `2` are disjoint**: `8 ∤ a₆` on the first and `16 ∣ a₆` on
the second. -/
theorem disjoint_ivStarOne2Locus_iiStar2Locus : Disjoint ivStarOne2Locus iiStar2Locus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  refine (headResIVstarOneTwo_key _ _ (mem_ivStarOne2Locus_iff.1 hx)).1 ?_
  rw [PadicInt.cast_toZModPow 3 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  refine dvd_trans (pow_dvd_pow ((2 : ℕ) : ℤ_[2]) (by norm_num : (3 : ℕ) ≤ 4)) ?_
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 4 6 (by norm_num)]
  exact (headResIIstarTwo_key _ _ (mem_iiStar2Locus_iff.1 hx')).2.1

end WeierstrassCurve

end
