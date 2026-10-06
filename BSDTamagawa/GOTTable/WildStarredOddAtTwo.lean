/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildStarredOddRunAtTwo

/-!
# The odd halves of `(III*, 2)` and `(II*, 1)`, and the rest of `(I₀, 1)`, at `p = 2`

Four residue loci of the coefficient plane at `2` lie in the minimal part of a fibre of the
Tamagawa number:

    (I₀,   1)  even family    a₄ ≡ 0 mod 16, a₆ ≡ 16 mod 64          1/1024  -> t = 1
    (III*, 2)  odd half       (5,6), (13,30), (21,22), (29,14) mod 32  1/256 -> t = 2
    (II*,  1)  odd half       a₄ ≡ 5 mod 16 with a₆ ≡ 5a₄ + 29 mod 64,
                              a₄ ≡ 13 mod 16 with a₆ ≡ 9a₄ - 7 mod 64  1/512 -> t = 1
    (I₀,   1)  mirror quarter a₄ ≡ 13 mod 16, a₆ ≡ 5a₄ - 51 mod 128   1/2048 -> t = 1

They are covered by four parametrised families:

    (I₀, 1) even     a₄ = 16A,     a₆ = 16(1 + 4G)
    (III*, 2) odd    a₄ = 5 + 8A,  a₆ = 6 + 24A + 32E
    (II*, 1) odd     a₄ = 5 + 8A,  a₆ = 54 + 40A + 16A² + 64G
    (I₀, 1) mirror   a₄ = 13 + 16α, a₆ = 14 + 80α + 128k

Together with the even halves of `(III*, 2)` and `(II*, 1)` and the split-congruence quarter of
`(I₀, 1)`, these loci exhaust the three strata; the file shows that they are disjoint from those
other pieces.

All four loci lie in the triple-root region of Tate's algorithm, and the translation parameter
handed to Step 8 is even, so Step 8 hands on. What separates the strata is the residue of the
lift `tY` of Step 7, which is pinned modulo `2` by `a₆` of the model handed to Step 8: on the
`III*` family `a₄` of the Step-9 translate has `2`-adic valuation exactly `3`, so Step 9 answers
`(III*, 2)`; on the `II*` family Step 10 answers `(II*, 1)`; and on the two good-reduction
families Step 11 fires and the descended model has unit discriminant, so the next round answers
`(I₀, 1)`.

## Main results

* `WeierstrassCurve.volume_goodEven2Locus`, `WeierstrassCurve.volume_iiiStarOdd2Locus`,
  `WeierstrassCurve.volume_iiStarOdd2Locus`, `WeierstrassCurve.volume_goodOdd2Locus`: the masses
  `1/1024`, `1/256`, `1/512`, `1/2048` of the four loci.
-/
open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm BSDTamagawa.LocalConstancy

/-! ### The even good-reduction locus, its mass and its minimality -/

/-- The four residue classes modulo `2 ^ 6` carrying the even half of the `(I₀, 1)` stratum:
`a₄ ≡ 0 mod 16` together with `a₆ ≡ 16 mod 64`. -/
def headResiduesGoodEvenTwo : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(0, 16), (16, 16), (32, 16), (48, 16)}

/-- `headResiduesGoodEvenTwo` consists of exactly four residue classes. -/
theorem card_headResiduesGoodEvenTwo : headResiduesGoodEvenTwo.card = 4 := by decide

/-- The two congruences the four classes satisfy: `16 ∣ a₄`, written `2 ^ 6 ∣ 4 a₄`, and
`2 ^ 6 ∣ a₆ - 16`. -/
theorem headResiduesGoodEvenTwo_spec :
    ∀ c ∈ headResiduesGoodEvenTwo, 4 * c.1 = 0 ∧ c.2 - 16 = 0 := by
  intro c hc
  simp only [headResiduesGoodEvenTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- The **even good-reduction locus** at `2`: four residue classes modulo `2 ^ 6`. -/
noncomputable def goodEven2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesGoodEvenTwo : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- A pair lies in `goodEven2Locus` iff its reduction modulo `2 ^ 6` lies in
`headResiduesGoodEvenTwo`. -/
theorem mem_goodEven2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ goodEven2Locus ↔
      (PadicInt.toZModPow 6 x.1, PadicInt.toZModPow 6 x.2) ∈ headResiduesGoodEvenTwo := by
  rw [goodEven2Locus, mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- The even good-reduction locus at `2` is measurable. -/
theorem measurableSet_goodEven2Locus : MeasurableSet goodEven2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesGoodEvenTwo

/-- `4 · 2⁻¹² = 4/4096 = 1/1024`, in the shape `PadicInt.volume_preimage_redPairPow` produces. -/
theorem four_mul_inv_pow_twelve_div_eq :
    ((4 : ℕ) : ℝ≥0∞) * ((((2 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 6) = 1 / 1024 := by
  rw [show ((4 : ℕ) : ℝ≥0∞) = 4 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 6) = 4096 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the even good-reduction locus at `2` is `4/4096 = 1/1024`.** -/
theorem volume_goodEven2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) goodEven2Locus = 1 / 1024 := by
  rw [goodEven2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesGoodEvenTwo,
    four_mul_inv_pow_twelve_div_eq]

/-- **The locus is the parametrised even family** `a₄ = 16A`, `a₆ = 16(1 + 4G)`. -/
theorem exists_params_of_mem_goodEven2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ goodEven2Locus) :
    ∃ A G : ℤ_[2], x.1 = 16 * A ∧ x.2 = 16 * (1 + 4 * G) := by
  obtain ⟨h4, h16⟩ := headResiduesGoodEvenTwo_spec _ (mem_goodEven2Locus_iff.1 hx)
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hd1 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ 4 * x.1 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_mul, map_ofNat]
    exact h4
  have hd2 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ x.2 - 16 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
    exact h16
  have h42 : (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 := by rw [hcast]; norm_num
  have hne : ((2 : ℕ) : ℤ_[2]) ^ 2 ≠ 0 := pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 := by
    rw [h42, show (6 : ℕ) = 2 + 4 from rfl, pow_add, mul_dvd_mul_iff_left hne] at hd1
    exact hd1
  obtain ⟨G, hG⟩ := hd2
  rw [hcast] at hA hG
  exact ⟨A, G, by linear_combination hA, by linear_combination hG⟩

/-- No point of the even good-reduction locus at `2` has `2 ^ 6 ∣ a₆`, so none is a dilate. -/
theorem notMem_range_of_mem_goodEven2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ goodEven2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  obtain ⟨A, G, hA, hG⟩ := exists_params_of_mem_goodEven2Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun hdvd => ?_
  obtain ⟨m, hm⟩ := hdvd
  have h16 : (16 : ℤ_[2]) ≠ 0 := by
    rw [show (16 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 4 by norm_num]
    exact pow_ne_zero 4 PadicInt.uniformizer_ne_zero
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  refine not_dvd_of_eq_one_add_two_mul (z := 1 + 4 * G) (y := 2 * G) (by ring) ⟨2 * m, ?_⟩
  refine mul_left_cancel₀ h16 ?_
  rw [hcast] at hm ⊢
  rw [← hG]
  linear_combination hm

/-- The short model is nonsingular on the locus: `Δ = -2¹²(1 + 2z)` with `1 + 2z` odd. -/
theorem Δ_ne_zero_of_mem_goodEven2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ goodEven2Locus) :
    (ofShortNF x.1 x.2).Δ ≠ 0 := by
  obtain ⟨A, G, hA, hG⟩ := exists_params_of_mem_goodEven2Locus hx
  have hΔ : (ofShortNF x.1 x.2).Δ
      = -4096 * (1 + 2 * (13 + 32 * A ^ 3 + 108 * G + 216 * G ^ 2)) := by
    rw [ofShortNF_Δ, hA, hG]; ring
  rw [hΔ]
  refine mul_ne_zero (by norm_num) fun h0 => ?_
  exact not_dvd_of_eq_one_add_two_mul
    (z := 1 + 2 * (13 + 32 * A ^ 3 + 108 * G + 216 * G ^ 2))
    (y := 13 + 32 * A ^ 3 + 108 * G + 216 * G ^ 2) (by ring) (h0 ▸ dvd_zero _)

/-- **The even good-reduction locus at `2` lies in the strata over `t = 1`.** -/
theorem goodEven2Locus_subset_iUnion_stratFibre :
    goodEven2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_goodEven2Locus hx
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨A, G, hA, hG⟩ := exists_params_of_mem_goodEven2Locus hx
  obtain ⟨hk, ht⟩ := TateAlgorithm.run_eq_I0_of_goodEven_two hA hG hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I 0,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **The even good-reduction locus at `2` lies in the minimal part of the `t = 1` row.** -/
theorem goodEven2Locus_subset_headMinimal :
    goodEven2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨goodEven2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_goodEven2Locus hx⟩

/-! ### The odd `III*` locus, its mass and its minimality -/

/-- The four residue classes modulo `2 ^ 5` carrying the odd half of the `(III*, 2)` stratum:
`a₄ ≡ 5 mod 8` together with `a₆ ≡ 3a₄ - 9 mod 32`. -/
def headResiduesIIIstarOddTwo : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(5, 6), (13, 30), (21, 22), (29, 14)}

/-- `headResiduesIIIstarOddTwo` consists of exactly four residue classes. -/
theorem card_headResiduesIIIstarOddTwo : headResiduesIIIstarOddTwo.card = 4 := by decide

/-- The two congruences the four classes satisfy: `8 ∣ a₄ - 5`, written `2 ^ 5 ∣ 4(a₄ - 5)`, and
`2 ^ 5 ∣ a₆ - 3a₄ + 9`. -/
theorem headResiduesIIIstarOddTwo_spec :
    ∀ c ∈ headResiduesIIIstarOddTwo, 4 * (c.1 - 5) = 0 ∧ c.2 - 3 * c.1 + 9 = 0 := by
  intro c hc
  simp only [headResiduesIIIstarOddTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- The odd half of the **`(III*, 2)` locus** at `2`: four residue classes modulo `2 ^ 5`. -/
noncomputable def iiiStarOdd2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (headResiduesIIIstarOddTwo : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- A pair lies in `iiiStarOdd2Locus` iff its reduction modulo `2 ^ 5` lies in
`headResiduesIIIstarOddTwo`. -/
theorem mem_iiiStarOdd2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iiiStarOdd2Locus ↔
      (PadicInt.toZModPow 5 x.1, PadicInt.toZModPow 5 x.2) ∈ headResiduesIIIstarOddTwo := by
  rw [iiiStarOdd2Locus, mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- The odd `III*` locus at `2` is measurable. -/
theorem measurableSet_iiiStarOdd2Locus : MeasurableSet iiiStarOdd2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResiduesIIIstarOddTwo

/-- `4 · 2⁻¹⁰ = 4/1024 = 1/256`, in the shape `PadicInt.volume_preimage_redPairPow` produces. -/
theorem four_mul_inv_pow_ten_div_eq :
    ((4 : ℕ) : ℝ≥0∞) * ((((2 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 5) = 1 / 256 := by
  rw [show ((4 : ℕ) : ℝ≥0∞) = 4 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 5) = 1024 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the odd `(III*, 2)` locus at `2` is `4/1024 = 1/256`.** -/
theorem volume_iiiStarOdd2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iiiStarOdd2Locus = 1 / 256 := by
  rw [iiiStarOdd2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIIIstarOddTwo,
    four_mul_inv_pow_ten_div_eq]

/-- **The locus is the parametrised odd family** `a₄ = 5 + 8A`, `a₆ = 6 + 24A + 32E`, and there
`Δ = -2¹⁰(1 + 2z)`. -/
theorem exists_params_of_mem_iiiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ iiiStarOdd2Locus) :
    ∃ A E z : ℤ_[2], x.1 = 5 + 8 * A ∧ x.2 = 6 + 24 * A + 32 * E ∧
      (ofShortNF x.1 x.2).Δ = -1024 * (1 + 2 * z) := by
  obtain ⟨h4, h3⟩ := headResiduesIIIstarOddTwo_spec _ (mem_iiiStarOdd2Locus_iff.1 hx)
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hd1 : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ 4 * (x.1 - 5) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_mul, map_sub, map_ofNat, map_ofNat]
    exact h4
  have hd2 : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.2 - 3 * x.1 + 9 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_sub, map_mul, map_ofNat, map_ofNat]
    exact h3
  have h42 : (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 := by rw [hcast]; norm_num
  have hne : ((2 : ℕ) : ℤ_[2]) ^ 2 ≠ 0 := pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ x.1 - 5 := by
    rw [h42, show (5 : ℕ) = 2 + 3 from rfl, pow_add, mul_dvd_mul_iff_left hne] at hd1
    exact hd1
  obtain ⟨E, hE⟩ := hd2
  rw [hcast] at hA hE
  obtain ⟨mA, hmA⟩ := TateAlgorithm.exists_sq_add_self_eq_two_mul (p := 2) rfl (by norm_num) A
  have hx1 : x.1 = 5 + 8 * A := by linear_combination hA
  have hx2 : x.2 = 6 + 24 * A + 32 * E := by linear_combination hE + 3 * hA
  refine ⟨A, E, mA + 11 + 79 * A + 151 * A ^ 2 + 16 * A ^ 3 + 81 * E + 324 * A * E
    + 216 * E ^ 2, hx1, hx2, ?_⟩
  rw [ofShortNF_Δ, hx1, hx2]
  linear_combination (-1024 : ℤ_[2]) * hmA

/-- The short model is nonsingular on the odd `III*` locus. -/
theorem Δ_ne_zero_of_mem_iiiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiiStarOdd2Locus) :
    (ofShortNF x.1 x.2).Δ ≠ 0 := by
  obtain ⟨A, E, z, hA, hE, hΔ⟩ := exists_params_of_mem_iiiStarOdd2Locus hx
  rw [hΔ]
  refine mul_ne_zero (by norm_num) fun h0 => ?_
  exact not_dvd_of_eq_one_add_two_mul (z := 1 + 2 * z) (y := z) rfl (h0 ▸ dvd_zero _)

/-- No point of the odd `III*` locus at `2` has an even `a₄`, so none is a dilate. -/
theorem notMem_range_of_mem_iiiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiiStarOdd2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  obtain ⟨A, E, z, hA, hE, hΔ⟩ := exists_params_of_mem_iiiStarOdd2Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  exact not_dvd_of_eq_one_add_two_mul (y := 2 + 4 * A) (by rw [hA]; ring)
    (dvd_trans (dvd_pow_self _ (by norm_num)) hdvd)

/-- **The odd `III*` locus at `2` lies in the strata over `t = 2`.** -/
theorem iiiStarOdd2Locus_subset_iUnion_stratFibre :
    iiiStarOdd2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_iiiStarOdd2Locus hx
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨A, E, z, hA, hE, hΔeq⟩ := exists_params_of_mem_iiiStarOdd2Locus hx
  obtain ⟨hk, ht⟩ := TateAlgorithm.run_eq_IIIstarOdd_two hA hE hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.III!,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **The odd `III*` locus at `2` lies in the minimal part of the `t = 2` row.** -/
theorem iiiStarOdd2Locus_subset_headMinimal :
    iiiStarOdd2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iiiStarOdd2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iiiStarOdd2Locus hx⟩

/-! ### The odd `II*` locus, its mass and its minimality -/

/-- The eight residue classes modulo `2 ^ 6` carrying the odd half of the `(II*, 1)` stratum:
`a₄ ≡ 5 mod 16` with `a₆ ≡ 5a₄ + 29 mod 64`, and `a₄ ≡ 13 mod 16` with `a₆ ≡ 9a₄ - 7 mod 64`. -/
def headResiduesIIstarOddTwo : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(5, 54), (13, 46), (21, 6), (29, 62), (37, 22), (45, 14), (53, 38), (61, 30)}

/-- `headResiduesIIstarOddTwo` consists of exactly eight residue classes. -/
theorem card_headResiduesIIstarOddTwo : headResiduesIIstarOddTwo.card = 8 := by decide

/-- Each of the eight classes satisfies one of the two congruence pairs. -/
theorem headResiduesIIstarOddTwo_spec :
    ∀ c ∈ headResiduesIIstarOddTwo,
      (4 * (c.1 - 5) = 0 ∧ c.2 - 5 * c.1 - 29 = 0) ∨
        (4 * (c.1 - 13) = 0 ∧ c.2 - 9 * c.1 + 7 = 0) := by
  intro c hc
  simp only [headResiduesIIstarOddTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inr ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inr ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inr ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inr ⟨by decide, by decide⟩

/-- The odd half of the **`(II*, 1)` locus** at `2`: eight residue classes modulo `2 ^ 6`. -/
noncomputable def iiStarOdd2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesIIstarOddTwo : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- A pair lies in `iiStarOdd2Locus` iff its reduction modulo `2 ^ 6` lies in
`headResiduesIIstarOddTwo`. -/
theorem mem_iiStarOdd2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iiStarOdd2Locus ↔
      (PadicInt.toZModPow 6 x.1, PadicInt.toZModPow 6 x.2) ∈ headResiduesIIstarOddTwo := by
  rw [iiStarOdd2Locus, mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- The odd `II*` locus at `2` is measurable. -/
theorem measurableSet_iiStarOdd2Locus : MeasurableSet iiStarOdd2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesIIstarOddTwo

/-- `8 · 2⁻¹² = 8/4096 = 1/512`, in the shape `PadicInt.volume_preimage_redPairPow` produces. -/
theorem eight_mul_inv_pow_twelve_div_eq :
    ((8 : ℕ) : ℝ≥0∞) * ((((2 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 6) = 1 / 512 := by
  rw [show ((8 : ℕ) : ℝ≥0∞) = 8 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 6) = 4096 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the odd `(II*, 1)` locus at `2` is `8/4096 = 1/512`.** -/
theorem volume_iiStarOdd2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iiStarOdd2Locus = 1 / 512 := by
  rw [iiStarOdd2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIIstarOddTwo,
    eight_mul_inv_pow_twelve_div_eq]

/-- **The locus is the parametrised odd family** `a₄ = 5 + 8A`, `a₆ = 54 + 40A + 16A² + 64G`, and
there `Δ = -2¹¹(1 + 2z)`. -/
theorem exists_params_of_mem_iiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiStarOdd2Locus) :
    ∃ A G z : ℤ_[2], x.1 = 5 + 8 * A ∧ x.2 = 54 + 40 * A + 16 * A ^ 2 + 64 * G ∧
      (ofShortNF x.1 x.2).Δ = -2048 * (1 + 2 * z) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have h42 : (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 := by rw [hcast]; norm_num
  have hne : ((2 : ℕ) : ℤ_[2]) ^ 2 ≠ 0 := pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  have key : ∀ A G : ℤ_[2], x.1 = 5 + 8 * A → x.2 = 54 + 40 * A + 16 * A ^ 2 + 64 * G →
      ∃ A G z : ℤ_[2], x.1 = 5 + 8 * A ∧ x.2 = 54 + 40 * A + 16 * A ^ 2 + 64 * G ∧
        (ofShortNF x.1 x.2).Δ = -2048 * (1 + 2 * z) := by
    intro A G h1 h2
    refine ⟨A, G, 309 + 465 * A + 366 * A ^ 2 + 143 * A ^ 3 + 27 * A ^ 4 + 729 * G
      + 540 * A * G + 216 * A ^ 2 * G + 432 * G ^ 2, h1, h2, ?_⟩
    rw [ofShortNF_Δ, h1, h2]; ring
  rcases headResiduesIIstarOddTwo_spec _ (mem_iiStarOdd2Locus_iff.1 hx) with ⟨h4, h5⟩ | ⟨h4, h9⟩
  · have hd1 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ 4 * (x.1 - 5) := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_mul, map_sub, map_ofNat, map_ofNat]
      exact h4
    have hd2 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ x.2 - 5 * x.1 - 29 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_sub, map_mul, map_ofNat, map_ofNat]
      exact h5
    obtain ⟨α, hα⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 - 5 := by
      rw [h42, show (6 : ℕ) = 2 + 4 from rfl, pow_add, mul_dvd_mul_iff_left hne] at hd1
      exact hd1
    obtain ⟨w, hw⟩ := hd2
    rw [hcast] at hα hw
    exact key (2 * α) (w - α ^ 2) (by linear_combination hα) (by linear_combination hw + 5 * hα)
  · have hd1 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ 4 * (x.1 - 13) := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_mul, map_sub, map_ofNat, map_ofNat]
      exact h4
    have hd2 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ x.2 - 9 * x.1 + 7 := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_sub, map_mul, map_ofNat, map_ofNat]
      exact h9
    obtain ⟨α, hα⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 - 13 := by
      rw [h42, show (6 : ℕ) = 2 + 4 from rfl, pow_add, mul_dvd_mul_iff_left hne] at hd1
      exact hd1
    obtain ⟨w, hw⟩ := hd2
    rw [hcast] at hα hw
    exact key (1 + 2 * α) (w - α ^ 2) (by linear_combination hα)
      (by linear_combination hw + 9 * hα)

/-- The short model is nonsingular on the odd `II*` locus. -/
theorem Δ_ne_zero_of_mem_iiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiStarOdd2Locus) :
    (ofShortNF x.1 x.2).Δ ≠ 0 := by
  obtain ⟨A, G, z, hA, hG, hΔ⟩ := exists_params_of_mem_iiStarOdd2Locus hx
  rw [hΔ]
  refine mul_ne_zero (by norm_num) fun h0 => ?_
  exact not_dvd_of_eq_one_add_two_mul (z := 1 + 2 * z) (y := z) rfl (h0 ▸ dvd_zero _)

/-- No point of the odd `II*` locus at `2` has an even `a₄`, so none is a dilate. -/
theorem notMem_range_of_mem_iiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iiStarOdd2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  obtain ⟨A, G, z, hA, hG, hΔ⟩ := exists_params_of_mem_iiStarOdd2Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  exact not_dvd_of_eq_one_add_two_mul (y := 2 + 4 * A) (by rw [hA]; ring)
    (dvd_trans (dvd_pow_self _ (by norm_num)) hdvd)

/-- **The odd `II*` locus at `2` lies in the strata over `t = 1`.** -/
theorem iiStarOdd2Locus_subset_iUnion_stratFibre :
    iiStarOdd2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_iiStarOdd2Locus hx
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨A, G, z, hA, hG, hΔeq⟩ := exists_params_of_mem_iiStarOdd2Locus hx
  obtain ⟨hk, ht⟩ := TateAlgorithm.run_eq_IIstarOdd_two hA hG hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.II!,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **The odd `II*` locus at `2` lies in the minimal part of the `t = 1` row.** -/
theorem iiStarOdd2Locus_subset_headMinimal :
    iiStarOdd2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨iiStarOdd2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iiStarOdd2Locus hx⟩

/-! ### The mirror good-reduction locus, its mass and its minimality -/

/-- The eight residue classes modulo `2 ^ 7` carrying the mirror quarter of the `(I₀, 1)` stratum:
`a₄ ≡ 13 mod 16` together with `a₆ ≡ 5a₄ - 51 mod 128`. -/
def headResiduesGoodOddTwo : Finset (ZMod (2 ^ 7) × ZMod (2 ^ 7)) :=
  {(13, 14), (29, 94), (45, 46), (61, 126), (77, 78), (93, 30), (109, 110), (125, 62)}

/-- `headResiduesGoodOddTwo` consists of exactly eight residue classes. -/
theorem card_headResiduesGoodOddTwo : headResiduesGoodOddTwo.card = 8 := by decide

/-- The two congruences the eight classes satisfy: `16 ∣ a₄ - 13`, written `2 ^ 7 ∣ 8(a₄ - 13)`,
and `2 ^ 7 ∣ a₆ - 5a₄ + 51`. -/
theorem headResiduesGoodOddTwo_spec :
    ∀ c ∈ headResiduesGoodOddTwo, 8 * (c.1 - 13) = 0 ∧ c.2 - 5 * c.1 + 51 = 0 := by
  intro c hc
  simp only [headResiduesGoodOddTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- The mirror quarter of the **`(I₀, 1)` locus** at `2`: eight residue classes modulo `2 ^ 7`. -/
noncomputable def goodOdd2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 7 ⁻¹' (headResiduesGoodOddTwo : Set (ZMod (2 ^ 7) × ZMod (2 ^ 7)))

/-- A pair lies in `goodOdd2Locus` iff its reduction modulo `2 ^ 7` lies in
`headResiduesGoodOddTwo`. -/
theorem mem_goodOdd2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ goodOdd2Locus ↔
      (PadicInt.toZModPow 7 x.1, PadicInt.toZModPow 7 x.2) ∈ headResiduesGoodOddTwo := by
  rw [goodOdd2Locus, mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- The mirror good-reduction locus at `2` is measurable. -/
theorem measurableSet_goodOdd2Locus : MeasurableSet goodOdd2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 7 headResiduesGoodOddTwo

/-- **The mass of the mirror good-reduction locus at `2` is `8/16384 = 1/2048`.** -/
theorem volume_goodOdd2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) goodOdd2Locus = 1 / 2048 := by
  rw [goodOdd2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesGoodOddTwo,
    eight_mul_inv_pow_fourteen_div_eq]

/-- **The locus is the parametrised mirror family** `a₄ = 13 + 16α`, `a₆ = 14 + 80α + 128k`, and
there `Δ = -2¹²(1 + 2z)`. -/
theorem exists_params_of_mem_goodOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ goodOdd2Locus) :
    ∃ α k z : ℤ_[2], x.1 = 13 + 16 * α ∧ x.2 = 14 + 80 * α + 128 * k ∧
      (ofShortNF x.1 x.2).Δ = -4096 * (1 + 2 * z) := by
  obtain ⟨h8, h5⟩ := headResiduesGoodOddTwo_spec _ (mem_goodOdd2Locus_iff.1 hx)
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hd1 : ((2 : ℕ) : ℤ_[2]) ^ 7 ∣ 8 * (x.1 - 13) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_mul, map_sub, map_ofNat, map_ofNat]
    exact h8
  have hd2 : ((2 : ℕ) : ℤ_[2]) ^ 7 ∣ x.2 - 5 * x.1 + 51 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_sub, map_mul, map_ofNat, map_ofNat]
    exact h5
  have h83 : (8 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 3 := by rw [hcast]; norm_num
  have hne : ((2 : ℕ) : ℤ_[2]) ^ 3 ≠ 0 := pow_ne_zero 3 PadicInt.uniformizer_ne_zero
  obtain ⟨α, hα⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 - 13 := by
    rw [h83, show (7 : ℕ) = 3 + 4 from rfl, pow_add, mul_dvd_mul_iff_left hne] at hd1
    exact hd1
  obtain ⟨k, hk⟩ := hd2
  rw [hcast] at hα hk
  obtain ⟨mα, hmα⟩ := TateAlgorithm.exists_sq_add_self_eq_two_mul (p := 2) rfl (by norm_num) α
  have hx1 : x.1 = 13 + 16 * α := by linear_combination hα
  have hx2 : x.2 = 14 + 80 * α + 128 * k := by linear_combination hk + 5 * hα
  refine ⟨α, k, mα + 27 + 181 * α + 415 * α ^ 2 + 32 * α ^ 3 + 189 * k + 1080 * α * k
    + 864 * k ^ 2, hx1, hx2, ?_⟩
  rw [ofShortNF_Δ, hx1, hx2]
  linear_combination (-4096 : ℤ_[2]) * hmα

/-- The short model is nonsingular on the mirror good-reduction locus. -/
theorem Δ_ne_zero_of_mem_goodOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ goodOdd2Locus) :
    (ofShortNF x.1 x.2).Δ ≠ 0 := by
  obtain ⟨α, k, z, hα, hk, hΔ⟩ := exists_params_of_mem_goodOdd2Locus hx
  rw [hΔ]
  refine mul_ne_zero (by norm_num) fun h0 => ?_
  exact not_dvd_of_eq_one_add_two_mul (z := 1 + 2 * z) (y := z) rfl (h0 ▸ dvd_zero _)

/-- No point of the mirror good-reduction locus at `2` has an even `a₄`, so none is a dilate. -/
theorem notMem_range_of_mem_goodOdd2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ goodOdd2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  obtain ⟨α, k, z, hα, hk, hΔ⟩ := exists_params_of_mem_goodOdd2Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  exact not_dvd_of_eq_one_add_two_mul (y := 6 + 8 * α) (by rw [hα]; ring)
    (dvd_trans (dvd_pow_self _ (by norm_num)) hdvd)

/-- **The mirror good-reduction locus at `2` lies in the strata over `t = 1`.** -/
theorem goodOdd2Locus_subset_iUnion_stratFibre :
    goodOdd2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_goodOdd2Locus hx
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨α, k, z, hα, hk, hΔeq⟩ := exists_params_of_mem_goodOdd2Locus hx
  obtain ⟨hkod, ht⟩ := TateAlgorithm.run_eq_I0_of_goodOdd_two hα hk hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I 0,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hkod ht)⟩

/-- **The mirror good-reduction locus at `2` lies in the minimal part of the `t = 1` row.** -/
theorem goodOdd2Locus_subset_headMinimal :
    goodOdd2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨goodOdd2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_goodOdd2Locus hx⟩

/-! ### Disjointness from the other halves of the three strata

The even and odd halves of each stratum are disjoint: the even `III*` and `II*` loci have `a₄`
even and the odd ones have `a₄` odd, and the three good-reduction quarters sit on
`a₄ ≡ 0, 5, 13` modulo `16`. -/

/-- No odd `III*` class is an even `III*` class. -/
theorem not_headResIIIstarTwo_of_mem_headResiduesIIIstarOddTwo :
    ∀ c ∈ headResiduesIIIstarOddTwo, ¬ HeadResIIIstarTwo c.1 c.2 := by
  intro c hc
  simp only [headResiduesIIIstarOddTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- **The two halves of the `(III*, 2)` stratum are disjoint.** -/
theorem disjoint_iiiStar2Locus_iiiStarOdd2Locus : Disjoint iiiStar2Locus iiiStarOdd2Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact not_headResIIIstarTwo_of_mem_headResiduesIIIstarOddTwo _
    (mem_iiiStarOdd2Locus_iff.1 hx') (mem_iiiStar2Locus_iff.1 hx)

/-- No odd `II*` class is an even `II*` class. -/
theorem not_headResIIstarTwo_of_mem_headResiduesIIstarOddTwo :
    ∀ c ∈ headResiduesIIstarOddTwo, ¬ HeadResIIstarTwo c.1 c.2 := by
  intro c hc
  simp only [headResiduesIIstarOddTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The two halves of the `(II*, 1)` stratum are disjoint.** -/
theorem disjoint_iiStar2Locus_iiStarOdd2Locus : Disjoint iiStar2Locus iiStarOdd2Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact not_headResIIstarTwo_of_mem_headResiduesIIstarOddTwo _
    (mem_iiStarOdd2Locus_iff.1 hx') (mem_iiStar2Locus_iff.1 hx)

/-- The mirror quarter and the split-congruence quarter of `(I₀, 1)` are different classes modulo
`2 ^ 7`. -/
theorem notMem_headResGoodTwo_of_mem_headResiduesGoodOddTwo :
    ∀ c ∈ headResiduesGoodOddTwo, c ∉ headResGoodTwo := by
  intro c hc
  simp only [headResiduesGoodOddTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The split-congruence quarter `good2Locus` and the mirror quarter `goodOdd2Locus` of the
`(I₀, 1)` stratum at `2` are disjoint. -/
theorem disjoint_good2Locus_goodOdd2Locus : Disjoint good2Locus goodOdd2Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact notMem_headResGoodTwo_of_mem_headResiduesGoodOddTwo _ (mem_goodOdd2Locus_iff.1 hx')
    (mem_good2Locus_iff.1 hx)

/-- The split-congruence quarter has `a₄ ≡ 5 mod 16` and the even family has `16 ∣ a₄`. -/
theorem disjoint_good2Locus_goodEven2Locus : Disjoint good2Locus goodEven2Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, w, z, hα, hw, hΔ⟩ := exists_params_of_mem_good2Locus hx
  obtain ⟨A, G, hA, hG⟩ := exists_params_of_mem_goodEven2Locus hx'
  exact not_dvd_of_eq_one_add_two_mul (z := (1 : ℤ_[2])) (y := 0) (by ring)
    ⟨8 * A - 2 - 8 * α, by
      rw [show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]; linear_combination hA - hα⟩

/-- The mirror quarter has `a₄ ≡ 13 mod 16` and the even family has `16 ∣ a₄`. -/
theorem disjoint_goodEven2Locus_goodOdd2Locus : Disjoint goodEven2Locus goodOdd2Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨A, G, hA, hG⟩ := exists_params_of_mem_goodEven2Locus hx
  obtain ⟨α, k, z, hα, hk, hΔ⟩ := exists_params_of_mem_goodOdd2Locus hx'
  exact not_dvd_of_eq_one_add_two_mul (z := (1 : ℤ_[2])) (y := 0) (by ring)
    ⟨8 * A - 6 - 8 * α, by
      rw [show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]; linear_combination hA - hα⟩

end WeierstrassCurve

end
