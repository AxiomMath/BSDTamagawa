/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowFourCloseAtThree
public import BSDTamagawa.GOTTable.WildRowOneCloseAtThree
public import BSDTamagawa.GOTTable.WildRowThreeCloseAtThree
public import BSDTamagawa.GOTTable.WildRowTwoCloseAtThree
public import BSDTamagawa.GOTTable.WildHeadLowerClose

/-!
# Every assembled locus of the `p = 3` head avoids the Family-B cell

Family B lives in one cell of the coefficient plane at `3`,

    `familyBCell = {(27α, 27β) : 3 ∤ α, 3 ∤ β, 27 ∣ 4α³ + β²}`,

and every locus assembled in the four head rows at `p = 3` is disjoint from it. Hence the
disjointness of a Family-B set from a row's assembled set follows from `B ⊆ familyBCell`, and the
row and column theorems hold with `B ⊆ familyBCell` in place of the disjointness hypothesis.

## Implementation notes

Most loci are separated by a valuation: on the cell `v₃(a₄) = v₃(a₆) = 3`, so the class modulo
`27` is `(0, 0)`, and

* `one3LocusFull`, `iii3Locus`, `iv3Locus` are cut by residues modulo `27` or `9` which exclude the
  zero class;
* the `9 ∣ a₄` loci `iZeroStarOne3Locus`, `iZeroStarTwo3Locus`, `iZeroStarFour3Locus` have
  `a₄ ≡ ±9 (mod 27)`;
* the `v₃(a₄) = 1` loci `IZeroStarUnitThree.locus u` and `FamilyAThree.locus` have `27 ∤ a₄`;
* the `3⁴ ∣ a₆` loci `ivStarOne3Locus`, `ivStarThree3Locus`, `iiiStar3Locus`, `iiStar3Locus` have
  `27 ∤ a₆/27`.

The four unit starred loci lie in the same cell `v₃(a₄) ≥ 3`, `v₃(a₆) = 3`, and only the
congruence `27 ∣ 4α³ + β²` separates them: on `ivStarOneUnit3Locus`, `ivStarThreeUnit3Locus` and
`iiiStarUnit3Locus` already `9 ∤ 4α³ + β²`, read off `(α, β)` modulo `9`, while on
`iiStarUnit3Locus` `9 ∣ 4α³ + β²` but `27 ∤ 4α³ + β²`, which needs `(α, β)` modulo `27`.

## Main definitions

* `WeierstrassCurve.familyBCell`: the Family-B cell of the coefficient plane at `3`.

## Main results

* `WeierstrassCurve.disjoint_familyBCell_*`: each assembled locus, and each row union, is disjoint
  from the cell.
* `WeierstrassCurve.row_one_close_at_three_of_cell` … `…row_four_close_at_three_of_cell` and
  `WeierstrassCurve.hasGOTDensities_three_of_cell`: the row and column theorems with the Family-B
  set required only to lie in the cell.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### The cell -/

/-- **The Family-B cell of the coefficient plane at `3`**: `a₄ = 27α`, `a₆ = 27β` with `α`, `β`
units and `27 ∣ 4α³ + β²`. -/
def familyBCell : Set (ℤ_[3] × ℤ_[3]) :=
  {x | ∃ α β : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * β ∧
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ β ∧
    ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ 4 * α ^ 3 + β ^ 2}

/-- On the cell the class modulo `27` is `(0, 0)`. -/
theorem toZModPow_three_eq_zero_of_mem_familyBCell {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ familyBCell) :
    PadicInt.toZModPow 3 x.1 = 0 ∧ PadicInt.toZModPow 3 x.2 = 0 := by
  obtain ⟨α, β, h1, h2, -, -, -⟩ := hx
  exact ⟨PadicInt.pow_dvd_iff_toZModPow_eq_zero.1 ⟨α, h1⟩,
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.1 ⟨β, h2⟩⟩

/-! ### Arithmetic lemmas -/

/-- `3α' = 27α` forces `3 ∣ α'`: a `v₃(a₄) = 1` point is not in the cell. -/
theorem dvd_of_mul_eq_pow_three_mul {α' α : ℤ_[3]}
    (h : ((3 : ℕ) : ℤ_[3]) * α' = ((3 : ℕ) : ℤ_[3]) ^ 3 * α) : ((3 : ℕ) : ℤ_[3]) ∣ α' :=
  ⟨((3 : ℕ) : ℤ_[3]) * α, mul_left_cancel₀ PadicInt.uniformizer_ne_zero (by rw [h]; ring)⟩

/-- `27β = 3ⁿ y` with `n ≥ 4` forces `3 ∣ β`: a `3⁴ ∣ a₆` point is not in the cell. -/
theorem dvd_of_pow_three_mul_eq_pow_mul {β y : ℤ_[3]} {n : ℕ} (hn : 4 ≤ n)
    (h : ((3 : ℕ) : ℤ_[3]) ^ 3 * β = ((3 : ℕ) : ℤ_[3]) ^ n * y) : ((3 : ℕ) : ℤ_[3]) ∣ β := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  refine ⟨((3 : ℕ) : ℤ_[3]) ^ m * y,
    mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_⟩
  rw [h]; ring

/-- `a₄ ≡ -9 (mod 27)` is not `a₄ ≡ 0 (mod 27)`, read on the class modulo `81`. -/
theorem cast_ne_zero_of_cast_add_nine : ∀ c : ZMod (3 ^ 4),
    (ZMod.cast (c + 9) : ZMod (3 ^ 3)) = 0 → (ZMod.cast c : ZMod (3 ^ 3)) ≠ 0 := by decide

/-- `a₄ ≡ 9 (mod 27)` is not `a₄ ≡ 0 (mod 27)`, read on the class modulo `81`. -/
theorem cast_ne_zero_of_cast_sub_nine : ∀ c : ZMod (3 ^ 4),
    (ZMod.cast (c - 9) : ZMod (3 ^ 3)) = 0 → (ZMod.cast c : ZMod (3 ^ 3)) ≠ 0 := by decide

/-! ### Reading `(α, β)` off a class of `(27α, 27β)`

A class of `a₄ = 27α` modulo `3ᵏ` determines `α` modulo `3ᵏ⁻³`, and `27 ∣ 4α³ + β²` is decided by
`(α, β)` modulo `27`, or already refuted by `(α, β)` modulo `9`. -/

set_option maxRecDepth 100000 in
/-- Multiplication by `27` on `ZMod 243` sees only the class modulo `9`. -/
theorem pow_three_mul_eq_pow_three_mul_val_five : ∀ y : ZMod (3 ^ 5),
    ((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * y
      = ((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * ((ZMod.cast y : ZMod (3 ^ 2)).val : ZMod (3 ^ 5)) := by
  decide

set_option maxRecDepth 100000 in
/-- Multiplication by `27` on `ZMod 729` sees only the class modulo `27`. -/
theorem pow_three_mul_eq_pow_three_mul_val_six : ∀ y : ZMod (3 ^ 6),
    ((3 : ℕ) : ZMod (3 ^ 6)) ^ 3 * y
      = ((3 : ℕ) : ZMod (3 ^ 6)) ^ 3 * ((ZMod.cast y : ZMod (3 ^ 3)).val : ZMod (3 ^ 6)) := by
  decide

/-- The class of `27α` modulo `243` is `27` times the class of `α` modulo `9`. -/
theorem toZModPow_five_pow_three_mul (α : ℤ_[3]) :
    PadicInt.toZModPow 5 (((3 : ℕ) : ℤ_[3]) ^ 3 * α)
      = ((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * ((PadicInt.toZModPow 2 α).val : ZMod (3 ^ 5)) := by
  rw [map_mul, map_pow, map_natCast, ← PadicInt.cast_toZModPow 2 5 (by norm_num) α]
  exact pow_three_mul_eq_pow_three_mul_val_five _

/-- The class of `27α` modulo `729` is `27` times the class of `α` modulo `27`. -/
theorem toZModPow_six_pow_three_mul (α : ℤ_[3]) :
    PadicInt.toZModPow 6 (((3 : ℕ) : ℤ_[3]) ^ 3 * α)
      = ((3 : ℕ) : ZMod (3 ^ 6)) ^ 3 * ((PadicInt.toZModPow 3 α).val : ZMod (3 ^ 6)) := by
  rw [map_mul, map_pow, map_natCast, ← PadicInt.cast_toZModPow 3 6 (by norm_num) α]
  exact pow_three_mul_eq_pow_three_mul_val_six _

/-- `9 ∤ 4α³ + β²`, read modulo `9`, refutes `27 ∣ 4α³ + β²`. -/
theorem not_pow_three_dvd_of_toZModPow_two {α β : ℤ_[3]}
    (h : 4 * (PadicInt.toZModPow 2 α) ^ 3 + (PadicInt.toZModPow 2 β) ^ 2 ≠ 0) :
    ¬ ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ 4 * α ^ 3 + β ^ 2 := by
  intro h27
  refine h ?_
  have h9 : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ 4 * α ^ 3 + β ^ 2 :=
    (pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans h27
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_pow,
    map_ofNat] at h9
  exact h9

/-- `27 ∤ 4α³ + β²`, read modulo `27`. -/
theorem not_pow_three_dvd_of_toZModPow_three {α β : ℤ_[3]}
    (h : 4 * (PadicInt.toZModPow 3 α) ^ 3 + (PadicInt.toZModPow 3 β) ^ 2 ≠ 0) :
    ¬ ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ 4 * α ^ 3 + β ^ 2 := by
  intro h27
  refine h ?_
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_pow,
    map_ofNat] at h27
  exact h27

/-! ### The four unit starred loci, by `decide` on the lifted residues -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `81` pairs modulo `9`, each tested against an eighteen-element `Finset` literal in `ZMod 243`
/-- On the `(IV*, 1)` unit locus, `9 ∤ 4α³ + β²`. -/
theorem headResIVstarOneUnitThree_cell : ∀ A B : ZMod (3 ^ 2),
    (((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * (A.val : ZMod (3 ^ 5)),
      ((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * (B.val : ZMod (3 ^ 5))) ∈ headResIVstarOneUnitThree →
    4 * A ^ 3 + B ^ 2 ≠ 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- as for `headResIVstarOneUnitThree_cell`
/-- On the `(IV*, 3)` unit locus, `9 ∤ 4α³ + β²`. -/
theorem headResIVstarThreeUnitThree_cell : ∀ A B : ZMod (3 ^ 2),
    (((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * (A.val : ZMod (3 ^ 5)),
      ((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * (B.val : ZMod (3 ^ 5))) ∈ headResIVstarThreeUnitThree →
    4 * A ^ 3 + B ^ 2 ≠ 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- as for `headResIVstarOneUnitThree_cell`
/-- On the `(III*, 2)` unit locus, `9 ∤ 4α³ + β²`. -/
theorem headResIIIstarUnitThree_cell : ∀ A B : ZMod (3 ^ 2),
    (((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * (A.val : ZMod (3 ^ 5)),
      ((3 : ℕ) : ZMod (3 ^ 5)) ^ 3 * (B.val : ZMod (3 ^ 5))) ∈ headResIIIstarUnitThree →
    4 * A ^ 3 + B ^ 2 ≠ 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- `729` pairs modulo `27`, each tested against a thirty-six-element `Finset` literal in `ZMod 729`
/-- On the `(II*, 1)` unit locus, `27 ∤ 4α³ + β²`, although `9 ∣ 4α³ + β²` there. -/
theorem headResIIstarUnitThree_cell : ∀ A B : ZMod (3 ^ 3),
    (((3 : ℕ) : ZMod (3 ^ 6)) ^ 3 * (A.val : ZMod (3 ^ 6)),
      ((3 : ℕ) : ZMod (3 ^ 6)) ^ 3 * (B.val : ZMod (3 ^ 6))) ∈ headResIIstarUnitThree →
    4 * A ^ 3 + B ^ 2 ≠ 0 := by
  decide

/-- The `(IV*, 1)` unit locus is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_ivStarOneUnit3Locus : Disjoint familyBCell ivStarOneUnit3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, β, h1, h2, -, -, h27⟩ := hx
  rw [ivStarOneUnit3Locus, Set.mem_preimage, Finset.mem_coe, PadicInt.redPairPow, h1, h2,
    toZModPow_five_pow_three_mul, toZModPow_five_pow_three_mul] at hx'
  exact not_pow_three_dvd_of_toZModPow_two (headResIVstarOneUnitThree_cell _ _ hx') h27

/-- The `(IV*, 3)` unit locus is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_ivStarThreeUnit3Locus :
    Disjoint familyBCell ivStarThreeUnit3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, β, h1, h2, -, -, h27⟩ := hx
  rw [ivStarThreeUnit3Locus, Set.mem_preimage, Finset.mem_coe, PadicInt.redPairPow, h1, h2,
    toZModPow_five_pow_three_mul, toZModPow_five_pow_three_mul] at hx'
  exact not_pow_three_dvd_of_toZModPow_two (headResIVstarThreeUnitThree_cell _ _ hx') h27

/-- The `(III*, 2)` unit locus is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iiiStarUnit3Locus : Disjoint familyBCell iiiStarUnit3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, β, h1, h2, -, -, h27⟩ := hx
  rw [iiiStarUnit3Locus, Set.mem_preimage, Finset.mem_coe, PadicInt.redPairPow, h1, h2,
    toZModPow_five_pow_three_mul, toZModPow_five_pow_three_mul] at hx'
  exact not_pow_three_dvd_of_toZModPow_two (headResIIIstarUnitThree_cell _ _ hx') h27

/-- The `(II*, 1)` unit locus is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iiStarUnit3Locus : Disjoint familyBCell iiStarUnit3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, β, h1, h2, -, -, h27⟩ := hx
  rw [iiStarUnit3Locus, Set.mem_preimage, Finset.mem_coe, PadicInt.redPairPow, h1, h2,
    toZModPow_six_pow_three_mul, toZModPow_six_pow_three_mul] at hx'
  exact not_pow_three_dvd_of_toZModPow_three (headResIIstarUnitThree_cell _ _ hx') h27

/-! ### The `3⁴ ∣ a₆` starred loci -/

/-- The `(IV*, 1)` locus with `3⁴ ∣ a₆` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_ivStarOne3Locus : Disjoint familyBCell ivStarOne3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, β, -, h2, -, hβ, -⟩ := hx
  obtain ⟨-, b, -, -, hb, -⟩ := exists_form_of_mem_ivStarOne3Locus hx'
  exact hβ (dvd_of_pow_three_mul_eq_pow_mul (by norm_num) (h2.symm.trans hb))

/-- The `(IV*, 3)` locus with `3⁴ ∣ a₆` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_ivStarThree3Locus : Disjoint familyBCell ivStarThree3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, β, -, h2, -, hβ, -⟩ := hx
  obtain ⟨-, b, -, -, hb, -⟩ := exists_form_of_mem_ivStarThree3Locus hx'
  exact hβ (dvd_of_pow_three_mul_eq_pow_mul (by norm_num) (h2.symm.trans hb))

/-- The `III*` locus with `3⁴ ∣ a₆` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iiiStar3Locus : Disjoint familyBCell iiiStar3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, β, -, h2, -, hβ, -⟩ := hx
  obtain ⟨-, c, -, hc, -⟩ := exists_form_of_mem_iiiStar3Locus hx'
  exact hβ (dvd_of_pow_three_mul_eq_pow_mul (by norm_num) (h2.symm.trans hc))

/-- The `II*` locus with `3⁴ ∣ a₆` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iiStar3Locus : Disjoint familyBCell iiStar3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, β, -, h2, -, hβ, -⟩ := hx
  obtain ⟨-, c, -, hc, -⟩ := exists_form_of_mem_iiStar3Locus hx'
  exact hβ (dvd_of_pow_three_mul_eq_pow_mul (by norm_num) (h2.symm.trans hc))

/-! ### The `v₃(a₄) = 1` loci: the two `I₀*` cylinders and Family A -/

/-- The `I₀*` cylinder `IZeroStarUnitThree.locus 2`, where `v₃(a₄) = 1`, is disjoint from the
Family-B cell. -/
theorem disjoint_familyBCell_locus_two : Disjoint familyBCell (IZeroStarUnitThree.locus 2) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, -, h1, -, -, -, -⟩ := hx
  obtain ⟨α', -, h1', hα', -, -, -⟩ :=
    IZeroStarUnitThree.exists_form_of_mem_locus IZeroStarUnitThree.res_cast_snd_two hx'
  exact hα' (dvd_of_mul_eq_pow_three_mul (h1'.symm.trans h1))

/-- The `I₀*` cylinder `IZeroStarUnitThree.locus 1`, where `v₃(a₄) = 1`, is disjoint from the
Family-B cell. -/
theorem disjoint_familyBCell_locus_one : Disjoint familyBCell (IZeroStarUnitThree.locus 1) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, -, h1, -, -, -, -⟩ := hx
  obtain ⟨α', -, h1', hα', -, -, -⟩ :=
    IZeroStarUnitThree.exists_form_of_mem_locus IZeroStarUnitThree.res_cast_snd_one hx'
  exact hα' (dvd_of_mul_eq_pow_three_mul (h1'.symm.trans h1))

/-- The Family-A locus, where `v₃(a₄) = 1`, is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_FamilyAThree_locus : Disjoint familyBCell FamilyAThree.locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, -, h1, -, -, -, -⟩ := hx
  obtain ⟨α', h1', hα', -, -⟩ := FamilyAThree.exists_form_of_mem_locus hx'
  exact hα' (dvd_of_mul_eq_pow_three_mul (h1'.symm.trans h1))

/-! ### The `9 ∣ a₄` loci -/

/-- The `(I₀*, 1)` locus, where `a₄ ≡ -9 (mod 27)`, is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iZeroStarOne3Locus : Disjoint familyBCell iZeroStarOne3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  refine cast_ne_zero_of_cast_add_nine (PadicInt.toZModPow 4 x.1)
    (headResIZeroStarOneThree_cast_three (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2)
      (mem_iZeroStarOne3Locus_iff.1 hx')) ?_
  rw [PadicInt.cast_toZModPow 3 4 (by norm_num)]
  exact (toZModPow_three_eq_zero_of_mem_familyBCell hx).1

/-- The `(I₀*, 2)` locus, where `a₄ ≡ 9 (mod 27)`, is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iZeroStarTwo3Locus : Disjoint familyBCell iZeroStarTwo3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  refine cast_ne_zero_of_cast_sub_nine (PadicInt.toZModPow 4 x.1)
    (headResIZeroStarTwoThree_cast_three (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2)
      (mem_iZeroStarTwo3Locus_iff.1 hx')) ?_
  rw [PadicInt.cast_toZModPow 3 4 (by norm_num)]
  exact (toZModPow_three_eq_zero_of_mem_familyBCell hx).1

/-- The `(I₀*, 4)` locus, where `a₄ ≡ -9 (mod 27)`, is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iZeroStarFour3Locus : Disjoint familyBCell iZeroStarFour3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  refine cast_ne_zero_of_cast_add_nine (PadicInt.toZModPow 4 x.1)
    (headResIZeroStarFourThree_cast_three (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2)
      (mem_iZeroStarFour3Locus_iff.1 hx')) ?_
  rw [PadicInt.cast_toZModPow 3 4 (by norm_num)]
  exact (toZModPow_three_eq_zero_of_mem_familyBCell hx).1

/-! ### The shallow loci -/

/-- The shallow locus `one3LocusFull` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_one3LocusFull : Disjoint familyBCell one3LocusFull := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨h1, h2⟩ := toZModPow_three_eq_zero_of_mem_familyBCell hx
  have h := mem_one3LocusFull_iff.1 hx'
  rw [h1, h2] at h
  exact not_headResOneThreeFull_zero h

/-- The shallow locus `iii3Locus` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iii3Locus : Disjoint familyBCell iii3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨h1, h2⟩ := toZModPow_three_eq_zero_of_mem_familyBCell hx
  have h := mem_iii3Locus_iff.1 hx'
  rw [← PadicInt.cast_toZModPow 2 3 (by norm_num) x.1,
    ← PadicInt.cast_toZModPow 2 3 (by norm_num) x.2, h1, h2, ZMod.cast_zero] at h
  exact not_headResThree_zero h

/-- The shallow locus `iv3Locus` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_iv3Locus : Disjoint familyBCell iv3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨h1, h2⟩ := toZModPow_three_eq_zero_of_mem_familyBCell hx
  have h := mem_iv3Locus_iff.1 hx'
  rw [h1, h2] at h
  exact not_headResIVThree_zero h

/-! ### The four rows -/

/-- The assembled locus of row `1` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_rowOneCore3Locus : Disjoint familyBCell rowOneCore3Locus := by
  rw [rowOneCore3Locus, rowOneIZeroStar3Locus, rowOneStarred3Locus]
  exact Set.disjoint_union_right.2
    ⟨Set.disjoint_union_right.2
        ⟨disjoint_familyBCell_one3LocusFull,
          Set.disjoint_union_right.2
            ⟨disjoint_familyBCell_iZeroStarOne3Locus, disjoint_familyBCell_locus_two⟩⟩,
      Set.disjoint_union_right.2
        ⟨Set.disjoint_union_right.2
            ⟨disjoint_familyBCell_ivStarOneUnit3Locus, disjoint_familyBCell_ivStarOne3Locus⟩,
          Set.disjoint_union_right.2
            ⟨disjoint_familyBCell_iiStarUnit3Locus, disjoint_familyBCell_iiStar3Locus⟩⟩⟩

/-- The full assembled locus of row `2` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_rowTwoFull3Locus : Disjoint familyBCell rowTwoFull3Locus := by
  rw [rowTwoFull3Locus, rowTwoCore3Locus, rowTwoIZeroStar3Locus, rowTwoStarred3Locus]
  exact Set.disjoint_union_right.2
    ⟨Set.disjoint_union_right.2
        ⟨Set.disjoint_union_right.2
            ⟨disjoint_familyBCell_iii3Locus,
              Set.disjoint_union_right.2
                ⟨disjoint_familyBCell_iZeroStarTwo3Locus, disjoint_familyBCell_locus_one⟩⟩,
          Set.disjoint_union_right.2
            ⟨disjoint_familyBCell_iiiStarUnit3Locus, disjoint_familyBCell_iiiStar3Locus⟩⟩,
      disjoint_familyBCell_FamilyAThree_locus.mono_right (FamilyAThree.part_subset_locus 2)⟩

/-- The assembled locus of row `3` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_rowThreeCore3Locus :
    Disjoint familyBCell rowThreeCore3Locus := by
  rw [rowThreeCore3Locus, rowThreeStarred3Locus]
  exact Set.disjoint_union_right.2
    ⟨disjoint_familyBCell_iv3Locus,
      Set.disjoint_union_right.2
        ⟨disjoint_familyBCell_ivStarThreeUnit3Locus, disjoint_familyBCell_ivStarThree3Locus⟩⟩

/-- The full assembled locus of row `4` is disjoint from the Family-B cell. -/
theorem disjoint_familyBCell_rowFourFull3Locus : Disjoint familyBCell rowFourFull3Locus := by
  rw [rowFourFull3Locus]
  exact Set.disjoint_union_right.2
    ⟨disjoint_familyBCell_iZeroStarFour3Locus,
      disjoint_familyBCell_FamilyAThree_locus.mono_right (FamilyAThree.part_subset_locus 4)⟩

/-! ### The row and column theorems, with Family B required only to lie in the cell -/

/-- If `B` is a measurable subset of the Family-B cell inside `headMinimal 3 1` of volume
`65 / 2125764`, then `1924841 / 2125728 ≤ δ 3 1`. -/
theorem row_one_close_at_three_of_cell (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B)
    (hBsub : B ⊆ headMinimal 3 1)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 65 / 2125764) (hBcell : B ⊆ familyBCell) :
    (1924841 : ℝ≥0∞) / 2125728 ≤ δ 3 1 :=
  row_one_close_at_three B hB hBsub hBvol
    (disjoint_familyBCell_rowOneCore3Locus.mono_left hBcell)

/-- If `FamilyAThree.part 2` has half the volume of `FamilyAThree.locus` and `B` is a measurable
subset of the Family-B cell inside `headMinimal 3 2` of volume `17 / 6377292`, then
`509345 / 6377184 ≤ δ 3 2`. -/
theorem row_two_close_at_three_of_cell
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 2)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus)
    (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B) (hBsub : B ⊆ headMinimal 3 2)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 17 / 6377292) (hBcell : B ⊆ familyBCell) :
    (509345 : ℝ≥0∞) / 6377184 ≤ δ 3 2 :=
  row_two_close_at_three hhalf B hB hBsub hBvol
    (disjoint_familyBCell_rowTwoFull3Locus.mono_left hBcell)

/-- If `B` is a measurable subset of the Family-B cell inside `headMinimal 3 3` of volume
`2 / 4782969`, then `30619 / 2391444 ≤ δ 3 3`. -/
theorem row_three_close_at_three_of_cell (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B)
    (hBsub : B ⊆ headMinimal 3 3)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 2 / 4782969) (hBcell : B ⊆ familyBCell) :
    (30619 : ℝ≥0∞) / 2391444 ≤ δ 3 3 :=
  row_three_close_at_three B hB hBsub hBvol
    (disjoint_familyBCell_rowThreeCore3Locus.mono_left hBcell)

/-- If `FamilyAThree.part 4` has half the volume of `FamilyAThree.locus` and `B` is a measurable
subset of the Family-B cell inside `headMinimal 3 4` of volume `2 / 14348907`, then
`1193 / 652212 ≤ δ 3 4`. -/
theorem row_four_close_at_three_of_cell
    (hhalf : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 4)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus)
    (B : Set (ℤ_[3] × ℤ_[3])) (hB : MeasurableSet B) (hBsub : B ⊆ headMinimal 3 4)
    (hBvol : (volume : Measure (ℤ_[3] × ℤ_[3])) B = 2 / 14348907) (hBcell : B ⊆ familyBCell) :
    (1193 : ℝ≥0∞) / 652212 ≤ δ 3 4 :=
  row_four_close_at_three hhalf B hB hBsub hBvol
    (disjoint_familyBCell_rowFourFull3Locus.mono_left hBcell)

/-- **`HasGOTDensities 3` from the halving of Family A and four Family-B sets in the cell.** Each
`Bₜ` is a measurable subset of `familyBCell` of the row's stated mass, inside the minimal part of
its row. -/
theorem hasGOTDensities_three_of_cell
    (hhalf₂ : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 2)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus)
    (hhalf₄ : 2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (FamilyAThree.part 4)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) FamilyAThree.locus)
    (B₁ B₂ B₃ B₄ : Set (ℤ_[3] × ℤ_[3]))
    (hB₁ : MeasurableSet B₁) (hB₁sub : B₁ ⊆ headMinimal 3 1)
    (hB₁vol : (volume : Measure (ℤ_[3] × ℤ_[3])) B₁ = 65 / 2125764) (hB₁cell : B₁ ⊆ familyBCell)
    (hB₂ : MeasurableSet B₂) (hB₂sub : B₂ ⊆ headMinimal 3 2)
    (hB₂vol : (volume : Measure (ℤ_[3] × ℤ_[3])) B₂ = 17 / 6377292) (hB₂cell : B₂ ⊆ familyBCell)
    (hB₃ : MeasurableSet B₃) (hB₃sub : B₃ ⊆ headMinimal 3 3)
    (hB₃vol : (volume : Measure (ℤ_[3] × ℤ_[3])) B₃ = 2 / 4782969) (hB₃cell : B₃ ⊆ familyBCell)
    (hB₄ : MeasurableSet B₄) (hB₄sub : B₄ ⊆ headMinimal 3 4)
    (hB₄vol : (volume : Measure (ℤ_[3] × ℤ_[3])) B₄ = 2 / 14348907)
    (hB₄cell : B₄ ⊆ familyBCell) :
    HasGOTDensities 3 :=
  hasGOTDensities_of_headLowerBounds_at_three
    (row_one_close_at_three_of_cell B₁ hB₁ hB₁sub hB₁vol hB₁cell)
    (row_two_close_at_three_of_cell hhalf₂ B₂ hB₂ hB₂sub hB₂vol hB₂cell)
    (row_three_close_at_three_of_cell B₃ hB₃ hB₃sub hB₃vol hB₃cell)
    (row_four_close_at_three_of_cell hhalf₄ B₄ hB₄ hB₄sub hB₄vol hB₄cell)

end WeierstrassCurve

end
