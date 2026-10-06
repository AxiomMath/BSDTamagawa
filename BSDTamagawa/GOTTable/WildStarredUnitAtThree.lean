/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildStarredUnitRunAtThree

/-!
# The starred strata at `p = 3` over a unit `a₆/3³`

Short models over `ℤ_3` with `3³ ∣ a₄` and `v₃(a₆) = 3` exactly form two thirds of the region
`{3³ ∣ a₄, 3³ ∣ a₆}`, and two thirds of every starred stratum inside it. Writing `a₄ = 27α`,
`a₆ = 27β` with `3 ∤ β`, and `3w = β² + 3α - 1` (an integer because `β` is a unit), the starred
strata of this region are

    `(IV*,  3)`   `3 ∤ w`, `-4βw ≡ 1`                     mass `2/6561`
    `(IV*,  1)`   `3 ∤ w`, `-4βw ≢ 1`                     mass `2/6561`
    `(III*, 2)`   `3 ∣ w`, `3 ∤ α + β²`                   mass `4/19683`
    `(II*,  1)`   `3 ∣ w`, `3 ∣ α + β²`, `3 ∤ w/3`        mass `4/59049`

Together with the loci where `3⁴ ∣ a₆`, these exhaust `IV*`, `III*` and `II*` inside the region:
the masses add to `1/2187`, `1/2187`, `2/6561` and `2/19683`.

The `x`-shift of Tate's algorithm through Step 8 is `3μ` with `μ = -β + 3j` a unit, where the
digit `j` is not determined by the curve. The `b`-invariants of the curve Step 8 hands on are

    `b₂ = 3²·4μ`,    `b₄ = 3³·2(α + μ²)`,    `b₆ = 3³·4(β + 3μα + μ³)`,

and `β + 3μα + μ³ = 3(-βw + 3(…))`, so each branch condition of Steps 8, 9 and 10 is independent
of `j`.

## Main results

* `WeierstrassCurve.volume_ivStarThreeUnit3Locus`, `WeierstrassCurve.volume_ivStarOneUnit3Locus`,
  `WeierstrassCurve.volume_iiiStarUnit3Locus`, `WeierstrassCurve.volume_iiStarUnit3Locus`: the
  masses `2/6561`, `2/6561`, `4/19683`, `4/59049` of the four loci.

## Implementation notes

`Δ ≠ 0` does not follow from `3 ∤ β` on this region: `4a₄³ + 27a₆² = 3⁹(4α³ + β²)` vanishes at
`(α, β) = (-1, 2)`, so `a₄ = -27`, `a₆ = 54` is singular with `β` a unit. Each locus avoids the
singular points by its own branch condition (`pow_two_dvd_w_of_Δ_eq_zero`).
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

/-! ### The four loci and their masses

Each locus is a `PadicInt.redPairPow` preimage, at depth `5` for the three that `a₄` modulo `81`
and `a₆` modulo `243` decide, and at depth `6` for `II*`, whose Step-10 test reads one digit
deeper. The class counts `18`, `18`, `12`, `36` give masses `2/6561`, `2/6561`, `4/19683`,
`4/59049`, in each case twice the mass of the corresponding locus with `3⁴ ∣ a₆`. -/

open StarredUnitThree StarredThree BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction
  TateAlgorithm

/-- The eighteen classes of the **`(IV*, 3)` locus over a unit `β`** at `3`. -/
def headResIVstarThreeUnitThree : Finset (ZMod (3 ^ 5) × ZMod (3 ^ 5)) :=
  {(0, 54), (0, 108), (27, 189), (27, 216), (54, 27), (54, 135), (81, 54), (81, 108),
    (108, 189), (108, 216), (135, 27), (135, 135), (162, 54), (162, 108), (189, 189),
    (189, 216), (216, 27), (216, 135)}

/-- The eighteen classes of the **`(IV*, 1)` locus over a unit `β`** at `3`. -/
def headResIVstarOneUnitThree : Finset (ZMod (3 ^ 5) × ZMod (3 ^ 5)) :=
  {(0, 135), (0, 189), (27, 27), (27, 54), (54, 108), (54, 216), (81, 135), (81, 189),
    (108, 27), (108, 54), (135, 108), (135, 216), (162, 135), (162, 189), (189, 27), (189, 54),
    (216, 108), (216, 216)}

/-- The twelve classes of the **`(III*, 2)` locus over a unit `β`** at `3`. -/
def headResIIIstarUnitThree : Finset (ZMod (3 ^ 5) × ZMod (3 ^ 5)) :=
  {(0, 27), (0, 216), (27, 108), (27, 135), (81, 27), (81, 216), (108, 108), (108, 135),
    (162, 27), (162, 216), (189, 108), (189, 135)}

/-- The thirty-six classes of the **`(II*, 1)` locus over a unit `β`** at `3`, at depth `6`. -/
def headResIIstarUnitThree : Finset (ZMod (3 ^ 6) × ZMod (3 ^ 6)) :=
  {(54, 54), (54, 297), (54, 432), (54, 675), (135, 54), (135, 189), (135, 540), (135, 675),
    (216, 189), (216, 297), (216, 432), (216, 540), (297, 54), (297, 297), (297, 432),
    (297, 675), (378, 54), (378, 189), (378, 540), (378, 675), (459, 189), (459, 297),
    (459, 432), (459, 540), (540, 54), (540, 297), (540, 432), (540, 675), (621, 54),
    (621, 189), (621, 540), (621, 675), (702, 189), (702, 297), (702, 432), (702, 540)}

-- The `Finset` literals live in `ZMod 243` and `ZMod 729`, whose `DecidableEq` unfolds through
-- `Nat.mod`; deduplicating eighteen or thirty-six of them outruns the default recursion depth.
set_option maxRecDepth 40000 in
/-- The `(IV*, 3)` locus over a unit `β` consists of eighteen residue classes modulo `3⁵`. -/
theorem card_headResIVstarThreeUnitThree : headResIVstarThreeUnitThree.card = 18 := by decide

set_option maxRecDepth 40000 in
/-- The `(IV*, 1)` locus over a unit `β` consists of eighteen residue classes modulo `3⁵`. -/
theorem card_headResIVstarOneUnitThree : headResIVstarOneUnitThree.card = 18 := by decide

set_option maxRecDepth 40000 in
/-- The `(III*, 2)` locus over a unit `β` consists of twelve residue classes modulo `3⁵`. -/
theorem card_headResIIIstarUnitThree : headResIIIstarUnitThree.card = 12 := by decide

set_option maxRecDepth 100000 in
/-- The `(II*, 1)` locus over a unit `β` consists of thirty-six residue classes modulo `3⁶`. -/
theorem card_headResIIstarUnitThree : headResIIstarUnitThree.card = 36 := by decide

/-- The **`(IV*, 3)` locus over a unit `β`** of the coefficient plane at `3`. -/
noncomputable def ivStarThreeUnit3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 5 ⁻¹' (headResIVstarThreeUnitThree : Set (ZMod (3 ^ 5) × ZMod (3 ^ 5)))

/-- The **`(IV*, 1)` locus over a unit `β`** of the coefficient plane at `3`. -/
noncomputable def ivStarOneUnit3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 5 ⁻¹' (headResIVstarOneUnitThree : Set (ZMod (3 ^ 5) × ZMod (3 ^ 5)))

/-- The **`(III*, 2)` locus over a unit `β`** of the coefficient plane at `3`. -/
noncomputable def iiiStarUnit3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 5 ⁻¹' (headResIIIstarUnitThree : Set (ZMod (3 ^ 5) × ZMod (3 ^ 5)))

/-- The **`(II*, 1)` locus over a unit `β`** of the coefficient plane at `3`. -/
noncomputable def iiStarUnit3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 6 ⁻¹' (headResIIstarUnitThree : Set (ZMod (3 ^ 6) × ZMod (3 ^ 6)))

/-- The `(IV*, 3)` locus over a unit `β` at `3` is measurable. -/
theorem measurableSet_ivStarThreeUnit3Locus : MeasurableSet ivStarThreeUnit3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResIVstarThreeUnitThree

/-- The `(IV*, 1)` locus over a unit `β` at `3` is measurable. -/
theorem measurableSet_ivStarOneUnit3Locus : MeasurableSet ivStarOneUnit3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResIVstarOneUnitThree

/-- The `(III*, 2)` locus over a unit `β` at `3` is measurable. -/
theorem measurableSet_iiiStarUnit3Locus : MeasurableSet iiiStarUnit3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResIIIstarUnitThree

/-- The `(II*, 1)` locus over a unit `β` at `3` is measurable. -/
theorem measurableSet_iiStarUnit3Locus : MeasurableSet iiStarUnit3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResIIstarUnitThree

/-- `18 · 3⁻¹⁰ = 18/59049 = 2/6561`. -/
theorem eighteen_mul_inv_pow_ten_three_eq :
    ((18 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 5) = 2 / 6561 := by
  rw [show ((18 : ℕ) : ℝ≥0∞) = 18 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 5) = 59049 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `12 · 3⁻¹⁰ = 12/59049 = 4/19683`. -/
theorem twelve_mul_inv_pow_ten_three_eq :
    ((12 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 5) = 4 / 19683 := by
  rw [show ((12 : ℕ) : ℝ≥0∞) = 12 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 5) = 59049 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `36 · 3⁻¹² = 36/531441 = 4/59049`. -/
theorem thirtySix_mul_inv_pow_twelve_three_eq :
    ((36 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 6) = 4 / 59049 := by
  rw [show ((36 : ℕ) : ℝ≥0∞) = 36 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 6) = 531441 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the `(IV*, 3)` unit locus at `3` is `18/59049 = 2/6561`** — twice
`volume_ivStarThree3Locus`, so the two together are the full stratum mass `1/2187`. -/
theorem volume_ivStarThreeUnit3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) ivStarThreeUnit3Locus = 2 / 6561 := by
  rw [ivStarThreeUnit3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResIVstarThreeUnitThree, eighteen_mul_inv_pow_ten_three_eq]

/-- **The mass of the `(IV*, 1)` unit locus at `3` is `18/59049 = 2/6561`.** -/
theorem volume_ivStarOneUnit3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) ivStarOneUnit3Locus = 2 / 6561 := by
  rw [ivStarOneUnit3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResIVstarOneUnitThree, eighteen_mul_inv_pow_ten_three_eq]

/-- **The mass of the `(III*, 2)` unit locus at `3` is `12/59049 = 4/19683`.** -/
theorem volume_iiiStarUnit3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iiiStarUnit3Locus = 4 / 19683 := by
  rw [iiiStarUnit3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResIIIstarUnitThree, twelve_mul_inv_pow_ten_three_eq]

/-- **The mass of the `(II*, 1)` unit locus at `3` is `36/531441 = 4/59049`.** -/
theorem volume_iiStarUnit3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iiStarUnit3Locus = 4 / 59049 := by
  rw [iiStarUnit3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResIIstarUnitThree, thirtySix_mul_inv_pow_twelve_three_eq]

/-! ### Reading a class off its numerals -/

/-- A `toZModPow` equation against a natural numeral is a divisibility of the difference. -/
theorem pow_dvd_sub_natCast_of_toZModPow {x : ℤ_[3]} {n k : ℕ}
    (h : PadicInt.toZModPow n x = (k : ZMod (3 ^ n))) :
    ((3 : ℕ) : ℤ_[3]) ^ n ∣ x - (k : ℤ_[3]) := by
  rw [← PadicInt.toZModPow_eq_iff_pow_dvd_sub, h, map_natCast]

/-- `3 ∤ k` as naturals transfers to `ℤ_[3]`. -/
theorem not_dvd_natCast_of_not_dvd {k : ℕ} (h : ¬ (3 : ℕ) ∣ k) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ (k : ℤ_[3]) := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_natCast]
  rw [show ((3 : ℕ) : ℕ) = 3 from rfl] at h
  exact fun hz => h ((ZMod.natCast_eq_zero_iff k 3).mp hz)

/-- A residue modulo `3` reached through a numeral plus a multiple of `3ⁿ`, `n ≥ 1`. -/
theorem toZMod_natCast_add {k : ℕ} {n : ℕ} (hn : 1 ≤ n) (y : ℤ_[3]) :
    PadicInt.toZMod ((k : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ n * y) = (k : ZMod 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [map_add, map_mul, map_pow,
    show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by rw [← PadicInt.dvd_iff_toZMod_eq_zero],
    zero_pow (by omega), zero_mul, add_zero, map_natCast]

/-- `3ⁿ ∣ x - 27A` with `27 ∣ 27A` gives `27 ∣ x`, for `n ≥ 3`. -/
theorem pow_three_dvd_of_sub {x : ℤ_[3]} {n A : ℕ} (hn : 3 ≤ n)
    (h : ((3 : ℕ) : ℤ_[3]) ^ n ∣ x - ((27 * A : ℕ) : ℤ_[3])) : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(A : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ (n - 3) * c, ?_⟩
  rw [show x = ((27 * A : ℕ) : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ n * c from by linear_combination hc,
    show ((3 : ℕ) : ℤ_[3]) ^ n = ((3 : ℕ) : ℤ_[3]) ^ 3 * ((3 : ℕ) : ℤ_[3]) ^ (n - 3) from by
      rw [← pow_add]; congr 1; omega]
  push_cast
  ring

/-! ### The shape of a point of each locus

Each class pins `a₄` and `a₆` modulo `3⁵` (or `3⁶`), and so determines `a₄ = 27α`, `a₆ = 27β` with
`3 ∤ β`, together with the residue of `w = (β² + 3α - 1)/3`. -/

/-- From `a₄ ≡ 27A` and `a₆ ≡ 27B` modulo `3^(n+3)`, a point of the coefficient plane is
`a₄ = 27α`, `a₆ = 27β` with `α = A + 3ⁿk`, `β = B + 3ⁿ⁺¹l`, and `w = W + 3ⁿ(…)` where
`3W = B² + 3A - 1`. -/
theorem exists_unit_form {x : ℤ_[3] × ℤ_[3]} {n : ℕ} {A B W : ℤ_[3]}
    (h₄ : ((3 : ℕ) : ℤ_[3]) ^ (n + 1 + 3) ∣ x.1 - ((3 : ℕ) : ℤ_[3]) ^ 3 * A)
    (h₆ : ((3 : ℕ) : ℤ_[3]) ^ (n + 1 + 3) ∣ x.2 - ((3 : ℕ) : ℤ_[3]) ^ 3 * B)
    (hd₄ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1) (hd₆ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.2)
    (hW : ((3 : ℕ) : ℤ_[3]) * W = B ^ 2 + ((3 : ℕ) : ℤ_[3]) * A - 1) :
    ∃ α β w l m : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * β ∧
      ((3 : ℕ) : ℤ_[3]) * w = β ^ 2 + ((3 : ℕ) : ℤ_[3]) * α - 1 ∧
      β = B + ((3 : ℕ) : ℤ_[3]) ^ (n + 1) * l ∧ w = W + ((3 : ℕ) : ℤ_[3]) ^ n * m := by
  obtain ⟨α, hα⟩ := hd₄
  obtain ⟨β, hβ⟩ := hd₆
  obtain ⟨k, hk⟩ : ∃ k : ℤ_[3], α = A + ((3 : ℕ) : ℤ_[3]) ^ (n + 1) * k := by
    obtain ⟨c, hc⟩ := h₄
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_⟩
    rw [hα] at hc
    rw [show ((3 : ℕ) : ℤ_[3]) ^ (n + 1 + 3)
        = ((3 : ℕ) : ℤ_[3]) ^ 3 * ((3 : ℕ) : ℤ_[3]) ^ (n + 1) from by
      rw [← pow_add]; ring_nf] at hc
    linear_combination hc
  obtain ⟨l, hl⟩ : ∃ l : ℤ_[3], β = B + ((3 : ℕ) : ℤ_[3]) ^ (n + 1) * l := by
    obtain ⟨c, hc⟩ := h₆
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_⟩
    rw [hβ] at hc
    rw [show ((3 : ℕ) : ℤ_[3]) ^ (n + 1 + 3)
        = ((3 : ℕ) : ℤ_[3]) ^ 3 * ((3 : ℕ) : ℤ_[3]) ^ (n + 1) from by
      rw [← pow_add]; ring_nf] at hc
    linear_combination hc
  refine ⟨α, β, W + ((3 : ℕ) : ℤ_[3]) ^ n * (2 * B * l + ((3 : ℕ) : ℤ_[3]) ^ (n + 1) * l ^ 2
      + ((3 : ℕ) : ℤ_[3]) * k), l,
    2 * B * l + ((3 : ℕ) : ℤ_[3]) ^ (n + 1) * l ^ 2 + ((3 : ℕ) : ℤ_[3]) * k, hα, hβ, ?_, hl, rfl⟩
  rw [hk, hl]
  push_cast at hW ⊢
  linear_combination hW

/-! ### From the shape to stratum membership

`Δ ≠ 0` comes from `pow_two_dvd_w_of_Δ_eq_zero` against the branch condition. -/

open scoped Classical in
/-- If `a₄ = 27α`, `a₆ = 27β` with `3 ∤ β`, `3w = β² + 3α - 1` and `3 ∤ w`, then the point lies
in the `(IV*, c)` stratum, with `c = 3` or `1` according as the residue of `-4βw` is a square. -/
theorem mem_stratFibre_IVstar_of_form {x : ℤ_[3] × ℤ_[3]} {α β w : ℤ_[3]}
    (h₄ : x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α) (h₆ : x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * β)
    (hβ : ¬ ((3 : ℕ) : ℤ_[3]) ∣ β)
    (hw : ((3 : ℕ) : ℤ_[3]) * w = β ^ 2 + ((3 : ℕ) : ℤ_[3]) * α - 1)
    (hwu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ w) {c : ℕ}
    (hc : c = if IsSquare (PadicInt.toZMod (-(4 * (β * w)))) then 3 else 1) :
    x ∈ stratFibre 3 (KodairaSymbol.IV!, c) := by
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h => hwu
    ((dvd_pow_self _ two_ne_zero).trans
      (pow_two_dvd_w_of_Δ_eq_zero (p := 3) rfl h₄ h₆ hw h).1)
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IVstar_unit_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 3 * α) (((3 : ℕ) : ℤ_[3]) ^ 3 * β)).Δ ≠ 0 from by
      rw [← h₄, ← h₆]; exact hΔ) rfl rfl hβ hw hwu
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  refine Prod.ext (by simp only [h₄, h₆]; exact hks) ?_
  simp only [h₄, h₆]
  rw [hts, hc]

open scoped Classical in
/-- If `a₄ = 27α`, `a₆ = 27β` with `3 ∤ β`, `3 ∣ w` and `3 ∤ α + β²`, then the point lies in the
`(III*, 2)` stratum. -/
theorem mem_stratFibre_IIIstar_of_form {x : ℤ_[3] × ℤ_[3]} {α β w : ℤ_[3]}
    (h₄ : x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α) (h₆ : x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * β)
    (hw : ((3 : ℕ) : ℤ_[3]) * w = β ^ 2 + ((3 : ℕ) : ℤ_[3]) * α - 1)
    (hwd : ((3 : ℕ) : ℤ_[3]) ∣ w) (hαβ : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α + β ^ 2) :
    x ∈ stratFibre 3 (KodairaSymbol.III!, 2) := by
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    intro h
    obtain ⟨e, he⟩ := (pow_two_dvd_w_of_Δ_eq_zero (p := 3) rfl h₄ h₆ hw h).2
    refine hαβ ?_
    exact ⟨e + w - α, by linear_combination he - hw⟩
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IIIstar_unit_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 3 * α) (((3 : ℕ) : ℤ_[3]) ^ 3 * β)).Δ ≠ 0 from by
      rw [← h₄, ← h₆]; exact hΔ) rfl rfl hw hwd hαβ
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  exact Prod.ext (by simp only [h₄, h₆]; exact hks) (by simp only [h₄, h₆]; exact hts)

open scoped Classical in
/-- If `a₄ = 27α`, `a₆ = 27β` with `3 ∤ β`, `w = 3g` with `3 ∤ g`, and `α + β² = 3k`, then the
point lies in the `(II*, 1)` stratum. -/
theorem mem_stratFibre_IIstar_of_form {x : ℤ_[3] × ℤ_[3]} {α β g k : ℤ_[3]}
    (h₄ : x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α) (h₆ : x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * β)
    (hβ : ¬ ((3 : ℕ) : ℤ_[3]) ∣ β)
    (hw : ((3 : ℕ) : ℤ_[3]) * (((3 : ℕ) : ℤ_[3]) * g) = β ^ 2 + ((3 : ℕ) : ℤ_[3]) * α - 1)
    (hk : α + β ^ 2 = ((3 : ℕ) : ℤ_[3]) * k) (hgu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ g) :
    x ∈ stratFibre 3 (KodairaSymbol.II!, 1) := by
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    intro h
    obtain ⟨W, hW⟩ := (pow_two_dvd_w_of_Δ_eq_zero (p := 3) rfl h₄ h₆ hw h).1
    exact hgu ⟨W, mul_left_cancel₀ (PadicInt.uniformizer_ne_zero (p := 3)) (by
      push_cast at hW ⊢; linear_combination hW)⟩
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IIstar_unit_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 3 * α) (((3 : ℕ) : ℤ_[3]) ^ 3 * β)).Δ ≠ 0 from by
      rw [← h₄, ← h₆]; exact hΔ) rfl rfl hβ hw hk hgu
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  exact Prod.ext (by simp only [h₄, h₆]; exact hks) (by simp only [h₄, h₆]; exact hts)

/-! ### One class, all the way to stratum membership

In each case the numerals are `A`, `B` (with `a₄ ≡ 27A`, `a₆ ≡ 27B`) and `W` (with
`3W = B² + 3A - 1`). -/

open scoped Classical in
/-- **One class of an `IV*` unit locus.** -/
theorem mem_stratFibre_IVstar_of_class {x : ℤ_[3] × ℤ_[3]} {A B W c : ℕ}
    (h₄ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.1 - ((27 * A : ℕ) : ℤ_[3]))
    (h₆ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.2 - ((27 * B : ℕ) : ℤ_[3]))
    (hW : ((3 : ℕ) : ℤ_[3]) * (W : ℤ_[3]) = (B : ℤ_[3]) ^ 2 + ((3 : ℕ) : ℤ_[3]) * (A : ℤ_[3]) - 1)
    (hB : ¬ (3 : ℕ) ∣ B) (hWu : ¬ (3 : ℕ) ∣ W)
    (hc : c = if IsSquare (-(4 * ((B : ZMod 3) * (W : ZMod 3)))) then 3 else 1) :
    x ∈ stratFibre 3 (KodairaSymbol.IV!, c) := by
  obtain ⟨α, β, w, l, m, hα, hβ, hw, hβl, hwm⟩ :=
    exists_unit_form (x := x) (n := 1) (A := (A : ℤ_[3])) (B := (B : ℤ_[3]))
      (W := (W : ℤ_[3])) (by rw [show ((3 : ℕ) : ℤ_[3]) ^ 3 * (A : ℤ_[3])
        = ((27 * A : ℕ) : ℤ_[3]) from by push_cast; ring]; exact h₄)
      (by rw [show ((3 : ℕ) : ℤ_[3]) ^ 3 * (B : ℤ_[3])
        = ((27 * B : ℕ) : ℤ_[3]) from by push_cast; ring]; exact h₆)
      (pow_three_dvd_of_sub (by norm_num) h₄) (pow_three_dvd_of_sub (by norm_num) h₆) hW
  refine mem_stratFibre_IVstar_of_form hα hβ ?_ hw ?_ ?_
  · rw [hβl, PadicInt.dvd_iff_toZMod_eq_zero, toZMod_natCast_add (n := 2) (by norm_num)]
    exact fun hz => not_dvd_natCast_of_not_dvd hB
      (by rw [PadicInt.dvd_iff_toZMod_eq_zero, map_natCast]; exact hz)
  · rw [hwm, PadicInt.dvd_iff_toZMod_eq_zero, toZMod_natCast_add (n := 1) le_rfl]
    exact fun hz => not_dvd_natCast_of_not_dvd hWu
      (by rw [PadicInt.dvd_iff_toZMod_eq_zero, map_natCast]; exact hz)
  · rw [hc, hβl, hwm, map_neg, map_mul, map_ofNat, map_mul,
      toZMod_natCast_add (n := 2) (by norm_num), toZMod_natCast_add (n := 1) le_rfl]

/-- **One class of the `III*` unit locus.** `3 ∣ W` and `3 ∤ A + B²` are the branch conditions, and
`α + β² ≡ A + B²` modulo `3`. -/
theorem mem_stratFibre_IIIstar_of_class {x : ℤ_[3] × ℤ_[3]} {A B W : ℕ}
    (h₄ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.1 - ((27 * A : ℕ) : ℤ_[3]))
    (h₆ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.2 - ((27 * B : ℕ) : ℤ_[3]))
    (hW : ((3 : ℕ) : ℤ_[3]) * (W : ℤ_[3]) = (B : ℤ_[3]) ^ 2 + ((3 : ℕ) : ℤ_[3]) * (A : ℤ_[3]) - 1)
    (hWd : (3 : ℕ) ∣ W) (hAB : ((A : ZMod 3) + (B : ZMod 3) ^ 2) ≠ 0) :
    x ∈ stratFibre 3 (KodairaSymbol.III!, 2) := by
  obtain ⟨α, β, w, l, m, hα, hβ, hw, hβl, hwm⟩ :=
    exists_unit_form (x := x) (n := 1) (A := (A : ℤ_[3])) (B := (B : ℤ_[3]))
      (W := (W : ℤ_[3])) (by rw [show ((3 : ℕ) : ℤ_[3]) ^ 3 * (A : ℤ_[3])
        = ((27 * A : ℕ) : ℤ_[3]) from by push_cast; ring]; exact h₄)
      (by rw [show ((3 : ℕ) : ℤ_[3]) ^ 3 * (B : ℤ_[3])
        = ((27 * B : ℕ) : ℤ_[3]) from by push_cast; ring]; exact h₆)
      (pow_three_dvd_of_sub (by norm_num) h₄) (pow_three_dvd_of_sub (by norm_num) h₆) hW
  obtain ⟨k, hk⟩ : ∃ k : ℤ_[3], α = (A : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ 2 * k := by
    obtain ⟨c, hc⟩ := h₄
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_⟩
    rw [hα] at hc
    push_cast at hc ⊢
    linear_combination hc
  refine mem_stratFibre_IIIstar_of_form hα hβ hw ?_ ?_
  · obtain ⟨W', hW'⟩ := hWd
    exact ⟨(W' : ℤ_[3]) + m, by rw [hwm, hW']; push_cast; ring⟩
  · rw [PadicInt.dvd_iff_toZMod_eq_zero, map_add, map_pow, hk, hβl,
      toZMod_natCast_add (n := 2) (by norm_num), toZMod_natCast_add (n := 2) (by norm_num)]
    exact hAB

/-- **One class of the `II*` unit locus.** Here the numerals go one digit deeper: `a₄ ≡ 27A` and
`a₆ ≡ 27B` modulo `3⁶`, with `3W = B² + 3A - 1`, `W = 3G`, `3 ∤ G` and `3 ∣ A + B²`. -/
theorem mem_stratFibre_IIstar_of_class {x : ℤ_[3] × ℤ_[3]} {A B G K : ℕ}
    (h₄ : ((3 : ℕ) : ℤ_[3]) ^ 6 ∣ x.1 - ((27 * A : ℕ) : ℤ_[3]))
    (h₆ : ((3 : ℕ) : ℤ_[3]) ^ 6 ∣ x.2 - ((27 * B : ℕ) : ℤ_[3]))
    (hW : ((3 : ℕ) : ℤ_[3]) * (((3 : ℕ) : ℤ_[3]) * (G : ℤ_[3]))
      = (B : ℤ_[3]) ^ 2 + ((3 : ℕ) : ℤ_[3]) * (A : ℤ_[3]) - 1)
    (hK : (A : ℤ_[3]) + (B : ℤ_[3]) ^ 2 = ((3 : ℕ) : ℤ_[3]) * (K : ℤ_[3]))
    (hB : ¬ (3 : ℕ) ∣ B) (hGu : ¬ (3 : ℕ) ∣ G) :
    x ∈ stratFibre 3 (KodairaSymbol.II!, 1) := by
  obtain ⟨α, β, w, l, m, hα, hβ, hw, hβl, hwm⟩ :=
    exists_unit_form (x := x) (n := 2) (A := (A : ℤ_[3])) (B := (B : ℤ_[3]))
      (W := ((3 : ℕ) : ℤ_[3]) * (G : ℤ_[3]))
      (by rw [show ((3 : ℕ) : ℤ_[3]) ^ 3 * (A : ℤ_[3])
        = ((27 * A : ℕ) : ℤ_[3]) from by push_cast; ring]; exact h₄)
      (by rw [show ((3 : ℕ) : ℤ_[3]) ^ 3 * (B : ℤ_[3])
        = ((27 * B : ℕ) : ℤ_[3]) from by push_cast; ring]; exact h₆)
      (pow_three_dvd_of_sub (by norm_num) h₄) (pow_three_dvd_of_sub (by norm_num) h₆) hW
  obtain ⟨k, hk⟩ : ∃ k : ℤ_[3], α = (A : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ 3 * k := by
    obtain ⟨c, hc⟩ := h₄
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_⟩
    rw [hα] at hc
    push_cast at hc ⊢
    linear_combination hc
  refine mem_stratFibre_IIstar_of_form (g := (G : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) * m)
    (k := (K : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ 2 * (k + 2 * (B : ℤ_[3]) * l
      + ((3 : ℕ) : ℤ_[3]) ^ 3 * l ^ 2)) hα hβ ?_ ?_ ?_ ?_
  · rw [hβl, PadicInt.dvd_iff_toZMod_eq_zero, toZMod_natCast_add (n := 3) (by norm_num)]
    exact fun hz => not_dvd_natCast_of_not_dvd hB
      (by rw [PadicInt.dvd_iff_toZMod_eq_zero, map_natCast]; exact hz)
  · rw [← hw, hwm]; ring
  · rw [hk, hβl]; push_cast at hK ⊢; linear_combination hK
  · rw [PadicInt.dvd_iff_toZMod_eq_zero,
      show ((G : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) * m) = (G : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ 1 * m from by
        rw [pow_one], toZMod_natCast_add (n := 1) le_rfl]
    exact fun hz => not_dvd_natCast_of_not_dvd hGu
      (by rw [PadicInt.dvd_iff_toZMod_eq_zero, map_natCast]; exact hz)

set_option maxRecDepth 40000 in
/-- **The `(III*, 2)` unit locus lies in the `(III*, 2)` stratum.** Each of the twelve classes has
`3 ∣ w` and `3 ∤ α + β²`. -/
theorem iiiStarUnit3Locus_subset_stratFibre :
    iiiStarUnit3Locus ⊆ stratFibre 3 (KodairaSymbol.III!, 2) := by
  intro x hx
  rw [iiiStarUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIIstarUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact mem_stratFibre_IIIstar_of_class (A := 0) (B := 1) (W := 0)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 0) (B := 8) (W := 21)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 1) (B := 4) (W := 6)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 1) (B := 5) (W := 9)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 3) (B := 1) (W := 3)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 3) (B := 8) (W := 24)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 4) (B := 4) (W := 9)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 4) (B := 5) (W := 12)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 6) (B := 1) (W := 6)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 6) (B := 8) (W := 27)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 7) (B := 4) (W := 12)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)
  · exact mem_stratFibre_IIIstar_of_class (A := 7) (B := 5) (W := 15)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide)

set_option maxRecDepth 40000 in
/-- **The `(IV*, 3)` unit locus lies in the `(IV*, 3)` stratum.** On each of the eighteen classes
`3 ∤ β`, `3 ∤ w`, and the residue of `-4βw` is the square `1`. -/
theorem ivStarThreeUnit3Locus_subset_stratFibre :
    ivStarThreeUnit3Locus ⊆ stratFibre 3 (KodairaSymbol.IV!, 3) := by
  intro x hx
  rw [ivStarThreeUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarThreeUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact mem_stratFibre_IVstar_of_class (A := 0) (B := 2) (W := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 0) (B := 4) (W := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 1) (B := 7) (W := 17)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 1) (B := 8) (W := 22)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 2) (B := 1) (W := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 2) (B := 5) (W := 10)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 3) (B := 2) (W := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 3) (B := 4) (W := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 4) (B := 7) (W := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 4) (B := 8) (W := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 5) (B := 1) (W := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 5) (B := 5) (W := 13)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 6) (B := 2) (W := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 6) (B := 4) (W := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 7) (B := 7) (W := 23)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 7) (B := 8) (W := 28)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 8) (B := 1) (W := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 8) (B := 5) (W := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)

set_option maxRecDepth 40000 in
/-- **The `(IV*, 1)` unit locus lies in the `(IV*, 1)` stratum.** On each of the eighteen classes
`3 ∤ β`, `3 ∤ w`, and the residue of `-4βw` is the non-square `2`. -/
theorem ivStarOneUnit3Locus_subset_stratFibre :
    ivStarOneUnit3Locus ⊆ stratFibre 3 (KodairaSymbol.IV!, 1) := by
  intro x hx
  rw [ivStarOneUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarOneUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact mem_stratFibre_IVstar_of_class (A := 0) (B := 5) (W := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 0) (B := 7) (W := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 1) (B := 1) (W := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 1) (B := 2) (W := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 2) (B := 4) (W := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 2) (B := 8) (W := 23)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 3) (B := 5) (W := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 3) (B := 7) (W := 19)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 4) (B := 1) (W := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 4) (B := 2) (W := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 5) (B := 4) (W := 10)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 5) (B := 8) (W := 26)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 6) (B := 5) (W := 14)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 6) (B := 7) (W := 22)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 7) (B := 1) (W := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 7) (B := 2) (W := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 8) (B := 4) (W := 13)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)
  · exact mem_stratFibre_IVstar_of_class (A := 8) (B := 8) (W := 29)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- **The `(II*, 1)` unit locus lies in the `(II*, 1)` stratum.** On each of the thirty-six classes
`3 ∤ β`, `w = 3G` with `3 ∤ G`, and `3 ∣ α + β²`. -/
theorem iiStarUnit3Locus_subset_stratFibre :
    iiStarUnit3Locus ⊆ stratFibre 3 (KodairaSymbol.II!, 1) := by
  intro x hx
  rw [iiStarUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIstarUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact mem_stratFibre_IIstar_of_class (A := 2) (B := 2) (G := 1) (K := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 2) (B := 11) (G := 14) (K := 41)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 2) (B := 16) (G := 29) (K := 86)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 2) (B := 25) (G := 70) (K := 209)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 5) (B := 2) (G := 2) (K := 3)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 5) (B := 7) (G := 7) (K := 18)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 5) (B := 20) (G := 46) (K := 135)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 5) (B := 25) (G := 71) (K := 210)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 8) (B := 7) (G := 8) (K := 19)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 8) (B := 11) (G := 16) (K := 43)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 8) (B := 16) (G := 31) (K := 88)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 8) (B := 20) (G := 47) (K := 136)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 11) (B := 2) (G := 4) (K := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 11) (B := 11) (G := 17) (K := 44)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 11) (B := 16) (G := 32) (K := 89)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 11) (B := 25) (G := 73) (K := 212)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 14) (B := 2) (G := 5) (K := 6)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 14) (B := 7) (G := 10) (K := 21)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 14) (B := 20) (G := 49) (K := 138)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 14) (B := 25) (G := 74) (K := 213)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 17) (B := 7) (G := 11) (K := 22)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 17) (B := 11) (G := 19) (K := 46)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 17) (B := 16) (G := 34) (K := 91)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 17) (B := 20) (G := 50) (K := 139)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 20) (B := 2) (G := 7) (K := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 20) (B := 11) (G := 20) (K := 47)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 20) (B := 16) (G := 35) (K := 92)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 20) (B := 25) (G := 76) (K := 215)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 23) (B := 2) (G := 8) (K := 9)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 23) (B := 7) (G := 13) (K := 24)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 23) (B := 20) (G := 52) (K := 141)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 23) (B := 25) (G := 77) (K := 216)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 26) (B := 7) (G := 14) (K := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 26) (B := 11) (G := 22) (K := 49)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 26) (B := 16) (G := 37) (K := 94)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)
  · exact mem_stratFibre_IIstar_of_class (A := 26) (B := 20) (G := 53) (K := 142)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h4]; decide))
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by push_cast; ring)
      (by push_cast; ring) (by decide) (by decide)

/-! ### Minimality

On all four loci `v₃(a₆) = 3`, while a `(3⁴, 3⁶)`-dilate has `3⁶ ∣ a₆`. -/

/-- **`3 ∤ β` makes `27β` indivisible by `3⁶`.** -/
theorem not_pow_six_dvd_of_not_dvd {x : ℤ_[3]} {β : ℤ_[3]}
    (h : x = ((3 : ℕ) : ℤ_[3]) ^ 3 * β) (hβ : ¬ ((3 : ℕ) : ℤ_[3]) ∣ β) :
    ¬ ((3 : ℕ) : ℤ_[3]) ^ 6 ∣ x := by
  intro ⟨c, hc⟩
  refine hβ ⟨((3 : ℕ) : ℤ_[3]) ^ 2 * c, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_
  rw [← h, hc]
  ring

/-- **On each unit locus `3 ∤ a₆/27`**, read off the class's `a₆` numeral. -/
theorem exists_unit_snd_of_mem {x : ℤ_[3] × ℤ_[3]} {n B : ℕ}
    (h₆ : ((3 : ℕ) : ℤ_[3]) ^ n ∣ x.2 - ((27 * B : ℕ) : ℤ_[3])) (hn : 4 ≤ n)
    (hB : ¬ (3 : ℕ) ∣ B) : ¬ ((3 : ℕ) : ℤ_[3]) ^ 6 ∣ x.2 := by
  obtain ⟨c, hc⟩ := h₆
  refine not_pow_six_dvd_of_not_dvd (β := (B : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ (n - 3) * c) ?_ ?_
  · rw [show x.2 = ((27 * B : ℕ) : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ n * c from by linear_combination hc,
      show ((3 : ℕ) : ℤ_[3]) ^ n = ((3 : ℕ) : ℤ_[3]) ^ 3 * ((3 : ℕ) : ℤ_[3]) ^ (n - 3) from by
        rw [← pow_add]; congr 1; omega]
    push_cast
    ring
  · rw [PadicInt.dvd_iff_toZMod_eq_zero,
      show ((B : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ (n - 3) * c)
        = (B : ℤ_[3]) + ((3 : ℕ) : ℤ_[3]) ^ (n - 3) * c from rfl,
      toZMod_natCast_add (n := n - 3) (by omega)]
    exact fun hz => not_dvd_natCast_of_not_dvd hB
      (by rw [PadicInt.dvd_iff_toZMod_eq_zero, map_natCast]; exact hz)

set_option maxRecDepth 40000 in
/-- **No point of the `ivStarThreeUnit3Locus` unit locus is a dilate**: there `v₃(a₆) = 3`. -/
theorem notMem_range_of_mem_ivStarThreeUnit3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ ivStarThreeUnit3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd ?_
  rw [ivStarThreeUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarThreeUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)

set_option maxRecDepth 40000 in
/-- **No point of the `ivStarOneUnit3Locus` unit locus is a dilate**: there `v₃(a₆) = 3`. -/
theorem notMem_range_of_mem_ivStarOneUnit3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ ivStarOneUnit3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd ?_
  rw [ivStarOneUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarOneUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)

set_option maxRecDepth 40000 in
/-- **No point of the `iiiStarUnit3Locus` unit locus is a dilate**: there `v₃(a₆) = 3`. -/
theorem notMem_range_of_mem_iiiStarUnit3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ iiiStarUnit3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd ?_
  rw [iiiStarUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIIstarUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 1)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 8)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 4)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 5)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)

set_option maxRecDepth 100000 in
/-- **No point of the `iiStarUnit3Locus` unit locus is a dilate**: there `v₃(a₆) = 3`. -/
theorem notMem_range_of_mem_iiStarUnit3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ iiStarUnit3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd ?_
  rw [iiStarUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIstarUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  rcases hx with ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|
    ⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩|⟨h4, h6⟩
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 2)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 25)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 7)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 11)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 16)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)
  · exact exists_unit_snd_of_mem (B := 20)
      (pow_dvd_sub_natCast_of_toZModPow (by rw [h6]; decide)) (by norm_num) (by decide)

/-! ### Head-minimal membership

Every point of each of the four loci lies in a stratum with the expected Tamagawa number and is
not a `(3⁴, 3⁶)`-dilate. -/

/-- Every point of the `(IV*, 3)` locus over a unit `β` at `3` lies in a stratum with Tamagawa
number `3` and is not a dilate. -/
theorem ivStarThreeUnit3Locus_subset_headMinimal :
    ivStarThreeUnit3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 3)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three ivStarThreeUnit3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_ivStarThreeUnit3Locus hx

/-- Every point of the `(IV*, 1)` locus over a unit `β` at `3` lies in a stratum with Tamagawa
number `1` and is not a dilate. -/
theorem ivStarOneUnit3Locus_subset_headMinimal :
    ivStarOneUnit3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three ivStarOneUnit3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_ivStarOneUnit3Locus hx

/-- Every point of the `(III*, 2)` locus over a unit `β` at `3` lies in a stratum with Tamagawa
number `2` and is not a dilate. -/
theorem iiiStarUnit3Locus_subset_headMinimal :
    iiiStarUnit3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three iiiStarUnit3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_iiiStarUnit3Locus hx

/-- Every point of the `(II*, 1)` locus over a unit `β` at `3` lies in a stratum with Tamagawa
number `1` and is not a dilate. -/
theorem iiStarUnit3Locus_subset_headMinimal :
    iiStarUnit3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three iiStarUnit3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_iiStarUnit3Locus hx

/-! ### Disjointness from the `3⁴ ∣ a₆` loci

Each new locus is disjoint from its `WildStarredAtThree` counterpart, because `v₃(a₆) = 3` here
and `v₃(a₆) ≥ 4` there. -/

/-- **The `(IV*, 3)` loci at the two `a₆`-depths are disjoint**, `3⁴ ∣ a₆` separating them. -/
theorem disjoint_ivStarThreeUnit3Locus : Disjoint ivStarThreeUnit3Locus ivStarThree3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, b, k, -, hb, hk⟩ := exists_form_of_mem_ivStarThree3Locus hx'
  rw [ivStarThreeUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarThreeUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  refine absurd (show ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 from ⟨b, hb⟩) ?_
  rcases hx with ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|
    ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩ <;>
    exact fun hd => absurd (PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp
      (dvd_trans (pow_dvd_pow _ (by norm_num : 4 ≤ 4)) hd)) (by
        rw [show PadicInt.toZModPow 4 x.2
            = ZMod.cast (PadicInt.toZModPow 5 x.2) from
          (PadicInt.cast_toZModPow 4 5 (by norm_num) x.2).symm, h6]
        decide)

/-- **The `(III*, 2)` loci at the two `a₆`-depths are disjoint**: `v₃(a₆) = 3` here, `≥ 5`
there. -/
theorem disjoint_iiiStarUnit3Locus : Disjoint iiiStarUnit3Locus iiiStar3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, c, -, hc, -⟩ := exists_form_of_mem_iiiStar3Locus hx'
  rw [iiiStarUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIIstarUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  refine absurd (show ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 from
    ⟨((3 : ℕ) : ℤ_[3]) * c, by rw [hc]; ring⟩) ?_
  rcases hx with ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|
    ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩ <;>
    exact fun hd => absurd (PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp hd) (by
      rw [show PadicInt.toZModPow 4 x.2 = ZMod.cast (PadicInt.toZModPow 5 x.2) from
        (PadicInt.cast_toZModPow 4 5 (by norm_num) x.2).symm, h6]
      decide)

/-! ### The `t = 1` row: four loci

The `t = 1` row collects `(IV*, 1)` and `(II*, 1)` at both `a₆`-depths. The `IV*` pair and the
`II*` pair are disjoint because their Kodaira symbols differ, and within each pair `3⁴ ∣ a₆`
separates the two loci. -/

/-- **The two `(IV*, 1)` loci are disjoint**, `3⁴ ∣ a₆` separating them. -/
theorem disjoint_ivStarOneUnit3Locus : Disjoint ivStarOneUnit3Locus ivStarOne3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, b, k, -, hb, hk⟩ := exists_form_of_mem_ivStarOne3Locus hx'
  rw [ivStarOneUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarOneUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  refine absurd (show ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 from ⟨b, hb⟩) ?_
  rcases hx with ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|
    ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩ <;>
    exact fun hd => absurd (PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp hd) (by
      rw [show PadicInt.toZModPow 4 x.2 = ZMod.cast (PadicInt.toZModPow 5 x.2) from
        (PadicInt.cast_toZModPow 4 5 (by norm_num) x.2).symm, h6]
      decide)

/-- **The two `(II*, 1)` loci are disjoint**: `v₃(a₆) = 3` here and `5` there. -/
theorem disjoint_iiStarUnit3Locus : Disjoint iiStarUnit3Locus iiStar3Locus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, c, -, hc, -⟩ := exists_form_of_mem_iiStar3Locus hx'
  rw [iiStarUnit3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIstarUnitThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  refine absurd (show ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 from
    ⟨((3 : ℕ) : ℤ_[3]) * c, by rw [hc]; ring⟩) ?_
  rcases hx with ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|
    ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|
    ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|
    ⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩|⟨-, h6⟩ <;>
    exact fun hd => absurd (PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp hd) (by
      rw [show PadicInt.toZModPow 4 x.2 = ZMod.cast (PadicInt.toZModPow 6 x.2) from
        (PadicInt.cast_toZModPow 4 6 (by norm_num) x.2).symm, h6]
      decide)

/-- **The `IV*` part and the `II*` part of the `t = 1` row are disjoint**, because their Kodaira
symbols differ. -/
theorem disjoint_IVstar_IIstar_unit :
    Disjoint (ivStarOneUnit3Locus ∪ ivStarOne3Locus) (iiStarUnit3Locus ∪ iiStar3Locus) := by
  refine Set.disjoint_of_subset (Set.union_subset ivStarOneUnit3Locus_subset_stratFibre
    ivStarOne3Locus_subset_stratFibre) (Set.union_subset iiStarUnit3Locus_subset_stratFibre
    iiStar3Locus_subset_stratFibre) ?_
  exact disjoint_stratFibre_of_ne (by simp) 1 1

/-- **The four `t = 1` loci together have mass `33/59049`.** `2/6561 + 1/6561 = 27/59049` from the
`IV*` pair and `4/59049 + 2/59049 = 6/59049` from the `II*` pair. -/
theorem volume_union_one_unit_at_three :
    (volume : Measure (ℤ_[3] × ℤ_[3]))
      ((ivStarOneUnit3Locus ∪ ivStarOne3Locus) ∪ (iiStarUnit3Locus ∪ iiStar3Locus))
      = 33 / 59049 := by
  have hIV : (volume : Measure (ℤ_[3] × ℤ_[3])) (ivStarOneUnit3Locus ∪ ivStarOne3Locus)
      = 27 / 59049 := by
    rw [measure_union disjoint_ivStarOneUnit3Locus measurableSet_ivStarOne3Locus,
      volume_ivStarOneUnit3Locus, volume_ivStarOne3Locus,
      show (2 : ℝ≥0∞) / 6561 = 18 / 59049 from
        enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      show (1 : ℝ≥0∞) / 6561 = 9 / 59049 from
        enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      ENNReal.div_add_div_same]
    norm_num
  have hII : (volume : Measure (ℤ_[3] × ℤ_[3])) (iiStarUnit3Locus ∪ iiStar3Locus)
      = 6 / 59049 := by
    rw [measure_union disjoint_iiStarUnit3Locus measurableSet_iiStar3Locus,
      volume_iiStarUnit3Locus, volume_iiStar3Locus, ENNReal.div_add_div_same]
    norm_num
  rw [measure_union disjoint_IVstar_IIstar_unit
    ((measurableSet_iiStarUnit3Locus).union measurableSet_iiStar3Locus), hIV, hII,
    ENNReal.div_add_div_same]
  norm_num

end WeierstrassCurve

end
