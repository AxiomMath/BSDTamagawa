/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarTailShellAtTwo
public import BSDTamagawa.GOTTable.WildRowFourPrepAtTwo
public import BSDTamagawa.GOTTable.WildRowThreeCloseAtTwo
public import BSDTamagawa.GOTTable.WildRowTwoPrepAtTwo
public import BSDTamagawa.GOTTable.WildHeadLowerClose

/-!
# The `q = 2` column of the Griffin–Ono–Tsai table

`HasGOTDensities 2` follows from four lower bounds on the head values. Rows `t = 2` and `t = 4` are
obtained by adding the two `Iₘ*` tail cylinders to the assembled parts of those rows. In minimal
masses, before the factor `1024/1023`,

    row `t = 2`      rowTwoCore2Locus        7435/24576
                   + aStarTailTwoLocus          1/512   =  48/24576
                   + bStarTailTwoLocus          1/2048  =  12/24576
                                             ----------------------
                                               7495/24576

    row `t = 4`      rowFourCore2Locus        433/32768
                   + aStarTailFourLocus         1/512   =  64/32768
                   + bStarTailFourLocus         1/2048  =  16/32768
                                             ----------------------
                                                513/32768

and `7495/24576 · 1024/1023 = 7495/24552`, `513/32768 · 1024/1023 = 171/10912` are exactly the
targets of the two rows.

Each tail is a union over the levels `m` of the strata over `Iₘ*`, so it shares Kodaira symbols
with the assembled loci, and every disjointness is a congruence. The two tails' classes modulo `32`
are `{(5, 10), (13, 18), (21, 26), (29, 2)}` for the `A`-tail and `{(20, 16)}` for the `B`-tail,
and each assembled locus is separated from them by:

    locus                                    separator
    -----------------------------------------------------------------------------
    iii2LocusFull                            the pair `(a₄, a₆)` modulo `4`
    iZeroStarTwo2Locus                       the pair modulo `16`
    iiiStar2Locus                            the pair modulo `32`
    iiiStarOdd2Locus                         the pair modulo `32`
    iStarOneTwoLocus, iStarOneFourLocus      the pair modulo `32`
    iStarTwoTwoLocus, iStarTwoFourLocus      `a₄ ≡ 12 (mod 16)`; the tails have `4, 5, 13`
    iStarThreeTwoLocus, iStarThreeFourLocus  `a₆ ≡ 0 (mod 32)`; the tails have `2, 10, 16, 18, 26`
    aStarTwoTwoLocus, aStarTwoFourLocus      `a₆ − a₄ ≡ 21 (mod 32)`; the `A`-tail has `5`
    iStarFourTwoLocus, iStarFourFourLocus    `a₄ ≡ 4 (mod 32)`; the tails have `5, 13, 20, 21, 29`
    multSplitLocusTwo 2 n                    `a₆ ≡ 6 (mod 16)`; the tails have `0, 2, 10`
    multNonSplitLocusTwo 2 n                 `a₆ ≡ 14 (mod 16)`, likewise
    A-tail against B-tail                    `a₄ ≡ 20 (mod 32)` on the second, never on the first

## Main definitions

* `WeierstrassCurve.HeadClose.TailShadowRes`: the five classes modulo `32` covering both tails.
* `WeierstrassCurve.RowTwoClose.rowTwoFull2Locus`,
  `WeierstrassCurve.RowFourClose.rowFourFull2Locus`: the full rows `t = 2` and `t = 4`.

## Main results

* `WeierstrassCurve.RowTwoClose.sevenFourNineFive_div_le_δ_two_at_two`: `7495/24552 ≤ δ_2(2)`.
* `WeierstrassCurve.RowFourClose.oneSevenOne_div_le_δ_four_at_two`: `171/10912 ≤ δ_2(4)`.
* `WeierstrassCurve.hasGOTDensities_two`: `HasGOTDensities 2`.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

namespace HeadClose

/-! ### The two tails' common shadow modulo `32` -/

/-- **The five residue classes modulo `32` covering both `Iₘ*` tails**: the `A`-tail's
`(5, 10)`, `(13, 18)`, `(21, 26)`, `(29, 2)` and the `B`-tail's `(20, 16)`. -/
abbrev TailShadowRes (a e : ZMod (2 ^ 5)) : Prop :=
  (a = 5 ∧ e = 10) ∨ (a = 13 ∧ e = 18) ∨ (a = 21 ∧ e = 26) ∨ (a = 29 ∧ e = 2) ∨
    (a = 20 ∧ e = 16)

/-- A point of the `A`-tail satisfies the shadow congruence. -/
theorem tailShadowRes_of_aStarTailRes {a e : ZMod (2 ^ 5)} (h : AStarTailRes a e) :
    TailShadowRes a e := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- A point of the `B`-tail satisfies the shadow congruence. -/
theorem tailShadowRes_of_bstarTailHeadRes {a e : ZMod (2 ^ 5)} (h : BStarTailHeadRes a e) :
    TailShadowRes a e :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Every point of `aStarTailLocus` reduces into the shadow modulo `32`. -/
theorem tailShadowRes_of_mem_aStarTailLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTailLocus) :
    TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) :=
  tailShadowRes_of_aStarTailRes (mem_aStarTailLocus_iff.1 hx)

/-- Every point of `bStarTailLocus` reduces into the shadow modulo `32`. -/
theorem tailShadowRes_of_mem_bStarTailLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ bStarTailLocus) :
    TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) :=
  tailShadowRes_of_bstarTailHeadRes (mem_bStarTailLocus_iff.1 hx)

/-! ### The twelve separating congruences -/

set_option maxRecDepth 20000 in
/-- On the shadow, `(a₄, a₆)` modulo `4` is never a type-`III` class. -/
theorem tailShadowRes_not_headResIIITwo : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    ¬ HeadResIIITwo (ZMod.cast a : ZMod (2 ^ 2)) (ZMod.cast e : ZMod (2 ^ 2)) := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `(a₄, a₆)` modulo `16` is never an `(I₀*, 2)` class. -/
theorem tailShadowRes_notMem_headResiduesIZeroStarTwo : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    ((ZMod.cast a : ZMod (2 ^ 4)), (ZMod.cast e : ZMod (2 ^ 4))) ∉
      headResiduesIZeroStarTwo := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `(a₄, a₆)` modulo `32` is never a `(III*, 2)` class of the even half. -/
theorem tailShadowRes_notMem_headResiduesIIIstarTwo : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    (a, e) ∉ headResiduesIIIstarTwo := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `(a₄, a₆)` modulo `32` is never a `(III*, 2)` class of the odd half. -/
theorem tailShadowRes_notMem_headResiduesIIIstarOddTwo : ∀ a e : ZMod (2 ^ 5),
    TailShadowRes a e → (a, e) ∉ headResiduesIIIstarOddTwo := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₆` is `2`, `10` or `0` modulo `16`, never `6` — which is what it is on both
multiplicative split loci. -/
theorem tailShadowRes_snd_ne_six : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    (ZMod.cast e : ZMod (2 ^ 4)) ≠ 6 := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `(a₄, a₆)` modulo `32` is never an `(I₁*, 2)` class. -/
theorem tailShadowRes_notMem_headResiduesIStarOneTwo : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    (a, e) ∉ headResiduesIStarOneTwo := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `(a₄, a₆)` modulo `32` is never an `(I₁*, 4)` class. -/
theorem tailShadowRes_notMem_headResiduesIStarOneFour : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    (a, e) ∉ headResiduesIStarOneFour := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₄` is `4`, `5` or `13` modulo `16`, never `12`, which is its value on both
`(I₂*, ·)` loci `iStarTwoTwoLocus` and `iStarTwoFourLocus`. -/
theorem tailShadowRes_fst_ne_twelve : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 12 := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₆` modulo `32` is `2`, `10`, `16`, `18` or `26`, never `0` — which is what it
is on both `(I₃*, ·)` loci. -/
theorem tailShadowRes_snd_ne_zero : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e → e ≠ 0 := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₆ − a₄` modulo `32` is `5`, `28` or `24`, never `21`, which is its value on
both `(I₂*, ·)` loci `aStarTwoTwoLocus` and `aStarTwoFourLocus`. -/
theorem tailShadowRes_sub_ne_twentyOne : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    e - a ≠ 21 := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₄` modulo `32` is `5`, `13`, `20`, `21` or `29`, never `4` — which is what it
is on both `(I₄*, ·)` loci. -/
theorem tailShadowRes_fst_ne_four : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e → a ≠ 4 := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₆` is `2`, `10` or `16` modulo `16`, never `14` — which is what it is on the
non-split multiplicative family. -/
theorem tailShadowRes_snd_ne_fourteen : ∀ a e : ZMod (2 ^ 5), TailShadowRes a e →
    (ZMod.cast e : ZMod (2 ^ 4)) ≠ 14 := by decide

set_option maxRecDepth 20000 in
/-- On the shadow, `a₄` is odd on the `A`-tail's four classes and even on the `B`-tail's one, which
is what separates the two tails from each other. -/
theorem aStarTailRes_fst_ne_twenty : ∀ a e : ZMod (2 ^ 5), AStarTailRes a e → a ≠ 20 := by decide

/-! ### The shadow separates a tail point from each assembled locus -/

/-- A shadow point is not in `iii2LocusFull`. -/
theorem notMem_iii2LocusFull {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iii2LocusFull := by
  intro hmem
  refine tailShadowRes_not_headResIIITwo _ _ hx ?_
  rw [PadicInt.cast_toZModPow 2 5 (by norm_num), PadicInt.cast_toZModPow 2 5 (by norm_num)]
  exact mem_iii2LocusFull_iff.1 hmem

/-- A shadow point is not in `iZeroStarTwo2Locus`. -/
theorem notMem_iZeroStarTwo2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iZeroStarTwo2Locus := by
  intro hmem
  refine tailShadowRes_notMem_headResiduesIZeroStarTwo _ _ hx ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num), PadicInt.cast_toZModPow 4 5 (by norm_num)]
  exact mem_iZeroStarTwo2Locus_iff.1 hmem

/-- A shadow point is not in `iiiStar2Locus`: there `a₄ ≡ 0 (mod 8)`. -/
theorem notMem_iiiStar2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iiiStar2Locus :=
  fun hmem => tailShadowRes_notMem_headResiduesIIIstarTwo _ _ hx
    (mem_headResiduesIIIstarTwo_iff.2 (mem_iiiStar2Locus_iff.1 hmem))

/-- A shadow point is not in `iiiStarOdd2Locus`: there `a₆ ≡ 6 (mod 8)`. -/
theorem notMem_iiiStarOdd2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iiiStarOdd2Locus :=
  fun hmem => tailShadowRes_notMem_headResiduesIIIstarOddTwo _ _ hx
    (mem_iiiStarOdd2Locus_iff.1 hmem)

/-- A shadow point is not in `iStarOneTwoLocus`. -/
theorem notMem_iStarOneTwoLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarOneTwoLocus :=
  fun hmem => tailShadowRes_notMem_headResiduesIStarOneTwo _ _ hx
    (mem_headResiduesIStarOneTwo_iff.2 (mem_iStarOneTwoLocus_iff.1 hmem))

/-- A shadow point is not in `iStarOneFourLocus`. -/
theorem notMem_iStarOneFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarOneFourLocus :=
  fun hmem => tailShadowRes_notMem_headResiduesIStarOneFour _ _ hx
    (mem_headResiduesIStarOneFour_iff.2 (mem_iStarOneFourLocus_iff.1 hmem))

/-- A shadow point is not in `iStarTwoTwoLocus`: there `a₄ ≡ 12 (mod 16)`. -/
theorem notMem_iStarTwoTwoLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarTwoTwoLocus := by
  intro hmem
  have h := headResIStarTwoTwo_fst _ _ (mem_iStarTwoTwoLocus_iff.1 hmem)
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num)] at h
  refine tailShadowRes_fst_ne_twelve _ _ hx ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num)]
  exact h

/-- A shadow point is not in `iStarTwoFourLocus`. -/
theorem notMem_iStarTwoFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarTwoFourLocus := by
  intro hmem
  have h := headResIStarTwoFour_fst _ _ (mem_iStarTwoFourLocus_iff.1 hmem)
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num)] at h
  refine tailShadowRes_fst_ne_twelve _ _ hx ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num)]
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- On the `(I₃*, 2)` residue set `a₆ ≡ 0 (mod 32)`. -/
theorem headResIStarThreeTwo_snd : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeTwo a e →
    (ZMod.cast e : ZMod (2 ^ 5)) = 0 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- On the `(I₃*, 4)` residue set `a₆ ≡ 0 (mod 32)` too. -/
theorem headResIStarThreeFour_snd : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeFour a e →
    (ZMod.cast e : ZMod (2 ^ 5)) = 0 := by decide

/-- A shadow point is not in `iStarThreeTwoLocus`: there `a₆ ≡ 0 (mod 32)`. -/
theorem notMem_iStarThreeTwoLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarThreeTwoLocus := by
  intro hmem
  have h := headResIStarThreeTwo_snd _ _ (mem_iStarThreeTwoLocus_iff.1 hmem)
  rw [PadicInt.cast_toZModPow 5 7 (by norm_num)] at h
  exact tailShadowRes_snd_ne_zero _ _ hx h

/-- A shadow point is not in `iStarThreeFourLocus`. -/
theorem notMem_iStarThreeFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarThreeFourLocus := by
  intro hmem
  have h := headResIStarThreeFour_snd _ _ (mem_iStarThreeFourLocus_iff.1 hmem)
  rw [PadicInt.cast_toZModPow 5 7 (by norm_num)] at h
  exact tailShadowRes_snd_ne_zero _ _ hx h

set_option maxRecDepth 100000 in
/-- On the `(I₂*, 2)` residue set `HeadResAStarTwoTwo`, `a₆ − a₄ ≡ 21 (mod 32)`. -/
theorem headResAStarTwoTwo_sub : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoTwo a e →
    (ZMod.cast e : ZMod (2 ^ 5)) - (ZMod.cast a : ZMod (2 ^ 5)) = 21 := by decide

set_option maxRecDepth 100000 in
/-- On the `(I₂*, 4)` residue set `HeadResAStarTwoFour`, `a₆ − a₄ ≡ 21 (mod 32)` too. -/
theorem headResAStarTwoFour_sub : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoFour a e →
    (ZMod.cast e : ZMod (2 ^ 5)) - (ZMod.cast a : ZMod (2 ^ 5)) = 21 := by decide

/-- A shadow point is not in `aStarTwoTwoLocus`: there `a₆ − a₄ ≡ 21 (mod 32)`, whereas on the
`A`-tail it is `5`. -/
theorem notMem_aStarTwoTwoLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ aStarTwoTwoLocus := by
  intro hmem
  have h := headResAStarTwoTwo_sub _ _ (mem_aStarTwoTwoLocus_iff.1 hmem)
  rw [PadicInt.cast_toZModPow 5 6 (by norm_num),
    PadicInt.cast_toZModPow 5 6 (by norm_num)] at h
  exact tailShadowRes_sub_ne_twentyOne _ _ hx h

/-- A shadow point is not in `aStarTwoFourLocus`. -/
theorem notMem_aStarTwoFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ aStarTwoFourLocus := by
  intro hmem
  have h := headResAStarTwoFour_sub _ _ (mem_aStarTwoFourLocus_iff.1 hmem)
  rw [PadicInt.cast_toZModPow 5 6 (by norm_num),
    PadicInt.cast_toZModPow 5 6 (by norm_num)] at h
  exact tailShadowRes_sub_ne_twentyOne _ _ hx h

/-- A shadow point is not in `iStarFourTwoLocus`: there `a₄ ≡ 4 (mod 32)`. -/
theorem notMem_iStarFourTwoLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarFourTwoLocus := by
  intro hmem
  obtain ⟨h4, -⟩ :=
    headResIStarFourTwo_congr_mod_thirtyTwo _ _ (mem_iStarFourTwoLocus_iff.1 hmem)
  have hA : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.1 - 4 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 8) (by norm_num) (by rwa [map_sub, map_ofNat])
  refine tailShadowRes_fst_ne_four _ _ hx ?_
  have h : PadicInt.toZModPow 5 (x.1 - 4) = 0 :=
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.1 hA
  rw [map_sub, map_ofNat, sub_eq_zero] at h
  exact h

/-- A shadow point is not in `iStarFourFourLocus`. -/
theorem notMem_iStarFourFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ iStarFourFourLocus := by
  intro hmem
  obtain ⟨h4, -⟩ := RowFour.headResIStarFourFour_class _ _ (mem_iStarFourFourLocus_iff.1 hmem)
  have hA : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ x.1 - 4 :=
    pow_dvd_of_cast_toZModPow_eq_zero (n := 8) (by norm_num) (by rwa [map_sub, map_ofNat])
  refine tailShadowRes_fst_ne_four _ _ hx ?_
  have h : PadicInt.toZModPow 5 (x.1 - 4) = 0 :=
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.1 hA
  rw [map_sub, map_ofNat, sub_eq_zero] at h
  exact h

/-- A shadow point is not in any split multiplicative locus: there `a₆ ≡ 6 (mod 16)`. -/
theorem notMem_multSplitLocusTwo {x : ℤ_[2] × ℤ_[2]} (n : ℕ)
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ multSplitLocusTwo 2 n := by
  intro hmem
  refine tailShadowRes_snd_ne_six _ _ hx ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num)]
  exact (mem_multSplitLocusTwo_iff.1 hmem).2.1

/-- A shadow point is not in any non-split multiplicative locus: there `a₆ ≡ 14 (mod 16)`. -/
theorem notMem_multNonSplitLocusTwo {x : ℤ_[2] × ℤ_[2]} (n : ℕ)
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ multNonSplitLocusTwo 2 n := by
  intro hmem
  refine tailShadowRes_snd_ne_fourteen _ _ hx ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num)]
  exact (mem_multNonSplitLocusTwo_iff.1 hmem).2.1

/-! ### The two tails are disjoint from each other -/

/-- **The `A`-tail and the `B`-tail are disjoint**, by the parity of `a₄`: odd on the first, even
on the second. -/
theorem disjoint_aStarTailLocus_bStarTailLocus :
    Disjoint aStarTailLocus bStarTailLocus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact aStarTailRes_fst_ne_twenty _ _ (mem_aStarTailLocus_iff.1 hx)
    ((mem_bStarTailLocus_iff.1 hx').1)

end HeadClose

/-! ### Row `t = 2`: the assembled part plus the two tails -/

namespace RowTwoClose

open HeadClose

/-- **The assembled part of the row `t = 2` is disjoint from both tails**: none of its eleven
constituents meets the tails' common shadow modulo `32`. -/
theorem notMem_rowTwoCore2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ rowTwoCore2Locus := by
  rw [rowTwoCore2Locus, rowTwoSteps2Locus, rowTwoStarred2Locus, rowTwoInStar2Locus,
    rowTwoMult2Locus]
  rintro ((((h | h) | (h | h)) | ((((h | h) | h) | h) | h)) | (h | h))
  · exact notMem_iii2LocusFull hx h
  · exact notMem_iZeroStarTwo2Locus hx h
  · exact notMem_iiiStar2Locus hx h
  · exact notMem_iiiStarOdd2Locus hx h
  · exact notMem_iStarOneTwoLocus hx h
  · exact notMem_iStarTwoTwoLocus hx h
  · exact notMem_iStarThreeTwoLocus hx h
  · exact notMem_aStarTwoTwoLocus hx h
  · exact notMem_iStarFourTwoLocus hx h
  · exact notMem_multSplitLocusTwo 2 hx h
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    exact notMem_multNonSplitLocusTwo (2 * j + 2) hx hj

/-- The assembled part of the row `t = 2` is disjoint from the `c = 2` half of the `A`-tail. -/
theorem disjoint_rowTwoCore2Locus_aStarTailTwoLocus :
    Disjoint rowTwoCore2Locus aStarTailTwoLocus :=
  Set.disjoint_right.2 fun _ hx =>
    notMem_rowTwoCore2Locus (tailShadowRes_of_mem_aStarTailLocus hx.1)

/-- The assembled part of the row `t = 2` is disjoint from the `c = 2` half of the `B`-tail. -/
theorem disjoint_rowTwoCore2Locus_bStarTailTwoLocus :
    Disjoint rowTwoCore2Locus bStarTailTwoLocus :=
  Set.disjoint_right.2 fun _ hx =>
    notMem_rowTwoCore2Locus (tailShadowRes_of_mem_bStarTailLocus hx.1)

/-- The `c = 2` halves of the `A`-tail and the `B`-tail are disjoint. -/
theorem disjoint_aStarTailTwoLocus_bStarTailTwoLocus :
    Disjoint aStarTailTwoLocus bStarTailTwoLocus :=
  disjoint_aStarTailLocus_bStarTailLocus.mono Set.inter_subset_left Set.inter_subset_left

/-- **The whole row `t = 2`**: its assembled part, the `A`-tail's `c = 2` half and the
`B`-tail's. -/
noncomputable def rowTwoFull2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  rowTwoCore2Locus ∪ aStarTailTwoLocus ∪ bStarTailTwoLocus

/-- The whole row `t = 2` lies in the union of the strata with `c = 2`, outside the image of the
scaling `(a₄, a₆) ↦ (2⁴ a₄, 2⁶ a₆)`. -/
theorem rowTwoFull2Locus_subset_headMinimal :
    rowTwoFull2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowTwoFull2Locus]
  exact Set.union_subset
    (Set.union_subset rowTwoCore2Locus_subset_headMinimal
      aStarTailTwoLocus_subset_headMinimal)
    bStarTailTwoLocus_subset_headMinimal

/-- **The mass of the whole row `t = 2` is `7435/24576 + 1/512 + 1/2048 = 7495/24576`.** -/
theorem volume_rowTwoFull2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowTwoFull2Locus = 7495 / 24576 := by
  rw [rowTwoFull2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_rowTwoCore2Locus_bStarTailTwoLocus,
          disjoint_aStarTailTwoLocus_bStarTailTwoLocus⟩)
      measurableSet_bStarTailTwoLocus,
    measure_union disjoint_rowTwoCore2Locus_aStarTailTwoLocus measurableSet_aStarTailTwoLocus,
    volume_rowTwoCore2Locus, TailShell.astar_volume_eq.1,
    (bstarTail_volume_eq_of_flip TailShell.bstarTailFlip).1,
    show (1 : ℝ≥0∞) / 512 = 48 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 2048 = 12 / 24576 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

/-- **`7495/24552 ≤ δ_2(2)`.** The row's minimal mass is `7495/24576`, and
`7495/24576 · 1024/1023 = 7495/24552`. -/
theorem sevenFourNineFive_div_le_δ_two_at_two : (7495 : ℝ≥0∞) / 24552 ≤ δ 2 2 := by
  refine le_trans (le_of_eq ?_) (le_δ_at_two_of_subset rowTwoFull2Locus_subset_headMinimal)
  rw [volume_rowTwoFull2Locus, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RowTwoClose

/-! ### Row `t = 4`: the assembled part plus the two tails -/

namespace RowFourClose

open HeadClose

/-- **The assembled part of the row `t = 4` is disjoint from both tails.** -/
theorem notMem_rowFourCore2Locus {x : ℤ_[2] × ℤ_[2]}
    (hx : TailShadowRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2)) :
    x ∉ rowFourCore2Locus := by
  rw [rowFourCore2Locus]
  rintro (((((h | h) | h) | h) | h) | h)
  · exact notMem_iStarOneFourLocus hx h
  · exact notMem_iStarTwoFourLocus hx h
  · exact notMem_iStarThreeFourLocus hx h
  · exact notMem_aStarTwoFourLocus hx h
  · exact notMem_iStarFourFourLocus hx h
  · exact notMem_multSplitLocusTwo 4 hx h

/-- The assembled part of the row `t = 4` is disjoint from the `c = 4` half of the `A`-tail. -/
theorem disjoint_rowFourCore2Locus_aStarTailFourLocus :
    Disjoint rowFourCore2Locus aStarTailFourLocus :=
  Set.disjoint_right.2 fun _ hx =>
    notMem_rowFourCore2Locus (tailShadowRes_of_mem_aStarTailLocus hx.1)

/-- The assembled part of the row `t = 4` is disjoint from the `c = 4` half of the `B`-tail. -/
theorem disjoint_rowFourCore2Locus_bStarTailFourLocus :
    Disjoint rowFourCore2Locus bStarTailFourLocus :=
  Set.disjoint_right.2 fun _ hx =>
    notMem_rowFourCore2Locus (tailShadowRes_of_mem_bStarTailLocus hx.1)

/-- The `c = 4` halves of the `A`-tail and the `B`-tail are disjoint. -/
theorem disjoint_aStarTailFourLocus_bStarTailFourLocus :
    Disjoint aStarTailFourLocus bStarTailFourLocus :=
  disjoint_aStarTailLocus_bStarTailLocus.mono Set.inter_subset_left Set.inter_subset_left

/-- **The whole row `t = 4`**: its assembled part, the `A`-tail's `c = 4` half and the
`B`-tail's. -/
noncomputable def rowFourFull2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  rowFourCore2Locus ∪ aStarTailFourLocus ∪ bStarTailFourLocus

/-- The whole row `t = 4` lies in the union of the strata with `c = 4`, outside the image of the
scaling `(a₄, a₆) ↦ (2⁴ a₄, 2⁶ a₆)`. -/
theorem rowFourFull2Locus_subset_headMinimal :
    rowFourFull2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  rw [rowFourFull2Locus]
  exact Set.union_subset
    (Set.union_subset rowFourCore2Locus_subset_headMinimal
      aStarTailFourLocus_subset_headMinimal)
    bStarTailFourLocus_subset_headMinimal

/-- **The mass of the whole row `t = 4` is `433/32768 + 1/512 + 1/2048 = 513/32768`.** -/
theorem volume_rowFourFull2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) rowFourFull2Locus = 513 / 32768 := by
  rw [rowFourFull2Locus,
    measure_union (Set.disjoint_union_left.2
        ⟨disjoint_rowFourCore2Locus_bStarTailFourLocus,
          disjoint_aStarTailFourLocus_bStarTailFourLocus⟩)
      measurableSet_bStarTailFourLocus,
    measure_union disjoint_rowFourCore2Locus_aStarTailFourLocus
      measurableSet_aStarTailFourLocus,
    volume_rowFourCore2Locus, TailShell.astar_volume_eq.2,
    (bstarTail_volume_eq_of_flip TailShell.bstarTailFlip).2,
    show (1 : ℝ≥0∞) / 512 = 64 / 32768 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 2048 = 16 / 32768 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  norm_num

/-- **`171/10912 ≤ δ_2(4)`.** The row's minimal mass is `513/32768`, and
`513/32768 · 1024/1023 = 513/32736 = 171/10912`. -/
theorem oneSevenOne_div_le_δ_four_at_two : (171 : ℝ≥0∞) / 10912 ≤ δ 2 4 := by
  refine le_trans (le_of_eq ?_) (le_δ_at_two_of_subset rowFourFull2Locus_subset_headMinimal)
  rw [volume_rowFourFull2Locus, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RowFourClose

/-! ### The column -/

/-- **`HasGOTDensities 2`: the `q = 2` column of the Griffin–Ono–Tsai table.** The four head
values are at least `241/396`, `7495/24552`, `1153/16368` and `171/10912`, and their total is
`32735/32736`, so each is equal to its table entry. -/
theorem hasGOTDensities_two : HasGOTDensities 2 :=
  hasGOTDensities_of_headLowerBounds_at_two twoFortyOne_div_le_δ_one_at_two
    RowTwoClose.sevenFourNineFive_div_le_δ_two_at_two elevenFiftyThree_div_le_δ_three_at_two
    RowFourClose.oneSevenOne_div_le_δ_four_at_two

end WeierstrassCurve

end
