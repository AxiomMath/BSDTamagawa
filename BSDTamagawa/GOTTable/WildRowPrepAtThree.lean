/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeSubsetAtThree
public import BSDTamagawa.GOTTable.WildIZeroStarUnitAtThree

/-!
# Kodaira symbols of the head loci at `p = 3`

Loci lying in strata over distinct Kodaira symbols are disjoint. This file records the Kodaira
symbol of each of the shallow loci and of the `I₀*` loci of the head at `p = 3`, and the symbol
`Iₘ*` with `m ≥ 1` on Family A, so that disjointness of loci in a common row can be read off from
the symbol. The two pairs of `(I₀*, t)` loci sharing a symbol are separated instead by `9 ∣ a₄`
against `v₃(a₄) = 1`.

## Main definitions

* `WeierstrassCurve.headMinimal`: the minimal part of the `t`-row at a prime `p`.

## Main results

* `WeierstrassCurve.RowsThree.disjoint_of_subset_stratFibre` and
  `WeierstrassCurve.RowsThree.disjoint_of_forall_stratFibre`: disjointness from the Kodaira symbol,
  at every prime and in every row.
* `WeierstrassCurve.one3LocusFull_subset_stratFibre_triple`: the `t = 1` locus `one3LocusFull` lies
  in the strata over `I₀`, `II` and `IV`.
* `WeierstrassCurve.iii3Locus_subset_stratFibre`, `WeierstrassCurve.iv3Locus_subset_stratFibre`,
  `WeierstrassCurve.iZeroStarOne3Locus_subset_stratFibre`,
  `WeierstrassCurve.iZeroStarTwo3Locus_subset_stratFibre`,
  `WeierstrassCurve.IZeroStarUnitThree.locus_two_subset_stratFibre` and
  `WeierstrassCurve.IZeroStarUnitThree.locus_one_subset_stratFibre`: each locus lies in a stratum
  with a named symbol.
* `WeierstrassCurve.FamilyAThree.exists_mem_stratFibre_of_mem_part`: every point of a half of
  Family A lies in a stratum over `Iₘ*` with `m ≠ 0`.
* `WeierstrassCurve.FamilyAThree.part_eq_inter` and
  `WeierstrassCurve.FamilyAThree.measurableSet_part`: the Tamagawa-`t` part of Family A is
  `locus ∩ ⋃ κ, stratFibre 3 (κ, t)`, hence measurable.
* `WeierstrassCurve.disjoint_iZeroStarOne3Locus_locus_two` and
  `WeierstrassCurve.disjoint_iZeroStarTwo3Locus_locus_one`: the two same-symbol pairs of `I₀*` loci
  are disjoint.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### The minimal part of a row, named -/

/-- **The minimal part of the `t`-row of the head at `p`**: the pairs whose reduction datum has
Tamagawa number `t`, less the `(p⁴, p⁶)`-dilates. -/
abbrev headMinimal (p : ℕ) [Fact p.Prime] (t : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  (⋃ κ : KodairaSymbol, stratFibre p (κ, t)) \
    Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])

namespace RowsThree

variable {p : ℕ} [Fact p.Prime]

/-! ### Disjointness from the Kodaira symbol, at every prime -/

/-- **Two loci lying in strata over distinct Kodaira symbols are disjoint.** -/
theorem disjoint_of_subset_stratFibre {κ κ' : KodairaSymbol} {c c' : ℕ}
    {L L' : Set (ℤ_[p] × ℤ_[p])} (h : κ ≠ κ') (hL : L ⊆ stratFibre p (κ, c))
    (hL' : L' ⊆ stratFibre p (κ', c')) : Disjoint L L' :=
  (disjoint_stratFibre_of_ne h c c').mono hL hL'

/-- **Two loci in a common row `t` are disjoint if no Kodaira symbol occurring on the first also
occurs on the second.** -/
theorem disjoint_of_forall_stratFibre {t : ℕ} {P Q : KodairaSymbol → Prop}
    {L L' : Set (ℤ_[p] × ℤ_[p])} (hPQ : ∀ κ, P κ → Q κ → False)
    (hL : ∀ x ∈ L, ∃ κ, P κ ∧ x ∈ stratFibre p (κ, t))
    (hL' : ∀ x ∈ L', ∃ κ, Q κ ∧ x ∈ stratFibre p (κ, t)) : Disjoint L L' := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨κ, hP, hκ⟩ := hL x hx
  obtain ⟨κ', hQ, hκ'⟩ := hL' x hx'
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hκ
  have hκκ : κ = κ' :=
    congrArg Prod.fst (((mem_stratFibre_iff hUp).1 hκ).symm.trans ((mem_stratFibre_iff hUp).1 hκ'))
  refine hPQ κ hP ?_
  rwa [hκκ]

end RowsThree

/-! ### The Kodaira symbol on the shallow loci -/

/-- **The `t = 1` locus `one3LocusFull` lies in the strata over `I₀`, `II` and `IV`.** -/
theorem one3LocusFull_subset_stratFibre_triple :
    one3LocusFull ⊆ stratFibre 3 (KodairaSymbol.I 0, 1) ∪ stratFibre 3 (KodairaSymbol.II, 1) ∪
      stratFibre 3 (KodairaSymbol.IV, 1) := by
  intro x hx
  have hA := mem_one3LocusFull_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_OneFull_three hA
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  rcases hA with hone | hIV
  · rw [PadicInt.cast_toZModPow 2 3 (by norm_num),
      PadicInt.cast_toZModPow 2 3 (by norm_num)] at hone
    rcases hone with hunit | hII
    · refine Or.inl (Or.inl ((mem_stratFibre_iff hUp).2 ?_))
      have h4 : ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.1 := by
        rwa [dvd_iff_cast_toZModPow_two_eq_zero]
      rw [strat, run_eq_of_not_dvd_Δ hΔ (not_three_dvd_Δ_of_not_dvd_fst h4)]
    · refine Or.inl (Or.inr ((mem_stratFibre_iff hUp).2 ?_))
      obtain ⟨hk, ht⟩ := run_eq_II_three hII hΔ
      rw [strat]
      exact Prod.ext hk ht
  · refine Or.inr ((mem_stratFibre_iff hUp).2 ?_)
    obtain ⟨hk, ht⟩ := run_eq_IVns_three hIV hΔ
    rw [strat]
    exact Prod.ext hk ht

/-- **The `III` locus lies in the `(III, 2)` stratum.** -/
theorem iii3Locus_subset_stratFibre : iii3Locus ⊆ stratFibre 3 (KodairaSymbol.III, 2) := by
  intro x hx
  have hA := mem_iii3Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_three hA
  obtain ⟨hk, ht⟩ := run_eq_III_three hA hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 (by rw [strat]; exact Prod.ext hk ht)

/-- **The split `IV` locus lies in the `(IV, 3)` stratum.** -/
theorem iv3Locus_subset_stratFibre : iv3Locus ⊆ stratFibre 3 (KodairaSymbol.IV, 3) := by
  intro x hx
  have hA := mem_iv3Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_IV_three hA
  obtain ⟨hk, ht⟩ := run_eq_IV_three hA hΔ
  exact (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 (by rw [strat]; exact Prod.ext hk ht)

/-! ### The Kodaira symbol on the `I₀*` loci

The four `I₀*` loci of the head: two in the `9 ∣ a₄` regime, two in the `v₃(a₄) = 1` regime. -/

open scoped Classical in
/-- **The `(I₀*, 1)` locus of the `9 ∣ a₄` regime lies in the `(I₀*, 1)` stratum.** -/
theorem iZeroStarOne3Locus_subset_stratFibre :
    iZeroStarOne3Locus ⊆ stratFibre 3 (KodairaSymbol.I! 0, 1) := by
  intro x hx
  obtain ⟨A, C, k, hA, hC, hk, hCu⟩ := exists_form_of_mem_iZeroStarOne3Locus hx
  have hAu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A := not_dvd_of_eq_add_mul_three (Or.inr rfl) hk
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hA, hC]
    exact ofShortNF_Δ_ne_zero_izeroStarOneTwo_three hAu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_I0star_one_three (p := 3) rfl (A := A) (C := C) (k := k) hk hCu
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 2 * A) (((3 : ℕ) : ℤ_[3]) ^ 3 * C)).Δ ≠ 0 from by
      rwa [← hA, ← hC])
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  exact Prod.ext (by simpa only [hA, hC] using hks) (by simpa only [hA, hC] using hts)

open scoped Classical in
/-- **The `(I₀*, 2)` locus of the `9 ∣ a₄` regime lies in the `(I₀*, 2)` stratum.** -/
theorem iZeroStarTwo3Locus_subset_stratFibre :
    iZeroStarTwo3Locus ⊆ stratFibre 3 (KodairaSymbol.I! 0, 2) := by
  intro x hx
  obtain ⟨A, C, k, hA, hC, hk⟩ := exists_form_of_mem_iZeroStarTwo3Locus hx
  have hAu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A := not_dvd_of_eq_add_mul_three (Or.inl rfl) hk
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hA, hC]
    exact ofShortNF_Δ_ne_zero_izeroStarOneTwo_three hAu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_I0star_two_three (p := 3) rfl (A := A) (C := C) (k := k) hk
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 2 * A) (((3 : ℕ) : ℤ_[3]) ^ 3 * C)).Δ ≠ 0 from by
      rwa [← hA, ← hC])
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  exact Prod.ext (by simpa only [hA, hC] using hks) (by simpa only [hA, hC] using hts)

namespace IZeroStarUnitThree

open scoped Classical in
/-- **The `u = 2` cylinder of the `v₃(a₄) = 1` regime lies in the `(I₀*, 1)` stratum.** -/
theorem locus_two_subset_stratFibre : locus 2 ⊆ stratFibre 3 (KodairaSymbol.I! 0, 1) := by
  intro x hx
  obtain ⟨α, M, h1, hα, he, hM, hsub⟩ := exists_form_of_mem_locus res_cast_snd_two hx
  obtain ⟨k, hk⟩ := exists_form_of_dvd_sub (v := -1) (w := 1) (by push_cast; norm_num) hsub
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [h1]
    exact ofShortNF_Δ_ne_zero_of_unit hM (not_dvd_of_eq_add_mul_three (Or.inr rfl) hk)
  obtain ⟨hks, hts⟩ := run_eq_I0star_one h1 he hM hk hΔ
  exact (mem_stratFibre_iff (show x ∈ nonsingularLocus 3 from hΔ)).2
    (by rw [strat]; exact Prod.ext hks hts)

open scoped Classical in
/-- **The `u = 1` cylinder of the `v₃(a₄) = 1` regime lies in the `(I₀*, 2)` stratum.** -/
theorem locus_one_subset_stratFibre : locus 1 ⊆ stratFibre 3 (KodairaSymbol.I! 0, 2) := by
  intro x hx
  obtain ⟨α, M, h1, hα, he, hM, hsub⟩ := exists_form_of_mem_locus res_cast_snd_one hx
  obtain ⟨k, hk⟩ := exists_form_of_dvd_sub (v := 1) (w := 0) (by push_cast; norm_num) hsub
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [h1]
    exact ofShortNF_Δ_ne_zero_of_unit hM (not_dvd_of_eq_add_mul_three (Or.inl rfl) hk)
  obtain ⟨hks, hts⟩ := run_eq_I0star_two h1 he hM hk hΔ
  exact (mem_stratFibre_iff (show x ∈ nonsingularLocus 3 from hΔ)).2
    (by rw [strat]; exact Prod.ext hks hts)

end IZeroStarUnitThree

/-! ### Family A's halves: their symbol and their measurability -/

namespace FamilyAThree

open scoped Classical in
/-- **Every point of a half of Family A lies in a stratum over `Iₘ*` with `m ≠ 0`.** -/
theorem exists_mem_stratFibre_of_mem_part {t : ℕ} {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ part t) :
    ∃ m : ℕ, m ≠ 0 ∧ x ∈ stratFibre 3 (KodairaSymbol.I! m, t) := by
  obtain ⟨hΔ, hL, ht⟩ := hx
  obtain ⟨m, hm, hks⟩ := exists_kodairaSymbol_eq_Istar_of_mem_locus hΔ hL
  exact ⟨m, hm,
    (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 (by rw [strat]; exact Prod.ext hks ht)⟩

open scoped Classical in
/-- **The Tamagawa-`t` part of Family A is the locus cut by the `t`-row.** -/
theorem part_eq_inter (t : ℕ) : part t = locus ∩ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, t) := by
  ext x
  constructor
  · rintro ⟨hΔ, hL, ht⟩
    refine ⟨hL, Set.mem_iUnion.2 ⟨(TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol,
      (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_⟩⟩
    rw [strat]
    exact Prod.ext rfl ht
  · rintro ⟨hL, hκ⟩
    obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 hκ
    have hUp : x ∈ nonsingularLocus 3 := stratFibre_subset _ hκ
    have h := (mem_stratFibre_iff hUp).1 hκ
    rw [strat] at h
    exact ⟨hUp, hL, congrArg Prod.snd h⟩

/-- **Each half of Family A is measurable.** -/
theorem measurableSet_part (t : ℕ) : MeasurableSet (part t) := by
  rw [part_eq_inter]
  exact measurableSet_locus.inter
    (MeasurableSet.iUnion fun κ => (isOpen_stratFibre (κ, t)).measurableSet)

end FamilyAThree

/-! ### The same-symbol pairs of the `I₀*` blocks

Rows `t = 1` and `t = 2` each carry two `(I₀*, t)` loci, one in each regime of `v₃(a₄)`, which the
symbol cannot tell apart; `9 ∣ a₄` on the one and `v₃(a₄) = 1` on the other separates them. -/

/-- **The two `(I₀*, 1)` loci are disjoint**: `9 ∣ a₄` on `iZeroStarOne3Locus`, `v₃(a₄) = 1` on
`IZeroStarUnitThree.locus 2`. -/
theorem disjoint_iZeroStarOne3Locus_locus_two :
    Disjoint iZeroStarOne3Locus (IZeroStarUnitThree.locus 2) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, M, h1, hα, -, -, -⟩ :=
    IZeroStarUnitThree.exists_form_of_mem_locus IZeroStarUnitThree.res_cast_snd_two hx'
  have h9 : (ZMod.cast (PadicInt.toZModPow 4 x.1) : ZMod (3 ^ 2)) = 0 :=
    headResIZeroStarOneThree_cast_two (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2)
      (mem_iZeroStarOne3Locus_iff.1 hx)
  rw [PadicInt.cast_toZModPow 2 4 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero,
    h1] at h9
  obtain ⟨c, hc⟩ := h9
  exact hα ⟨c, mul_left_cancel₀ PadicInt.uniformizer_ne_zero (by rw [hc]; ring)⟩

/-- **The two `(I₀*, 2)` loci are disjoint**, for the same reason. -/
theorem disjoint_iZeroStarTwo3Locus_locus_one :
    Disjoint iZeroStarTwo3Locus (IZeroStarUnitThree.locus 1) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨α, M, h1, hα, -, -, -⟩ :=
    IZeroStarUnitThree.exists_form_of_mem_locus IZeroStarUnitThree.res_cast_snd_one hx'
  have h9 : (ZMod.cast (PadicInt.toZModPow 4 x.1) : ZMod (3 ^ 2)) = 0 :=
    headResIZeroStarTwoThree_cast_two (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2)
      (mem_iZeroStarTwo3Locus_iff.1 hx)
  rw [PadicInt.cast_toZModPow 2 4 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero,
    h1] at h9
  obtain ⟨c, hc⟩ := h9
  exact hα ⟨c, mul_left_cancel₀ PadicInt.uniformizer_ne_zero (by rw [hc]; ring)⟩

end WeierstrassCurve

end
