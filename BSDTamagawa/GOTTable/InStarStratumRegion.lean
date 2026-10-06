/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarEntryTransfer
public import BSDTamagawa.GOTTable.InStarGoodRegion

/-!
# The minimal `Iₘ*` stratum is the dilate of `goodRegion p m c`

For every prime `p ≥ 5`, every `m ≥ 1` and every Tamagawa number `c`,

  `stratFibre p (Iₘ*, c) ∖ σ_p(ℤ_p²) = deepScale p '' goodRegion p m c`,

an equality of sets. Both inclusions rest on one computation: for `t` and `c₀` units and `m ≥ 1`,
the point `goodPair p t (pᵐc₀)` lies on the stratum `(Iₘ*, 4)` or `(Iₘ*, 2)` according as
`goodModelTest t c₀ m` is a square. Conversely, a point of the minimal stratum is a good pair
`goodPair p t C` with `C = p^k c₀`, `c₀` a unit and `k = v(C) ≥ 1`, and comparing Kodaira symbols
gives `k = m`.

## Main results

* `exists_pow_mul_isUnit`: a nonzero element of `ℤ_[p]` divisible by `p` is `p^k` times a unit
  with `k ≥ 1`.
* `goodPair_notMem_range_scaleProdByPPow`: a good pair with `t` a unit is not in `σ_p(ℤ_p²)`.
* `mem_stratFibre_goodPair`: the good pair `goodPair p t (pᵐc₀)` lies on the stratum `(Iₘ*, c)`
  with `c = 4` or `2` according to the square test.
* `stratFibre_Istar_diff_range_eq_deepScale_image`: the displayed equality of sets.
* `measurableSet_goodRegion`: `goodRegion p m c` is measurable.
-/

open MeasureTheory Set CommRing Ideal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Splitting off the `p`-power part -/

/-- **A nonzero `p`-adic integer divisible by `p` is `p^k` times a unit, with `k ≥ 1`.** -/
theorem exists_pow_mul_isUnit {C : ℤ_[p]} (hC0 : C ≠ 0) (hC : (p : ℤ_[p]) ∣ C) :
    ∃ (k : ℕ) (c₀ : ℤ_[p]), 1 ≤ k ∧ IsUnit c₀ ∧ C = (p : ℤ_[p]) ^ k * c₀ := by
  have hspec := PadicInt.unitCoeff_spec hC0
  have hk : 1 ≤ C.valuation := by
    rcases Nat.eq_zero_or_pos C.valuation with h0 | h0
    · refine absurd (isUnit_of_dvd_unit hC ?_) PadicInt.prime_p.not_isUnit
      rw [hspec, h0, pow_zero, mul_one]
      exact (PadicInt.unitCoeff hC0).isUnit
    · exact h0
  exact ⟨C.valuation, (PadicInt.unitCoeff hC0 : ℤ_[p]), hk, (PadicInt.unitCoeff hC0).isUnit,
    by rw [mul_comm]; exact hspec⟩

/-! ### A good pair is minimal -/

/-- **A good pair with `t` a unit is not a dilate**, i.e. lies outside
`σ_p(ℤ_p²) = range (PadicInt.scaleProdByPPow 4 6)`. Its first coordinate is `-3p²t²`, whose
valuation is exactly `2` for `p ≥ 5`, so `p⁴` does not divide it. -/
theorem goodPair_notMem_range_scaleProdByPPow (hp : 5 ≤ p) {t C : ℤ_[p]} (ht : IsUnit t) :
    goodPair p t C
      ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  intro hr
  obtain ⟨h4, -⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
  obtain ⟨z, hz⟩ := h4
  have hz' : (-3 : ℤ_[p]) * (p : ℤ_[p]) ^ 2 * t ^ 2 = (p : ℤ_[p]) ^ 4 * z := hz
  have hcan : (-3 : ℤ_[p]) * t ^ 2 = (p : ℤ_[p]) ^ 2 * z :=
    mul_left_cancel₀ (pow_ne_zero 2 hϖ) (by linear_combination hz')
  have hdvd : (p : ℤ_[p]) ∣ (-3 : ℤ_[p]) * t ^ 2 := ⟨(p : ℤ_[p]) * z, by rw [hcan]; ring⟩
  exact PadicInt.dvd_iff_not_isUnit.1 hdvd (((PadicInt.isUnit_three hp).neg).mul (ht.pow 2))

/-! ### The run on a good pair -/

open scoped Classical in
/-- **Tate's algorithm on the good pair `(-3p²t², p³(2t³ + pᵐc₀))`, for `t` and `c₀` units and
`m ≥ 1`, answers `Iₘ*` with Tamagawa number `4` or `2` according as `goodModelTest t c₀ m` is a
square.** -/
theorem mem_stratFibre_goodPair (hp : 5 ≤ p) {t c₀ : ℤ_[p]} (ht : IsUnit t) (hc₀ : IsUnit c₀)
    {m : ℕ} (hm : 1 ≤ m) :
    goodPair p t ((p : ℤ_[p]) ^ m * c₀)
      ∈ stratFibre p (KodairaSymbol.I! m, if IsSquare (goodModelTest t c₀ m) then 4 else 2) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have ht' : ¬ (p : ℤ_[p]) ∣ t := fun h => (PadicInt.dvd_iff_not_isUnit.1 h) ht
  have hc₀' : ¬ (p : ℤ_[p]) ∣ c₀ := fun h => (PadicInt.dvd_iff_not_isUnit.1 h) hc₀
  have hC : (p : ℤ_[p]) ∣ (p : ℤ_[p]) ^ m * c₀ :=
    dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) c₀
  have hC0 : (p : ℤ_[p]) ^ m * c₀ ≠ 0 := mul_ne_zero (pow_ne_zero m hϖ) hc₀.ne_zero
  have hΔ : (ofShortNF (goodPair p t ((p : ℤ_[p]) ^ m * c₀)).1
      (goodPair p t ((p : ℤ_[p]) ^ m * c₀)).2).Δ ≠ 0 :=
    (ofShortNF_goodPair_Δ_ne_zero_iff hp ht hC).2 hC0
  have hU : goodPair p t ((p : ℤ_[p]) ^ m * c₀) ∈ nonsingularLocus p := hΔ
  obtain ⟨A, B, hx1, hx2, hmem⟩ := mem_deepResidueLocus_iff.1
    ((mem_deepResidueLocus_doubleRootResidues_iff hp).2 ⟨t, _, ht, hC, rfl⟩)
  rw [doubleRootResidues, Finset.mem_filter] at hmem
  obtain ⟨hcusp, hAne⟩ := hmem
  have h5 := step5_run_eq_ok_of_dvd hp
    (⟨A, hx1⟩ : (p : ℤ_[p]) ^ 2 ∣ (goodPair p t ((p : ℤ_[p]) ^ m * c₀)).1)
    (⟨B, hx2⟩ : (p : ℤ_[p]) ^ 3 ∣ (goodPair p t ((p : ℤ_[p]) ^ m * c₀)).2)
  have hd := (step6_cubic_bridge hp hx1 hx2 h5).1.2 hcusp
  have h6 := step6_run_eq_ok_of_hasDoubleRoot h5 hd
  have hnt : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p])
      (ofShortNF (goodPair p t ((p : ℤ_[p]) ^ m * c₀)).1
        (goodPair p t ((p : ℤ_[p]) ^ m * c₀)).2))) 1 1).HasTripleRoot := by
    rw [hasTripleRoot_step6_cubic_iff_toZMod_eq_zero hp hx1 h5]
    exact hAne
  obtain ⟨out, h7, -, -, -⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hnt
  have hrun := TateAlgorithm.run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7)
  have hΔV : (goodModel t ((p : ℤ_[p]) ^ m * c₀)).Δ ≠ 0 := goodModel_Δ_ne_zero hp ht' hc₀' hm
  have hV : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c₀))
      ⟨1, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩ :=
    hasValuation_goodModel t c₀ (show m + 3 = 2 * 2 + (m - 1) by omega)
  have ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t ((p : ℤ_[p]) ^ m * c₀)).a₂ :=
    not_sq_dvd_goodModel_a₂ hp ht'
  obtain ⟨hk1, hc1⟩ := Step7.run_error_eq_subprocedure_of_isIntTranslate hp hΔ hΔV h6 hnt hV ha₂
    (isIntTranslate_ofShortNF_goodModel t ((p : ℤ_[p]) ^ m * c₀)) h7
  obtain ⟨hk2, hc2⟩ := Step7.subprocedure_goodModel_entry hp ht' hc₀' hm
    PadicInt.uniformizer_ne_zero hΔV hV ha₂
  rw [mem_stratFibre_iff hU, strat]
  exact Prod.ext (by rw [hrun, hk1, hk2]) (by rw [hrun, hc1, hc2])

/-! ### The stratum as a region of the `(A, B)` plane -/

open scoped Classical in
/-- **The minimal part of the `Iₘ*` stratum at Tamagawa number `c` is exactly the dilate of
`goodRegion p m c`**, for every `m ≥ 1`, every `c`, and every prime `p ≥ 5`:

  `stratFibre p (Iₘ*, c) ∖ σ_p(ℤ_p²) = deepScale p '' goodRegion p m c`. -/
theorem stratFibre_Istar_diff_range_eq_deepScale_image (hp : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m) (c : ℕ) :
    stratFibre p (KodairaSymbol.I! m, c)
        \ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = deepScale p '' goodRegion p m c := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨hxF, hxR⟩ := hx
    obtain ⟨t, C, ht, hC, rfl⟩ := (mem_deepResidueLocus_doubleRootResidues_iff hp).1
      (stratFibre_Istar_pos_diff_range_subset hp (by omega : m ≠ 0) c ⟨hxF, hxR⟩)
    have hU : goodPair p t C ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have hC0 : C ≠ 0 := (goodPair_mem_nonsingularLocus_iff hp ht hC).1 hU
    obtain ⟨k, c₀, hk, hc₀, rfl⟩ := exists_pow_mul_isUnit hC0 hC
    have heq := ((mem_stratFibre_iff hU).1 (mem_stratFibre_goodPair hp ht hc₀ hk)).symm.trans
      ((mem_stratFibre_iff hU).1 hxF)
    have hidx : k = m := by injection congrArg Prod.fst heq
    subst hidx
    exact ⟨((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ k * c₀),
      ⟨t, c₀, ht, hc₀, rfl, congrArg Prod.snd heq⟩,
      deepScale_ofCoords t ((p : ℤ_[p]) ^ k * c₀)⟩
  · rintro x ⟨z, ⟨t, c₀, ht, hc₀, rfl, rfl⟩, rfl⟩
    rw [deepScale_ofCoords]
    exact ⟨mem_stratFibre_goodPair hp ht hc₀ hm, goodPair_notMem_range_scaleProdByPPow hp ht⟩

/-- **`goodRegion p m c` is measurable**, for every `m ≥ 1`, every `c` and every prime `p ≥ 5`. It
is the preimage under the measurable embedding `deepScale` of the measurable set
`stratFibre p (Iₘ*, c) ∖ σ_p(ℤ_p²)`. -/
theorem measurableSet_goodRegion (hp : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m) (c : ℕ) :
    MeasurableSet (goodRegion p m c) := by
  have hemb : MeasurableEmbedding (deepScale p) :=
    PadicInt.measurableEmbedding_scaleProdByPPow 2 3
  have hset : MeasurableSet (deepScale p '' goodRegion p m c) := by
    rw [← stratFibre_Istar_diff_range_eq_deepScale_image hp hm c]
    exact (isOpen_stratFibre _).measurableSet.diff
      (PadicInt.measurableEmbedding_scaleProdByPPow 4 6).measurableSet_range
  rw [← Set.preimage_image_eq (goodRegion p m c) hemb.injective]
  exact hemb.measurable hset

end WeierstrassCurve
