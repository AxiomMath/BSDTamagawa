/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateTailLawUnconditional

/-!
# Densities of the strata `(I₂, 2)`, `(II, 1)`, `(III, 2)`, `(IV, 3)`, `(IV, 1)` for `p ≥ 5`

For a prime `p ≥ 5`, write `N = |goodRes p|`, so that `2N = p - 1`, and `T = (1 - p⁻¹⁰)⁻¹` for the
mass of the `σ_p`-tower of non-minimal models above a minimal one. Every reduction datum `K`
satisfies `δ_p(K) = μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²)) · T`, so a density is computed by identifying the
minimal part of its stratum as a congruence locus. This file does so for five strata:

| stratum | density | closed form |
|---|---|---|
| `(I₂, 2)` | `4N² p⁻⁴ T` | `(p-1)²p⁶/(p¹⁰-1)` |
| `(II, 1)` | `2N p⁻³ T` | `(p-1)p⁷/(p¹⁰-1)` |
| `(III, 2)` | `2N p⁻⁴ T` | `(p-1)p⁶/(p¹⁰-1)` |
| `(IV, 3)`, `(IV, 1)` | `N p⁻⁵ T` | `(p-1)p⁵/(2(p¹⁰-1))` |


## Main definitions

* `WeierstrassCurve.ivNonSplitLocus`: `p² ∣ a₄` and `a₆ = p²u` with `u` a unit of non-square
  residue.

## Main results

* `WeierstrassCurve.splits_step5_quadratic_iff`: Step 5's quadratic splits exactly when `a₆/p²` has
  square residue.
* `WeierstrassCurve.run_eq_IV_of_eq_sq_mul`: a short model with `p² ∣ a₄`, `a₆ = p²u`, `p ∤ u` has
  reduction datum `(IV, 3)` or `(IV, 1)` according as the residue of `u` is a square or not.
* `WeierstrassCurve.deltaP_eq_mul_inv_one_sub`: `δ_p(K) = μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²)) · T` for every
  reduction datum `K`.
* `WeierstrassCurve.deltaP_I_two_eq`, `WeierstrassCurve.deltaP_II_eq`,
  `WeierstrassCurve.deltaP_III_eq`, `WeierstrassCurve.deltaP_IV_three_eq`,
  `WeierstrassCurve.deltaP_IV_one_eq`: the five densities above.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### A monic quadratic splits exactly when its discriminant is a square -/

/-- **Multiplying by `4` does not change squareness**, away from characteristic `2`: `4x = (2s)²`
when `x = s²`, and `x = (y/2)²` when `4x = y²`. -/
theorem isSquare_four_mul_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (x : K) :
    IsSquare (4 * x) ↔ IsSquare x := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  refine ⟨fun ⟨y, hy⟩ => ⟨y / 2, ?_⟩, fun ⟨s, hs⟩ => ⟨2 * s, by rw [hs]; ring⟩⟩
  field_simp
  linear_combination hy

/-- **A monic quadratic that splits has square discriminant**, away from characteristic `2`. -/
theorem isSquare_of_splits_quadratic {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b : K}
    (h : (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X
      + Polynomial.C (-b)).Splits) : IsSquare (a ^ 2 + 4 * b) := by
  obtain ⟨y, hy⟩ := h.exists_eval_eq_zero (by
    rw [Polynomial.degree_quadratic (one_ne_zero (α := K))]; decide)
  refine (TateAlgorithm.Step2.exists_sq_add_mul_sub_eq_zero_iff h2 a b).1 ⟨y, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X] at hy
  linear_combination hy

/-- **A monic quadratic splits exactly when its discriminant is a square.** -/
theorem splits_quadratic_iff_isSquare {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (a b : K) :
    (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X
        + Polynomial.C (-b)).Splits ↔ IsSquare (a ^ 2 + 4 * b) :=
  ⟨isSquare_of_splits_quadratic h2, splits_quadratic_of_isSquare h2⟩

/-! ### Step 5's split test, as an equivalence -/

/-- **Step 5's quadratic on the Step-2 translate of a short model, with its discriminant.** For
`p ≥ 5`, `p² ∣ a₄` and `a₆ = p²u`, the quadratic Step 5 tests is `⟨0, 1, c, -d⟩` for residues
`c = a₃(V)/p`, `d = a₆(V)/p²` of the translate `V`, and its discriminant `c² + 4d` is `4u` modulo
`p`. -/
theorem exists_step5_quadratic_disc (hp : 5 ≤ p) {a₄ a₆ u : ℤ_[p]} (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄)
    (ha₆ : a₆ = (p : ℤ_[p]) ^ 2 * u) :
    ∃ c d : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])},
      quadratic (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) 1 = ⟨0, 1, c, -d⟩ ∧
        c ^ 2 + 4 * d = 4 * CommRing.mod (p : ℤ_[p]) u := by
  have hϖ0 : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h6 : (p : ℤ_[p]) ^ 2 ∣ a₆ := ⟨u, ha₆⟩
  set V : WeierstrassCurve ℤ_[p] := Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆) with hV
  have hs3 := step3_run_eq_ok_of_dvd hp (dvd_trans (dvd_pow_self _ two_ne_zero) h4) h6
  have hv3 := Step3.run_hasValuation hs3
  have hc₄ : (p : ℤ_[p]) ^ 2 ∣ V.c₄ := by
    rw [hV, Step2.translate_c₄, ofShortNF_c₄]
    exact h4.mul_left _
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok V := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv3.b₂) hv3.b₆).2 hc₄)
  have hv4 := Step4.run_hasValuation hϖ0 hs4
  have ha₃ : (p : ℤ_[p]) ∣ V.a₃ := by simpa using hv4.a₃
  have e1 : (p : ℤ_[p]) * CommRing.div V.a₃ (p : ℤ_[p]) = V.a₃ := CommRing.mul_div hϖ0 ha₃
  have e2 : (p : ℤ_[p]) ^ 2 * CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2) = V.a₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ0) hv4.a₆
  have e3 : (p : ℤ_[p]) ^ 2 * CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) = V.b₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ0) hv4.b₆
  have hdisc : CommRing.div V.a₃ (p : ℤ_[p]) ^ 2 + 4 * CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2)
      = CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ0) ?_
    rw [e3, WeierstrassCurve.b₆]
    linear_combination ((p : ℤ_[p]) * CommRing.div V.a₃ (p : ℤ_[p]) + V.a₃) * e1 + 4 * e2
  have hmodw : CommRing.mod (p : ℤ_[p]) (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2))
      = 4 * CommRing.mod (p : ℤ_[p]) u := by
    have hcb := cb_dvd_c₆_add_mul_b₆_of_dvd (by simpa using hv4.b₂) hv4.b₄
    have hc₆ : V.c₆ = -864 * a₆ := by rw [hV, Step2.translate_c₆, ofShortNF_c₆]
    have hfac : V.c₆ + 216 * V.b₆
        = (p : ℤ_[p]) ^ 2 * (216 * (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) - 4 * u)) := by
      linear_combination hc₆ - 864 * ha₆ - 216 * e3
    rw [hfac] at hcb
    obtain ⟨z, hz⟩ := hcb
    have hdvd : (p : ℤ_[p]) ∣ 216 * (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) - 4 * u) :=
      ⟨z, mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by rw [hz]; ring)⟩
    rw [(isUnit_twoHundredSixteen hp).dvd_mul_left] at hdvd
    have h0 := (CommRing.mod_eq_zero (p : ℤ_[p])
      (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) - 4 * u)).2 hdvd
    rw [map_sub, map_mul, map_ofNat, sub_eq_zero] at h0
    exact h0
  refine ⟨CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₃ (p : ℤ_[p])),
    CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2)), by simp [quadratic], ?_⟩
  rw [show CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₃ (p : ℤ_[p])) ^ 2
        + 4 * CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2))
      = CommRing.mod (p : ℤ_[p])
          (CommRing.div V.a₃ (p : ℤ_[p]) ^ 2 + 4 * CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2)) from by
    simp only [map_add, map_mul, map_pow, map_ofNat], hdisc, hmodw]

/-- **Step 5's split test, as an equivalence.** For every prime `p ≥ 5`, on a short model with
`p² ∣ a₄` and `a₆ = p²u`,

  `(quadratic p V 1).toPoly.Splits  ↔  u` has square residue modulo `p`,

`V` being the Step-2 translate. -/
theorem splits_step5_quadratic_iff (hp : 5 ≤ p) {a₄ a₆ u : ℤ_[p]} (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄)
    (ha₆ : a₆ = (p : ℤ_[p]) ^ 2 * u) :
    (quadratic (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) 1).toPoly.Splits
      ↔ IsSquare (PadicInt.toZMod u) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2' : (2 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≠ 0 := by
    rw [show (2 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = CommRing.mod (p : ℤ_[p]) 2 from by
      simp only [map_ofNat], Ne, CommRing.mod_eq_zero]
    exact not_dvd_two_of_odd hodd
  obtain ⟨c, d, hquad, hdisc⟩ := exists_step5_quadratic_disc hp h4 ha₆
  rw [hquad, Cubic.of_a_eq_zero rfl, splits_quadratic_iff_isSquare h2', hdisc,
    isSquare_four_mul_iff h2', isSquare_mod_iff_isSquare_toZMod]

/-! ### The forward run at `IV` -/

open scoped Classical in
/-- **The forward run at `IV`.** For every prime `p ≥ 5`, a short model over `ℤ_p` with `p² ∣ a₄`
and `a₆ = p²u`, `p ∤ u`, has reduction datum

  `(IV, 3)` if the residue of `u` is a square, and `(IV, 1)` if it is not.
-/
theorem run_eq_IV_of_eq_sq_mul (hp : 5 ≤ p) {a₄ a₆ u : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄) (hu : ¬ (p : ℤ_[p]) ∣ u)
    (ha₆ : a₆ = (p : ℤ_[p]) ^ 2 * u) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if IsSquare (PadicInt.toZMod u) then 3 else 1 := by
  have h6 : (p : ℤ_[p]) ^ 2 ∣ a₆ := ⟨u, ha₆⟩
  have h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ a₆ := by
    rintro ⟨z, hz⟩
    exact hu ⟨z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [← ha₆, hz]; ring)⟩
  have hκ := run_kodairaSymbol_eq_IV_of_emultiplicity_eq_two hp hΔ h4 h6 h6'
  have hs3 := step3_run_eq_ok_of_dvd hp (dvd_trans (dvd_pow_self _ two_ne_zero) h4) h6
  have hv3 := Step3.run_hasValuation hs3
  have hc₄ : (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₄ := by
    rw [Step2.translate_c₄, ofShortNF_c₄]
    exact h4.mul_left _
  have hc₆ : ¬ (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₆ := by
    rw [Step2.translate_c₆, ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left]
    exact h6'
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv3.b₂) hv3.b₆).2 hc₄)
  have hv4 := Step4.run_hasValuation PadicInt.uniformizer_ne_zero hs4
  have hs5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.error
      ⟨Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆), KodairaSymbol.IV,
        if (quadratic (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))
          1).toPoly.Splits then 3 else 1⟩ := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    exact ite_eq_right fun hcon =>
      hc₆ ((cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv4.b₂) hv4.b₄).1 hcon)
  refine ⟨hκ, ?_⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step5 hΔ hs5)]
  exact if_congr (splits_step5_quadratic_iff hp h4 ha₆) rfl rfl

/-! ### The two `IV` loci -/

variable (p) in
/-- The elements `a₆ = p²u` with `u` a unit whose residue is **not** a square. -/
noncomputable def ivBadSnd : Set ℤ_[p] :=
  PadicInt.scaleByPPow 2 '' (PadicInt.toZMod ⁻¹' (nonSqUnits p : Set (ZMod p)))

variable (p) in
/-- The **non-split `IV` locus**: `p² ∣ a₄` and `a₆ = p²u` with `u` a unit of non-square residue.
-/
noncomputable def ivNonSplitLocus : Set (ℤ_[p] × ℤ_[p]) :=
  ((Ideal.span {(p : ℤ_[p]) ^ 2} : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ ivBadSnd p

/-- A pair lies in the non-split `IV` locus iff `p² ∣ a₄` and `a₆ = p²u` for a unit `u` whose
residue is not a square. -/
theorem mem_ivNonSplitLocus_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ ivNonSplitLocus p ↔ (p : ℤ_[p]) ^ 2 ∣ x.1 ∧ ∃ u : ℤ_[p], ¬ (p : ℤ_[p]) ∣ u ∧
      ¬ IsSquare (PadicInt.toZMod u) ∧ x.2 = (p : ℤ_[p]) ^ 2 * u := by
  rw [ivNonSplitLocus, Set.mem_prod]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton, ivBadSnd, Set.mem_image,
    Set.mem_preimage, mem_nonSqUnits_iff, PadicInt.scaleByPPow,
    ← PadicInt.dvd_iff_toZMod_eq_zero, ne_eq]
  constructor
  · rintro ⟨h1, u, ⟨hu0, husq⟩, hu2⟩
    exact ⟨h1, u, hu0, husq, hu2.symm⟩
  · rintro ⟨h1, u, hu, husq, hu2⟩
    exact ⟨h1, u, ⟨hu, husq⟩, hu2.symm⟩

/-- **The mass of the non-split `IV` locus is `N p⁻⁵`.** -/
theorem volume_ivNonSplitLocus (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (ivNonSplitLocus p)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 := by
  have hz : (p : ℝ≥0∞) ^ (-((2 : ℕ) : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 2 :=
    (PadicInt.measure_span_pPow (p := p) 2).symm.trans (PadicInt.measure_span_pPow' 2)
  rw [ivNonSplitLocus, ivBadSnd, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.measure_span_pPow' 2, PadicInt.measure_image_scaleByPPow,
    PadicInt.volume_preimage_toZMod_coe, ← card_sqUnits_eq_card_nonSqUnits hp,
    card_sqUnits_eq_card_goodRes hp, hz]
  ring

/-- **The split `IV` locus lies in the stratum `τ_p⁻¹((IV, 3))`.** -/
theorem ivSplitLocus_subset_stratFibre (hp : 5 ≤ p) :
    ivSplitLocus p ⊆ stratFibre p (KodairaSymbol.IV, 3) := by
  intro x hx
  obtain ⟨h4, u, hu, husq, h2eq⟩ := mem_ivSplitLocus_iff.1 hx
  have h6 : (p : ℤ_[p]) ^ 2 ∣ x.2 := ⟨u, h2eq⟩
  have h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ x.2 := by
    rintro ⟨z, hz⟩
    exact hu ⟨z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [← h2eq, hz]; ring)⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_five_dvd_ofShortNF_Δ_of_IV hp h4 h6 h6' (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, hc⟩ := run_eq_IV_of_eq_sq_mul hp hΔ h4 hu h2eq
  rw [ite_eq_left husq] at hc
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-- **The non-split `IV` locus lies in the stratum `τ_p⁻¹((IV, 1))`.** -/
theorem ivNonSplitLocus_subset_stratFibre (hp : 5 ≤ p) :
    ivNonSplitLocus p ⊆ stratFibre p (KodairaSymbol.IV, 1) := by
  intro x hx
  obtain ⟨h4, u, hu, husq, h2eq⟩ := mem_ivNonSplitLocus_iff.1 hx
  have h6 : (p : ℤ_[p]) ^ 2 ∣ x.2 := ⟨u, h2eq⟩
  have h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ x.2 := by
    rintro ⟨z, hz⟩
    exact hu ⟨z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [← h2eq, hz]; ring)⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_five_dvd_ofShortNF_Δ_of_IV hp h4 h6 h6' (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, hc⟩ := run_eq_IV_of_eq_sq_mul hp hΔ h4 hu h2eq
  rw [ite_eq_right husq] at hc
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-! ### Strata over distinct Kodaira symbols are disjoint -/

/-- The strata over distinct Kodaira symbols are disjoint. -/
theorem disjoint_stratFibre_of_ne {κ κ' : KodairaSymbol} (h : κ ≠ κ') (c c' : ℕ) :
    Disjoint (stratFibre p (κ, c)) (stratFibre p (κ', c')) :=
  Set.disjoint_left.2 fun x hx hx' => by
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
    have e1 := (mem_stratFibre_iff hUp).1 hx
    have e2 := (mem_stratFibre_iff hUp).1 hx'
    rw [e1] at e2
    exact h (congrArg Prod.fst e2)

/-! ### Only Step 5 answers `IV`

An answer of `IV` at Steps 1–11 forces `p³ ∤ c₆`, i.e. `v_p(a₆) = 2` on the short plane. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Step 3 answers `II`, not `IV`. -/
theorem Step3.not_cb_dvd_c₆_of_eq_IV (h : Step3.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · obtain ⟨n, hn⟩ := Step2.exists_kodairaSymbol_eq_I h
    rw [hn] at hκ
    simp at hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 4 answers `III`, not `IV`. -/
theorem Step4.not_cb_dvd_c₆_of_eq_IV (h : Step4.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.not_cb_dvd_c₆_of_eq_IV h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **Step 5's answer `IV` forces `p³ ∤ c₆`.** -/
theorem Step5.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p)
    (h : Step5.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step4.not_cb_dvd_c₆_of_eq_IV h hκ
  · have hv := Step4.run_hasValuation PadicInt.uniformizer_ne_zero h'
    have key : ¬ (p : ℤ_[p]) ^ 3 ∣ W'.b₆ → ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := fun hb₆ hc =>
      hb₆ ((cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv.b₂) hv.b₄).2
        (by rw [Step4.run_c₆ h']; exact hc))
    split_ifs at h with hb₆ <;> exact key hb₆

/-- Step 6 answers `I₀*`, not `IV`. -/
theorem Step6.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p)
    (h : Step6.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.not_cb_dvd_c₆_of_eq_IV hp h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- No answer of the `Iₙ*` subprocedure of Step 7 is `IV`. -/
theorem Step7.subprocedure_kodairaSymbol_ne_IV (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.IV := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 answers `Iₙ*`, not `IV`. -/
theorem Step7.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.not_cb_dvd_c₆_of_eq_IV hp (heq.trans h) hκ
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hκ ?_
    apply Step7.subprocedure_kodairaSymbol_ne_IV

/-- Step 8 answers `IV*`, not `IV`. -/
theorem Step8.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.not_cb_dvd_c₆_of_eq_IV hp hΔ h hκ
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- Step 9 answers `III*`, not `IV`. -/
theorem Step9.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.not_cb_dvd_c₆_of_eq_IV hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 10 answers `II*`, not `IV`. -/
theorem Step10.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.not_cb_dvd_c₆_of_eq_IV hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `IV` at Steps 1–11 forces `p³ ∤ c₆`, i.e. `v_p(a₆) = 2` on the short plane.** -/
theorem Step11.not_cb_dvd_c₆_of_eq_IV (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV) : ¬ (p : ℤ_[p]) ^ 3 ∣ W.c₆ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.not_cb_dvd_c₆_of_eq_IV hp hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The minimal part of the two `IV` strata -/

open scoped Classical in
/-- **The minimal part of an `IV` stratum is a congruence locus.** For every prime `p ≥ 5`, a point
of `τ_p⁻¹((IV, c))` which is not a `σ_p`-dilate has `p² ∣ a₄` and `a₆ = p²u` with `p ∤ u`, and `c`
is `3` or `1` according as the residue of `u` is a square or not. -/
theorem exists_eq_sq_mul_of_mem_stratFibre_IV (hp : 5 ≤ p) {c : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hxF : x ∈ stratFibre p (KodairaSymbol.IV, c))
    (hxR : x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :
    (p : ℤ_[p]) ^ 2 ∣ x.1 ∧ ∃ u : ℤ_[p], ¬ (p : ℤ_[p]) ∣ u ∧ x.2 = (p : ℤ_[p]) ^ 2 * u ∧
      c = if IsSquare (PadicInt.toZMod u) then 3 else 1 := by
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  obtain ⟨h4, h6⟩ := pow_dvd_of_mem_stratFibre_additive hp hxF
  rw [show (KodairaSymbol.IV, c).1.additiveC₄Level = 2 from rfl] at h4
  rw [show (KodairaSymbol.IV, c).1.additiveC₆Level = 2 from rfl] at h6
  have hs := (mem_stratFibre_iff hxUp).1 hxF
  rw [strat] at hs
  have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.IV := congrArg Prod.fst hs
  have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = c := congrArg Prod.snd hs
  have h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ x.2 := by
    intro hsq
    have hc₆ : (p : ℤ_[p]) ^ 3 ∣ (ofShortNF x.1 x.2).c₆ := by
      rw [ofShortNF_c₆]
      exact hsq.mul_left _
    rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp with out' | W'
    · exact absurd hc₆ (TateAlgorithm.Step11.not_cb_dvd_c₆_of_eq_IV hp hxUp e
        (by rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
            exact hκ))
    · refine hxR (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩)
      · have hd : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
          ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hd
      · have hd : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
          ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hd
  obtain ⟨u, hu2⟩ := h6
  have hu : ¬ (p : ℤ_[p]) ∣ u := fun ⟨z, hz⟩ => h6' ⟨z, by rw [hu2, hz]; ring⟩
  obtain ⟨-, hcIV⟩ := run_eq_IV_of_eq_sq_mul hp hxUp h4 hu hu2
  exact ⟨h4, u, hu, hu2, by rw [← hc, hcIV]⟩

open scoped Classical in
/-- **The minimal part of the stratum `τ_p⁻¹((IV, 3))` is the split `IV` locus**, for every prime
`p ≥ 5`:

  `τ_p⁻¹((IV, 3)) ∖ σ_p(ℤ_p²) = {p² ∣ a₄, a₆ = p²u, p ∤ u, u` a square mod `p}`.
-/
theorem stratFibre_diff_range_eq_ivSplitLocus (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.IV, 3) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = ivSplitLocus p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    obtain ⟨h4, u, hu, hu2, hcv⟩ := exists_eq_sq_mul_of_mem_stratFibre_IV hp hxF hxR
    refine mem_ivSplitLocus_iff.2 ⟨h4, u, hu, ?_, hu2⟩
    by_contra hns
    rw [ite_eq_right hns] at hcv
    omega
  · intro x hx
    obtain ⟨h4, u, hu, husq, hu2⟩ := mem_ivSplitLocus_iff.1 hx
    refine ⟨ivSplitLocus_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨-, h6⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    obtain ⟨z, hz⟩ := h6
    exact hu ⟨(p : ℤ_[p]) ^ 3 * z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [← hu2, hz]; ring)⟩

open scoped Classical in
/-- **The minimal part of the stratum `τ_p⁻¹((IV, 1))` is the non-split `IV` locus**, for every
prime `p ≥ 5`. -/
theorem stratFibre_diff_range_eq_ivNonSplitLocus (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.IV, 1) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = ivNonSplitLocus p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    obtain ⟨h4, u, hu, hu2, hcv⟩ := exists_eq_sq_mul_of_mem_stratFibre_IV hp hxF hxR
    refine mem_ivNonSplitLocus_iff.2 ⟨h4, u, hu, ?_, hu2⟩
    intro hsq
    rw [ite_eq_left hsq] at hcv
    omega
  · intro x hx
    obtain ⟨h4, u, hu, husq, hu2⟩ := mem_ivNonSplitLocus_iff.1 hx
    refine ⟨ivNonSplitLocus_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨-, h6⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    obtain ⟨z, hz⟩ := h6
    exact hu ⟨(p : ℤ_[p]) ^ 3 * z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [← hu2, hz]; ring)⟩

/-! ### Summing the `σ_p`-tower over a stratum

At `p ≥ 5` the density of a stratum satisfies `δ_p(K) = p⁻¹⁰ δ_p(K) + μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²))`;
solving this equation gives each density as the mass of the minimal part of its stratum times
`(1 - p⁻¹⁰)⁻¹`. -/

omit [Fact p.Prime] in
/-- `p⁻¹⁰ < 1` at `p ≥ 5`. -/
private theorem inv_pow_ten_lt_one_of_five_le (hp : 5 ≤ p) : ((p : ℝ≥0∞)⁻¹) ^ 10 < 1 := by
  have h1 : (p : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by exact_mod_cast (by omega : 1 < p))
  exact pow_lt_one₀ zero_le h1 (by norm_num)

/-- For `r < 1` and `x ≠ ⊤`, `x = r x + c` implies `x = c(1 - r)⁻¹`. -/
private theorem eq_mul_inv_one_sub_of_lt_one {r c x : ℝ≥0∞} (hr : r < 1) (hx : x ≠ ⊤)
    (hxe : x = r * x + c) : x = c * (1 - r)⁻¹ := by
  have hrx : r * x ≠ ⊤ := ENNReal.mul_ne_top (ne_top_of_lt hr) hx
  have hsub : x - r * x = c := ENNReal.sub_eq_of_eq_add hrx (hxe.trans (add_comm _ _))
  have hmul : (1 - r) * x = c := by rw [ENNReal.sub_mul (fun _ _ => hx), one_mul, hsub]
  have h1 : (1 : ℝ≥0∞) - r ≠ 0 := (tsub_pos_of_lt hr).ne'
  have h2 : (1 : ℝ≥0∞) - r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  calc x = (1 - r)⁻¹ * ((1 - r) * x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h1 h2, one_mul]
    _ = c * (1 - r)⁻¹ := by rw [hmul, mul_comm]

/-- **Every density is the mass of the minimal part of its stratum times `(1 - p⁻¹⁰)⁻¹`**, at every
prime `p ≥ 5`:

  `δ_p(K) = μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²)) · (1 - p⁻¹⁰)⁻¹`.
-/
theorem deltaP_eq_mul_inv_one_sub (hp : 5 ≤ p) (K : ReductionData) :
    deltaP p K = (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p K \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have hz : (p : ℝ≥0∞) ^ (-(10 : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 10 := by
    rw [show (-(10 : ℤ)) = -((10 : ℕ) : ℤ) from by norm_num]
    exact (PadicInt.measure_span_pPow (p := p) 10).symm.trans (PadicInt.measure_span_pPow' 10)
  have hfix := deltaP_eq_inv_pow_mul_add (stratScaleInvariant_of_five_le hp) K
  rw [hz] at hfix
  exact eq_mul_inv_one_sub_of_lt_one (inv_pow_ten_lt_one_of_five_le hp) (deltaP_ne_top p K) hfix

/-! ### The densities of the two `IV` strata -/

/-- **The density of the split `IV` stratum**, for every prime `p ≥ 5`:

  `δ_p((IV, 3)) = N p⁻⁵ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)p⁵/(2(p¹⁰-1))`. -/
theorem deltaP_IV_three_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.IV, 3)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_ivSplitLocus hp,
    volume_ivSplitLocus hp]

/-- **The density of the non-split `IV` stratum**, for every prime `p ≥ 5`:

  `δ_p((IV, 1)) = N p⁻⁵ (1 - p⁻¹⁰)⁻¹`.
-/
theorem deltaP_IV_one_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.IV, 1)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_ivNonSplitLocus hp,
    volume_ivNonSplitLocus hp]

/-! ### The density of the `II` stratum -/

/-- **The minimal part of the stratum `τ_p⁻¹((II, 1))` is the minimal `II` locus**, for every prime
`p ≥ 5`. -/
theorem stratFibre_diff_range_eq_stratMinimalII (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.II, 1) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = stratMinimalII p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    rcases stratFibre_II_subset_union hp hxF with h | h
    · exact h
    · exact absurd h hxR
  · intro x hx
    obtain ⟨-, -, h6'⟩ := mem_stratMinimalII_iff.1 hx
    refine ⟨stratMinimalII_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨-, h6r⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    exact h6' (dvd_trans (pow_dvd_pow _ (by norm_num)) h6r)

/-- **The density of the `II` stratum**, for every prime `p ≥ 5`:

  `δ_p((II, 1)) = 2N p⁻³ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)p⁷/(p¹⁰-1)`. -/
theorem deltaP_II_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.II, 1)
      = 2 * ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 3 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_stratMinimalII hp,
    volume_stratMinimalII, one_sub_inv_eq hp]
  ring

/-! ### The density of the `I₂` stratum

At level `2` Step 2 reports the Tamagawa number `2` on both of its branches, so the whole level-`2`
multiplicative locus, split and non-split, is the minimal part of the single stratum
`τ_p⁻¹((I₂, 2))`. -/

/-- **The level-2 multiplicative locus lies in the stratum `τ_p⁻¹((I₂, 2))`.** -/
theorem iLocus_two_subset_stratFibre (hp : 5 ≤ p) :
    iLocus p 2 ⊆ stratFibre p (KodairaSymbol.I 2, 2) := by
  intro x hx
  have hUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_of_mem_iLocus hp hx
  have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = 2 := by
    have h := emultiplicity_Δ_of_mem_iLocus hp hx
    rwa [show (((2 : ℕ) : ℕ∞)) = (2 : ℕ∞) from by norm_num] at h
  obtain ⟨hκ, hc⟩ := run_kodaira_tamagawa_of_emultiplicity_eq_two hUp
    (not_dvd_c₄_of_mem_iLocus hp hx) hΔv
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-- **The minimal part of the stratum `τ_p⁻¹((I₂, 2))` is the whole level-2 multiplicative locus**,
for every prime `p ≥ 5`:

  `τ_p⁻¹((I₂, 2)) ∖ σ_p(ℤ_p²) = {p ∤ a₄, v_p(4a₄³ + 27a₆²) = 2}`.
-/
theorem stratFibre_diff_range_eq_iLocus_two (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.I 2, 2) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = iLocus p 2 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have h4 : ¬ (p : ℤ_[p]) ∣ x.1 := fun hd =>
      hxR (mem_range_of_mem_stratFibre_of_dvd_fst hp (by omega) hxF hd)
    have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
      rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
      exact h4
    have hs := (mem_stratFibre_iff hUp).1 hxF
    rw [strat] at hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I 2 := congrArg Prod.fst hs
    have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
      by_contra hnd
      rw [run_eq_of_not_dvd_Δ hUp hnd] at hκ
      exact absurd (KodairaSymbol.I.inj hκ) (by omega)
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄] at hκ
    have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((2 : ℕ) : ℕ∞) :=
      (toNat_emultiplicity_Δ_eq_iff hUp 2).1 (KodairaSymbol.I.inj hκ)
    rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add] at hΔv
    exact ⟨h4, hΔv⟩
  · intro x hx
    refine ⟨iLocus_two_subset_stratFibre hp hx, fun hr => ?_⟩
    exact hx.1 (dvd_trans (dvd_pow_self _ (by norm_num : 4 ≠ 0))
      (PadicInt.mem_range_scaleProdByPPow_iff.1 hr).1)

/-- **The density of the `I₂` stratum**, for every prime `p ≥ 5`:

  `δ_p((I₂, 2)) = 4N² p⁻⁴ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)²p⁶/(p¹⁰-1)`. -/
theorem deltaP_I_two_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.I 2, 2)
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 4
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_iLocus_two hp,
    volume_iLocus hp (by norm_num), one_sub_inv_eq hp]
  ring

/-! ### Only Step 4 answers `III`

An answer of `III` at Steps 1–11 forces `p² ∤ c₄`, i.e. `v_p(a₄) = 1` on the short plane. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- **Step 4's answer `III` forces `p² ∤ c₄`.** -/
theorem Step4.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p)
    (h : Step4.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
    rcases h with h | ⟨W'', -, h⟩
    · obtain ⟨n, hn⟩ := Step2.exists_kodairaSymbol_eq_I h
      rw [hn] at hκ
      simp at hκ
    · split_ifs at h
      obtain rfl := Except.error.inj h
      simp at hκ
  · have hv := Step3.run_hasValuation h'
    have key : ¬ (p : ℤ_[p]) ^ 3 ∣ W'.b₈ → ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := fun hb₈ hc =>
      hb₈ ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv.b₂) hv.b₆).2
        (by rw [Step3.run_c₄ h']; exact hc))
    split_ifs at h with hb₈
    exact key hb₈

/-- Step 5 answers `IV`, not `III`. -/
theorem Step5.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p)
    (h : Step5.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.not_sq_dvd_c₄_of_eq_III hp h hκ
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- Step 6 answers `I₀*`, not `III`. -/
theorem Step6.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p)
    (h : Step6.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.not_sq_dvd_c₄_of_eq_III hp h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- No answer of the `Iₙ*` subprocedure of Step 7 is `III`. -/
theorem Step7.subprocedure_kodairaSymbol_ne_III (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.III := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 answers `Iₙ*`, not `III`. -/
theorem Step7.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.not_sq_dvd_c₄_of_eq_III hp (heq.trans h) hκ
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hκ ?_
    apply Step7.subprocedure_kodairaSymbol_ne_III

/-- Step 8 answers `IV*`, not `III`. -/
theorem Step8.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.not_sq_dvd_c₄_of_eq_III hp hΔ h hκ
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- Step 9 answers `III*`, which is a different symbol from `III`. -/
theorem Step9.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.not_sq_dvd_c₄_of_eq_III hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 10 answers `II*`, not `III`. -/
theorem Step10.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.not_sq_dvd_c₄_of_eq_III hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `III` at Steps 1–11 forces `p² ∤ c₄`, i.e. `v_p(a₄) = 1` on the short
plane.** -/
theorem Step11.not_sq_dvd_c₄_of_eq_III (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₄ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.not_sq_dvd_c₄_of_eq_III hp hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The density of the `III` stratum -/

/-- **The minimal part of the stratum `τ_p⁻¹((III, 2))` is the minimal `III` locus**, for every
prime `p ≥ 5`:

  `τ_p⁻¹((III, 2)) ∖ σ_p(ℤ_p²) = {v_p(a₄) = 1, p² ∣ a₆}`.
-/
theorem stratFibre_diff_range_eq_stratMinimalIII (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.III, 2) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = stratMinimalIII p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    obtain ⟨h4, h6⟩ := pow_dvd_of_mem_stratFibre_additive hp hxF
    rw [show (KodairaSymbol.III, 2).1.additiveC₄Level = 1 from rfl, pow_one] at h4
    rw [show (KodairaSymbol.III, 2).1.additiveC₆Level = 2 from rfl] at h6
    have hs := (mem_stratFibre_iff hxUp).1 hxF
    rw [strat] at hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.III := congrArg Prod.fst hs
    refine mem_stratMinimalIII_iff.2 ⟨⟨h4, ?_⟩, h6⟩
    intro hsq
    have hc₄ : (p : ℤ_[p]) ^ 2 ∣ (ofShortNF x.1 x.2).c₄ := by
      rw [ofShortNF_c₄]
      exact hsq.mul_left _
    rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp with out' | W'
    · exact absurd hc₄ (TateAlgorithm.Step11.not_sq_dvd_c₄_of_eq_III hp hxUp e
        (by rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
            exact hκ))
    · refine hxR (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩)
      · have hd : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
          ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hd
      · have hd : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
          ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hd
  · intro x hx
    obtain ⟨⟨-, h4'⟩, -⟩ := mem_stratMinimalIII_iff.1 hx
    refine ⟨stratMinimalIII_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨h4r, -⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    exact h4' (dvd_trans (pow_dvd_pow _ (by norm_num)) h4r)

/-- **The density of the `III` stratum**, for every prime `p ≥ 5`:

  `δ_p((III, 2)) = 2N p⁻⁴ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)p⁶/(p¹⁰-1)`. -/
theorem deltaP_III_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.III, 2)
      = 2 * ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 4
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_stratMinimalIII hp,
    volume_stratMinimalIII, one_sub_inv_eq hp]
  ring

end WeierstrassCurve
