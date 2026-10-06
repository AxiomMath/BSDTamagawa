/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.CubicRootCounts
public import BSDTamagawa.NumberTheory.HeadDensityOne
public import BSDTamagawa.NumberTheory.HeadDensityTwoExact
public import BSDTamagawa.NumberTheory.HeadDensityByDifference

/-!
# The `I₀*` strata, and `δ_p(1)` for `p ≥ 5`

For a prime `p ≥ 5` and `T = (1 - p⁻¹⁰)⁻¹`, this file computes the density of every stratum
`τ_p⁻¹((I₀*, 1 + k))`. Its minimal part is exactly the deep locus `{p² ∣ a₄, p³ ∣ a₆}` refined by
the separable residue pairs `(Ā, B̄) ∈ 𝔽_p²` whose depressed cubic `X³ + ĀX + B̄` has exactly `k`
roots in `𝔽_p`, so `δ_p((I₀*, 1 + k))` is the number of such pairs times `p⁻⁷ T`. Writing `r₀` for
the number of pairs whose cubic has no root, so that `3r₀ + 1 = p²`, the `(I₀*, 1)` stratum has
density `r₀ p⁻⁷ T = ((p² - 1)/3) p⁻⁷ T`, and this yields the closed form of `δ_p(1)`.

## Main results

* `WeierstrassCurve.step6_cubic_card_roots`: Step 6's cubic of a short model in the deep locus has
  as many roots as the depressed cubic of its residue pair.
* `WeierstrassCurve.TateAlgorithm.Step11.step6_error_of_kodairaSymbol_eq_I0star`: an answer of
  `I₀*` at Steps 1–11 is Step 6's answer.
* `WeierstrassCurve.stratFibre_diff_range_eq_deepResidueLocus`: the minimal part of
  `τ_p⁻¹((I₀*, 1+k))` is the deep locus refined by `ellipticResidues p ∩ rootCountResidues p k`.
* `WeierstrassCurve.deltaP_I0star_eq`: the density of every stratum `(I₀*, 1 + k)`.
* `WeierstrassCurve.deltaP_I0star_one_eq`, `WeierstrassCurve.deltaP_I0star_two_eq`: the
  `(I₀*, 1)` and `(I₀*, 2)` densities.
* `WeierstrassCurve.δ_one_eq_ofReal_gotδ`: `δ_p(1) = ENNReal.ofReal (gotδ p 1)` for `p ≥ 5`.
* `WeierstrassCurve.δ_two_eq_ofReal_gotδ_iff_InStar`: `δ_p(2) = ENNReal.ofReal (gotδ p 2)` if and
  only if `∑_{n ≥ 1} δ_p((Iₙ*, 2)) = ENNReal.ofReal (gotInStarTwo p)`.
* `WeierstrassCurve.hasGOTDensities_of_InStar`: the latter identity implies `HasGOTDensities p`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The root count of a depressed cubic, transported along an isomorphism -/

namespace Cubic

/-- **The root set of a depressed monic cubic transports along an isomorphism of fields**: the
roots of `X³ + (EA)X + EB` in `L` are the images of the roots of `X³ + AX + B` in `K`. -/
theorem roots_toFinset_depressed_congr {K L : Type*} [Field K] [Field L] [DecidableEq K]
    [DecidableEq L] (E : K ≃+* L) (A B : K) :
    (Cubic.toPoly ⟨1, 0, E A, E B⟩ : Polynomial L).roots.toFinset
      = (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K).roots.toFinset.image E := by
  have hK0 : (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K) ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (P := ⟨1, 0, A, B⟩) one_ne_zero
  have hL0 : (Cubic.toPoly ⟨1, 0, E A, E B⟩ : Polynomial L) ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (P := ⟨1, 0, E A, E B⟩) one_ne_zero
  have hevK : ∀ x : K, (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K).eval x = x ^ 3 + A * x + B := by
    intro x
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hevL : ∀ y : L,
      (Cubic.toPoly ⟨1, 0, E A, E B⟩ : Polynomial L).eval y = y ^ 3 + E A * y + E B := by
    intro y
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  ext y
  simp only [Finset.mem_image, Multiset.mem_toFinset, Polynomial.mem_roots', Polynomial.IsRoot,
    hevK, hevL]
  constructor
  · rintro ⟨-, hy⟩
    refine ⟨E.symm y, ⟨hK0, E.injective ?_⟩, E.apply_symm_apply y⟩
    simpa only [map_add, map_mul, map_pow, map_zero, RingEquiv.apply_symm_apply] using hy
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    refine ⟨hL0, ?_⟩
    simpa only [map_add, map_mul, map_pow, map_zero] using congrArg E hx

end Cubic

open scoped Classical in
/-- **Step 6's depressed cubic over the residue field has as many roots as the depressed cubic of
the residue pair has over `𝔽_p`.** -/
theorem card_roots_mod_eq_card_cubicRootSet (A B : ℤ_[p]) :
    (Cubic.toPoly ⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
        Polynomial (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})).roots.toFinset.card
      = (cubicRootSet (PadicInt.toZMod A, PadicInt.toZMod B)).card := by
  classical
  have hc : cubicRootSet (PadicInt.toZMod A, PadicInt.toZMod B)
      = (Cubic.toPoly ⟨1, 0, PadicInt.toZMod A, PadicInt.toZMod B⟩ :
          Polynomial (ZMod p)).roots.toFinset :=
    cubicRootSet_eq_roots_toFinset _
  have h := Cubic.roots_toFinset_depressed_congr (residueEquiv p)
    (CommRing.mod (p : ℤ_[p]) A) (CommRing.mod (p : ℤ_[p]) B)
  rw [residueEquiv_mod, residueEquiv_mod] at h
  rw [hc, h, Finset.card_image_of_injective _ (residueEquiv p).injective]

open scoped Classical in
/-- **`k` roots of the depressed cubic over the residue field is membership in
`rootCountResidues p k`**, for every `k` at once. -/
theorem card_roots_mod_eq_iff (A B : ℤ_[p]) (k : ℕ) :
    (Cubic.toPoly ⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
        Polynomial (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})).roots.toFinset.card = k
      ↔ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ rootCountResidues p k := by
  classical
  rw [card_roots_mod_eq_card_cubicRootSet, mem_rootCountResidues]

/-! ### Step 6's root count, read off the residue pair -/

open scoped Classical in
/-- **Step 6's root count on a short model in the deep locus equals the root count of the depressed
cubic of its residue pair**, for `a₄ = p²A`, `a₆ = p³B` and `p ≥ 5`. -/
theorem step6_cubic_card_roots (hp : 5 ≤ p) {a₄ a₆ A B : ℤ_[p]}
    (h4 : a₄ = (p : ℤ_[p]) ^ 2 * A) (h6 : a₆ = (p : ℤ_[p]) ^ 3 * B)
    {W' : WeierstrassCurve ℤ_[p]}
    (h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok W') :
    (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).toPoly.roots.toFinset.card
      = (Cubic.toPoly ⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
          Polynomial (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})).roots.toFinset.card := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hv6 := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ h5)
  obtain ⟨A₁, hA₁⟩ := hv6.a₁
  obtain ⟨A₂, hA₂⟩ := hv6.a₂
  obtain ⟨A₃, hA₃⟩ := hv6.a₃
  obtain ⟨A₄, hA₄⟩ := hv6.a₄
  obtain ⟨A₆, hA₆⟩ := hv6.a₆
  rw [pow_one] at hA₁ hA₂
  have f₄ : (Step6.translate (p : ℤ_[p]) W').c₄ = -48 * ((p : ℤ_[p]) ^ 2 * A) := by
    rw [Step6.translate_c₄, Step5.run_c₄ h5, ofShortNF_c₄, h4]
  have f₆ : (Step6.translate (p : ℤ_[p]) W').c₆ = -864 * ((p : ℤ_[p]) ^ 3 * B) := by
    rw [Step6.translate_c₆, Step5.run_c₆ h5, ofShortNF_c₆, h6]
  obtain ⟨e, c, d, hcub, hu₄, hu₆⟩ :=
    exists_depressed_residue hp hA₁ hA₂ hA₃ hA₄ hA₆ f₄ f₆
  have hdep : (⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
      Cubic (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}))
      = ⟨1, 0, c - 3 * e ^ 2, 2 * e ^ 3 - c * e + d⟩ := by
    rw [hu₄, hu₆]
  rw [hcub, hdep, Cubic.card_roots_depress]

/-! ### Only Step 6 answers `I₀*` -/

/-- A positively-indexed `Iₙ*` is not `I₀*`. -/
theorem KodairaSymbol.Istar_ne_Istar_zero {m : ℕ} (hm : m ≠ 0) :
    KodairaSymbol.I! m ≠ KodairaSymbol.I! 0 := by
  intro h
  exact hm (KodairaSymbol.I!.inj h)

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- **Every answer of the `Iₙ*` subprocedure of Step 7 is `Iₘ*` with `m ≥ 1`.** -/
theorem Step7.subprocedure_kodairaSymbol_ne_I0star (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.I! 0 := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => exact KodairaSymbol.Istar_ne_Istar_zero (by omega)
  | case3 => exact KodairaSymbol.Istar_ne_Istar_zero (by omega)

/-- An answer `I₀*` of Step 7 is Step 6's answer. -/
theorem Step7.step6_error_of_kodairaSymbol_eq_I0star (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! 0) :
    Step6.run (p : ℤ_[p]) W = Except.error out := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact heq.trans h
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hκ ?_
    apply Step7.subprocedure_kodairaSymbol_ne_I0star

/-- An answer `I₀*` of Step 8 is Step 6's answer. -/
theorem Step8.step6_error_of_kodairaSymbol_eq_I0star (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! 0) :
    Step6.run (p : ℤ_[p]) W = Except.error out := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.step6_error_of_kodairaSymbol_eq_I0star hΔ h hκ
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- An answer `I₀*` of Step 9 is Step 6's answer. -/
theorem Step9.step6_error_of_kodairaSymbol_eq_I0star (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! 0) :
    Step6.run (p : ℤ_[p]) W = Except.error out := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.step6_error_of_kodairaSymbol_eq_I0star hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- An answer `I₀*` of Step 10 is Step 6's answer. -/
theorem Step10.step6_error_of_kodairaSymbol_eq_I0star (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! 0) :
    Step6.run (p : ℤ_[p]) W = Except.error out := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.step6_error_of_kodairaSymbol_eq_I0star hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `I₀*` at Steps 1–11 is Step 6's answer.** -/
theorem Step11.step6_error_of_kodairaSymbol_eq_I0star (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! 0) :
    Step6.run (p : ℤ_[p]) W = Except.error out := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.step6_error_of_kodairaSymbol_eq_I0star hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The minimal part of the strata `τ_p⁻¹((I₀*, 1 + k))` -/

/-- **A rootless residue pair is separable**: `4 c.1³ + 27 c.2² ≠ 0` for every
`c ∈ rootCountResidues p 0`, when `p ≥ 5`. -/
theorem four_mul_pow_add_ne_zero_of_mem_rootCountResidues_zero (hp : 5 ≤ p)
    {c : ZMod p × ZMod p} (hc : c ∈ rootCountResidues p 0) : 4 * c.1 ^ 3 + 27 * c.2 ^ 2 ≠ 0 := by
  have hcard : (cubicRootSet c).card = 0 := mem_rootCountResidues.1 hc
  have h1 : (cubicRootSet c).card ≠ 1 := by rw [hcard]; norm_num
  have h2 : (cubicRootSet c).card ≠ 2 := by rw [hcard]; norm_num
  have hell := mem_ellipticResidues_of_card_ne hp h1 h2
  simp only [ellipticResidues, Finset.mem_filter, Finset.mem_univ, true_and] at hell
  exact hell

/-- Membership in `ellipticResidues p` unfolded: the pair is off the cuspidal cubic. -/
theorem mem_ellipticResidues_iff {c : ZMod p × ZMod p} :
    c ∈ ellipticResidues p ↔ 4 * c.1 ^ 3 + 27 * c.2 ^ 2 ≠ 0 := by
  simp only [ellipticResidues, Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
/-- **The minimal part of the stratum `τ_p⁻¹((I₀*, 1 + k))` is the deep locus over the separable
residue pairs with exactly `k` roots**, for every prime `p ≥ 5` and every `k`:

    `τ_p⁻¹((I₀*, 1+k)) ∖ σ_p(ℤ_p²)
       = deepResidueLocus p (ellipticResidues p ∩ rootCountResidues p k)`.
-/
theorem stratFibre_diff_range_eq_deepResidueLocus (hp : 5 ≤ p) (k : ℕ) :
    stratFibre p (KodairaSymbol.I! 0, 1 + k) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = deepResidueLocus p (ellipticResidues p ∩ rootCountResidues p k) := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have hs := (mem_stratFibre_iff hxUp).1 hxF
    rw [strat] at hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.I! 0 :=
      congrArg Prod.fst hs
    have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = 1 + k := congrArg Prod.snd hs
    have h4 : (p : ℤ_[p]) ^ 2 ∣ x.1 := by
      have hd := (pow_dvd_of_mem_stratFibre_additive hp hxF).1
      simpa only [KodairaSymbol.additiveC₄Level] using hd
    have h6 : (p : ℤ_[p]) ^ 3 ∣ x.2 := by
      have hd := (pow_dvd_of_mem_stratFibre_additive hp hxF).2
      simpa only [KodairaSymbol.additiveC₆Level] using hd
    obtain ⟨A, hx1⟩ := h4
    obtain ⟨B, hx2⟩ := h6
    refine mem_deepResidueLocus_iff.2 ⟨A, B, hx1, hx2, ?_⟩
    by_cases hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2))) 1 1).HasDoubleRoot
    · refine absurd hκ ?_
      rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hxUp with out' | W'
      · intro hκ'
        have hκ'' : out'.kodairaSymbol = KodairaSymbol.I! 0 := by
          rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
          exact hκ'
        have h6e := TateAlgorithm.Step11.step6_error_of_kodairaSymbol_eq_I0star hxUp e hκ''
        rw [step6_run_eq_ok_of_hasDoubleRoot
          (step5_run_eq_ok_of_dvd hp ⟨A, hx1⟩ ⟨B, hx2⟩) hd] at h6e
        simp at h6e
      · refine absurd (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩) hxR
        · have hdv : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
            ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
          rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hdv
        · have hdv : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
            ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
          rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hdv
    · obtain ⟨-, hcv⟩ :=
        run_eq_I0star_of_not_hasDoubleRoot hp hxUp ⟨A, hx1⟩ ⟨B, hx2⟩ hd
      rw [hc] at hcv
      have h5 := step5_run_eq_ok_of_dvd hp (⟨A, hx1⟩ : (p : ℤ_[p]) ^ 2 ∣ x.1)
        (⟨B, hx2⟩ : (p : ℤ_[p]) ^ 3 ∣ x.2)
      obtain ⟨hbd, -⟩ := step6_cubic_bridge hp hx1 hx2 h5
      refine Finset.mem_inter.2 ⟨mem_ellipticResidues_iff.2 fun h0 => hd (hbd.2 ?_), ?_⟩
      · simp only [cuspidalResidues, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h0
      · rw [← card_roots_mod_eq_iff, ← step6_cubic_card_roots hp hx1 hx2 h5]
        omega
  · intro x hx
    obtain ⟨A, B, hx1, hx2, hmem'⟩ := mem_deepResidueLocus_iff.1 hx
    obtain ⟨hell, hmem⟩ := Finset.mem_inter.1 hmem'
    have hsep : 4 * (PadicInt.toZMod A) ^ 3 + 27 * (PadicInt.toZMod B) ^ 2 ≠ 0 :=
      mem_ellipticResidues_iff.1 hell
    have hform : ¬ (p : ℤ_[p]) ∣ 4 * A ^ 3 + 27 * B ^ 2 := by
      rw [PadicInt.dvd_iff_toZMod_eq_zero]
      simpa only [map_add, map_mul, map_pow, map_ofNat] using hsep
    have hformne : (4 * A ^ 3 + 27 * B ^ 2 : ℤ_[p]) ≠ 0 := fun h => hform (h ▸ dvd_zero _)
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
      rw [ofShortNF_Δ, hx1, hx2,
        show 4 * ((p : ℤ_[p]) ^ 2 * A) ^ 3 + 27 * ((p : ℤ_[p]) ^ 3 * B) ^ 2
          = (p : ℤ_[p]) ^ 6 * (4 * A ^ 3 + 27 * B ^ 2) from by ring]
      exact mul_ne_zero (isUnit_sixteen hp).neg.ne_zero
        (mul_ne_zero (pow_ne_zero 6 PadicInt.uniformizer_ne_zero) hformne)
    have hUp : x ∈ nonsingularLocus p := hΔ
    have h4 : (p : ℤ_[p]) ^ 2 ∣ x.1 := ⟨A, hx1⟩
    have h6 : (p : ℤ_[p]) ^ 3 ∣ x.2 := ⟨B, hx2⟩
    have h5 := step5_run_eq_ok_of_dvd hp h4 h6
    obtain ⟨hbd, -⟩ := step6_cubic_bridge hp hx1 hx2 h5
    have hnd : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2))) 1 1).HasDoubleRoot := by
      rw [hbd, cuspidalResidues, Finset.mem_filter]
      exact fun h => hsep h.2
    have hcard : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2))) 1 1).toPoly.roots.toFinset.card = k := by
      rw [step6_cubic_card_roots hp hx1 hx2 h5, card_roots_mod_eq_iff]
      exact hmem
    obtain ⟨hκ, hcv⟩ := run_eq_I0star_of_not_hasDoubleRoot hp hΔ h4 h6 hnd
    refine ⟨(mem_stratFibre_iff hUp).2 ?_, ?_⟩
    · rw [strat]
      exact Prod.ext hκ (by rw [hcv, hcard])
    · intro hr
      obtain ⟨h4', h6'⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
      obtain ⟨z, hz⟩ := h4'
      obtain ⟨w, hw⟩ := h6'
      have hA : (p : ℤ_[p]) ∣ A := ⟨(p : ℤ_[p]) * z,
        mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero) (by rw [← hx1, hz]; ring)⟩
      have hB : (p : ℤ_[p]) ∣ B := ⟨(p : ℤ_[p]) ^ 2 * w,
        mul_left_cancel₀ (pow_ne_zero 3 PadicInt.uniformizer_ne_zero) (by rw [← hx2, hw]; ring)⟩
      rw [PadicInt.dvd_iff_toZMod_eq_zero] at hA hB
      exact hsep (by rw [hA, hB]; ring)

/-! ### The densities of the `I₀*` strata -/

/-- **The densities of the `I₀*` strata**, for every prime `p ≥ 5` and every `k`:

  `δ_p((I₀*, 1+k)) = |{separable pairs with k roots}| p⁻⁷ (1 - p⁻¹⁰)⁻¹`.
-/
theorem deltaP_I0star_eq (hp : 5 ≤ p) (k : ℕ) :
    deltaP p (KodairaSymbol.I! 0, 1 + k)
      = (((ellipticResidues p ∩ rootCountResidues p k).card : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 7
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_deepResidueLocus hp k,
    volume_deepResidueLocus]

/-- Every rootless residue pair is separable. -/
theorem ellipticResidues_inter_rootCountResidues_zero (hp : 5 ≤ p) :
    ellipticResidues p ∩ rootCountResidues p 0 = rootCountResidues p 0 :=
  Finset.inter_eq_right.2 fun _ hc =>
    mem_ellipticResidues_iff.2 (four_mul_pow_add_ne_zero_of_mem_rootCountResidues_zero hp hc)

/-- The separable residue pairs with one root are `oneRootResidues p`. -/
theorem ellipticResidues_inter_rootCountResidues_one :
    ellipticResidues p ∩ rootCountResidues p 1 = oneRootResidues p := rfl

/-- **The density of `(I₀*, 1)`**, for every prime `p ≥ 5`: `δ_p((I₀*, 1)) = r₀ p⁻⁷ T` with
`3r₀ + 1 = p²`, i.e. `((p²-1)/3) p⁻⁷ T`. -/
theorem deltaP_I0star_one_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.I! 0, 1)
      = (((rootCountResidues p 0).card : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 7
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have h := deltaP_I0star_eq hp 0
  rw [ellipticResidues_inter_rootCountResidues_zero hp] at h
  rw [show (1 : ℕ) = 1 + 0 from rfl]
  exact h

/-- **The density of `(I₀*, 2)`**, for every prime `p ≥ 5`:
`δ_p((I₀*, 2)) = |oneRootResidues p| p⁻⁷ T` with `2|oneRootResidues p| + p = p²`, i.e.
`(p(p-1)/2) p⁻⁷ T`. -/
theorem deltaP_I0star_two_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.I! 0, 2)
      = (((oneRootResidues p).card : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 7
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have h := deltaP_I0star_eq hp 1
  rw [ellipticResidues_inter_rootCountResidues_one] at h
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  exact h

/-! ### Transfer to `ℝ` -/

omit [Fact p.Prime] in
/-- `1 - p⁻¹⁰` in `ℝ≥0∞` is the `ENNReal.ofReal` of the same expression on `ℝ`. -/
private theorem ofReal_one_sub_inv_pow_ten (hp : 5 ≤ p) :
    (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10 = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinvE,
    ← ENNReal.ofReal_pow (by positivity)]

omit [Fact p.Prime] in
/-- **`n p⁻⁷ (1 - p⁻¹⁰)⁻¹` in `ℝ≥0∞` is the `ENNReal.ofReal` of the same expression on `ℝ`**, for
`p ≥ 5`. -/
theorem deltaP_row_eq_ofReal (hp : 5 ≤ p) (n : ℕ) :
    ((n : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 7 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      = ENNReal.ofReal ((n : ℝ) * ((p : ℝ)⁻¹) ^ 7 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos10 : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 :=
    sub_pos.2 (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by linarith)) (by norm_num))
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  rw [ofReal_one_sub_inv_pow_ten hp, ← ENNReal.ofReal_inv_of_pos hpos10, hinvE,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-! ### `δ_p(1)`, closed -/

/-- **The density of `(I₀*, 1)` in closed form**:
`δ_p((I₀*, 1)) = ENNReal.ofReal (gotIZeroStarOne p)`, i.e. `((p²-1)/3) p⁻⁷ T`, at every prime
`p ≥ 5`. -/
theorem deltaP_I0star_one_eq_ofReal (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.I! 0, 1) = ENNReal.ofReal (gotIZeroStarOne p) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hcard : (((rootCountResidues p 0).card : ℕ) : ℝ) = ((p : ℝ) ^ 2 - 1) / 3 := by
    have hcast : 3 * (((rootCountResidues p 0).card : ℕ) : ℝ) + 1 = (p : ℝ) ^ 2 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_rootCountResidues_zero (p := p) hp)
    linarith
  rw [deltaP_I0star_one_eq hp, deltaP_row_eq_ofReal hp]
  congr 1
  rw [gotIZeroStarOne, hcard]
  congr 1
  rw [inv_pow]
  field_simp

/-- **The closed form of `δ_p(1)` at `p ≥ 5`**:

  `δ_p(1) = ENNReal.ofReal (gotδ p 1)`.
-/
theorem δ_one_eq_ofReal_gotδ (hp : 5 ≤ p) : δ p 1 = ENNReal.ofReal (gotδ p 1) :=
  δ_one_eq_ofReal_gotδ_of_IZeroStar_row hp (deltaP_I0star_one_eq_ofReal hp)

/-! ### `δ_p(2)` reduced to the non-split `Iₙ*` family, `n ≥ 1` -/

/-- **The density of `(I₀*, 2)` in closed form**:
`δ_p((I₀*, 2)) = ENNReal.ofReal (gotIZeroStarTwo p)`, i.e. `(p(p-1)/2) p⁻⁷ T`, at every prime
`p ≥ 5`. -/
theorem deltaP_I0star_two_eq_ofReal (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.I! 0, 2) = ENNReal.ofReal (gotIZeroStarTwo p) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hcard : (((oneRootResidues p).card : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    have hcast : 2 * (((oneRootResidues p).card : ℕ) : ℝ) + (p : ℝ) = (p : ℝ) ^ 2 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_oneRootResidues (p := p) hp)
    linear_combination hcast / 2
  rw [deltaP_I0star_two_eq hp, deltaP_row_eq_ofReal hp]
  congr 1
  rw [gotIZeroStarTwo, hcard]
  congr 1
  rw [inv_pow]
  field_simp

/-- **The closed form of `δ_p(2)` is equivalent to one for the `Iₙ*` strata with `n ≥ 1`**, for
every prime `p ≥ 5`:

  `δ_p(2) = ENNReal.ofReal (gotδ p 2)`
    ↔  `∑_{n ≥ 1} δ_p((Iₙ*, 2)) = ENNReal.ofReal (((p-1)/2) p⁻⁷ T)`.
-/
theorem δ_two_eq_ofReal_gotδ_iff_InStar (hp : 5 ≤ p) :
    δ p 2 = ENNReal.ofReal (gotδ p 2) ↔
      ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2)
        = ENNReal.ofReal (gotInStarTwo p) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hpos10 : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 :=
    sub_pos.2 (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by linarith)) (by norm_num))
  have hTr : (0 : ℝ) < (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ := inv_pos.2 hpos10
  have hZ : (0 : ℝ) ≤ gotIZeroStarTwo p := by
    rw [gotIZeroStarTwo]
    exact mul_nonneg (div_nonneg (by nlinarith) (by positivity)) hTr.le
  have hN : (0 : ℝ) ≤ gotInStarTwo p := by
    rw [gotInStarTwo]
    exact mul_nonneg (div_nonneg hp1 (by positivity)) hTr.le
  rw [δ_two_eq_ofReal_gotδ_iff hp, tsum_deltaP_Istar_two_eq_add,
    deltaP_I0star_two_eq_ofReal hp, ← gotIZeroStarTwo_add_gotInStarTwo_eq hp,
    ENNReal.ofReal_add hZ hN, ENNReal.add_right_inj ENNReal.ofReal_ne_top]

/-- **The closed form of `δ_p(2)` at `p ≥ 5`**, given
`∑_{n ≥ 1} δ_p((Iₙ*, 2)) = ENNReal.ofReal (gotInStarTwo p)`. -/
theorem δ_two_eq_ofReal_gotδ_of_InStar (hp : 5 ≤ p)
    (hIn : ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2)
      = ENNReal.ofReal (gotInStarTwo p)) :
    δ p 2 = ENNReal.ofReal (gotδ p 2) :=
  (δ_two_eq_ofReal_gotδ_iff_InStar hp).2 hIn

/-- **The closed form of `δ_p(4)` at `p ≥ 5`**, given
`∑_{n ≥ 1} δ_p((Iₙ*, 2)) = ENNReal.ofReal (gotInStarTwo p)`. -/
theorem δ_four_eq_ofReal_gotδ_of_InStar (hp : 5 ≤ p)
    (hIn : ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2)
      = ENNReal.ofReal (gotInStarTwo p)) :
    δ p 4 = ENNReal.ofReal (gotδ p 4) :=
  δ_four_eq_ofReal_gotδ_of_one_two_three (δ_one_eq_ofReal_gotδ hp)
    (δ_two_eq_ofReal_gotδ_of_InStar hp hIn) (δ_three_eq_ofReal_gotδ hp)

/-- **All four closed forms of the head densities at `p ≥ 5`**, given
`∑_{n ≥ 1} δ_p((Iₙ*, 2)) = ENNReal.ofReal (gotInStarTwo p)`. -/
theorem hasGOTDensities_of_InStar (hp : 5 ≤ p)
    (hIn : ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2)
      = ENNReal.ofReal (gotInStarTwo p)) :
    HasGOTDensities p :=
  hasGOTDensities_of_three_heads (δ_two_eq_ofReal_gotδ_of_InStar hp hIn)
    (δ_three_eq_ofReal_gotδ hp) (δ_four_eq_ofReal_gotδ_of_InStar hp hIn)

end WeierstrassCurve
