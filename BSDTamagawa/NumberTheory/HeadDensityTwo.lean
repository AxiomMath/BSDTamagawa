/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityIVStar

/-!
# The `III*` stratum and the fibre `{c = 2}` for `p ≥ 5`

For a prime `p ≥ 5`, write `N = |goodRes p|`, so that `2N = p - 1`, and `T = (1 - p⁻¹⁰)⁻¹`. Running
Step 9 of Tate's algorithm forwards, this file shows that the minimal part of the stratum
`τ_p⁻¹((III*, 2))` is the locus `{v_p(a₄) = 3, p⁵ ∣ a₆}`, so that
`δ_p((III*, 2)) = 2N p⁻⁹ T = (p-1)p/(p¹⁰-1)`. It also shows that the Tamagawa number `2` is carried
exactly by `Iₙ` with `n` even, `III`, `Iₙ*` and `III*`, so that the fibre `{c = 2}` is

    `⋃ₙ τ_p⁻¹((I_{2n}, 2)) ∪ τ_p⁻¹((III, 2)) ∪ ⋃ₙ τ_p⁻¹((Iₙ*, 2)) ∪ τ_p⁻¹((III*, 2))`.

## Main definitions

* `WeierstrassCurve.iiiStarLocus`: the locus `{v_p(a₄) = 3, p⁵ ∣ a₆}`.
* `WeierstrassCurve.IsTamagawaTwoSymbol`: the Kodaira symbol is `Iₙ` with `n` even, `III`, `Iₙ*` or
  `III*`.

## Main results

* `WeierstrassCurve.pow_four_dvd_c₄_iff`: on the curve Step 9 tests, `p⁴ ∣ a₄` exactly when
  `p⁴ ∣ c₄`.
* `WeierstrassCurve.run_eq_IIIstar_of_dvd`: a short model with `v_p(a₄) = 3` and `p⁵ ∣ a₆` has
  reduction datum `(III*, 2)`.
* `WeierstrassCurve.stratFibre_diff_range_eq_iiiStarLocus`: the minimal part of `τ_p⁻¹((III*, 2))`
  is `iiiStarLocus p`.
* `WeierstrassCurve.deltaP_IIIstar_two_eq`: `δ_p((III*, 2)) = 2N p⁻⁹ T`.
* `WeierstrassCurve.TateAlgorithm.run_kodairaSymbol_of_tamagawaNumber_eq_two`: only `Iₙ` with `n`
  even, `III`, `Iₙ*` and `III*` carry the Tamagawa number `2`.
* `WeierstrassCurve.iUnion_stratFibre_two_eq`: the fibre `{c = 2}` as a union of strata.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Step 9's branch condition read off `c₄` -/

/-- **Step 9's test `p⁴ ∣ a₄` is `p⁴ ∣ c₄`.** On a curve with `p ∣ a₁`, `p² ∣ a₂`, `p³ ∣ a₃` and
`p³ ∣ a₄`, one has

  `c₄ = p³(-48(a₄/p³) + p·((a₁/p)² + 4(a₂/p²))² - 24p(a₁/p)(a₃/p³))`,

so for `p ≥ 5`, `p⁴ ∣ c₄` exactly when `p⁴ ∣ a₄`. -/
theorem pow_four_dvd_c₄_iff (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]} {A₁ A₂ A₃ A₄ : ℤ_[p]}
    (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) ^ 2 * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 3 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 3 * A₄) :
    (p : ℤ_[p]) ^ 4 ∣ W.c₄ ↔ (p : ℤ_[p]) ^ 4 ∣ W.a₄ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hu : IsUnit (-48 : ℤ_[p]) := isUnit_neg_fortyEight hp
  have hc₄ : W.c₄ = (p : ℤ_[p]) ^ 3 * (-48 * A₄
      + (p : ℤ_[p]) * ((A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * A₁ * A₃)) := by
    rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h1, h2, h3, h4]
    ring
  rw [hc₄, pow_succ_dvd_pow_mul hϖ 3, h4, pow_succ_dvd_pow_mul hϖ 3]
  refine ⟨fun h => ?_, fun h => dvd_add (by rwa [hu.dvd_mul_left]) (dvd_mul_right _ _)⟩
  have h2' : (p : ℤ_[p]) ∣ -48 * A₄ := by
    have hs := dvd_sub h (dvd_mul_right (p : ℤ_[p]) ((A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * A₁ * A₃))
    rwa [show -48 * A₄ + (p : ℤ_[p]) * ((A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * A₁ * A₃)
      - (p : ℤ_[p]) * ((A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * A₁ * A₃) = -48 * A₄ from by ring] at hs
  rwa [hu.dvd_mul_left] at h2'

/-! ### Steps 8 and 9 run forwards -/

/-- Step 8 succeeds, returning its translate, when its quadratic has a double root. -/
theorem step8_run_eq_ok_of_hasDoubleRoot {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W')
    (hq : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot) :
    Step8.run PadicInt.uniformizer_ne_zero hΔ
      = Except.ok (Step8.translate (p : ℤ_[p]) W') := by
  rw [Step8.run.eq_def, h7]
  simp only [except_ok_bind]
  exact ite_eq_left hq

open scoped Classical in
/-- Step 9 answers `(III*, 2)` when `p⁴ ∤ a₄` of its translate. -/
theorem step9_run_eq_error_of_not_dvd {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h8 : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W')
    (ha₄ : ¬ (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) W').a₄) :
    Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error
      ⟨Step9.translate (p : ℤ_[p]) W', KodairaSymbol.III!, 2⟩ := by
  rw [Step9.run.eq_def, h8]
  simp only [except_ok_bind]
  exact ite_eq_right ha₄

/-- An answer of Step 9 is the answer of Step 11. -/
theorem step11_error_of_step9 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) {out : Output ℤ_[p]}
    (h9 : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  have h10 : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step10.run.eq_def, h9]; rfl
  rw [Step11.run.eq_def, h10]; rfl

/-- **The forward run at `III*`, from the invariants.** For every prime `p ≥ 5`, a curve over `ℤ_p`
on which Steps 1–5 succeed and whose invariants satisfy `p³ ∣ c₄`, `p⁴ ∤ c₄` and `p⁵ ∣ c₆` has
reduction datum `(III*, 2)`. -/
theorem run_eq_IIIstar_of_invariants (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok W') (hc₄ : (p : ℤ_[p]) ^ 3 ∣ W.c₄)
    (hc₄' : ¬ (p : ℤ_[p]) ^ 4 ∣ W.c₄) (hc₆ : (p : ℤ_[p]) ^ 5 ∣ W.c₆) :
    (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.III! ∧
      (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hv5 := Step5.run_hasValuation hϖ h5
  have hv6 := Step6.hasValuation_translate hϖ hv5
  have e₄ : (Step6.translate (p : ℤ_[p]) W').c₄ = W.c₄ := by
    rw [Step6.translate_c₄, Step5.run_c₄ h5]
  have e₆ : (Step6.translate (p : ℤ_[p]) W').c₆ = W.c₆ := by
    rw [Step6.translate_c₆, Step5.run_c₆ h5]
  have hc₆4 : (p : ℤ_[p]) ^ 4 ∣ W.c₆ :=
    dvd_trans (pow_dvd_pow _ (by norm_num : 4 ≤ 5)) hc₆
  obtain ⟨A₁, hA₁⟩ := hv6.a₁
  obtain ⟨A₂, hA₂⟩ := hv6.a₂
  obtain ⟨A₃, hA₃⟩ := hv6.a₃
  obtain ⟨A₄, hA₄⟩ := hv6.a₄
  obtain ⟨A₆, hA₆⟩ := hv6.a₆
  rw [pow_one] at hA₁ hA₂
  have ht : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasTripleRoot :=
    (hasTripleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆).2 (by rw [e₄]; exact hc₄)
  have hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot :=
    (hasDoubleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆ ht).2 (by rw [e₆]; exact hc₆4)
  have hs6 := step6_run_eq_ok_of_hasDoubleRoot h5 hd
  have hs7 := step7_run_eq_ok_of_hasTripleRoot hΔ hs6 ht
  have hv8 := Step8.hasValuation_translate hϖ hv6 hd ht
  obtain ⟨B₁, hB₁⟩ := hv8.a₁
  obtain ⟨B₂, hB₂⟩ := hv8.a₂
  obtain ⟨B₃, hB₃⟩ := hv8.a₃
  obtain ⟨B₄, hB₄⟩ := hv8.a₄
  obtain ⟨B₆, hB₆⟩ := hv8.a₆
  rw [pow_one] at hB₁
  have f₄ : (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')).c₄ = W.c₄ := by
    rw [Step8.translate_c₄, e₄]
  have f₆ : (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')).c₆ = W.c₆ := by
    rw [Step8.translate_c₆, e₆]
  have hq : (quadratic (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')) 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff hp hB₁ hB₂ hB₃ hB₄ hB₆, f₆]
    exact hc₆
  have hs8 := step8_run_eq_ok_of_hasDoubleRoot hΔ hs7 hq
  have hv9 := Step9.hasValuation_translate hϖ hv8 hq
  obtain ⟨C₁, hC₁⟩ := hv9.a₁
  obtain ⟨C₂, hC₂⟩ := hv9.a₂
  obtain ⟨C₃, hC₃⟩ := hv9.a₃
  obtain ⟨C₄, hC₄⟩ := hv9.a₄
  rw [pow_one] at hC₁
  have g₄ : (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W'))).c₄ = W.c₄ := by
    rw [Step9.translate, Step7.translateY_c₄, f₄]
  have ha₄ : ¬ (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W'))).a₄ := by
    rw [← pow_four_dvd_c₄_iff hp hC₁ hC₂ hC₃ hC₄, g₄]
    exact hc₄'
  have hs9 := step9_run_eq_error_of_not_dvd hΔ hs8 ha₄
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step9 hΔ hs9)]
  exact ⟨rfl, rfl⟩

/-- A short model with `v_p(a₄) = 3` and `p⁵ ∣ a₆` satisfies `p¹⁰ ∤ Δ`. -/
theorem not_pow_ten_dvd_ofShortNF_Δ_of_IIIstar (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (h4 : (p : ℤ_[p]) ^ 3 ∣ a₄) (h4' : ¬ (p : ℤ_[p]) ^ 4 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 5 ∣ a₆) :
    ¬ (p : ℤ_[p]) ^ 10 ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨b, rfl⟩ := h6
  intro hd
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left] at hd
  have h1 : (p : ℤ_[p]) ^ 10 ∣ 27 * ((p : ℤ_[p]) ^ 5 * b) ^ 2 := ⟨27 * b ^ 2, by ring⟩
  have h2 : (p : ℤ_[p]) ^ 10 ∣ (p : ℤ_[p]) ^ 9 * (4 * c ^ 3) := by
    have hs := dvd_sub hd h1
    rwa [show 4 * ((p : ℤ_[p]) ^ 3 * c) ^ 3 + 27 * ((p : ℤ_[p]) ^ 5 * b) ^ 2
      - 27 * ((p : ℤ_[p]) ^ 5 * b) ^ 2 = (p : ℤ_[p]) ^ 9 * (4 * c ^ 3) from by ring] at hs
  obtain ⟨z, hz⟩ := h2
  have h3 : (p : ℤ_[p]) ∣ 4 * c ^ 3 :=
    ⟨z, mul_left_cancel₀ (pow_ne_zero 9 PadicInt.uniformizer_ne_zero) (by rw [hz]; ring)⟩
  rw [(isUnit_four hp).dvd_mul_left] at h3
  exact h4' (by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ]
                exact mul_dvd_mul_left _ (PadicInt.prime_p.dvd_of_dvd_pow h3))

/-- **The forward run at `III*` on the short plane.** For every prime `p ≥ 5`, a short model over
`ℤ_p` with `v_p(a₄) = 3` and `p⁵ ∣ a₆` has reduction datum `(III*, 2)`. -/
theorem run_eq_IIIstar_of_dvd (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]} (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0)
    (h4 : (p : ℤ_[p]) ^ 3 ∣ a₄) (h4' : ¬ (p : ℤ_[p]) ^ 4 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 5 ∣ a₆) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.III! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hs5 := step5_run_eq_ok_of_dvd hp (dvd_trans (pow_dvd_pow _ (by norm_num : 2 ≤ 3)) h4)
    (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 5)) h6)
  refine run_eq_IIIstar_of_invariants hp hΔ hs5 ?_ ?_ ?_
  · rw [ofShortNF_c₄]; exact h4.mul_left _
  · rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]; exact h4'
  · rw [ofShortNF_c₆]; exact h6.mul_left _

/-! ### Only Step 9 answers `III*`

An answer of `III*` at Steps 1–11 forces `p³ ∣ c₄`, `p⁴ ∤ c₄` and `p⁵ ∣ c₆`, i.e. `v_p(a₄) = 3` and
`v_p(a₆) ≥ 5` on the short plane. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Steps 1–2 answer `Iₙ`, not `III*`. -/
theorem Step2.kodairaSymbol_ne_IIIstar (h : Step2.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  obtain ⟨n, hn⟩ := Step2.exists_kodairaSymbol_eq_I h
  rw [hn]; simp

/-- Step 3 answers `II`, not `III*`. -/
theorem Step3.kodairaSymbol_ne_IIIstar (h : Step3.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_ne_IIIstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 4 answers `III`, not `III*`. -/
theorem Step4.kodairaSymbol_ne_IIIstar (h : Step4.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_ne_IIIstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 5 answers `IV`, not `III*`. -/
theorem Step5.kodairaSymbol_ne_IIIstar (h : Step5.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_ne_IIIstar h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 6 answers `I₀*`, not `III*`. -/
theorem Step6.kodairaSymbol_ne_IIIstar (h : Step6.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_ne_IIIstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- No answer of the `Iₙ*` subprocedure of Step 7 is `III*`. -/
theorem Step7.subprocedure_kodairaSymbol_ne_IIIstar (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.III! := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 answers `Iₙ*`, not `III*`. -/
theorem Step7.kodairaSymbol_ne_IIIstar (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_ne_IIIstar (heq.trans h)
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    apply Step7.subprocedure_kodairaSymbol_ne_IIIstar

/-- Step 8 answers `IV*`, not `III*`. -/
theorem Step8.kodairaSymbol_ne_IIIstar (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.III! := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_ne_IIIstar hΔ h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- **Step 9's answer `III*` forces `p³ ∣ c₄`, `p⁴ ∤ c₄` and `p⁵ ∣ c₆`.** -/
theorem Step9.pow_dvd_c₄_c₆_of_eq_IIIstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ ¬ (p : ℤ_[p]) ^ 4 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact absurd hκ (Step8.kodairaSymbol_ne_IIIstar hΔ h)
  · have hv9 := Step9.hasValuation_translate hϖ (Step8.run_hasValuation hϖ hΔ h')
      (Step8.run_hasDoubleRoot hϖ hΔ h')
    have e₄ : (Step9.translate (p : ℤ_[p]) W').c₄ = W.c₄ := by
      rw [Step9.translate, Step7.translateY_c₄, Step8.run_c₄ hϖ hΔ h']
    have e₆ : (Step9.translate (p : ℤ_[p]) W').c₆ = W.c₆ := by
      rw [Step9.translate, Step7.translateY_c₆, Step8.run_c₆ hϖ hΔ h']
    obtain ⟨C₁, hC₁⟩ := hv9.a₁
    obtain ⟨C₂, hC₂⟩ := hv9.a₂
    obtain ⟨C₃, hC₃⟩ := hv9.a₃
    obtain ⟨C₄, hC₄⟩ := hv9.a₄
    dsimp only at hC₁ hC₂ hC₃ hC₄
    rw [pow_one] at hC₁
    have hcon : ¬ (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) W').a₄ := by
      intro ha₄
      rw [ite_eq_left ha₄] at h
      simp at h
    refine ⟨e₄ ▸ hv9.c₄, ?_, e₆ ▸ hv9.c₆⟩
    rw [← e₄, pow_four_dvd_c₄_iff hp hC₁ hC₂ hC₃ hC₄]
    exact hcon

/-- An answer of `III*` at Steps 1–10 forces `p³ ∣ c₄`, `p⁴ ∤ c₄` and `p⁵ ∣ c₆`. -/
theorem Step10.pow_dvd_c₄_c₆_of_eq_IIIstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ ¬ (p : ℤ_[p]) ^ 4 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.pow_dvd_c₄_c₆_of_eq_IIIstar hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `III*` at Steps 1–11 forces `p³ ∣ c₄`, `p⁴ ∤ c₄` and `p⁵ ∣ c₆`**, i.e.
`v_p(a₄) = 3` and `v_p(a₆) ≥ 5` on the short plane. -/
theorem Step11.pow_dvd_c₄_c₆_of_eq_IIIstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.III!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ ¬ (p : ℤ_[p]) ^ 4 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.pow_dvd_c₄_c₆_of_eq_IIIstar hp hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The `III*` locus -/

variable (p) in
/-- The **`III*` locus**: `v_p(a₄) = 3` and `p⁵ ∣ a₆`. -/
noncomputable def iiiStarLocus : Set (ℤ_[p] × ℤ_[p]) :=
  {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = ((3 : ℕ) : ℕ∞)} ×ˢ
    ((Ideal.span {(p : ℤ_[p]) ^ 5} : Ideal ℤ_[p]) : Set ℤ_[p])

/-- A point lies in the `III*` locus iff `p³ ∣ a₄`, `p⁴ ∤ a₄` and `p⁵ ∣ a₆`. -/
theorem mem_iiiStarLocus_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ iiiStarLocus p ↔
      ((p : ℤ_[p]) ^ 3 ∣ x.1 ∧ ¬ (p : ℤ_[p]) ^ 4 ∣ x.1) ∧ (p : ℤ_[p]) ^ 5 ∣ x.2 := by
  rw [iiiStarLocus, Set.mem_prod]
  simp only [Set.mem_ofPred_eq, emultiplicity_eq_coe (n := 3), SetLike.mem_coe,
    PadicInt.mem_span_pPow_iff_le_emultiplicity, ← pow_dvd_iff_le_emultiplicity]

/-- **The mass of the `III*` locus is `(1 - p⁻¹)p⁻⁸`.** -/
theorem volume_iiiStarLocus :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (iiiStarLocus p)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 8 := by
  rw [iiiStarLocus, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.volume_setOf_emultiplicity_eq, PadicInt.measure_span_pPow' 5]
  ring

/-- **The `III*` locus lies in the stratum `τ_p⁻¹((III*, 2))`.** -/
theorem iiiStarLocus_subset_stratFibre (hp : 5 ≤ p) :
    iiiStarLocus p ⊆ stratFibre p (KodairaSymbol.III!, 2) := by
  intro x hx
  obtain ⟨⟨h4, h4'⟩, h6⟩ := mem_iiiStarLocus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_ten_dvd_ofShortNF_Δ_of_IIIstar hp h4 h4' h6 (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, hc⟩ := run_eq_IIIstar_of_dvd hp hΔ h4 h4' h6
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-! ### The minimal part of the `III*` stratum -/

/-- **The minimal part of an `III*` stratum lies in the `III*` locus.** For every prime `p ≥ 5`, a
point of `τ_p⁻¹((III*, c))` which is not a `σ_p`-dilate has `v_p(a₄) = 3` and `p⁵ ∣ a₆`, and
`c = 2`. -/
theorem exists_eq_of_mem_stratFibre_IIIstar (hp : 5 ≤ p) {c : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hxF : x ∈ stratFibre p (KodairaSymbol.III!, c))
    (hxR : x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :
    ((p : ℤ_[p]) ^ 3 ∣ x.1 ∧ ¬ (p : ℤ_[p]) ^ 4 ∣ x.1) ∧ (p : ℤ_[p]) ^ 5 ∣ x.2 ∧ c = 2 := by
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  have hs := (mem_stratFibre_iff hxUp).1 hxF
  rw [strat] at hs
  have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.III! := congrArg Prod.fst hs
  have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = c := congrArg Prod.snd hs
  rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp with out' | W'
  · obtain ⟨h4, h4', h6⟩ := TateAlgorithm.Step11.pow_dvd_c₄_c₆_of_eq_IIIstar hp hxUp e
      (by rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
          exact hκ)
    rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4
    rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4'
    rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6
    obtain ⟨-, hcv⟩ := run_eq_IIIstar_of_dvd hp hxUp h4 h4' h6
    exact ⟨⟨h4, h4'⟩, h6, by rw [← hc, hcv]⟩
  · refine absurd (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩) hxR
    · have hd : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
        ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hd
    · have hd : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
        ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hd

/-- **The minimal part of the stratum `τ_p⁻¹((III*, 2))` is the `III*` locus**, for every prime
`p ≥ 5`:

  `τ_p⁻¹((III*, 2)) ∖ σ_p(ℤ_p²) = {v_p(a₄) = 3, p⁵ ∣ a₆}`.
-/
theorem stratFibre_diff_range_eq_iiiStarLocus (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.III!, 2) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = iiiStarLocus p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    obtain ⟨h4, h6, -⟩ := exists_eq_of_mem_stratFibre_IIIstar hp hxF hxR
    exact mem_iiiStarLocus_iff.2 ⟨h4, h6⟩
  · intro x hx
    obtain ⟨⟨-, h4'⟩, -⟩ := mem_iiiStarLocus_iff.1 hx
    refine ⟨iiiStarLocus_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨h4r, -⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    exact h4' h4r

/-- **The density of the `III*` stratum**, for every prime `p ≥ 5`:

  `δ_p((III*, 2)) = 2N p⁻⁹ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)p/(p¹⁰-1)`. -/
theorem deltaP_IIIstar_two_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.III!, 2)
      = 2 * ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 9
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_iiiStarLocus hp,
    volume_iiiStarLocus, one_sub_inv_eq hp]
  ring

/-! ### Which Kodaira symbols can carry the Tamagawa number `2`

The Tamagawa number `2` is reported only by Step 2 (`Iₙ` with `n` even), Step 4 (`III`), Step 6
(`I₀*` with one rational root), Step 7's subprocedure (`Iₙ*`) and Step 9 (`III*`). -/

/-- The Kodaira symbol is `Iₙ` with `n` even, `III`, `Iₙ*` for some `n`, or `III*`. -/
def IsTamagawaTwoSymbol (κ : KodairaSymbol) : Prop :=
  (∃ n, Even n ∧ κ = KodairaSymbol.I n) ∨ κ = KodairaSymbol.III
    ∨ (∃ n, κ = KodairaSymbol.I! n) ∨ κ = KodairaSymbol.III!

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Step 1 answers `(I₀, 1)`. -/
theorem Step1.kodairaSymbol_of_tamagawaNumber_eq_two
    (h : Step1.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 2) :
    IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  simp at hc

/-- **Step 2 answers `Iₙ`, and the Tamagawa number `2` forces `n` to be even.** -/
theorem Step2.kodairaSymbol_of_tamagawaNumber_eq_two
    (h : Step2.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 2) :
    IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step1.kodairaSymbol_of_tamagawaNumber_eq_two h hc
  · have hb : ¬ (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W').b₂ := by
      intro hb'
      rw [ite_eq_left hb'] at h
      simp at h
    rw [ite_eq_right hb] at h
    obtain rfl := Except.error.inj h
    dsimp only at hc ⊢
    split_ifs at hc with hsp hodd
    · refine Or.inl ⟨_, ?_, rfl⟩
      rw [hc]
      decide
    · simp at hc
    · exact Or.inl ⟨_, Nat.not_odd_iff_even.1 hodd, rfl⟩

/-- Step 3 answers `(II, 1)`. -/
theorem Step3.kodairaSymbol_of_tamagawaNumber_eq_two
    (h : Step3.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 2) :
    IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_of_tamagawaNumber_eq_two h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- Step 4 answers `(III, 2)`. -/
theorem Step4.kodairaSymbol_of_tamagawaNumber_eq_two
    (h : Step4.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 2) :
    IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_of_tamagawaNumber_eq_two h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (Or.inl rfl)

/-- Step 5 answers `IV` with Tamagawa number `3` or `1`, never `2`. -/
theorem Step5.kodairaSymbol_of_tamagawaNumber_eq_two
    (h : Step5.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 2) :
    IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_of_tamagawaNumber_eq_two h hc
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hc

open scoped Classical in
/-- Step 6 answers `I₀*`. -/
theorem Step6.kodairaSymbol_of_tamagawaNumber_eq_two
    (h : Step6.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 2) :
    IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_of_tamagawaNumber_eq_two h hc
  · have hcon : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot := by
      intro hdr
      rw [ite_eq_left hdr] at h
      simp at h
    rw [ite_eq_right hcon] at h
    obtain rfl := Except.error.inj h
    exact Or.inr (Or.inr (Or.inl ⟨0, rfl⟩))

/-- Every answer of the `Iₙ*` subprocedure of Step 7 is an `I!ₘ`. -/
theorem Step7.subprocedure_exists_kodairaSymbol_eq_Istar (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    ∃ m, (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = KodairaSymbol.I! m := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => exact ⟨_, rfl⟩
  | case3 => exact ⟨_, rfl⟩

/-- Step 7 answers inside its `Iₙ*` subprocedure, whose symbols are all `I!ₘ`. -/
theorem Step7.kodairaSymbol_of_tamagawaNumber_eq_two (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 2) : IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_of_tamagawaNumber_eq_two (heq.trans h) hc
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine Or.inr (Or.inr (Or.inl ?_))
    apply Step7.subprocedure_exists_kodairaSymbol_eq_Istar

/-- Step 8 answers `IV*` with Tamagawa number `3` or `1`, never `2`. -/
theorem Step8.kodairaSymbol_of_tamagawaNumber_eq_two (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 2) : IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_of_tamagawaNumber_eq_two hΔ h hc
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hc

/-- Step 9 answers `(III*, 2)`. -/
theorem Step9.kodairaSymbol_of_tamagawaNumber_eq_two (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 2) : IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.kodairaSymbol_of_tamagawaNumber_eq_two hΔ h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (Or.inr (Or.inr rfl))

/-- Step 10 answers `(II*, 1)`. -/
theorem Step10.kodairaSymbol_of_tamagawaNumber_eq_two (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 2) : IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.kodairaSymbol_of_tamagawaNumber_eq_two hΔ h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- **An answer of Tamagawa number `2` at Steps 1–11 has Kodaira symbol `Iₙ` with `n` even, `III`,
`Iₙ*` or `III*`.** -/
theorem Step11.kodairaSymbol_of_tamagawaNumber_eq_two (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 2) : IsTamagawaTwoSymbol out.kodairaSymbol := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.kodairaSymbol_of_tamagawaNumber_eq_two hΔ h hc
  · simp at h

/-- **Only `Iₙ` with `n` even, `III`, `Iₙ*` and `III*` carry the Tamagawa number `2`**, for every
Weierstrass curve over `ℤ_p` with `Δ ≠ 0`. -/
theorem run_kodairaSymbol_of_tamagawaNumber_eq_two {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) :
    (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 →
      IsTamagawaTwoSymbol (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol := by
  induction W, hΔ using run.induct PadicInt.uniformizer_ne_zero with
  | case1 W hΔ out h =>
    intro hc
    rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ h] at hc ⊢
    exact Step11.kodairaSymbol_of_tamagawaNumber_eq_two hΔ h hc
  | case2 W hΔ W' h ih =>
    intro hc
    have hΔ' : W'.Δ ≠ 0 := fun h0 =>
      hΔ (by rw [← Step11.run_Δ PadicInt.uniformizer_ne_zero hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ h hΔ'] at hc ⊢
    exact ih hc

end TateAlgorithm

/-! ### The fibre `{c = 2}`, exactly -/

/-- **The fibre `{c = 2}` is exactly the union of the strata `(I_{2n}, 2)`, `(III, 2)`, `(Iₙ*, 2)`
and `(III*, 2)`**, at every prime. -/
theorem iUnion_stratFibre_two_eq :
    (⋃ κ : KodairaSymbol, stratFibre p (κ, 2))
      = (⋃ n : ℕ, stratFibre p (KodairaSymbol.I (2 * n), 2))
          ∪ stratFibre p (KodairaSymbol.III, 2)
          ∪ (⋃ n : ℕ, stratFibre p (KodairaSymbol.I! n, 2))
          ∪ stratFibre p (KodairaSymbol.III!, 2) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨κ, hxκ⟩ := Set.mem_iUnion.1 hx
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxκ
    have hs := (mem_stratFibre_iff hUp).1 hxκ
    rw [strat] at hs
    have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 2 := congrArg Prod.snd hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = κ := congrArg Prod.fst hs
    rcases TateAlgorithm.run_kodairaSymbol_of_tamagawaNumber_eq_two hUp hc with
      ⟨n, hn, h⟩ | h | ⟨n, h⟩ | h
    · obtain ⟨m, hm⟩ := hn
      have he : κ = KodairaSymbol.I (2 * m) := by
        rw [hκ.symm.trans h, show n = 2 * m from by omega]
      rw [he] at hxκ
      exact Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨m, hxκ⟩)))
    · rw [hκ.symm.trans h] at hxκ
      exact Or.inl (Or.inl (Or.inr hxκ))
    · rw [hκ.symm.trans h] at hxκ
      exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨n, hxκ⟩))
    · rw [hκ.symm.trans h] at hxκ
      exact Or.inr hxκ
  · refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
    · exact Set.iUnion_subset fun n => Set.subset_iUnion (fun κ => stratFibre p (κ, 2)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 2)) _
    · exact Set.iUnion_subset fun n => Set.subset_iUnion (fun κ => stratFibre p (κ, 2)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 2)) _

end WeierstrassCurve
