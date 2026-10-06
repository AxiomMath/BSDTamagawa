/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateEvenSteps
public import BSDTamagawa.NumberTheory.TateEvenStepSeven

/-!
# `RunIntTranslateInvariant` and `StratScaleInvariant` at the even prime

At `p = 2`, Tate's algorithm returns the same Kodaira symbol and Tamagawa number on a curve over
`ℤ_2` and on any integral translate of it, that is, any curve obtained from it by a change of
variables with `u = 1` and `r, s, t ∈ ℤ_2`. Consequently the reduction datum of a short model over
`ℤ_2` is unchanged by the dilation `σ_2(a₄, a₆) = (2⁴a₄, 2⁶a₆)`.

For each step `n` of the algorithm, `Stepn.intTranslate_determination_of_eq_two` asserts that on
two integral translates the step takes the same branch, returns the same Kodaira symbol and
Tamagawa number when it terminates, and hands on integral translates when it continues. Each pass
through Steps 1–11 that does not terminate lowers `v_ϖ(Δ)` by `12`, so a recursion on `v_ϖ(Δ)`
completes the argument.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step11.isIntTranslate_translate_of_dvd_two`: Step 11's rescaling
  carries integral translates to integral translates when `ϖ ∣ 2` and `3` is a unit.
* `WeierstrassCurve.TateAlgorithm.Step2.intTranslate_determination_of_eq_two`, …,
  `WeierstrassCurve.TateAlgorithm.Step11.intTranslate_determination_of_eq_two`: the steps of Tate's
  algorithm agree on integral translates.
* `WeierstrassCurve.runIntTranslateInvariant_of_eq_two`: `p = 2 → RunIntTranslateInvariant p`.
* `WeierstrassCurve.stratScaleInvariant_of_eq_two`: `p = 2 → StratScaleInvariant p`.
* `WeierstrassCurve.stratScaleInvariant_two`: `StratScaleInvariant 2`.

## Implementation notes

At an odd prime the parameters `r`, `s`, `t` relating two translates are bounded below in valuation
by reading coefficients in which they appear multiplied by `2`, such as `a₁ ↦ a₁ + 2s`. At `p = 2`
they are read instead off the `-s²` of `a₂`, the `-t²` of `a₆` and the `3r²` of `a₄`, using that
`3` is a unit in `ℤ_2`.
-/

@[expose] public section

universe u

open CommRing Ideal Polynomial

namespace WeierstrassCurve.TateAlgorithm

/-! ### Step 11's rescaling at the even prime -/

section Step11Even

variable {R : Type u} [CommRing R] {ϖ : R}

/-- Let `ϖ` be a prime with `ϖ ∣ 2` and `3` a unit, and let `W` and its translate by
`(1, r, s, t)` both satisfy `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ⁴ ∣ a₄` and `ϖ⁶ ∣ a₆`. Then their
Step-11 rescalings are integral translates of one another. -/
theorem Step11.isIntTranslate_translate_of_dvd_two [(span {ϖ}).IsMaximal] [IsDomain R]
    (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2) (h3 : IsUnit (3 : R)) {W : WeierstrassCurve R} {r s t : R}
    (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₄ : ϖ ^ 4 ∣ W.a₄)
    (ha₆ : ϖ ^ 6 ∣ W.a₆) (ha₂' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • W).a₂)
    (ha₃' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • W).a₃)
    (ha₄' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • W).a₄)
    (ha₆' : ϖ ^ 6 ∣ ((VariableChange.mk 1 r s t) • W).a₆) :
    IsIntTranslate (Step11.translate ϖ W)
      (Step11.translate ϖ ((VariableChange.mk 1 r s t) • W)) := by
  have hϖ : ϖ ≠ 0 := hprime.ne_zero
  have ha₂1 : ϖ ∣ W.a₂ := (dvd_pow_self ϖ two_ne_zero).trans ha₂
  have ha₃1 : ϖ ∣ W.a₃ := (dvd_pow_self ϖ three_ne_zero).trans ha₃
  have ha₄1 : ϖ ∣ W.a₄ := (dvd_pow_self ϖ (by norm_num)).trans ha₄
  have ha₆1 : ϖ ∣ W.a₆ := (dvd_pow_self ϖ (by norm_num)).trans ha₆
  have hr1 : ϖ ∣ r :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 ha₃1 ha₄1
      ((dvd_pow_self ϖ three_ne_zero).trans ha₃') ((dvd_pow_self ϖ (by norm_num)).trans ha₄')
  have hs : ϖ ∣ s :=
    WeierstrassCurve.dvd_s_of_dvd_a₂ hprime ha₁ hr1 ha₂1 ((dvd_pow_self ϖ two_ne_zero).trans ha₂')
  have hr : ϖ ^ 2 ∣ r :=
    WeierstrassCurve.dvd_r_of_dvd_a₂ h3 ha₂ ha₂' (pow_two ϖ ▸ mul_dvd_mul hs ha₁)
      (pow_two ϖ ▸ pow_two s ▸ mul_dvd_mul hs hs)
  have ht1 : ϖ ∣ t :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr1 ha₃1 ha₆1
      ((dvd_pow_self ϖ (by norm_num)).trans ha₆')
  have ht2 : ϖ ^ 2 ∣ t :=
    WeierstrassCurve.dvd_sq_t_of_dvd_a₆ hprime hr1 ha₁ ha₂1
      ((pow_dvd_pow ϖ (by norm_num : 2 ≤ 3)).trans ha₃)
      ((pow_dvd_pow ϖ (by norm_num : 2 ≤ 4)).trans ha₄) ht1
      ((pow_dvd_pow ϖ (by norm_num : 3 ≤ 6)).trans ha₆)
      ((pow_dvd_pow ϖ (by norm_num : 3 ≤ 6)).trans ha₆')
  have ht : ϖ ^ 3 ∣ t :=
    WeierstrassCurve.dvd_cb_t_of_dvd_a₆ hprime hr ha₁ ha₂1 ha₃
      ((pow_dvd_pow ϖ (by norm_num : 3 ≤ 4)).trans ha₄) ht2
      ((pow_dvd_pow ϖ (by norm_num : 5 ≤ 6)).trans ha₆)
      ((pow_dvd_pow ϖ (by norm_num : 5 ≤ 6)).trans ha₆')
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨τ, rfl⟩ := ht
  refine ⟨ρ, σ, τ, ?_⟩
  simpa only [Step11.scaleUp_translate hϖ ha₁ ha₂ ha₃ ha₄ ha₆] using
    Step11.translate_smul_scaleUp hϖ (Step11.translate ϖ W) ρ σ τ

end Step11Even

variable {p : ℕ} [Fact p.Prime]

/-! ### Steps 1–5 -/

open scoped Classical in
/-- **Steps 1 and 2 agree on an integral translate, at the even prime.** On two curves over `ℤ_2`
that are integral translates of one another, Steps 1 and 2 of Tate's algorithm take the same
branch, return the same Kodaira symbol and Tamagawa number when they terminate, and hand on
integral translates when they continue. -/
theorem Step2.intTranslate_determination_of_eq_two (hp2 : p = 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step2.run (p : ℤ_[p]) W).isOk = (Step2.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step2.run (p : ℤ_[p]) W = .error o →
        Step2.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step2.run (p : ℤ_[p]) W = .ok c →
        Step2.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  have hsq := PadicInt.sq_eq_self_residue_of_eq_two hp2
  by_cases hd : (p : ℤ_[p]) ∣ W.Δ
  · have hd' : (p : ℤ_[p]) ∣ W'.Δ := by rwa [h.Δ_eq]
    rw [Step2.run_eq_of_dvd_Δ (p : ℤ_[p]) hd, Step2.run_eq_of_dvd_Δ (p : ℤ_[p]) hd']
    have hIT : IsIntTranslate (Step2.translate (p : ℤ_[p]) W) (Step2.translate (p : ℤ_[p]) W') :=
      ((Step2.isIntTranslate_translate W).symm'.trans h).trans (Step2.isIntTranslate_translate W')
    have hb : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W').b₂
        ↔ (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂ := by
      rw [Step2.dvd_translate_b₂_iff_dvd_c₄ hd', Step2.dvd_translate_b₂_iff_dvd_c₄ hd, h.c₄_eq]
    have hmΔ : (Step2.translate (p : ℤ_[p]) W').Δ = (Step2.translate (p : ℤ_[p]) W).Δ := by
      rw [Step2.translate_Δ, Step2.translate_Δ, h.Δ_eq]
    by_cases hbr : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂
    · rw [ite_eq_left hbr, ite_eq_left (hb.mpr hbr)]
      refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c c' hc hc' => ?_⟩
      rw [Except.ok.injEq] at hc hc'
      subst hc hc'
      exact hIT
    · obtain ⟨r₂, s₂, t₂, hrel⟩ := hIT
      have hv := Step2.hasValuation_translate hd
      have hv' := Step2.hasValuation_translate hd'
      have hr₂ : (p : ℤ_[p]) ∣ r₂ :=
        WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ PadicInt.prime_p hϖ2 h3 (by simpa using hv.a₃)
          (by simpa using hv.a₄) (by rw [← hrel]; simpa using hv'.a₃)
          (by rw [← hrel]; simpa using hv'.a₄)
      have hsplits : ((X ^ 2 + C (Step2.translate (p : ℤ_[p]) W').a₁ * X
            - C (Step2.translate (p : ℤ_[p]) W').a₂).map (mod (p : ℤ_[p]))).Splits
          ↔ ((X ^ 2 + C (Step2.translate (p : ℤ_[p]) W).a₁ * X
            - C (Step2.translate (p : ℤ_[p]) W).a₂).map (mod (p : ℤ_[p]))).Splits := by
        rw [hrel]
        exact Step2.splits_smul_of_dvd_two PadicInt.prime_p hϖ2 hsq hr₂ hbr
      rw [ite_eq_right hbr, ite_eq_right fun hc => hbr (hb.mp hc)]
      refine ⟨rfl, fun o o' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      refine ⟨by simp only [hmΔ], ?_⟩
      simp only [hmΔ]
      by_cases hsp : ((X ^ 2 + C (Step2.translate (p : ℤ_[p]) W).a₁ * X
          - C (Step2.translate (p : ℤ_[p]) W).a₂).map (mod (p : ℤ_[p]))).Splits
      · rw [ite_eq_left hsp, ite_eq_left (hsplits.mpr hsp)]
      · rw [ite_eq_right hsp, ite_eq_right fun hc => hsp (hsplits.mp hc)]
  · have hd' : ¬ (p : ℤ_[p]) ∣ W'.Δ := fun hc => hd (by rwa [← h.Δ_eq])
    rw [Step2.run_eq_of_not_dvd_Δ (p : ℤ_[p]) hd, Step2.run_eq_of_not_dvd_Δ (p : ℤ_[p]) hd']
    refine ⟨rfl, fun o o' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
    rw [Except.error.injEq] at ho ho'
    subst ho ho'
    exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 3 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 3 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step3.intTranslate_determination_of_eq_two (hp2 : p = 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step3.run (p : ℤ_[p]) W).isOk = (Step3.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step3.run (p : ℤ_[p]) W = .error o →
        Step3.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step3.run (p : ℤ_[p]) W = .ok c →
        Step3.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ := Step2.intTranslate_determination_of_eq_two hp2 h
  cases hs : Step2.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step2.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step3.run_eq_of_step2_error (p : ℤ_[p]) hs, Step3.run_eq_of_step2_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step2.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      obtain ⟨r₂, s₂, t₂, hrel⟩ : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step2.run_hasValuation hs
      have hv' := Step2.run_hasValuation hs'
      obtain ⟨hr, ht⟩ :=
        Step2.dvd_of_state_of_dvd_two PadicInt.prime_p hϖ2 h3 (by simpa using hv.a₃)
          (by simpa using hv.a₄) (by simpa using hv.a₆)
          (by rw [← hrel]; simpa using hv'.a₃) (by rw [← hrel]; simpa using hv'.a₄)
          (by rw [← hrel]; simpa using hv'.a₆)
      have hiff : (p : ℤ_[p]) ^ 2 ∣ c'.a₆ ↔ (p : ℤ_[p]) ^ 2 ∣ c.a₆ := by
        rw [hrel]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.sq_dvd_sub_a₆_smulOne hr ht
          (by simpa using hv.a₃) (by simpa using hv.a₄))
      rw [Step3.run_eq_of_step2_ok (p : ℤ_[p]) hs, Step3.run_eq_of_step2_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 2 ∣ c.a₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₂, s₂, t₂, hrel⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 4 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 4 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step4.intTranslate_determination_of_eq_two (hp2 : p = 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step4.run (p : ℤ_[p]) W).isOk = (Step4.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step4.run (p : ℤ_[p]) W = .error o →
        Step4.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step4.run (p : ℤ_[p]) W = .ok c →
        Step4.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ := Step3.intTranslate_determination_of_eq_two hp2 h
  cases hs : Step3.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step3.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step4.run_eq_of_step3_error (p : ℤ_[p]) hs, Step4.run_eq_of_step3_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step3.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      obtain ⟨r₂, s₂, t₂, hrel⟩ : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step3.run_hasValuation hs
      have hv' := Step3.run_hasValuation hs'
      obtain ⟨hr, -⟩ :=
        Step2.dvd_of_state_of_dvd_two PadicInt.prime_p hϖ2 h3 (by simpa using hv.a₃)
          (by simpa using hv.a₄) ((dvd_pow_self _ two_ne_zero).trans hv.a₆)
          (by rw [← hrel]; simpa using hv'.a₃) (by rw [← hrel]; simpa using hv'.a₄)
          (by rw [← hrel]; exact (dvd_pow_self _ two_ne_zero).trans hv'.a₆)
      have hiff : (p : ℤ_[p]) ^ 3 ∣ c'.b₈ ↔ (p : ℤ_[p]) ^ 3 ∣ c.b₈ := by
        rw [hrel]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.cb_dvd_sub_b₈_smulOne hr
          (by simpa using hv.b₂) (by simpa using hv.b₄) hv.b₆)
      rw [Step4.run_eq_of_step3_ok (p : ℤ_[p]) hs, Step4.run_eq_of_step3_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 3 ∣ c.b₈
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₂, s₂, t₂, hrel⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 5 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 5 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step5.intTranslate_determination_of_eq_two (hp2 : p = 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step5.run (p : ℤ_[p]) W).isOk = (Step5.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step5.run (p : ℤ_[p]) W = .error o →
        Step5.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step5.run (p : ℤ_[p]) W = .ok c →
        Step5.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  have hsq := PadicInt.sq_eq_self_residue_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ := Step4.intTranslate_determination_of_eq_two hp2 h
  cases hs : Step4.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step4.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step5.run_eq_of_step4_error (p : ℤ_[p]) hs, Step5.run_eq_of_step4_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step4.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      obtain ⟨r₂, s₂, t₂, hrel⟩ : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step4.run_hasValuation hϖ hs
      have hv' := Step4.run_hasValuation hϖ hs'
      obtain ⟨hr, ht⟩ :=
        Step2.dvd_of_state_of_dvd_two PadicInt.prime_p hϖ2 h3 (by simpa using hv.a₃)
          (by simpa using hv.a₄) ((dvd_pow_self _ two_ne_zero).trans hv.a₆)
          (by rw [← hrel]; simpa using hv'.a₃) (by rw [← hrel]; simpa using hv'.a₄)
          (by rw [← hrel]; exact (dvd_pow_self _ two_ne_zero).trans hv'.a₆)
      have hiff : (p : ℤ_[p]) ^ 3 ∣ c'.b₆ ↔ (p : ℤ_[p]) ^ 3 ∣ c.b₆ := by
        rw [hrel]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.cb_dvd_sub_b₆_smulOne hr
          (by simpa using hv.b₂) hv.b₄)
      rw [Step5.run_eq_of_step4_ok (p : ℤ_[p]) hs, Step5.run_eq_of_step4_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 3 ∣ c.b₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₂, s₂, t₂, hrel⟩
      · have hsplits : (quadratic (p : ℤ_[p]) c' 1).toPoly.Splits
            ↔ (quadratic (p : ℤ_[p]) c 1).toPoly.Splits := by
          rw [hrel]
          exact Step5.splits_smul_of_dvd_two PadicInt.prime_p hϖ2 hsq hr ht
            (by simpa using hv.a₃) (by simpa using hv.a₄) hv.a₆ (by simpa using hv.b₂) hv.b₈ hbr
        rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        refine ⟨rfl, ?_⟩
        by_cases hsp : (quadratic (p : ℤ_[p]) c 1).toPoly.Splits
        · rw [ite_eq_left hsp, ite_eq_left (hsplits.mpr hsp)]
        · rw [ite_eq_right hsp, ite_eq_right fun hcon => hsp (hsplits.mp hcon)]

/-! ### Step 6 -/

open scoped Classical in
/-- **Step 6 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 6 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step6.intTranslate_determination_of_eq_two (hp2 : p = 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step6.run (p : ℤ_[p]) W).isOk = (Step6.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step6.run (p : ℤ_[p]) W = .error o →
        Step6.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step6.run (p : ℤ_[p]) W = .ok c →
        Step6.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ := Step5.intTranslate_determination_of_eq_two hp2 h
  cases hs : Step5.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step5.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step6.run_eq_of_step5_error (p : ℤ_[p]) hs, Step6.run_eq_of_step5_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step5.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hIT : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ hs)
      have hv' := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ hs')
      have hIT1 : IsIntTranslate c (Step6.translate (p : ℤ_[p]) c) := ⟨0, _, _, rfl⟩
      have hIT2 : IsIntTranslate c' (Step6.translate (p : ℤ_[p]) c') := ⟨0, _, _, rfl⟩
      obtain ⟨r₃, s₃, t₃, hrel₃⟩ : IsIntTranslate (Step6.translate (p : ℤ_[p]) c)
          (Step6.translate (p : ℤ_[p]) c') :=
        (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
      have hiff : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c') 1 1).HasDoubleRoot
          ↔ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c) 1 1).HasDoubleRoot := by
        rw [hrel₃]
        exact Step6.hasDoubleRoot_smul_of_dvd_two hϖ PadicInt.prime_p hϖ2 h3
          (by simpa using hv.a₁) (by simpa using hv.a₂) hv.a₃ hv.a₄ hv.a₆
          (by rw [← hrel₃]; simpa using hv'.a₂) (by rw [← hrel₃]; exact hv'.a₃)
          (by rw [← hrel₃]; exact hv'.a₄) (by rw [← hrel₃]; exact hv'.a₆)
      have hcard := Step6.card_roots_smul_of_dvd_two (V := Step6.translate (p : ℤ_[p]) c)
        (r := r₃) (s := s₃) (t := t₃) hϖ PadicInt.prime_p hϖ2 h3 (by simpa using hv.a₁)
        (by simpa using hv.a₂) hv.a₃ hv.a₄ hv.a₆ (by rw [← hrel₃]; simpa using hv'.a₂)
        (by rw [← hrel₃]; exact hv'.a₃) (by rw [← hrel₃]; exact hv'.a₄)
        (by rw [← hrel₃]; exact hv'.a₆)
      rw [← hrel₃] at hcard
      rw [Step6.run_eq_of_step5_ok (p : ℤ_[p]) hs, Step6.run_eq_of_step5_ok (p : ℤ_[p]) hs']
      by_cases hbr : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c) 1 1).HasDoubleRoot
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₃, s₃, t₃, hrel₃⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        exact ⟨rfl, by rw [hcard]⟩

/-! ### Steps 7–11, and the top-level recursion -/

/-- **Step 7 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 7 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step7.intTranslate_determination_of_eq_two (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step7.run hϖ hΔ).isOk = (Step7.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step7.run hϖ hΔ = .error o → Step7.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step7.run hϖ hΔ = .ok c → Step7.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ := Step6.intTranslate_determination_of_eq_two hp2 h
  cases h₆ : Step6.run (p : ℤ_[p]) W with
  | error o =>
    cases h₆' : Step6.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step7.run_eq_of_step6_error hϖ hΔ h₆, Step7.run_eq_of_step6_error hϖ hΔ' h₆']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ h₆ h₆'
    | ok c' => rw [h₆, h₆'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₆' : Step6.run (p : ℤ_[p]) W' with
    | error o' => rw [h₆, h₆'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hIT : IsIntTranslate c c' := hcurve _ _ h₆ h₆'
      have hvc := Step6.run_hasValuation hϖ h₆
      have hvc' := Step6.run_hasValuation hϖ h₆'
      have hdr := Step6.run_hasDoubleRoot h₆
      have hdr' := Step6.run_hasDoubleRoot h₆'
      obtain ⟨rc, sc, tc, hrelc⟩ : IsIntTranslate c c' := hIT
      have htriff : (cubic (p : ℤ_[p]) c' 1 1).HasTripleRoot
          ↔ (cubic (p : ℤ_[p]) c 1 1).HasTripleRoot := by
        rw [hrelc]
        exact Step6.hasTripleRoot_smul_of_dvd_two hϖ PadicInt.prime_p hϖ2 h3
          (by simpa using hvc.a₁) (by simpa using hvc.a₂) hvc.a₃ hvc.a₄ hvc.a₆
          (by rw [← hrelc]; simpa using hvc'.a₂) (by rw [← hrelc]; exact hvc'.a₃)
          (by rw [← hrelc]; exact hvc'.a₄) (by rw [← hrelc]; exact hvc'.a₆)
      by_cases htr : (cubic (p : ℤ_[p]) c 1 1).HasTripleRoot
      · rw [Step7.run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ h₆ htr,
          Step7.run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ' h₆' (htriff.mpr htr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun e e' he he' => ?_⟩
        rw [Except.ok.injEq] at he he'
        subst he he'
        exact ⟨rc, sc, tc, hrelc⟩
      · have htr' : ¬(cubic (p : ℤ_[p]) c' 1 1).HasTripleRoot := fun hcon => htr (htriff.mp hcon)
        have hΔc : (Step7.translate (p : ℤ_[p]) c).Δ ≠ 0 := by
          rw [Step7.translate_Δ, Step6.run_Δ h₆]; exact hΔ
        have hΔc' : (Step7.translate (p : ℤ_[p]) c').Δ ≠ 0 := by
          rw [Step7.translate_Δ, Step6.run_Δ h₆']; exact hΔ'
        have hvT := Step7.hasValuation_translate hϖ hvc hdr htr
        have hvT' := Step7.hasValuation_translate hϖ hvc' hdr' htr'
        have ha₂T := Step7.not_dvd_translate_a₂ hϖ hvc.a₂ hdr htr
        have ha₂T' := Step7.not_dvd_translate_a₂ hϖ hvc'.a₂ hdr' htr'
        have hIT1 : IsIntTranslate c (Step7.translate (p : ℤ_[p]) c) := ⟨_, 0, 0, rfl⟩
        have hIT2 : IsIntTranslate c' (Step7.translate (p : ℤ_[p]) c') := ⟨_, 0, 0, rfl⟩
        obtain ⟨r₄, s₄, t₄, hrel₄⟩ :
            IsIntTranslate (Step7.translate (p : ℤ_[p]) c) (Step7.translate (p : ℤ_[p]) c') :=
          (IsIntTranslate.symm' hIT1).trans
            (IsIntTranslate.trans ⟨rc, sc, tc, hrelc⟩ hIT2)
        obtain ⟨hs₄, hr₄⟩ := Step7.dvd_sq_r_of_state_of_dvd_two PadicInt.prime_p hϖ2 h3
          (by simpa using hvT.a₁) (by simpa using hvT.a₂) hvT.a₃ hvT.a₄ hvT.a₆ ha₂T
          (by rw [← hrel₄]; simpa using hvT'.a₂) (by rw [← hrel₄]; exact hvT'.a₃)
          (by rw [← hrel₄]; exact hvT'.a₄) (by rw [← hrel₄]; exact hvT'.a₆)
        have hdm : multiplicity (p : ℤ_[p]) (Step7.translate (p : ℤ_[p]) c).Δ
            ≤ multiplicity (p : ℤ_[p]) W.Δ := by
          rw [Step7.translate_Δ, Step6.run_Δ h₆]
        have hsix : 6 ≤ multiplicity (p : ℤ_[p]) W.Δ := Step7.six_le_multiplicity_Δ hϖ hΔ h₆
        rw [Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h₆ htr hΔc hvT ha₂T,
          Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ' h₆' htr' hΔc' hvT' ha₂T']
        refine ⟨rfl, fun o o' ho ho' => ?_, fun e e' he _ => absurd he (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        exact Step7.subprocedure_smul_of_dvd_two (d := multiplicity (p : ℤ_[p]) W.Δ)
          PadicInt.prime_p hϖ2 hϖ hΔc hΔc' le_rfl hvT hvT' ha₂T ha₂T' hrel₄ hs₄ hr₄
          (by omega) hdm

open scoped Classical in
/-- **Step 8 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 8 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step8.intTranslate_determination_of_eq_two (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step8.run hϖ hΔ).isOk = (Step8.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step8.run hϖ hΔ = .error o → Step8.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step8.run hϖ hΔ = .ok c → Step8.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step7.intTranslate_determination_of_eq_two hp2 hϖ hΔ hΔ' h
  cases h₇ : Step7.run hϖ hΔ with
  | error o =>
    cases h₇' : Step7.run hϖ hΔ' with
    | error o' =>
      rw [Step8.run_eq_of_step7_error hϖ hΔ h₇, Step8.run_eq_of_step7_error hϖ hΔ' h₇']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ h₇ h₇'
    | ok c' => rw [h₇, h₇'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₇' : Step7.run hϖ hΔ' with
    | error o' => rw [h₇, h₇'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hIT : IsIntTranslate c c' := hcurve _ _ h₇ h₇'
      have hv := Step8.hasValuation_translate hϖ (Step7.run_hasValuation hϖ hΔ h₇)
        (Step7.run_hasDoubleRoot hϖ hΔ h₇) (Step7.run_hasTripleRoot hϖ hΔ h₇)
      have hv' := Step8.hasValuation_translate hϖ (Step7.run_hasValuation hϖ hΔ' h₇')
        (Step7.run_hasDoubleRoot hϖ hΔ' h₇') (Step7.run_hasTripleRoot hϖ hΔ' h₇')
      have hIT1 : IsIntTranslate c (Step8.translate (p : ℤ_[p]) c) := ⟨_, 0, 0, rfl⟩
      have hIT2 : IsIntTranslate c' (Step8.translate (p : ℤ_[p]) c') := ⟨_, 0, 0, rfl⟩
      obtain ⟨r₅, s₅, t₅, hrel₅⟩ :
          IsIntTranslate (Step8.translate (p : ℤ_[p]) c) (Step8.translate (p : ℤ_[p]) c') :=
        (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
      have hr₅1 : (p : ℤ_[p]) ∣ r₅ :=
        WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ PadicInt.prime_p hϖ2 h3
          ((dvd_pow_self _ two_ne_zero).trans hv.a₃)
          ((dvd_pow_self _ three_ne_zero).trans hv.a₄)
          (by rw [← hrel₅]; exact (dvd_pow_self _ two_ne_zero).trans hv'.a₃)
          (by rw [← hrel₅]; exact (dvd_pow_self _ three_ne_zero).trans hv'.a₄)
      have hs₅ : (p : ℤ_[p]) ∣ s₅ :=
        WeierstrassCurve.dvd_s_of_dvd_a₂ PadicInt.prime_p (by simpa using hv.a₁) hr₅1
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂)
          (by rw [← hrel₅]; exact (dvd_pow_self _ two_ne_zero).trans hv'.a₂)
      have hr₅ : (p : ℤ_[p]) ^ 2 ∣ r₅ :=
        WeierstrassCurve.dvd_r_of_dvd_a₂ h3 hv.a₂ (by rw [← hrel₅]; exact hv'.a₂)
          (by rw [pow_two]; exact mul_dvd_mul hs₅ (by simpa using hv.a₁))
          (by rw [pow_two ((p : ℤ_[p])), pow_two s₅]; exact mul_dvd_mul hs₅ hs₅)
      have ht₅1 : (p : ℤ_[p]) ∣ t₅ :=
        WeierstrassCurve.dvd_t_of_dvd_a₆ PadicInt.prime_p hr₅1
          ((dvd_pow_self _ two_ne_zero).trans hv.a₃)
          ((dvd_pow_self _ (by norm_num)).trans hv.a₆)
          (by rw [← hrel₅]; exact (dvd_pow_self _ (by norm_num)).trans hv'.a₆)
      have ht₅ : (p : ℤ_[p]) ^ 2 ∣ t₅ :=
        WeierstrassCurve.dvd_sq_t_of_dvd_a₆ PadicInt.prime_p hr₅1 (by simpa using hv.a₁)
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂) hv.a₃
          ((pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans hv.a₄) ht₅1
          ((pow_dvd_pow _ (by norm_num : 3 ≤ 4)).trans hv.a₆)
          (by rw [← hrel₅]; exact (pow_dvd_pow _ (by norm_num : 3 ≤ 4)).trans hv'.a₆)
      obtain ⟨γ, hγ⟩ : ∃ γ, quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c') 2
          = (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).shiftBy γ := by
        rw [hrel₅]
        exact Step8.quadratic_smul_of_dvd_two hϖ hϖ2 hr₅ ht₅ (by simpa using hv.a₁)
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂) hv.a₃ hv.a₄ hv.a₆
      have hiff : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c') 2).HasDoubleRoot
          ↔ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).HasDoubleRoot := by
        rw [hγ]; exact Cubic.hasDoubleRoot_shiftBy _ _
      have hsplits : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c') 2).toPoly.Splits
          ↔ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).toPoly.Splits := by
        rw [hγ]; exact Cubic.splits_shiftBy _ _
      rw [Step8.run_eq_of_step7_ok hϖ hΔ h₇, Step8.run_eq_of_step7_ok hϖ hΔ' h₇']
      by_cases hbr : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).HasDoubleRoot
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₅, s₅, t₅, hrel₅⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        refine ⟨rfl, ?_⟩
        by_cases hsp : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).toPoly.Splits
        · rw [ite_eq_left hsp, ite_eq_left (hsplits.mpr hsp)]
        · rw [ite_eq_right hsp, ite_eq_right fun hcon => hsp (hsplits.mp hcon)]

open scoped Classical in
/-- **Step 9 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 9 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step9.intTranslate_determination_of_eq_two (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step9.run hϖ hΔ).isOk = (Step9.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step9.run hϖ hΔ = .error o → Step9.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step9.run hϖ hΔ = .ok c → Step9.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step8.intTranslate_determination_of_eq_two hp2 hϖ hΔ hΔ' h
  cases h₈ : Step8.run hϖ hΔ with
  | error o =>
    cases h₈' : Step8.run hϖ hΔ' with
    | error o' =>
      rw [Step9.run_eq_of_step8_error hϖ hΔ h₈, Step9.run_eq_of_step8_error hϖ hΔ' h₈']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ h₈ h₈'
    | ok c' => rw [h₈, h₈'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₈' : Step8.run hϖ hΔ' with
    | error o' => rw [h₈, h₈'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hIT : IsIntTranslate c c' := hcurve _ _ h₈ h₈'
      have hv := Step9.hasValuation_translate hϖ (Step8.run_hasValuation hϖ hΔ h₈)
        (Step8.run_hasDoubleRoot hϖ hΔ h₈)
      have hv' := Step9.hasValuation_translate hϖ (Step8.run_hasValuation hϖ hΔ' h₈')
        (Step8.run_hasDoubleRoot hϖ hΔ' h₈')
      have hIT1 : IsIntTranslate c (Step9.translate (p : ℤ_[p]) c) := ⟨0, 0, _, rfl⟩
      have hIT2 : IsIntTranslate c' (Step9.translate (p : ℤ_[p]) c') := ⟨0, 0, _, rfl⟩
      obtain ⟨r₆, s₆, t₆, hrel₆⟩ :
          IsIntTranslate (Step9.translate (p : ℤ_[p]) c) (Step9.translate (p : ℤ_[p]) c') :=
        (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
      have hr₆1 : (p : ℤ_[p]) ∣ r₆ :=
        WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ PadicInt.prime_p hϖ2 h3
          ((dvd_pow_self _ three_ne_zero).trans hv.a₃)
          ((dvd_pow_self _ three_ne_zero).trans hv.a₄)
          (by rw [← hrel₆]; exact (dvd_pow_self _ three_ne_zero).trans hv'.a₃)
          (by rw [← hrel₆]; exact (dvd_pow_self _ three_ne_zero).trans hv'.a₄)
      have hs₆ : (p : ℤ_[p]) ∣ s₆ :=
        WeierstrassCurve.dvd_s_of_dvd_a₂ PadicInt.prime_p (by simpa using hv.a₁) hr₆1
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂)
          (by rw [← hrel₆]; exact (dvd_pow_self _ two_ne_zero).trans hv'.a₂)
      have hr₆ : (p : ℤ_[p]) ^ 2 ∣ r₆ :=
        WeierstrassCurve.dvd_r_of_dvd_a₂ h3 hv.a₂ (by rw [← hrel₆]; exact hv'.a₂)
          (by rw [pow_two]; exact mul_dvd_mul hs₆ (by simpa using hv.a₁))
          (by rw [pow_two ((p : ℤ_[p])), pow_two s₆]; exact mul_dvd_mul hs₆ hs₆)
      have ht₆1 : (p : ℤ_[p]) ∣ t₆ :=
        WeierstrassCurve.dvd_t_of_dvd_a₆ PadicInt.prime_p hr₆1
          ((dvd_pow_self _ three_ne_zero).trans hv.a₃)
          ((dvd_pow_self _ (by norm_num)).trans hv.a₆)
          (by rw [← hrel₆]; exact (dvd_pow_self _ (by norm_num)).trans hv'.a₆)
      have ht₆2 : (p : ℤ_[p]) ^ 2 ∣ t₆ :=
        WeierstrassCurve.dvd_sq_t_of_dvd_a₆ PadicInt.prime_p hr₆1 (by simpa using hv.a₁)
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂)
          ((pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans hv.a₃)
          ((pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans hv.a₄) ht₆1
          ((pow_dvd_pow _ (by norm_num : 3 ≤ 5)).trans hv.a₆)
          (by rw [← hrel₆]; exact (pow_dvd_pow _ (by norm_num : 3 ≤ 5)).trans hv'.a₆)
      have ht₆ : (p : ℤ_[p]) ^ 3 ∣ t₆ :=
        WeierstrassCurve.dvd_cb_t_of_dvd_a₆ PadicInt.prime_p hr₆ (by simpa using hv.a₁)
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂) hv.a₃ hv.a₄ ht₆2 hv.a₆
          (by rw [← hrel₆]; exact hv'.a₆)
      have hiff : (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) c').a₄
          ↔ (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) c).a₄ := by
        rw [hrel₆]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.pow_four_dvd_sub_a₄_smulOne hs₆ hr₆ ht₆
          (by simpa using hv.a₁) hv.a₂ hv.a₃)
      rw [Step9.run_eq_of_step8_ok hϖ hΔ h₈, Step9.run_eq_of_step8_ok hϖ hΔ' h₈']
      by_cases hbr : (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) c).a₄
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₆, s₆, t₆, hrel₆⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 10 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 10 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step10.intTranslate_determination_of_eq_two (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step10.run hϖ hΔ).isOk = (Step10.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step10.run hϖ hΔ = .error o → Step10.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step10.run hϖ hΔ = .ok c → Step10.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step9.intTranslate_determination_of_eq_two hp2 hϖ hΔ hΔ' h
  cases h₉ : Step9.run hϖ hΔ with
  | error o =>
    cases h₉' : Step9.run hϖ hΔ' with
    | error o' =>
      rw [Step10.run_eq_of_step9_error hϖ hΔ h₉, Step10.run_eq_of_step9_error hϖ hΔ' h₉']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ h₉ h₉'
    | ok c' => rw [h₉, h₉'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₉' : Step9.run hϖ hΔ' with
    | error o' => rw [h₉, h₉'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hv := Step9.run_hasValuation hϖ hΔ h₉
      have hv' := Step9.run_hasValuation hϖ hΔ' h₉'
      obtain ⟨r₇, s₇, t₇, hrel₇⟩ : IsIntTranslate c c' := hcurve _ _ h₉ h₉'
      have hr₇1 : (p : ℤ_[p]) ∣ r₇ :=
        WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ PadicInt.prime_p hϖ2 h3
          ((dvd_pow_self _ three_ne_zero).trans hv.a₃)
          ((dvd_pow_self _ (by norm_num)).trans hv.a₄)
          (by rw [← hrel₇]; exact (dvd_pow_self _ three_ne_zero).trans hv'.a₃)
          (by rw [← hrel₇]; exact (dvd_pow_self _ (by norm_num)).trans hv'.a₄)
      have hs₇ : (p : ℤ_[p]) ∣ s₇ :=
        WeierstrassCurve.dvd_s_of_dvd_a₂ PadicInt.prime_p (by simpa using hv.a₁) hr₇1
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂)
          (by rw [← hrel₇]; exact (dvd_pow_self _ two_ne_zero).trans hv'.a₂)
      have hr₇ : (p : ℤ_[p]) ^ 2 ∣ r₇ :=
        WeierstrassCurve.dvd_r_of_dvd_a₂ h3 hv.a₂ (by rw [← hrel₇]; exact hv'.a₂)
          (by rw [pow_two]; exact mul_dvd_mul hs₇ (by simpa using hv.a₁))
          (by rw [pow_two ((p : ℤ_[p])), pow_two s₇]; exact mul_dvd_mul hs₇ hs₇)
      have ht₇1 : (p : ℤ_[p]) ∣ t₇ :=
        WeierstrassCurve.dvd_t_of_dvd_a₆ PadicInt.prime_p hr₇1
          ((dvd_pow_self _ three_ne_zero).trans hv.a₃)
          ((dvd_pow_self _ (by norm_num)).trans hv.a₆)
          (by rw [← hrel₇]; exact (dvd_pow_self _ (by norm_num)).trans hv'.a₆)
      have ht₇2 : (p : ℤ_[p]) ^ 2 ∣ t₇ :=
        WeierstrassCurve.dvd_sq_t_of_dvd_a₆ PadicInt.prime_p hr₇1 (by simpa using hv.a₁)
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂)
          ((pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans hv.a₃)
          ((pow_dvd_pow _ (by norm_num : 2 ≤ 4)).trans hv.a₄) ht₇1
          ((pow_dvd_pow _ (by norm_num : 3 ≤ 5)).trans hv.a₆)
          (by rw [← hrel₇]; exact (pow_dvd_pow _ (by norm_num : 3 ≤ 5)).trans hv'.a₆)
      have ht₇ : (p : ℤ_[p]) ^ 3 ∣ t₇ :=
        WeierstrassCurve.dvd_cb_t_of_dvd_a₆ PadicInt.prime_p hr₇ (by simpa using hv.a₁)
          ((dvd_pow_self _ two_ne_zero).trans hv.a₂) hv.a₃
          ((pow_dvd_pow _ (by norm_num : 3 ≤ 4)).trans hv.a₄) ht₇2 hv.a₆
          (by rw [← hrel₇]; exact hv'.a₆)
      have hiff : (p : ℤ_[p]) ^ 6 ∣ c'.a₆ ↔ (p : ℤ_[p]) ^ 6 ∣ c.a₆ := by
        rw [hrel₇]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.pow_six_dvd_sub_a₆_smulOne hr₇ ht₇
          (by simpa using hv.a₁) hv.a₂ hv.a₃ hv.a₄)
      rw [Step10.run_eq_of_step9_ok hϖ hΔ h₉, Step10.run_eq_of_step9_ok hϖ hΔ' h₉']
      by_cases hbr : (p : ℤ_[p]) ^ 6 ∣ c.a₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc hc'
        exact ⟨r₇, s₇, t₇, hrel₇⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho ho'
        exact ⟨rfl, rfl⟩

/-- **Step 11 agrees on an integral translate, at the even prime.** On two curves over `ℤ_2` that
are integral translates of one another, Step 11 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step11.intTranslate_determination_of_eq_two (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step11.run hϖ hΔ).isOk = (Step11.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step11.run hϖ hΔ = .error o → Step11.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step11.run hϖ hΔ = .ok c → Step11.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step10.intTranslate_determination_of_eq_two hp2 hϖ hΔ hΔ' h
  cases h₁₀ : Step10.run hϖ hΔ with
  | error o =>
    cases h₁₀' : Step10.run hϖ hΔ' with
    | error o' =>
      rw [Step11.run_eq_of_step10_error hϖ hΔ h₁₀, Step11.run_eq_of_step10_error hϖ hΔ' h₁₀']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho ho'
      exact hans _ _ h₁₀ h₁₀'
    | ok c' => rw [h₁₀, h₁₀'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₁₀' : Step10.run hϖ hΔ' with
    | error o' => rw [h₁₀, h₁₀'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hIT : IsIntTranslate c c' := hcurve _ _ h₁₀ h₁₀'
      have hv := Step10.run_hasValuation hϖ hΔ h₁₀
      have hv' := Step10.run_hasValuation hϖ hΔ' h₁₀'
      have hITT : IsIntTranslate (Step11.translate (p : ℤ_[p]) c)
          (Step11.translate (p : ℤ_[p]) c') := by
        obtain ⟨r, s, t, rfl⟩ := hIT
        exact Step11.isIntTranslate_translate_of_dvd_two PadicInt.prime_p hϖ2 h3
          (by simpa using hv.a₁) hv.a₂ hv.a₃ hv.a₄ hv.a₆ hv'.a₂ hv'.a₃ hv'.a₄ hv'.a₆
      rw [Step11.run_eq_of_step10_ok hϖ hΔ h₁₀, Step11.run_eq_of_step10_ok hϖ hΔ' h₁₀']
      refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
      rw [Except.ok.injEq] at hc hc'
      subst hc hc'
      exact hITT

/-- For `p = 2` and every `n`, Tate's algorithm agrees on two integral translates `W`, `W'` with
`v_ϖ(W.Δ) = n`. -/
private theorem run_intTranslate_aux_of_eq_two (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0) (n : ℕ) :
    ∀ (W W' : WeierstrassCurve ℤ_[p]) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0),
      multiplicity (p : ℤ_[p]) W.Δ = n → IsIntTranslate W W' →
      (run hϖ hΔ).kodairaSymbol = (run hϖ hΔ').kodairaSymbol ∧
      (run hϖ hΔ).tamagawaNumber = (run hϖ hΔ').tamagawaNumber := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W W' hΔ hΔ' hn hIT
    obtain ⟨hbranch, herror, hcont⟩ :=
      Step11.intTranslate_determination_of_eq_two hp2 hϖ hΔ hΔ' hIT
    cases h₁₁ : Step11.run hϖ hΔ with
    | error o =>
      cases h₁₁' : Step11.run hϖ hΔ' with
      | error o' =>
        rw [run_eq_of_step11_error hϖ hΔ h₁₁, run_eq_of_step11_error hϖ hΔ' h₁₁']
        exact herror o o' h₁₁ h₁₁'
      | ok c' => rw [h₁₁, h₁₁'] at hbranch; exact Bool.noConfusion hbranch
    | ok c =>
      cases h₁₁' : Step11.run hϖ hΔ' with
      | error o' => rw [h₁₁, h₁₁'] at hbranch; exact Bool.noConfusion hbranch
      | ok c' =>
        have hc : c.Δ ≠ 0 := Δ_ne_zero_of_step11_ok hϖ hΔ h₁₁
        have hc' : c'.Δ ≠ 0 := Δ_ne_zero_of_step11_ok hϖ hΔ' h₁₁'
        have hdrop : multiplicity (p : ℤ_[p]) W.Δ = multiplicity (p : ℤ_[p]) c.Δ + 12 :=
          Step11.multiplicity_Δ_run hϖ hΔ h₁₁
        rw [run_eq_of_step11_ok hϖ hΔ h₁₁ hc, run_eq_of_step11_ok hϖ hΔ' h₁₁' hc']
        exact ih (multiplicity (p : ℤ_[p]) c.Δ) (by omega) c c' hc hc' rfl (hcont c c' h₁₁ h₁₁')

end WeierstrassCurve.TateAlgorithm

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy

/-- **`RunIntTranslateInvariant p` at the even prime.** Tate's algorithm returns the same Kodaira
symbol and the same local Tamagawa number on a curve over `ℤ_2` and on any curve obtained from it
by a change of variables with `u = 1`. -/
theorem runIntTranslateInvariant_of_eq_two (hp2 : p = 2) : RunIntTranslateInvariant p := by
  intro W W' hΔ hΔ' hIT
  exact TateAlgorithm.run_intTranslate_aux_of_eq_two hp2 PadicInt.uniformizer_ne_zero
    (multiplicity (p : ℤ_[p]) W.Δ) W W' hΔ hΔ' rfl hIT

/-- **`StratScaleInvariant p` at the even prime**: the reduction datum of a short model over `ℤ_2`
is unchanged by the dilation `σ_2(a₄, a₆) = (2⁴a₄, 2⁶a₆)`. -/
theorem stratScaleInvariant_of_eq_two (hp2 : p = 2) : StratScaleInvariant p :=
  stratScaleInvariant_of_runIntTranslateInvariant_two hp2 (runIntTranslateInvariant_of_eq_two hp2)

/-- `StratScaleInvariant 2`. -/
theorem stratScaleInvariant_two : StratScaleInvariant 2 :=
  stratScaleInvariant_of_eq_two rfl

end WeierstrassCurve
