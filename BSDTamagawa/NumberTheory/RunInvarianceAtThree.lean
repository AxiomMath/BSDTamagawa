/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateOddTransport

/-!
# `RunIntTranslateInvariant` and `StratScaleInvariant` at every odd prime

For every prime `p ≠ 2`, Tate's algorithm returns the same Kodaira symbol and Tamagawa number on a
curve over `ℤ_p` and on any integral translate of it, that is, any curve obtained from it by a
change of variables with `u = 1` and `r, s, t ∈ ℤ_p`. Consequently the reduction datum of a short
model over `ℤ_p` is unchanged by the dilation `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)`.

For each step `n` of the algorithm, `Stepn.intTranslate_determination_of_ne_two` asserts that on
two integral translates the step takes the same branch, returns the same Kodaira symbol and
Tamagawa number when it terminates, and hands on integral translates when it continues. Each pass
through Steps 1–11 that does not terminate lowers `v_ϖ(Δ)` by `12`, so a recursion on `v_ϖ(Δ)`
completes the argument.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step2.intTranslate_determination_of_ne_two`, …,
  `WeierstrassCurve.TateAlgorithm.Step11.intTranslate_determination_of_ne_two`: the steps of Tate's
  algorithm agree on integral translates.
* `WeierstrassCurve.runIntTranslateInvariant_of_ne_two`: `p ≠ 2 → RunIntTranslateInvariant p`.
* `WeierstrassCurve.stratScaleInvariant_of_ne_two`: `p ≠ 2 → StratScaleInvariant p`.
* `WeierstrassCurve.stratScaleInvariant_three`: `p = 3 → StratScaleInvariant p`.
-/

@[expose] public section

open CommRing Ideal Polynomial

namespace WeierstrassCurve.TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Steps 1–5 -/

open scoped Classical in
/-- **Steps 1 and 2 agree on an integral translate, at every odd prime.** On two curves over `ℤ_p`
that are integral translates of one another, Steps 1 and 2 of Tate's algorithm take the same
branch, return the same Kodaira symbol and Tamagawa number when they terminate, and hand on
integral translates when they continue. -/
theorem Step2.intTranslate_determination_of_ne_two (hp2 : p ≠ 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step2.run (p : ℤ_[p]) W).isOk = (Step2.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step2.run (p : ℤ_[p]) W = .error o →
        Step2.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step2.run (p : ℤ_[p]) W = .ok c →
        Step2.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  by_cases hd : (p : ℤ_[p]) ∣ W.Δ
  · have hd' : (p : ℤ_[p]) ∣ W'.Δ := by rw [h.Δ_eq]; exact hd
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
      subst hc; subst hc'
      exact hIT
    · obtain ⟨r₂, s₂, t₂, hrel⟩ := hIT
      have hb₄ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₄ := by
        simpa using (Step2.hasValuation_translate hd).b₄
      have hb₆ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₆ := by
        simpa using (Step2.hasValuation_translate hd).b₆
      have hb₄' : (p : ℤ_[p]) ∣
          ((VariableChange.mk 1 r₂ s₂ t₂) • Step2.translate (p : ℤ_[p]) W).b₄ := by
        rw [← hrel]; simpa using (Step2.hasValuation_translate hd').b₄
      have hb₆' : (p : ℤ_[p]) ∣
          ((VariableChange.mk 1 r₂ s₂ t₂) • Step2.translate (p : ℤ_[p]) W).b₆ := by
        rw [← hrel]; simpa using (Step2.hasValuation_translate hd').b₆
      have hr₂ : (p : ℤ_[p]) ∣ r₂ :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 hb₄ hb₄' hb₆ hb₆'
      have hsplits : ((X ^ 2 + C (Step2.translate (p : ℤ_[p]) W').a₁ * X
            - C (Step2.translate (p : ℤ_[p]) W').a₂).map (mod (p : ℤ_[p]))).Splits
          ↔ ((X ^ 2 + C (Step2.translate (p : ℤ_[p]) W).a₁ * X
            - C (Step2.translate (p : ℤ_[p]) W).a₂).map (mod (p : ℤ_[p]))).Splits := by
        rw [hrel]; exact Step2.splits_smul h2 hr₂
      rw [ite_eq_right hbr, ite_eq_right fun hc => hbr (hb.mp hc)]
      refine ⟨rfl, fun o o' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      refine ⟨by simp only [hmΔ], ?_⟩
      simp only [hmΔ]
      by_cases hsp : ((X ^ 2 + C (Step2.translate (p : ℤ_[p]) W).a₁ * X
          - C (Step2.translate (p : ℤ_[p]) W).a₂).map (mod (p : ℤ_[p]))).Splits
      · rw [ite_eq_left hsp, ite_eq_left (hsplits.mpr hsp)]
      · rw [ite_eq_right hsp, ite_eq_right fun hc => hsp (hsplits.mp hc)]
  · have hd' : ¬ (p : ℤ_[p]) ∣ W'.Δ := fun hc => hd (by rw [← h.Δ_eq]; exact hc)
    rw [Step2.run_eq_of_not_dvd_Δ (p : ℤ_[p]) hd, Step2.run_eq_of_not_dvd_Δ (p : ℤ_[p]) hd']
    refine ⟨rfl, fun o o' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
    rw [Except.error.injEq] at ho ho'
    subst ho; subst ho'
    exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 3 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 3 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step3.intTranslate_determination_of_ne_two (hp2 : p ≠ 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step3.run (p : ℤ_[p]) W).isOk = (Step3.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step3.run (p : ℤ_[p]) W = .error o →
        Step3.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step3.run (p : ℤ_[p]) W = .ok c →
        Step3.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ := Step2.intTranslate_determination_of_ne_two hp2 h
  cases hs : Step2.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step2.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step3.run_eq_of_step2_error (p : ℤ_[p]) hs, Step3.run_eq_of_step2_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step2.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      obtain ⟨r₂, s₂, t₂, hrel⟩ : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step2.run_hasValuation hs
      have hv' := Step2.run_hasValuation hs'
      have hr : (p : ℤ_[p]) ∣ r₂ :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 (by simpa using hv.b₄)
          (by rw [← hrel]; simpa using hv'.b₄) (by simpa using hv.b₆)
          (by rw [← hrel]; simpa using hv'.b₆)
      have ht : (p : ℤ_[p]) ∣ t₂ := by
        have hx := dvd_t_of_dvd_a₃ (m := 1) (V := c) (r := r₂) (s := s₂) (t := t₂) h2
          (by simpa using hv.a₃) (by rw [← hrel]; simpa using hv'.a₃)
          (by simpa using hr.mul_right c.a₁)
        simpa using hx
      have hiff : (p : ℤ_[p]) ^ 2 ∣ c'.a₆ ↔ (p : ℤ_[p]) ^ 2 ∣ c.a₆ := by
        rw [hrel]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.sq_dvd_sub_a₆_smulOne hr ht
          (by simpa using hv.a₃) (by simpa using hv.a₄))
      rw [Step3.run_eq_of_step2_ok (p : ℤ_[p]) hs, Step3.run_eq_of_step2_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 2 ∣ c.a₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact ⟨r₂, s₂, t₂, hrel⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 4 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 4 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step4.intTranslate_determination_of_ne_two (hp2 : p ≠ 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step4.run (p : ℤ_[p]) W).isOk = (Step4.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step4.run (p : ℤ_[p]) W = .error o →
        Step4.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step4.run (p : ℤ_[p]) W = .ok c →
        Step4.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ := Step3.intTranslate_determination_of_ne_two hp2 h
  cases hs : Step3.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step3.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step4.run_eq_of_step3_error (p : ℤ_[p]) hs, Step4.run_eq_of_step3_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step3.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      obtain ⟨r₂, s₂, t₂, hrel⟩ : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step3.run_hasValuation hs
      have hv' := Step3.run_hasValuation hs'
      have hr : (p : ℤ_[p]) ∣ r₂ :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 (by simpa using hv.b₄)
          (by rw [← hrel]; simpa using hv'.b₄)
          ((dvd_pow_self _ two_ne_zero).trans hv.b₆)
          (by rw [← hrel]; exact (dvd_pow_self _ two_ne_zero).trans hv'.b₆)
      have hiff : (p : ℤ_[p]) ^ 3 ∣ c'.b₈ ↔ (p : ℤ_[p]) ^ 3 ∣ c.b₈ := by
        rw [hrel]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.cb_dvd_sub_b₈_smulOne hr
          (by simpa using hv.b₂) (by simpa using hv.b₄) hv.b₆)
      rw [Step4.run_eq_of_step3_ok (p : ℤ_[p]) hs, Step4.run_eq_of_step3_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 3 ∣ c.b₈
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact ⟨r₂, s₂, t₂, hrel⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 5 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 5 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step5.intTranslate_determination_of_ne_two (hp2 : p ≠ 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step5.run (p : ℤ_[p]) W).isOk = (Step5.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step5.run (p : ℤ_[p]) W = .error o →
        Step5.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step5.run (p : ℤ_[p]) W = .ok c →
        Step5.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ := Step4.intTranslate_determination_of_ne_two hp2 h
  cases hs : Step4.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step4.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step5.run_eq_of_step4_error (p : ℤ_[p]) hs, Step5.run_eq_of_step4_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step4.run (p : ℤ_[p]) W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      obtain ⟨r₂, s₂, t₂, hrel⟩ : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step4.run_hasValuation hϖ hs
      have hv' := Step4.run_hasValuation hϖ hs'
      have hr : (p : ℤ_[p]) ∣ r₂ :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 ((dvd_pow_self _ two_ne_zero).trans hv.b₄)
          (by rw [← hrel]; exact (dvd_pow_self _ two_ne_zero).trans hv'.b₄)
          ((dvd_pow_self _ two_ne_zero).trans hv.b₆)
          (by rw [← hrel]; exact (dvd_pow_self _ two_ne_zero).trans hv'.b₆)
      have hiff : (p : ℤ_[p]) ^ 3 ∣ c'.b₆ ↔ (p : ℤ_[p]) ^ 3 ∣ c.b₆ := by
        rw [hrel]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.cb_dvd_sub_b₆_smulOne hr
          (by simpa using hv.b₂) hv.b₄)
      obtain ⟨γ, hγ⟩ : ∃ γ, quadratic (p : ℤ_[p]) c' 1 = (quadratic (p : ℤ_[p]) c 1).shiftBy γ := by
        rw [hrel]
        exact Step5.quadratic_smul_of_dvd h2 hϖ hr (by simpa using hv.a₃) hv.a₆
          (by simpa using hv.b₂) hv.b₄ (by rw [← hrel]; simpa using hv'.a₃)
          (by rw [← hrel]; exact hv'.a₆)
      have hsplits : (quadratic (p : ℤ_[p]) c' 1).toPoly.Splits
          ↔ (quadratic (p : ℤ_[p]) c 1).toPoly.Splits := by
        rw [hγ]; exact Cubic.splits_shiftBy _ _
      rw [Step5.run_eq_of_step4_ok (p : ℤ_[p]) hs, Step5.run_eq_of_step4_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 3 ∣ c.b₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact ⟨r₂, s₂, t₂, hrel⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        refine ⟨rfl, ?_⟩
        by_cases hsp : (quadratic (p : ℤ_[p]) c 1).toPoly.Splits
        · rw [ite_eq_left hsp, ite_eq_left (hsplits.mpr hsp)]
        · rw [ite_eq_right hsp, ite_eq_right fun hcon => hsp (hsplits.mp hcon)]

/-! ### Step 6 -/

open scoped Classical in
/-- **Step 6 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 6 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step6.intTranslate_determination_of_ne_two (hp2 : p ≠ 2)
    {W W' : WeierstrassCurve ℤ_[p]} (h : IsIntTranslate W W') :
    ((Step6.run (p : ℤ_[p]) W).isOk = (Step6.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step6.run (p : ℤ_[p]) W = .error o →
        Step6.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step6.run (p : ℤ_[p]) W = .ok c →
        Step6.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ := Step5.intTranslate_determination_of_ne_two hp2 h
  cases hs : Step5.run (p : ℤ_[p]) W with
  | error o =>
    cases hs' : Step5.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step6.run_eq_of_step5_error (p : ℤ_[p]) hs, Step6.run_eq_of_step5_error (p : ℤ_[p]) hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
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
      have hs₃ : (p : ℤ_[p]) ∣ s₃ := by
        simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using hv.a₁)
          (by rw [← hrel₃]; simpa using hv'.a₁)
      have hr₃ : (p : ℤ_[p]) ∣ r₃ :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 ((dvd_pow_self _ two_ne_zero).trans hv.b₄)
          (by rw [← hrel₃]; exact (dvd_pow_self _ two_ne_zero).trans hv'.b₄)
          ((dvd_pow_self _ three_ne_zero).trans hv.b₆)
          (by rw [← hrel₃]; exact (dvd_pow_self _ three_ne_zero).trans hv'.b₆)
      have ht₃ : (p : ℤ_[p]) ^ 2 ∣ t₃ :=
        dvd_t_of_dvd_a₃ h2 hv.a₃ (by rw [← hrel₃]; exact hv'.a₃)
          (by rw [pow_two]; exact mul_dvd_mul hr₃ (by simpa using hv.a₁))
      have hiff : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c') 1 1).HasDoubleRoot
          ↔ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c) 1 1).HasDoubleRoot := by
        rw [hrel₃]
        exact Step6.hasDoubleRoot_smul_of_dvd hϖ hs₃ hr₃ ht₃ (by simpa using hv.a₁)
          (by simpa using hv.a₂) hv.a₃ hv.a₄ hv.a₆
      have hcard := Step6.card_roots_smul_of_dvd (V := Step6.translate (p : ℤ_[p]) c) (r := r₃)
        (s := s₃) (t := t₃) hϖ hs₃ hr₃ ht₃ (by simpa using hv.a₁) (by simpa using hv.a₂)
        hv.a₃ hv.a₄ hv.a₆
      rw [← hrel₃] at hcard
      rw [Step6.run_eq_of_step5_ok (p : ℤ_[p]) hs, Step6.run_eq_of_step5_ok (p : ℤ_[p]) hs']
      by_cases hbr : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c) 1 1).HasDoubleRoot
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact ⟨r₃, s₃, t₃, hrel₃⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, by rw [hcard]⟩

/-! ### Steps 7–11, and the top-level recursion -/

/-- **Step 7 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 7 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step7.intTranslate_determination_of_ne_two (hp2 : p ≠ 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step7.run hϖ hΔ).isOk = (Step7.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step7.run hϖ hΔ = .error o → Step7.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step7.run hϖ hΔ = .ok c → Step7.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ := Step6.intTranslate_determination_of_ne_two hp2 h
  cases h₆ : Step6.run (p : ℤ_[p]) W with
  | error o =>
    cases h₆' : Step6.run (p : ℤ_[p]) W' with
    | error o' =>
      rw [Step7.run_eq_of_step6_error hϖ hΔ h₆, Step7.run_eq_of_step6_error hϖ hΔ' h₆']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
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
      have hsc : (p : ℤ_[p]) ∣ sc := by
        simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using hvc.a₁)
          (by rw [← hrelc]; simpa using hvc'.a₁)
      have hrc : (p : ℤ_[p]) ∣ rc :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 ((dvd_pow_self _ two_ne_zero).trans hvc.b₄)
          (by rw [← hrelc]; exact (dvd_pow_self _ two_ne_zero).trans hvc'.b₄)
          ((dvd_pow_self _ three_ne_zero).trans hvc.b₆)
          (by rw [← hrelc]; exact (dvd_pow_self _ three_ne_zero).trans hvc'.b₆)
      have htc : (p : ℤ_[p]) ^ 2 ∣ tc :=
        dvd_t_of_dvd_a₃ h2 hvc.a₃ (by rw [← hrelc]; exact hvc'.a₃)
          (by rw [pow_two]; exact mul_dvd_mul hrc (by simpa using hvc.a₁))
      have htriff : (cubic (p : ℤ_[p]) c' 1 1).HasTripleRoot
          ↔ (cubic (p : ℤ_[p]) c 1 1).HasTripleRoot := by
        rw [hrelc]
        exact Step6.hasTripleRoot_smul_of_dvd hϖ hsc hrc htc (by simpa using hvc.a₁)
          (by simpa using hvc.a₂) hvc.a₃ hvc.a₄ hvc.a₆
      by_cases htr : (cubic (p : ℤ_[p]) c 1 1).HasTripleRoot
      · rw [Step7.run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ h₆ htr,
          Step7.run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ' h₆' (htriff.mpr htr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun e e' he he' => ?_⟩
        rw [Except.ok.injEq] at he he'
        subst he; subst he'
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
        obtain ⟨hs₄, hr₄⟩ := Step7.dvd_sq_r_of_state_of_dvd_b PadicInt.prime_p h2
          (by simpa using hvT.a₁) (by simpa using hvT.a₂) hvT.a₃ hvT.a₄ hvT.a₆ ha₂T
          (by rw [← hrel₄]; simpa using hvT'.a₁) (by rw [← hrel₄]; exact hvT'.a₃)
          (by rw [← hrel₄]; exact hvT'.a₄) (by rw [← hrel₄]; exact hvT'.a₆)
        have hdm : multiplicity (p : ℤ_[p]) (Step7.translate (p : ℤ_[p]) c).Δ
            ≤ multiplicity (p : ℤ_[p]) W.Δ := by
          rw [Step7.translate_Δ, Step6.run_Δ h₆]
        have hsix : 6 ≤ multiplicity (p : ℤ_[p]) W.Δ := Step7.six_le_multiplicity_Δ hϖ hΔ h₆
        rw [Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h₆ htr hΔc hvT ha₂T,
          Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ' h₆' htr' hΔc' hvT' ha₂T']
        refine ⟨rfl, fun o o' ho ho' => ?_, fun e e' he _ => absurd he (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact Step7.subprocedure_smul (d := multiplicity (p : ℤ_[p]) W.Δ) h2 hϖ hΔc hΔc' le_rfl
          hvT hvT' ha₂T ha₂T' hrel₄ hs₄ hr₄ (by omega) hdm

open scoped Classical in
/-- **Step 8 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 8 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step8.intTranslate_determination_of_ne_two (hp2 : p ≠ 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step8.run hϖ hΔ).isOk = (Step8.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step8.run hϖ hΔ = .error o → Step8.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step8.run hϖ hΔ = .ok c → Step8.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step7.intTranslate_determination_of_ne_two hp2 hϖ hΔ hΔ' h
  cases h₇ : Step7.run hϖ hΔ with
  | error o =>
    cases h₇' : Step7.run hϖ hΔ' with
    | error o' =>
      rw [Step8.run_eq_of_step7_error hϖ hΔ h₇, Step8.run_eq_of_step7_error hϖ hΔ' h₇']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
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
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 ((dvd_pow_self _ three_ne_zero).trans hv.b₄)
          (by rw [← hrel₅]; exact (dvd_pow_self _ three_ne_zero).trans hv'.b₄)
          ((dvd_pow_self _ (by norm_num)).trans hv.b₆)
          (by rw [← hrel₅]; exact (dvd_pow_self _ (by norm_num)).trans hv'.b₆)
      have hr₅ : (p : ℤ_[p]) ^ 2 ∣ r₅ :=
        WeierstrassCurve.dvd_sq_r_of_dvd_b₆ PadicInt.prime_p h2 hv.b₂ hv.b₄ hv.b₆
          (by rw [← hrel₅]; exact hv'.b₆) hr₅1
      obtain ⟨γ, hγ⟩ : ∃ γ, quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c') 2
          = (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).shiftBy γ := by
        rw [hrel₅]
        exact Step8.quadratic_smul_of_dvd h2 hϖ hr₅ hv.a₃ hv.a₆ hv.b₂ hv.b₄
          (by rw [← hrel₅]; exact hv'.a₃) (by rw [← hrel₅]; exact hv'.a₆)
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
        subst hc; subst hc'
        exact ⟨r₅, s₅, t₅, hrel₅⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        refine ⟨rfl, ?_⟩
        by_cases hsp : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).toPoly.Splits
        · rw [ite_eq_left hsp, ite_eq_left (hsplits.mpr hsp)]
        · rw [ite_eq_right hsp, ite_eq_right fun hcon => hsp (hsplits.mp hcon)]

open scoped Classical in
/-- **Step 9 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 9 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step9.intTranslate_determination_of_ne_two (hp2 : p ≠ 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step9.run hϖ hΔ).isOk = (Step9.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step9.run hϖ hΔ = .error o → Step9.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step9.run hϖ hΔ = .ok c → Step9.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step8.intTranslate_determination_of_ne_two hp2 hϖ hΔ hΔ' h
  cases h₈ : Step8.run hϖ hΔ with
  | error o =>
    cases h₈' : Step8.run hϖ hΔ' with
    | error o' =>
      rw [Step9.run_eq_of_step8_error hϖ hΔ h₈, Step9.run_eq_of_step8_error hϖ hΔ' h₈']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
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
      have hs₆ : (p : ℤ_[p]) ∣ s₆ := by
        have hx := dvd_s_of_dvd_a₁ (i := 1) (V := Step9.translate (p : ℤ_[p]) c) (r := r₆)
          (s := s₆) (t := t₆) h2 (by simpa using hv.a₁)
          (by rw [← hrel₆]; simpa using hv'.a₁)
        simpa using hx
      have hr₆1 : (p : ℤ_[p]) ∣ r₆ :=
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 ((dvd_pow_self _ three_ne_zero).trans hv.b₄)
          (by rw [← hrel₆]; exact (dvd_pow_self _ three_ne_zero).trans hv'.b₄)
          ((dvd_pow_self _ (by norm_num)).trans hv.b₆)
          (by rw [← hrel₆]; exact (dvd_pow_self _ (by norm_num)).trans hv'.b₆)
      have hr₆ : (p : ℤ_[p]) ^ 2 ∣ r₆ :=
        WeierstrassCurve.dvd_sq_r_of_dvd_b₆ PadicInt.prime_p h2 hv.b₂ hv.b₄
          ((pow_dvd_pow _ (by norm_num : 4 ≤ 5)).trans hv.b₆)
          (by rw [← hrel₆]; exact (pow_dvd_pow _ (by norm_num : 4 ≤ 5)).trans hv'.b₆) hr₆1
      have ht₆ : (p : ℤ_[p]) ^ 3 ∣ t₆ :=
        dvd_t_of_dvd_a₃ h2 hv.a₃ (by rw [← hrel₆]; exact hv'.a₃)
          (by
            rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]
            exact mul_dvd_mul hr₆ (by simpa using hv.a₁))
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
        subst hc; subst hc'
        exact ⟨r₆, s₆, t₆, hrel₆⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 10 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 10 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step10.intTranslate_determination_of_ne_two (hp2 : p ≠ 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step10.run hϖ hΔ).isOk = (Step10.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step10.run hϖ hΔ = .error o → Step10.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step10.run hϖ hΔ = .ok c → Step10.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step9.intTranslate_determination_of_ne_two hp2 hϖ hΔ hΔ' h
  cases h₉ : Step9.run hϖ hΔ with
  | error o =>
    cases h₉' : Step9.run hϖ hΔ' with
    | error o' =>
      rw [Step10.run_eq_of_step9_error hϖ hΔ h₉, Step10.run_eq_of_step9_error hϖ hΔ' h₉']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
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
        dvd_r_of_dvd_b₄_b₆ PadicInt.prime_p h2 ((dvd_pow_self _ (by norm_num)).trans hv.b₄)
          (by rw [← hrel₇]; exact (dvd_pow_self _ (by norm_num)).trans hv'.b₄)
          ((dvd_pow_self _ (by norm_num)).trans hv.b₆)
          (by rw [← hrel₇]; exact (dvd_pow_self _ (by norm_num)).trans hv'.b₆)
      have hr₇ : (p : ℤ_[p]) ^ 2 ∣ r₇ :=
        WeierstrassCurve.dvd_sq_r_of_dvd_b₆ PadicInt.prime_p h2 hv.b₂
          ((pow_dvd_pow _ (by norm_num : 3 ≤ 4)).trans hv.b₄)
          ((pow_dvd_pow _ (by norm_num : 4 ≤ 5)).trans hv.b₆)
          (by rw [← hrel₇]; exact (pow_dvd_pow _ (by norm_num : 4 ≤ 5)).trans hv'.b₆) hr₇1
      have ht₇ : (p : ℤ_[p]) ^ 3 ∣ t₇ :=
        dvd_t_of_dvd_a₃ h2 hv.a₃ (by rw [← hrel₇]; exact hv'.a₃)
          (by
            rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]
            exact mul_dvd_mul hr₇ (by simpa using hv.a₁))
      have hiff : (p : ℤ_[p]) ^ 6 ∣ c'.a₆ ↔ (p : ℤ_[p]) ^ 6 ∣ c.a₆ := by
        rw [hrel₇]
        exact dvd_iff_of_dvd_sub (WeierstrassCurve.pow_six_dvd_sub_a₆_smulOne hr₇ ht₇
          (by simpa using hv.a₁) hv.a₂ hv.a₃ hv.a₄)
      rw [Step10.run_eq_of_step9_ok hϖ hΔ h₉, Step10.run_eq_of_step9_ok hϖ hΔ' h₉']
      by_cases hbr : (p : ℤ_[p]) ^ 6 ∣ c.a₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact ⟨r₇, s₇, t₇, hrel₇⟩
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

/-- **Step 11 agrees on an integral translate, at every odd prime.** On two curves over `ℤ_p` that
are integral translates of one another, Step 11 of Tate's algorithm takes the same branch, returns
the same Kodaira symbol and Tamagawa number when it terminates, and hands on integral translates
when it continues. -/
theorem Step11.intTranslate_determination_of_ne_two (hp2 : p ≠ 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step11.run hϖ hΔ).isOk = (Step11.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step11.run hϖ hΔ = .error o → Step11.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step11.run hϖ hΔ = .ok c → Step11.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨hbranch, hans, hcurve⟩ :=
    Step10.intTranslate_determination_of_ne_two hp2 hϖ hΔ hΔ' h
  cases h₁₀ : Step10.run hϖ hΔ with
  | error o =>
    cases h₁₀' : Step10.run hϖ hΔ' with
    | error o' =>
      rw [Step11.run_eq_of_step10_error hϖ hΔ h₁₀, Step11.run_eq_of_step10_error hϖ hΔ' h₁₀']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
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
        exact Step11.isIntTranslate_translate_of_dvd_b PadicInt.prime_p h2
          (by simpa using hv.a₁) hv.a₂ hv.a₃ hv.a₄ hv.a₆ (by simpa using hv'.a₁) hv'.a₃ hv'.a₄
          hv'.a₆
      rw [Step11.run_eq_of_step10_ok hϖ hΔ h₁₀, Step11.run_eq_of_step10_ok hϖ hΔ' h₁₀']
      refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
      rw [Except.ok.injEq] at hc hc'
      subst hc; subst hc'
      exact hITT

/-- For `p ≠ 2` and every `n`, Tate's algorithm agrees on two integral translates `W`, `W'` with
`v_ϖ(W.Δ) = n`. -/
private theorem run_intTranslate_aux_of_ne_two (hp2 : p ≠ 2) (hϖ : (p : ℤ_[p]) ≠ 0) (n : ℕ) :
    ∀ (W W' : WeierstrassCurve ℤ_[p]) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0),
      multiplicity (p : ℤ_[p]) W.Δ = n → IsIntTranslate W W' →
      (run hϖ hΔ).kodairaSymbol = (run hϖ hΔ').kodairaSymbol ∧
      (run hϖ hΔ).tamagawaNumber = (run hϖ hΔ').tamagawaNumber := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W W' hΔ hΔ' hn hIT
    obtain ⟨hbranch, herror, hcont⟩ :=
      Step11.intTranslate_determination_of_ne_two hp2 hϖ hΔ hΔ' hIT
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

/-- **`RunIntTranslateInvariant p` for every odd prime.** Tate's algorithm returns the same Kodaira
symbol and the same local Tamagawa number on a curve over `ℤ_p` and on any curve obtained from it
by a change of variables with `u = 1`. -/
theorem runIntTranslateInvariant_of_ne_two (hp2 : p ≠ 2) : RunIntTranslateInvariant p := by
  intro W W' hΔ hΔ' hIT
  exact TateAlgorithm.run_intTranslate_aux_of_ne_two hp2 PadicInt.uniformizer_ne_zero
    (multiplicity (p : ℤ_[p]) W.Δ) W W' hΔ hΔ' rfl hIT

/-- **`StratScaleInvariant p` for every odd prime**: the reduction datum of a short model over
`ℤ_p` is unchanged by the dilation `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)`. -/
theorem stratScaleInvariant_of_ne_two (hp2 : p ≠ 2) : StratScaleInvariant p := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hrun : ∀ (W₁ W₂ : WeierstrassCurve ℤ_[p]), W₁ = W₂ → ∀ (h₁ : W₁.Δ ≠ 0) (h₂ : W₂.Δ ≠ 0),
      TateAlgorithm.run hϖ h₁ = TateAlgorithm.run hϖ h₂ := by
    intro W₁ W₂ e h₁ h₂; subst e; rfl
  intro x hx hσx
  have heq : ofShortNF (PadicInt.scaleProdByPPow 4 6 x).1 (PadicInt.scaleProdByPPow 4 6 x).2
      = scaleUp (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    rw [scaleUp_ofShortNF]; rfl
  have hΔσ : (scaleUp (p : ℤ_[p]) (ofShortNF x.1 x.2)).Δ ≠ 0 := by rw [← heq]; exact hσx
  obtain ⟨V, hV⟩ :=
    TateAlgorithm.Step11.run_eq_ok_of_scaleUp hϖ PadicInt.prime_p h2 hΔσ
  have hVΔ : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔσ hV
  have hIT : IsIntTranslate (ofShortNF x.1 x.2) V :=
    TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp_of_prime hϖ PadicInt.prime_p h2 hΔσ hV
  obtain ⟨hk, ht⟩ := runIntTranslateInvariant_of_ne_two hp2 (ofShortNF x.1 x.2) V hx hVΔ hIT
  simp only [strat, Prod.mk.injEq]
  rw [hrun _ _ heq hσx hΔσ, TateAlgorithm.run_eq_of_step11_ok hϖ hΔσ hV hVΔ]
  exact ⟨hk.symm, ht.symm⟩

/-- `StratScaleInvariant p` at `p = 3`. -/
theorem stratScaleInvariant_three (hp3 : p = 3) : StratScaleInvariant p :=
  stratScaleInvariant_of_ne_two (by omega)

end WeierstrassCurve
