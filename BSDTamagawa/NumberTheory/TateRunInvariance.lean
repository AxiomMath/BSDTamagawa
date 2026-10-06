/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.CubicDoubleRoot

/-!
# Invariance of Tate's algorithm under integral translation

For a prime `p ≥ 5`, Tate's algorithm over `ℤ_p` returns the same Kodaira symbol and Tamagawa
number on two Weierstrass curves related by a change of variables `⟨1, r, s, t⟩` with integral `r`,
`s`, `t` (`WeierstrassCurve.IsIntTranslate`). Consequently
`WeierstrassCurve.RunIntTranslateInvariant p` and `WeierstrassCurve.StratScaleInvariant p` hold for
every prime `p ≥ 5`.

Each step of the algorithm takes the same branch on the two curves, returns the same Kodaira symbol
and Tamagawa number when it terminates, and hands on integral translates when it continues; the run
is then treated by recursion on `v_ϖ(Δ)`, which drops by `12` at each pass. The branch conditions
are rewritten as conditions on `c₄`, `c₆` and `Δ`, which are invariant under a `u = 1` change of
variables.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step11.isIntTranslate_translate`: Step 11's rescaling conjugates
  an integral translation into an integral translation.
* `WeierstrassCurve.TateAlgorithm.Step7.dvd_sq_r_of_state`: the relating parameters of the two
  Step-7 translates satisfy `ϖ ∣ s` and `ϖ² ∣ r`.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_smul`: the Step-7 subprocedure returns the
  same answer on an integral translate.
* `WeierstrassCurve.runIntTranslateInvariant_of_five_le`: Tate's algorithm over `ℤ_p` is invariant
  under integral translation for `p ≥ 5`.
* `WeierstrassCurve.stratScaleInvariant_of_five_le`: `WeierstrassCurve.StratScaleInvariant p` holds
  for `p ≥ 5`.

-/

@[expose] public section

universe u

open CommRing Ideal Polynomial

namespace WeierstrassCurve

/-! ### Step 11's rescaling

Step 11 is the one step whose substitution is not a `u = 1` change of variables: it divides the
coefficients by powers of `ϖ`. -/

namespace TateAlgorithm.Step11

variable {R : Type u} [CommRing R] [IsDomain R] {ϖ : R}

/-- A curve whose coefficients have the Step-10 valuations is the dilate of its Step-11
rescaling. -/
theorem scaleUp_translate (hϖ : ϖ ≠ 0) {W : WeierstrassCurve R} (ha₁ : ϖ ∣ W.a₁)
    (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₄ : ϖ ^ 4 ∣ W.a₄) (ha₆ : ϖ ^ 6 ∣ W.a₆) :
    scaleUp ϖ (translate ϖ W) = W := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · exact translate_a₁ hϖ ha₁
  · exact translate_a₂ hϖ ha₂
  · exact translate_a₃ hϖ ha₃
  · exact translate_a₄ hϖ ha₄
  · exact translate_a₆ hϖ ha₆

/-- **Step 11's rescaling carries an integral translate to an integral translate.** If `W` has the
Step-10 valuations and `⟨1, r, s, t⟩ • W` does too, then `ϖ ∣ s`, `ϖ² ∣ r`, `ϖ³ ∣ t`, and the two
rescaled curves differ by `⟨1, r/ϖ², s/ϖ, t/ϖ³⟩`. -/
theorem isIntTranslate_translate [(span {ϖ}).IsMaximal] (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (hϖ : ϖ ≠ 0) {W : WeierstrassCurve R} {r s t : R} (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂)
    (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₄ : ϖ ^ 4 ∣ W.a₄) (ha₆ : ϖ ^ 6 ∣ W.a₆)
    (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • W).a₁)
    (ha₂' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • W).a₂)
    (ha₃' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • W).a₃) :
    IsIntTranslate (translate ϖ W) (translate ϖ ((VariableChange.mk 1 r s t) • W)) := by
  have hbase : scaleUp ϖ (translate ϖ W) = W := scaleUp_translate hϖ ha₁ ha₂ ha₃ ha₄ ha₆
  obtain ⟨hs, hr, ht⟩ :=
    dvd_of_smul_scaleUp h2 h3 (translate ϖ W) (by rw [hbase]; exact ha₁')
      (by rw [hbase]; exact ha₂') (by rw [hbase]; exact ha₃')
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨τ, rfl⟩ := ht
  refine ⟨ρ, σ, τ, ?_⟩
  have key := translate_smul_scaleUp hϖ (translate ϖ W) ρ σ τ
  rw [hbase] at key
  exact key

end TateAlgorithm.Step11

/-! ### The Step-2 and Step-3 branch conditions, in invariant form -/

namespace TateAlgorithm

variable {R : Type u} [CommRing R] {ϖ : R}

/-- **Step 2's branch condition is `ϖ ∣ c₄`.** If `ϖ ∣ Δ`, then `ϖ` divides `b₂` of the Step-2
translate if and only if `ϖ ∣ c₄`. -/
theorem Step2.dvd_translate_b₂_iff_dvd_c₄ [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})]
    {W : WeierstrassCurve R} (hΔ : ϖ ∣ W.Δ) :
    ϖ ∣ (Step2.translate ϖ W).b₂ ↔ ϖ ∣ W.c₄ := by
  refine ⟨fun h => ?_, Step2.dvd_translate_b₂_of_dvd_c₄ hΔ⟩
  have hb₄ : ϖ ∣ (Step2.translate ϖ W).b₄ := by simpa using (Step2.hasValuation_translate hΔ).b₄
  have key : (Step2.translate ϖ W).c₄
      = (Step2.translate ϖ W).b₂ * (Step2.translate ϖ W).b₂ - 24 * (Step2.translate ϖ W).b₄ := by
    rw [WeierstrassCurve.c₄]; ring
  rw [← Step2.translate_c₄ (ϖ := ϖ) (W := W), key]
  exact dvd_sub (h.mul_right _) (hb₄.mul_left 24)

variable {p : ℕ} [Fact p.Prime]

/-- **Step 3's branch condition, in invariant form: `ϖ² ∣ c₆`.** For `p ≥ 5`, a curve over `ℤ_p`
with `p ∣ b₂`, `p ∣ b₄` and `p ∣ a₃` satisfies `p² ∣ a₆ ↔ p² ∣ c₆`, because
`c₆ + 864a₆ = -b₂³ + 36b₂b₄ - 216a₃²` lies in `(p²)` and `864` is a unit. -/
theorem sq_dvd_a₆_iff_sq_dvd_c₆ (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (hb₂ : (p : ℤ_[p]) ∣ V.b₂) (hb₄ : (p : ℤ_[p]) ∣ V.b₄) (ha₃ : (p : ℤ_[p]) ∣ V.a₃) :
    (p : ℤ_[p]) ^ 2 ∣ V.a₆ ↔ (p : ℤ_[p]) ^ 2 ∣ V.c₆ := by
  have key := sq_dvd_c₆_add_mul_a₆_of_dvd hb₂ hb₄ ha₃
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := dvd_sub key (h.mul_left 864)
    rwa [add_sub_cancel_right] at hs
  · have hs := dvd_sub key h
    rw [add_sub_cancel_left] at hs
    rwa [(isUnit_eightSixFour hp).dvd_mul_left] at hs

end TateAlgorithm

end WeierstrassCurve

/-! ### The three invariants of an integral translation

`c₄`, `c₆` and `Δ` are unchanged by a `u = 1` change of variables. -/

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {ϖ : R} {W W' : WeierstrassCurve R}

/-- Two integral translates have the same `c₄`. -/
theorem IsIntTranslate.c₄_eq (h : IsIntTranslate W W') : W'.c₄ = W.c₄ := by
  obtain ⟨r, s, t, rfl⟩ := h
  exact smulOne_c₄ W r s t

/-- Two integral translates have the same `c₆`. -/
theorem IsIntTranslate.c₆_eq (h : IsIntTranslate W W') : W'.c₆ = W.c₆ := by
  obtain ⟨r, s, t, rfl⟩ := h
  exact smulOne_c₆ W r s t

/-- Two integral translates have the same discriminant. -/
theorem IsIntTranslate.Δ_eq (h : IsIntTranslate W W') : W'.Δ = W.Δ := by
  obtain ⟨r, s, t, rfl⟩ := h
  exact smulOne_Δ W r s t

/-! ### Steps 1–6

Each statement below has three conjuncts: the step takes the same branch on the two curves, the
answers agree when it terminates, and the curves handed on are again integral translates. -/

namespace TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **Steps 1 and 2 agree on an integral translate.** For `p ≥ 5`, Step 2 of Tate's algorithm
terminates on `W` exactly when it terminates on an integral translate `W'`, with the same Kodaira
symbol and Tamagawa number, and otherwise hands on integral translates. -/
theorem Step2.intTranslate_determination (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]}
    (h : IsIntTranslate W W') :
    ((Step2.run (p : ℤ_[p]) W).isOk = (Step2.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step2.run (p : ℤ_[p]) W = .error o →
        Step2.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step2.run (p : ℤ_[p]) W = .ok c →
        Step2.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
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
/-- **Step 3 agrees on an integral translate.** For `p ≥ 5`, Step 3 terminates on `W` exactly when
it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number, and
otherwise hands on integral translates. -/
theorem Step3.intTranslate_determination (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]}
    (h : IsIntTranslate W W') :
    ((Step3.run (p : ℤ_[p]) W).isOk = (Step3.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step3.run (p : ℤ_[p]) W = .error o →
        Step3.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step3.run (p : ℤ_[p]) W = .ok c →
        Step3.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  obtain ⟨hbranch, hans, hcurve⟩ := Step2.intTranslate_determination hp h
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
      have hIT : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step2.run_hasValuation hs
      have hv' := Step2.run_hasValuation hs'
      have hc₆ : c'.c₆ = c.c₆ := by rw [Step2.run_c₆ hs', Step2.run_c₆ hs]; exact h.c₆_eq
      have hiff : (p : ℤ_[p]) ^ 2 ∣ c'.a₆ ↔ (p : ℤ_[p]) ^ 2 ∣ c.a₆ := by
        rw [sq_dvd_a₆_iff_sq_dvd_c₆ hp (by simpa using hv'.b₂) (by simpa using hv'.b₄)
            (by simpa using hv'.a₃),
          sq_dvd_a₆_iff_sq_dvd_c₆ hp (by simpa using hv.b₂) (by simpa using hv.b₄)
            (by simpa using hv.a₃), hc₆]
      rw [Step3.run_eq_of_step2_ok (p : ℤ_[p]) hs, Step3.run_eq_of_step2_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 2 ∣ c.a₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact hIT
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 4 agrees on an integral translate.** For `p ≥ 5`, Step 4 terminates on `W` exactly when
it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number, and
otherwise hands on integral translates. -/
theorem Step4.intTranslate_determination (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]}
    (h : IsIntTranslate W W') :
    ((Step4.run (p : ℤ_[p]) W).isOk = (Step4.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step4.run (p : ℤ_[p]) W = .error o →
        Step4.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step4.run (p : ℤ_[p]) W = .ok c →
        Step4.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  obtain ⟨hbranch, hans, hcurve⟩ := Step3.intTranslate_determination hp h
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
      have hIT : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step3.run_hasValuation hs
      have hv' := Step3.run_hasValuation hs'
      have hc₄ : c'.c₄ = c.c₄ := by rw [Step3.run_c₄ hs', Step3.run_c₄ hs]; exact h.c₄_eq
      have hiff : (p : ℤ_[p]) ^ 3 ∣ c'.b₈ ↔ (p : ℤ_[p]) ^ 3 ∣ c.b₈ := by
        rw [cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv'.b₂) hv'.b₆,
          cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv.b₂) hv.b₆, hc₄]
      rw [Step4.run_eq_of_step3_ok (p : ℤ_[p]) hs, Step4.run_eq_of_step3_ok (p : ℤ_[p]) hs']
      by_cases hbr : (p : ℤ_[p]) ^ 3 ∣ c.b₈
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact hIT
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 5 agrees on an integral translate.** For `p ≥ 5`, Step 5 terminates on `W` exactly when
it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number, and
otherwise hands on integral translates. -/
theorem Step5.intTranslate_determination (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]}
    (h : IsIntTranslate W W') :
    ((Step5.run (p : ℤ_[p]) W).isOk = (Step5.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step5.run (p : ℤ_[p]) W = .error o →
        Step5.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step5.run (p : ℤ_[p]) W = .ok c →
        Step5.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  obtain ⟨hbranch, hans, hcurve⟩ := Step4.intTranslate_determination hp h
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
      have hIT : IsIntTranslate c c' := hcurve _ _ hs hs'
      have hv := Step4.run_hasValuation hϖ hs
      have hv' := Step4.run_hasValuation hϖ hs'
      have hc₆ : c'.c₆ = c.c₆ := by rw [Step4.run_c₆ hs', Step4.run_c₆ hs]; exact h.c₆_eq
      have hiff : (p : ℤ_[p]) ^ 3 ∣ c'.b₆ ↔ (p : ℤ_[p]) ^ 3 ∣ c.b₆ := by
        rw [cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv'.b₂) hv'.b₄,
          cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv.b₂) hv.b₄, hc₆]
      obtain ⟨r₂, s₂, t₂, hrel⟩ := hIT
      have hquad : ∃ γ, quadratic (p : ℤ_[p]) c' 1 = (quadratic (p : ℤ_[p]) c 1).shiftBy γ := by
        rw [hrel]
        exact Step5.quadratic_smul h2 h3 hϖ (by simpa using hv.a₃) hv.a₆ (by simpa using hv.b₂)
          hv.b₄ (by rw [← hrel]; simpa using hv'.a₃) (by rw [← hrel]; exact hv'.a₆)
          (by rw [← hrel]; simpa using hv'.b₂)
      obtain ⟨γ, hγ⟩ := hquad
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

open scoped Classical in
/-- **Step 6 agrees on an integral translate.** For `p ≥ 5`, Step 6 terminates on `W` exactly when
it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number, and
otherwise hands on integral translates. -/
theorem Step6.intTranslate_determination (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]}
    (h : IsIntTranslate W W') :
    ((Step6.run (p : ℤ_[p]) W).isOk = (Step6.run (p : ℤ_[p]) W').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step6.run (p : ℤ_[p]) W = .error o →
        Step6.run (p : ℤ_[p]) W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step6.run (p : ℤ_[p]) W = .ok c →
        Step6.run (p : ℤ_[p]) W' = .ok c' → IsIntTranslate c c') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  obtain ⟨hbranch, hans, hcurve⟩ := Step5.intTranslate_determination hp h
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
      have hITT : IsIntTranslate (Step6.translate (p : ℤ_[p]) c)
          (Step6.translate (p : ℤ_[p]) c') :=
        (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
      have hΔeq : (Step6.translate (p : ℤ_[p]) c').Δ = (Step6.translate (p : ℤ_[p]) c).Δ := by
        rw [Step6.translate_Δ, Step6.translate_Δ, Step5.run_Δ hs, Step5.run_Δ hs']
        exact h.Δ_eq
      have hiff : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c') 1 1).HasDoubleRoot
          ↔ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) c) 1 1).HasDoubleRoot := by
        rw [hasDoubleRoot_iff_pow_dvd_Δ hp (by simpa using hv'.a₁) (by simpa using hv'.a₂)
            hv'.a₃ hv'.a₄ hv'.a₆,
          hasDoubleRoot_iff_pow_dvd_Δ hp (by simpa using hv.a₁) (by simpa using hv.a₂)
            hv.a₃ hv.a₄ hv.a₆, hΔeq]
      obtain ⟨r₃, s₃, t₃, hrel₃⟩ := hITT
      have hcard := Step6.card_roots_smul (V := Step6.translate (p : ℤ_[p]) c) (r := r₃)
        (s := s₃) (t := t₃) h2 h3 hϖ (by simpa using hv.a₁) (by simpa using hv.a₂)
        hv.a₃ hv.a₄ hv.a₆ (by rw [← hrel₃]; simpa using hv'.a₁)
        (by rw [← hrel₃]; simpa using hv'.a₂) (by rw [← hrel₃]; exact hv'.a₃)
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

end TateAlgorithm

end WeierstrassCurve

/-! ### Step 7's subprocedure -/

namespace Cubic

/-- `Cubic.roots` is the root multiset of the associated polynomial. -/
theorem roots_eq_toPoly_roots {k : Type u} [Field k] (P : Cubic k) : P.roots = P.toPoly.roots :=
  rfl

end Cubic

namespace WeierstrassCurve.TateAlgorithm.Step7

variable {R : Type u} [CommRing R] {ϖ : R}

/-- **The subprocedure's parameter invariant holds on entry.** If two curves related by
`⟨1, r, s, t⟩` both satisfy `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄`, `ϖ⁴ ∣ a₆` and `¬ ϖ² ∣ a₂`, then
`ϖ ∣ s` and `ϖ² ∣ r`. -/
theorem dvd_sq_r_of_state [IsDomain R] (hprime : Prime ϖ) (h2 : IsUnit (2 : R))
    (h3 : IsUnit (3 : R)) {V : WeierstrassCurve R} {r s t : R} (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂)
    (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₄ : ϖ ^ 3 ∣ V.a₄) (ha₆ : ϖ ^ 4 ∣ V.a₆) (ha₂n : ¬ ϖ ^ 2 ∣ V.a₂)
    (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₁)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ϖ ∣ s ∧ ϖ ^ 2 ∣ r := by
  have hϖ : ϖ ≠ 0 := hprime.ne_zero
  have hs : ϖ ∣ s := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using ha₁) (by simpa using ha₁')
  have hr1 : ϖ ∣ r := by
    simpa using dvd_r_of_dvd_a₂ (j := 1) h3 (by simpa using ha₂) (by simpa using ha₂')
      (by simpa using hs.mul_right V.a₁) (by simpa using dvd_pow hs two_ne_zero)
  have ht2 : ϖ ^ 2 ∣ t :=
    dvd_t_of_dvd_a₃ h2 ha₃ ha₃' (by rw [pow_two]; exact mul_dvd_mul hr1 ha₁)
  refine ⟨hs, ?_⟩
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr1
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht2
  have k4 : ϖ ∣ ρ * (2 * α₂ + 3 * ρ) := by
    have hsub : ϖ ^ 3 ∣ ϖ ^ 2 * (ρ * (2 * α₂ + 3 * ρ)) := by
      have hx := dvd_sub ha₄' (dvd_mul_right (ϖ ^ 3)
        (α₄ - σ * α₃ - τ * α₁ - ρ * σ * α₁ - 2 * σ * τ))
      rwa [show ((VariableChange.mk 1 r s t) • V).a₄
          - ϖ ^ 3 * (α₄ - σ * α₃ - τ * α₁ - ρ * σ * α₁ - 2 * σ * τ)
          = ϖ ^ 2 * (ρ * (2 * α₂ + 3 * ρ)) from by
        rw [smulOne_a₄, e₁, e₂, e₃, e₄, hρ, hσ, hτ]; ring] at hx
    rwa [show (ϖ : R) ^ 3 = ϖ ^ 2 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ)] at hsub
  have k6 : ϖ ∣ ρ * (ρ * (α₂ + ρ)) := by
    have hsub : ϖ ^ 4 ∣ ϖ ^ 3 * (ρ * (ρ * (α₂ + ρ))) := by
      have hx := dvd_sub ha₆' (dvd_mul_right (ϖ ^ 4)
        (α₆ + ρ * α₄ - τ * α₃ - τ ^ 2 - ρ * τ * α₁))
      rwa [show ((VariableChange.mk 1 r s t) • V).a₆
          - ϖ ^ 4 * (α₆ + ρ * α₄ - τ * α₃ - τ ^ 2 - ρ * τ * α₁)
          = ϖ ^ 3 * (ρ * (ρ * (α₂ + ρ))) from by
        rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring] at hx
    rwa [show (ϖ : R) ^ 4 = ϖ ^ 3 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 3 hϖ)] at hsub
  by_contra hcon
  have hρnd : ¬ ϖ ∣ ρ := by
    rintro ⟨ρ', hρ'⟩
    exact hcon ⟨ρ', by rw [hρ, hρ']; ring⟩
  have hk1 : ϖ ∣ 2 * α₂ + 3 * ρ := (hprime.dvd_mul.mp k4).resolve_left hρnd
  have hk2 : ϖ ∣ α₂ + ρ :=
    (hprime.dvd_mul.mp ((hprime.dvd_mul.mp k6).resolve_left hρnd)).resolve_left hρnd
  have hα₂ : ϖ ∣ α₂ := by
    have hx := dvd_sub hk1 (hk2.mul_left 3)
    rw [show 2 * α₂ + 3 * ρ - 3 * (α₂ + ρ) = -α₂ from by ring] at hx
    exact dvd_neg.mp hx
  obtain ⟨α₂', hα₂'⟩ := hα₂
  exact ha₂n ⟨α₂', by rw [e₂, hα₂']; ring⟩

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]

/-- **Step 7's subprocedure returns the same answer on an integral translate.** If
`V' = ⟨1, r, s, t⟩ • V` with `ϖ ∣ s` and `ϖ ^ n ∣ r`, then the subprocedure entered at level `n`
returns the same Kodaira symbol and Tamagawa number on `V` and `V'`. -/
theorem subprocedure_smul (h2 : IsUnit (2 : R)) (hϖ : ϖ ≠ 0) {d n : ℕ}
    {V V' : WeierstrassCurve R} {r s t : R}
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv b₂' b₄' b₆' b₈' c₄' c₆' Δv' : ℕ} (hΔ : V.Δ ≠ 0) (hΔ' : V'.Δ ≠ 0)
    (hn : 2 ≤ n) (hW : HasValuation ϖ V ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (hW' : HasValuation ϖ V' ⟨1, 1, n, n + 1, 2 * n, b₂', b₄', b₆', b₈', c₄', c₆', Δv'⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ V.a₂) (ha₂' : ¬ϖ ^ 2 ∣ V'.a₂)
    (hVV' : V' = (VariableChange.mk 1 r s t) • V) (hs : ϖ ∣ s) (hr : ϖ ^ n ∣ r)
    (hd : 2 * n + 2 ≤ d) (hdm : multiplicity ϖ V.Δ ≤ d) :
    (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol
        = (subprocedure hϖ hΔ' hn hW' ha₂').kodairaSymbol ∧
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
        = (subprocedure hϖ hΔ' hn hW' ha₂').tamagawaNumber := by
  classical
  have hb₂V : ϖ ∣ V.b₂ := by
    obtain ⟨x, hx⟩ := hW.a₁
    obtain ⟨y, hy⟩ := hW.a₂
    exact ⟨ϖ * x ^ 2 + 4 * y, by rw [WeierstrassCurve.b₂, hx, hy]; ring⟩
  have hb₄V : ϖ ^ (n + 1) ∣ V.b₄ := by
    obtain ⟨x, hx⟩ := hW.a₁
    obtain ⟨z, hz⟩ := hW.a₃
    obtain ⟨w, hw⟩ := hW.a₄
    exact ⟨2 * w + x * z, by rw [WeierstrassCurve.b₄, hx, hz, hw]; ring⟩
  obtain ⟨γY, hγY⟩ : ∃ γ, quadratic ϖ V' n = (quadratic ϖ V n).shiftBy γ := by
    rw [hVV']
    exact quadratic_smul h2 hϖ (by omega) hr hW.a₃ hW.a₆ hb₂V hb₄V
      (by rw [← hVV']; exact hW'.a₃) (by rw [← hVV']; exact hW'.a₆)
  by_cases hY : (quadratic ϖ V n).HasDoubleRoot
  · have hY' : (quadratic ϖ V' n).HasDoubleRoot := by
      rw [hγY]; exact (Cubic.hasDoubleRoot_shiftBy _ _).mpr hY
    have hvY := hasValuation_translateY hn hϖ hW hY
    have hvY' := hasValuation_translateY hn hϖ hW' hY'
    have ha₂Y : ¬ϖ ^ 2 ∣ (translateY ϖ V n).a₂ := not_dvd_translateY_a₂ n ha₂
    have ha₂Y' : ¬ϖ ^ 2 ∣ (translateY ϖ V' n).a₂ := not_dvd_translateY_a₂ n ha₂'
    obtain ⟨t₂, hYY⟩ : ∃ t₂, translateY ϖ V' n
        = (VariableChange.mk 1 r s t₂) • translateY ϖ V n := by
      subst hVV'
      exact ⟨_, translateY_smul V r s t n⟩
    have ha₃Y' : ϖ ^ (n + 1) ∣ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n).a₃ := by
      rw [← hYY]; exact hvY'.a₃
    have ht₂ : ϖ ^ (n + 1) ∣ t₂ :=
      dvd_t_of_dvd_a₃_of_dvd_r h2 hr (by simpa using hvY.a₁) hvY.a₃ ha₃Y'
    have hcubY : cubic ϖ (translateY ϖ V' n) 0 n
        = (cubic ϖ (translateY ϖ V n) 0 n).shiftBy (mod ϖ (div r (ϖ ^ n))) := by
      rw [hYY]
      exact cubic_smul hϖ hn hs hr ht₂ (by simpa using hvY.a₁) (by simpa using hvY.a₂)
        hvY.a₃ hvY.a₄ hvY.a₆
    by_cases hX : (cubic ϖ (translateY ϖ V n) 0 n).HasDoubleRoot
    · have hX' : (cubic ϖ (translateY ϖ V' n) 0 n).HasDoubleRoot := by
        rw [hcubY]; exact (Cubic.hasDoubleRoot_shiftBy _ _).mpr hX
      have hvX := hasValuation_translateX hn hϖ hvY ha₂Y hX
      have hvX' := hasValuation_translateX hn hϖ hvY' ha₂Y' hX'
      have hΔX : (translateX ϖ (translateY ϖ V n) n).Δ ≠ 0 := by
        rw [translateX_Δ, translateY_Δ]; exact hΔ
      have hΔX' : (translateX ϖ (translateY ϖ V' n) n).Δ ≠ 0 := by
        rw [translateX_Δ, translateY_Δ]; exact hΔ'
      have ha₂X := not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y
      have ha₂X' := not_dvd_translateX_a₂ hn hϖ hvY'.a₂ ha₂Y'
      have hXX : translateX ϖ (translateY ϖ V' n) n
          = (VariableChange.mk 1
              (r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n) n
                - rX ϖ (translateY ϖ V n) n)) s
              (t₂ + ϖ ^ n * rX ϖ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n) n * s))
            • translateX ϖ (translateY ϖ V n) n := by
        rw [hYY]; exact translateX_smul (translateY ϖ V n) r s t₂ n
      have hr₃ : ϖ ^ (n + 1) ∣
          r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n) n
            - rX ϖ (translateY ϖ V n) n) :=
        dvd_r_translateX_smul h2 hϖ hn hs hr ht₂ (by simpa using hvY.a₁)
          (by simpa using hvY.a₂) hvY.a₃ hvY.a₄ hvY.a₆ ha₂Y
      have hΔ₅ : 2 * n + 5 ≤ multiplicity ϖ V.Δ := by
        refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
        have hdvd := hvX.Δ
        rwa [translateX_Δ, translateY_Δ] at hdvd
      have hdmX : multiplicity ϖ (translateX ϖ (translateY ϖ V n) n).Δ ≤ d := by
        rw [translateX_Δ, translateY_Δ]; exact hdm
      rw [subprocedure_eq_subprocedure hϖ hΔ hn hW ha₂ hY hX hΔX (by omega) hvX ha₂X,
        subprocedure_eq_subprocedure hϖ hΔ' hn hW' ha₂' hY' hX' hΔX' (by omega) hvX' ha₂X']
      exact subprocedure_smul h2 hϖ hΔX hΔX' (by omega) hvX hvX' ha₂X ha₂X' hXX hs hr₃
        (by omega) hdmX
    · have hX' : ¬(cubic ϖ (translateY ϖ V' n) 0 n).HasDoubleRoot := by
        rw [hcubY]; exact fun hc => hX ((Cubic.hasDoubleRoot_shiftBy _ _).mp hc)
      have hcard : (cubic ϖ (translateY ϖ V' n) 0 n).roots.toFinset.card
          = (cubic ϖ (translateY ϖ V n) 0 n).roots.toFinset.card := by
        rw [Cubic.roots_eq_toPoly_roots, Cubic.roots_eq_toPoly_roots, hcubY,
          Cubic.card_toFinset_roots_shiftBy]
      rw [subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX,
        subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ' hn hW' ha₂' hY' hX']
      exact ⟨rfl, by simp only [hcard]⟩
  · have hY' : ¬(quadratic ϖ V' n).HasDoubleRoot := by
      rw [hγY]; exact fun hc => hY ((Cubic.hasDoubleRoot_shiftBy _ _).mp hc)
    have hcard : (quadratic ϖ V' n).roots.toFinset.card
        = (quadratic ϖ V n).roots.toFinset.card := by
      rw [Cubic.roots_eq_toPoly_roots, Cubic.roots_eq_toPoly_roots, hγY,
        Cubic.card_toFinset_roots_shiftBy]
    rw [subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY,
      subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ' hn hW' ha₂' hY']
    exact ⟨rfl, by simp only [hcard]⟩
termination_by d - n
decreasing_by omega

end WeierstrassCurve.TateAlgorithm.Step7

/-! ### Steps 7–11, and the top-level recursion -/

namespace WeierstrassCurve.TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-- **Step 7 agrees on an integral translate.** For `p ≥ 5`, Step 7 of Tate's algorithm terminates
on `W` exactly when it terminates on an integral translate `W'`, with the same Kodaira symbol and
Tamagawa number, and otherwise hands on integral translates. -/
theorem Step7.intTranslate_determination (hp : 5 ≤ p) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step7.run hϖ hΔ).isOk = (Step7.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step7.run hϖ hΔ = .error o → Step7.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step7.run hϖ hΔ = .ok c → Step7.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  obtain ⟨hbranch, hans, hcurve⟩ := Step6.intTranslate_determination hp h
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
      have hc₄ : c'.c₄ = c.c₄ := by rw [Step6.run_c₄ h₆', Step6.run_c₄ h₆]; exact h.c₄_eq
      have htriff : (cubic (p : ℤ_[p]) c' 1 1).HasTripleRoot
          ↔ (cubic (p : ℤ_[p]) c 1 1).HasTripleRoot := by
        rw [hasTripleRoot_iff_cb_dvd_c₄ hp (by simpa using hvc'.a₁) (by simpa using hvc'.a₂)
            hvc'.a₃ hvc'.a₄,
          hasTripleRoot_iff_cb_dvd_c₄ hp (by simpa using hvc.a₁) (by simpa using hvc.a₂)
            hvc.a₃ hvc.a₄, hc₄]
      by_cases htr : (cubic (p : ℤ_[p]) c 1 1).HasTripleRoot
      · rw [Step7.run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ h₆ htr,
          Step7.run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ' h₆' (htriff.mpr htr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun e e' he he' => ?_⟩
        rw [Except.ok.injEq] at he he'
        subst he; subst he'
        exact hIT
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
          (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
        obtain ⟨hs₄, hr₄⟩ := Step7.dvd_sq_r_of_state PadicInt.prime_p h2 h3
          (by simpa using hvT.a₁) (by simpa using hvT.a₂) hvT.a₃ hvT.a₄ hvT.a₆ ha₂T
          (by rw [← hrel₄]; simpa using hvT'.a₁) (by rw [← hrel₄]; simpa using hvT'.a₂)
          (by rw [← hrel₄]; exact hvT'.a₃) (by rw [← hrel₄]; exact hvT'.a₄)
          (by rw [← hrel₄]; exact hvT'.a₆)
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
/-- **Step 8 agrees on an integral translate.** For `p ≥ 5`, Step 8 terminates on `W` exactly when
it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number, and
otherwise hands on integral translates. -/
theorem Step8.intTranslate_determination (hp : 5 ≤ p) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step8.run hϖ hΔ).isOk = (Step8.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step8.run hϖ hΔ = .error o → Step8.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step8.run hϖ hΔ = .ok c → Step8.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  obtain ⟨hbranch, hans, hcurve⟩ := Step7.intTranslate_determination hp hϖ hΔ hΔ' h
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
      have hc₆ : (Step8.translate (p : ℤ_[p]) c').c₆ = (Step8.translate (p : ℤ_[p]) c).c₆ := by
        rw [Step8.translate_c₆, Step8.translate_c₆, Step7.run_c₆ hϖ hΔ' h₇',
          Step7.run_c₆ hϖ hΔ h₇]
        exact h.c₆_eq
      have hiff : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c') 2).HasDoubleRoot
          ↔ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).HasDoubleRoot := by
        rw [quadratic_hasDoubleRoot_iff hp hv'.a₃ hv'.a₆ hv'.b₂ hv'.b₄,
          quadratic_hasDoubleRoot_iff hp hv.a₃ hv.a₆ hv.b₂ hv.b₄, hc₆]
      have hIT1 : IsIntTranslate c (Step8.translate (p : ℤ_[p]) c) := ⟨_, 0, 0, rfl⟩
      have hIT2 : IsIntTranslate c' (Step8.translate (p : ℤ_[p]) c') := ⟨_, 0, 0, rfl⟩
      obtain ⟨r₅, s₅, t₅, hrel₅⟩ :
          IsIntTranslate (Step8.translate (p : ℤ_[p]) c) (Step8.translate (p : ℤ_[p]) c') :=
        (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
      obtain ⟨γ, hγ⟩ : ∃ γ, quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c') 2
          = (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) c) 2).shiftBy γ := by
        rw [hrel₅]
        exact Step8.quadratic_smul h2 h3 hϖ (by simpa using hv.a₁) hv.a₂ hv.a₃ hv.a₆ hv.b₂ hv.b₄
          (by rw [← hrel₅]; simpa using hv'.a₁) (by rw [← hrel₅]; exact hv'.a₂)
          (by rw [← hrel₅]; exact hv'.a₃) (by rw [← hrel₅]; exact hv'.a₆)
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
/-- **Step 9 agrees on an integral translate.** For `p ≥ 5`, Step 9 terminates on `W` exactly when
it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number, and
otherwise hands on integral translates. -/
theorem Step9.intTranslate_determination (hp : 5 ≤ p) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step9.run hϖ hΔ).isOk = (Step9.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step9.run hϖ hΔ = .error o → Step9.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step9.run hϖ hΔ = .ok c → Step9.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  obtain ⟨hbranch, hans, hcurve⟩ := Step8.intTranslate_determination hp hϖ hΔ hΔ' h
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
      have hc₄ : (Step9.translate (p : ℤ_[p]) c').c₄ = (Step9.translate (p : ℤ_[p]) c).c₄ := by
        rw [Step9.translate, Step9.translate, Step7.translateY_c₄, Step7.translateY_c₄,
          Step8.run_c₄ hϖ hΔ' h₈', Step8.run_c₄ hϖ hΔ h₈]
        exact h.c₄_eq
      have hiff : (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) c').a₄
          ↔ (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) c).a₄ := by
        rw [pow_four_dvd_a₄_iff hp (by simpa using hv'.a₁) hv'.a₃ hv'.b₂,
          pow_four_dvd_a₄_iff hp (by simpa using hv.a₁) hv.a₃ hv.b₂, hc₄]
      have hIT1 : IsIntTranslate c (Step9.translate (p : ℤ_[p]) c) := ⟨0, 0, _, rfl⟩
      have hIT2 : IsIntTranslate c' (Step9.translate (p : ℤ_[p]) c') := ⟨0, 0, _, rfl⟩
      have hITT : IsIntTranslate (Step9.translate (p : ℤ_[p]) c)
          (Step9.translate (p : ℤ_[p]) c') :=
        (IsIntTranslate.symm' hIT1).trans (hIT.trans hIT2)
      rw [Step9.run_eq_of_step8_ok hϖ hΔ h₈, Step9.run_eq_of_step8_ok hϖ hΔ' h₈']
      by_cases hbr : (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) c).a₄
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact hITT
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 10 agrees on an integral translate.** For `p ≥ 5`, Step 10 terminates on `W` exactly
when it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number,
and otherwise hands on integral translates. -/
theorem Step10.intTranslate_determination (hp : 5 ≤ p) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step10.run hϖ hΔ).isOk = (Step10.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step10.run hϖ hΔ = .error o → Step10.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step10.run hϖ hΔ = .ok c → Step10.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  obtain ⟨hbranch, hans, hcurve⟩ := Step9.intTranslate_determination hp hϖ hΔ hΔ' h
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
      have hIT : IsIntTranslate c c' := hcurve _ _ h₉ h₉'
      have hv := Step9.run_hasValuation hϖ hΔ h₉
      have hv' := Step9.run_hasValuation hϖ hΔ' h₉'
      have hc₆ : c'.c₆ = c.c₆ := by
        rw [Step9.run_c₆ hϖ hΔ' h₉', Step9.run_c₆ hϖ hΔ h₉]; exact h.c₆_eq
      have hiff : (p : ℤ_[p]) ^ 6 ∣ c'.a₆ ↔ (p : ℤ_[p]) ^ 6 ∣ c.a₆ := by
        rw [pow_six_dvd_a₆_iff hp hv'.a₃ hv'.b₂ hv'.b₄,
          pow_six_dvd_a₆_iff hp hv.a₃ hv.b₂ hv.b₄, hc₆]
      rw [Step10.run_eq_of_step9_ok hϖ hΔ h₉, Step10.run_eq_of_step9_ok hϖ hΔ' h₉']
      by_cases hbr : (p : ℤ_[p]) ^ 6 ∣ c.a₆
      · rw [ite_eq_left hbr, ite_eq_left (hiff.mpr hbr)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact hIT
      · rw [ite_eq_right hbr, ite_eq_right fun hcon => hbr (hiff.mp hcon)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

/-- **Step 11 agrees on an integral translate.** For `p ≥ 5`, Step 11 terminates on `W` exactly
when it terminates on an integral translate `W'`, with the same Kodaira symbol and Tamagawa number,
and otherwise hands on integral translates. -/
theorem Step11.intTranslate_determination (hp : 5 ≤ p) (hϖ : (p : ℤ_[p]) ≠ 0)
    {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (h : IsIntTranslate W W') :
    ((Step11.run hϖ hΔ).isOk = (Step11.run hϖ hΔ').isOk) ∧
    (∀ o o' : Output ℤ_[p], Step11.run hϖ hΔ = .error o → Step11.run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve ℤ_[p], Step11.run hϖ hΔ = .ok c → Step11.run hϖ hΔ' = .ok c' →
      IsIntTranslate c c') := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  obtain ⟨hbranch, hans, hcurve⟩ := Step10.intTranslate_determination hp hϖ hΔ hΔ' h
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
        exact Step11.isIntTranslate_translate h2 h3 hϖ (by simpa using hv.a₁) hv.a₂ hv.a₃ hv.a₄
          hv.a₆ (by simpa using hv'.a₁) hv'.a₂ hv'.a₃
      rw [Step11.run_eq_of_step10_ok hϖ hΔ h₁₀, Step11.run_eq_of_step10_ok hϖ hΔ' h₁₀']
      refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
      rw [Except.ok.injEq] at hc hc'
      subst hc; subst hc'
      exact hITT

/-- For `p ≥ 5` and integral translates `W`, `W'` with `v_ϖ(W.Δ) = n`, Tate's algorithm returns the
same Kodaira symbol and Tamagawa number on `W` and `W'`. -/
private theorem run_intTranslate_aux (hp : 5 ≤ p) (hϖ : (p : ℤ_[p]) ≠ 0) (n : ℕ) :
    ∀ (W W' : WeierstrassCurve ℤ_[p]) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0),
      multiplicity (p : ℤ_[p]) W.Δ = n → IsIntTranslate W W' →
      (run hϖ hΔ).kodairaSymbol = (run hϖ hΔ').kodairaSymbol ∧
      (run hϖ hΔ).tamagawaNumber = (run hϖ hΔ').tamagawaNumber := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W W' hΔ hΔ' hn hIT
    obtain ⟨hbranch, herror, hcont⟩ := Step11.intTranslate_determination hp hϖ hΔ hΔ' hIT
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

/-- **`RunIntTranslateInvariant p` for every prime `p ≥ 5`.** Tate's algorithm returns the same
Kodaira symbol and the same local Tamagawa number on a curve over `ℤ_p` and on any curve obtained
from it by a change of variables with `u = 1`. -/
theorem runIntTranslateInvariant_of_five_le (hp : 5 ≤ p) : RunIntTranslateInvariant p := by
  intro W W' hΔ hΔ' hIT
  exact TateAlgorithm.run_intTranslate_aux hp PadicInt.uniformizer_ne_zero
    (multiplicity (p : ℤ_[p]) W.Δ) W W' hΔ hΔ' rfl hIT

/-- **`StratScaleInvariant p` for every prime `p ≥ 5`.** The reduction datum of a short model over
`ℤ_p` is unchanged by the dilation `(a₄, a₆) ↦ (p⁴a₄, p⁶a₆)`. -/
theorem stratScaleInvariant_of_five_le (hp : 5 ≤ p) : StratScaleInvariant p :=
  stratScaleInvariant_of_runIntTranslateInvariant hp (runIntTranslateInvariant_of_five_le hp)

end WeierstrassCurve
