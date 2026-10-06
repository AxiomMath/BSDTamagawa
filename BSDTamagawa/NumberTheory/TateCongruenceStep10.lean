/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep9

/-!
# Finite determination of Step 10 of Tate's algorithm

Step 10 of Tate's algorithm performs no change of variables: it runs Step 9 and, if Step 9
continues with a curve `c`, tests `ϖ ^ 6 ∣ c.a₆`, continuing with `c` when the test holds and
terminating with Kodaira symbol `II*` and local Tamagawa number `1` otherwise. We show that Step 10
is determined by the coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Here `Except.ok c`
means that the algorithm continues with `c`, and `Except.error o` that it terminates with answer
`o`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step10.ten_le_multiplicity_Δ`: if Step 9 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 10`.
* `WeierstrassCurve.TateAlgorithm.Step10.run_eq_of_step9_error`,
  `WeierstrassCurve.TateAlgorithm.Step10.run_eq_of_step9_ok`: `Step10.run` in terms of the outcome
  of Step 9.
* `WeierstrassCurve.TateAlgorithm.Step10.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 10 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.
-/

@[expose] public section

universe u

open CommRing Ideal

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {W W' : WeierstrassCurve R}

namespace TateAlgorithm.Step10

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]

/-! ### The branch structure of Step 10 -/

/-- Unfolding of Step 10 in the case where Step 9 terminates: Step 10 passes the answer through
unchanged. -/
theorem run_eq_of_step9_error (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {o : Output R}
    (h : Step9.run hϖ hΔ = .error o) : run hϖ hΔ = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 10 in the case where Step 9 continues with the curve `c`: Step 10 tests
whether `ϖ ^ 6` divides `c.a₆`, continuing (`Except.ok`) with the very same curve `c` when it does
and terminating (`Except.error`) with Kodaira symbol `II*` and local Tamagawa number `1` when it
does not. -/
theorem run_eq_of_step9_ok (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step9.run hϖ hΔ = .ok c) :
    run hϖ hΔ = if ϖ ^ 6 ∣ c.a₆ then .ok c else .error ⟨c, .II!, 1⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 10 -/

/-- If Step 9 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 10`. -/
theorem ten_le_multiplicity_Δ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step9.run hϖ hΔ = .ok c) : 10 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step9.run_Δ hϖ hΔ h]
  exact (Step9.run_hasValuation hϖ hΔ h).Δ

/-- **Step 10 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step10.run hϖ hΔ` and `Step10.run hϖ hΔ'` have the same `Except.isOk` flag.
2. If both terminate (`Except.error`), the two answers have the same Kodaira symbol and the same
   local Tamagawa number.
3. If both continue (`Except.ok`), the two curves returned are congruent to depth `v_ϖ(W.Δ)`. -/
theorem finite_determination (hϖ : ϖ ≠ 0) {W W' : WeierstrassCurve R} (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W') :
    ((run hϖ hΔ).isOk = (run hϖ hΔ').isOk) ∧
    (∀ o o' : Output R, run hϖ hΔ = .error o → run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve R, run hϖ hΔ = .ok c → run hϖ hΔ' = .ok c' →
      CongrDepth ϖ (multiplicity ϖ W.Δ) c c') := by
  obtain ⟨hbranch, herror, hcont⟩ := Step9.finite_determination hϖ hΔ hΔ' h
  cases h₉ : Step9.run hϖ hΔ with
  | error o =>
    cases h₉' : Step9.run hϖ hΔ' with
    | error o' =>
      rw [run_eq_of_step9_error hϖ hΔ h₉, run_eq_of_step9_error hϖ hΔ' h₉']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₉ h₉'
    | ok c' => rw [h₉, h₉'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₉' : Step9.run hϖ hΔ' with
    | error o' => rw [h₉, h₉'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₉ h₉'
      have hiff : ϖ ^ 6 ∣ c.a₆ ↔ ϖ ^ 6 ∣ c'.a₆ :=
        (hcong.mono (le_trans (by norm_num) (ten_le_multiplicity_Δ hϖ hΔ h₉))).dvd_pow_a₆_iff
      rw [run_eq_of_step9_ok hϖ hΔ h₉, run_eq_of_step9_ok hϖ hΔ' h₉']
      by_cases ha₆ : ϖ ^ 6 ∣ c.a₆
      · rw [ite_eq_left ha₆, ite_eq_left (hiff.mp ha₆)]
        refine ⟨rfl, fun p p' hp _ => absurd hp (by simp), fun d d' hd hd' => ?_⟩
        rw [Except.ok.injEq] at hd hd'
        subst hd; subst hd'
        exact hcong
      · rw [ite_eq_right ha₆, ite_eq_right fun hc => ha₆ (hiff.mpr hc)]
        refine ⟨rfl, fun p p' hp hp' => ?_, fun d d' hd _ => absurd hd (by simp)⟩
        rw [Except.error.injEq] at hp hp'
        subst hp; subst hp'
        exact ⟨rfl, rfl⟩

end TateAlgorithm.Step10

end WeierstrassCurve
