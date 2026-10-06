/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep7
public import BSDTamagawa.NumberTheory.TateCongruenceStep8

/-!
# Finite determination of Step 9 of Tate's algorithm

Step 9 of Tate's algorithm runs Step 8 and, if Step 8 continues with a curve `c`, applies the
change of variables `Step9.translate` that moves the double root of the quadratic `quadratic ϖ · 2`
to the origin, and tests whether `ϖ ^ 4` divides the `a₄` of the result. It continues with the
substituted curve when it does, and otherwise terminates with Kodaira symbol `III*` and local
Tamagawa number `2`. We show that Step 9 is determined by the coefficients of the input curve
modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Here `Except.ok c` means that the algorithm continues with `c`, and
`Except.error o` that it terminates with answer `o`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step9.eight_le_multiplicity_Δ`: if Step 8 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 8`.
* `WeierstrassCurve.TateAlgorithm.Step9.run_eq_of_step8_error`,
  `WeierstrassCurve.TateAlgorithm.Step9.run_eq_of_step8_ok`: `Step9.run` in terms of the outcome of
  Step 8.
* `WeierstrassCurve.TateAlgorithm.Step9.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 9 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.
-/

@[expose] public section

universe u

open CommRing Ideal

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {W W' : WeierstrassCurve R}

namespace TateAlgorithm.Step9

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]

/-! ### The branch structure of Step 9 -/

/-- Unfolding of Step 9 in the case where Step 8 terminates: Step 9 passes the answer through
unchanged. -/
theorem run_eq_of_step8_error (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {o : Output R}
    (h : Step8.run hϖ hΔ = .error o) : run hϖ hΔ = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 9 in the case where Step 8 continues with the curve `c`: Step 9 substitutes
`Step9.translate` and tests whether `ϖ ^ 4` divides the `a₄` of the result, continuing
(`Except.ok`) with the substituted curve when it does and terminating (`Except.error`) with Kodaira
symbol `III*` and local Tamagawa number `2` when it does not. -/
theorem run_eq_of_step8_ok (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step8.run hϖ hΔ = .ok c) :
    run hϖ hΔ =
      if ϖ ^ 4 ∣ (translate ϖ c).a₄ then .ok (translate ϖ c)
      else .error ⟨translate ϖ c, .III!, 2⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 9 -/

/-- If Step 8 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 8`. -/
theorem eight_le_multiplicity_Δ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step8.run hϖ hΔ = .ok c) : 8 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step8.run_Δ hϖ hΔ h]
  exact (Step8.run_hasValuation hϖ hΔ h).Δ

/-- **Step 9 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step9.run hϖ hΔ` and `Step9.run hϖ hΔ'` have the same `Except.isOk` flag.
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
  obtain ⟨hbranch, herror, hcont⟩ :=
    Step8.finite_determination hϖ hΔ hΔ' h (Step7.finite_determination hϖ hΔ hΔ')
  cases h₈ : Step8.run hϖ hΔ with
  | error o =>
    cases h₈' : Step8.run hϖ hΔ' with
    | error o' =>
      rw [run_eq_of_step8_error hϖ hΔ h₈, run_eq_of_step8_error hϖ hΔ' h₈']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₈ h₈'
    | ok c' => rw [h₈, h₈'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₈' : Step8.run hϖ hΔ' with
    | error o' => rw [h₈, h₈'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₈ h₈'
      have hle : 8 ≤ multiplicity ϖ W.Δ := eight_le_multiplicity_Δ hϖ hΔ h₈
      have hv := Step8.run_hasValuation hϖ hΔ h₈
      have hquad : quadratic ϖ c 2 = quadratic ϖ c' 2 :=
        quadratic_eq_of_congrDepth hϖ hcong (m := 2) (by omega) hv.a₃ hv.a₆
      have hcongV : CongrDepth ϖ (multiplicity ϖ W.Δ) (translate ϖ c) (translate ϖ c') :=
        Step7.translateY_congrDepth (Step7.tY_eq_of_quadratic_eq hquad) hcong
      have hiff : ϖ ^ 4 ∣ (translate ϖ c).a₄ ↔ ϖ ^ 4 ∣ (translate ϖ c').a₄ :=
        hcongV.pow_dvd_a₄_iff (by omega)
      rw [run_eq_of_step8_ok hϖ hΔ h₈, run_eq_of_step8_ok hϖ hΔ' h₈']
      by_cases ha₄ : ϖ ^ 4 ∣ (translate ϖ c).a₄
      · rw [ite_eq_left ha₄, ite_eq_left (hiff.mp ha₄)]
        refine ⟨rfl, fun p p' hp _ => absurd hp (by simp), fun d d' hd hd' => ?_⟩
        rw [Except.ok.injEq] at hd hd'
        subst hd; subst hd'
        exact hcongV
      · rw [ite_eq_right ha₄, ite_eq_right fun hc => ha₄ (hiff.mpr hc)]
        refine ⟨rfl, fun p p' hp hp' => ?_, fun d d' hd _ => absurd hd (by simp)⟩
        rw [Except.error.injEq] at hp hp'
        subst hp; subst hp'
        exact ⟨rfl, rfl⟩

end TateAlgorithm.Step9

end WeierstrassCurve
