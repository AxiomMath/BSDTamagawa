/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep3

/-!
# Finite determination of Step 4 of Tate's algorithm

Step 4 of Tate's algorithm performs no change of variables: it runs Step 3 and, if Step 3 continues
with a curve `c`, tests `ϖ ^ 3 ∣ c.b₈`, continuing with `c` when the test holds and terminating
with Kodaira symbol `III` and local Tamagawa number `2` otherwise. We show that Step 4 is
determined by the coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Here `Except.ok c`
means that the algorithm continues with `c`, and `Except.error o` that it terminates with answer
`o`.

## Main results

* `WeierstrassCurve.CongrDepth.pow_dvd_b₈_iff`: curves congruent to depth `n` pass the test
  `ϖ ^ k ∣ b₈` together, for every `k ≤ n`.
* `WeierstrassCurve.TateAlgorithm.Step4.three_le_multiplicity_Δ`: if Step 3 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 3`.
* `WeierstrassCurve.TateAlgorithm.Step4.run_eq_of_step3_error`,
  `WeierstrassCurve.TateAlgorithm.Step4.run_eq_of_step3_ok`: `Step4.run` in terms of the outcome of
  Step 3.
* `WeierstrassCurve.TateAlgorithm.Step4.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 4 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {k n : ℕ} {W W' : WeierstrassCurve R}

namespace CongrDepth

/-- Curves congruent to depth `n` pass the divisibility test `ϖ ^ k ∣ b₈` together, for any
`k ≤ n`. -/
theorem pow_dvd_b₈_iff (h : CongrDepth ϖ n W W') (hk : k ≤ n) :
    ϖ ^ k ∣ W.b₈ ↔ ϖ ^ k ∣ W'.b₈ :=
  dvd_iff_dvd_of_dvd_sub <| Ideal.mem_span_singleton.mp (h.mono hk).b₈_sub_mem

end CongrDepth

namespace TateAlgorithm.Step4

/-! ### The branch structure of Step 4 -/

variable (ϖ : R) [(Ideal.span {ϖ}).IsMaximal] [PerfectField (R ⧸ Ideal.span {ϖ})]

/-- Unfolding of Step 4 in the case where Step 3 terminates: Step 4 passes the answer through
unchanged. -/
theorem run_eq_of_step3_error {W : WeierstrassCurve R} {o : Output R}
    (h : Step3.run ϖ W = .error o) : run ϖ W = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 4 in the case where Step 3 continues with the curve `c`: Step 4 tests
`ϖ ^ 3 ∣ c.b₈`, continuing (`Except.ok`) with `c` itself when the test succeeds and terminating
(`Except.error`) with Kodaira symbol `III` and local Tamagawa number `2` when it fails. -/
theorem run_eq_of_step3_ok {W c : WeierstrassCurve R} (h : Step3.run ϖ W = .ok c) :
    run ϖ W = if ϖ ^ 3 ∣ c.b₈ then .ok c else .error ⟨c, .III, 2⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 4 -/

/-- If Step 3 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 3`. -/
theorem three_le_multiplicity_Δ [IsDomain R] [IsNoetherianRing R] {W c : WeierstrassCurve R}
    (hΔ : W.Δ ≠ 0) (h : Step3.run ϖ W = .ok c) : 3 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step3.run_Δ h]
  exact (Step3.run_hasValuation h).Δ

/-- **Step 4 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step4.run ϖ W` and `Step4.run ϖ W'` have the same `Except.isOk` flag.
2. If both terminate (`Except.error`), the two answers have the same Kodaira symbol and the same
   local Tamagawa number.
3. If both continue (`Except.ok`), the two curves returned are congruent to depth `v_ϖ(W.Δ)`. -/
theorem finite_determination [IsDomain R] [IsNoetherianRing R] {W W' : WeierstrassCurve R}
    (hΔ : W.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W') :
    ((run ϖ W).isOk = (run ϖ W').isOk) ∧
    (∀ o o' : Output R, run ϖ W = .error o → run ϖ W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve R, run ϖ W = .ok c → run ϖ W' = .ok c' →
      CongrDepth ϖ (multiplicity ϖ W.Δ) c c') := by
  obtain ⟨hbranch, herror, hcont⟩ := Step3.finite_determination ϖ hΔ h
  cases h₃ : Step3.run ϖ W with
  | error o =>
    cases h₃' : Step3.run ϖ W' with
    | error o' =>
      rw [run_eq_of_step3_error ϖ h₃, run_eq_of_step3_error ϖ h₃']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₃ h₃'
    | ok c' => rw [h₃, h₃'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₃' : Step3.run ϖ W' with
    | error o' => rw [h₃, h₃'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₃ h₃'
      have h3 : 3 ≤ multiplicity ϖ W.Δ := three_le_multiplicity_Δ ϖ hΔ h₃
      rw [run_eq_of_step3_ok ϖ h₃, run_eq_of_step3_ok ϖ h₃']
      by_cases hb₈ : ϖ ^ 3 ∣ c.b₈
      · rw [ite_eq_left hb₈, ite_eq_left ((hcong.pow_dvd_b₈_iff h3).mp hb₈)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun d d' hd hd' => ?_⟩
        rw [Except.ok.injEq] at hd hd'
        subst hd; subst hd'
        exact hcong
      · rw [ite_eq_right hb₈, ite_eq_right fun hc => hb₈ ((hcong.pow_dvd_b₈_iff h3).mpr hc)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun d d' hd _ => absurd hd (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

end TateAlgorithm.Step4

end WeierstrassCurve
