/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruence

/-!
# Finite determination of Step 3 of Tate's algorithm

Step 3 of Tate's algorithm performs no change of variables: it runs Step 2 and, if Step 2 continues
with a curve `c`, tests `ϖ ^ 2 ∣ c.a₆`, continuing with `c` when the test holds and terminating
with Kodaira symbol `II` and local Tamagawa number `1` otherwise. We show that Step 3 is determined
by the coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Here `Except.ok c` means that the
algorithm continues with `c`, and `Except.error o` that it terminates with answer `o`.

## Main results

* `WeierstrassCurve.CongrDepth.dvd_pow_a₆_iff`: curves congruent to depth `n` pass the test
  `ϖ ^ n ∣ a₆` together.
* `WeierstrassCurve.TateAlgorithm.Step3.run_eq_of_step2_error`,
  `WeierstrassCurve.TateAlgorithm.Step3.run_eq_of_step2_ok`: `Step3.run` in terms of the outcome of
  Step 2.
* `WeierstrassCurve.TateAlgorithm.Step3.two_le_multiplicity_Δ`: if Step 2 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 2`.
* `WeierstrassCurve.TateAlgorithm.Step3.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 3 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {n : ℕ} {W W' : WeierstrassCurve R}

namespace CongrDepth

/-- Curves congruent to depth `n` pass the divisibility test `ϖ ^ n ∣ a₆` together. -/
theorem dvd_pow_a₆_iff (h : CongrDepth ϖ n W W') : ϖ ^ n ∣ W.a₆ ↔ ϖ ^ n ∣ W'.a₆ := by
  have ha₆ := ((congrDepth_iff_sub_mem ϖ n W W').mp h).2.2.2.2
  rw [Ideal.mem_span_singleton] at ha₆
  exact dvd_iff_dvd_of_dvd_sub ha₆

end CongrDepth

namespace TateAlgorithm.Step3

variable (ϖ : R) [(Ideal.span {ϖ}).IsMaximal] [PerfectField (R ⧸ Ideal.span {ϖ})]

/-! ### The branch structure of Step 3 -/

/-- Unfolding of Step 3 in the case where Step 2 terminates: Step 3 passes the answer through
unchanged. -/
theorem run_eq_of_step2_error {W : WeierstrassCurve R} {o : Output R}
    (h : Step2.run ϖ W = .error o) : run ϖ W = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 3 in the case where Step 2 continues with the curve `c`: Step 3 tests
`ϖ ^ 2 ∣ c.a₆`, continuing (`Except.ok`) with the very same curve `c` when the test succeeds and
terminating (`Except.error`) with Kodaira symbol `II` and local Tamagawa number `1` otherwise. -/
theorem run_eq_of_step2_ok {W c : WeierstrassCurve R} (h : Step2.run ϖ W = .ok c) :
    run ϖ W = if ϖ ^ 2 ∣ c.a₆ then .ok c else .error ⟨c, .II, 1⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 3 -/

/-- If Step 2 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 2`. -/
theorem two_le_multiplicity_Δ [IsDomain R] [IsNoetherianRing R] {W c : WeierstrassCurve R}
    (hΔ : W.Δ ≠ 0) (h : Step2.run ϖ W = .ok c) : 2 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step2.run_Δ h]
  exact (Step2.run_hasValuation h).Δ

open scoped Classical in
/-- **Step 3 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step3.run ϖ W` and `Step3.run ϖ W'` have the same `Except.isOk` flag.
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
  obtain ⟨hbranch, hans, hcurve⟩ := Step2.finite_determination ϖ hΔ h
  cases hs : Step2.run ϖ W with
  | error o =>
    cases hs' : Step2.run ϖ W' with
    | error o' =>
      rw [run_eq_of_step2_error ϖ hs, run_eq_of_step2_error ϖ hs']
      refine ⟨rfl, fun o₁ o₁' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      exact hans _ _ hs hs'
    | ok c' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases hs' : Step2.run ϖ W' with
    | error o' => rw [hs, hs'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcurve _ _ hs hs'
      have ha₆ : ϖ ^ 2 ∣ c.a₆ ↔ ϖ ^ 2 ∣ c'.a₆ :=
        (hcong.mono (two_le_multiplicity_Δ ϖ hΔ hs)).dvd_pow_a₆_iff
      rw [run_eq_of_step2_ok ϖ hs, run_eq_of_step2_ok ϖ hs']
      by_cases hd : ϖ ^ 2 ∣ c.a₆
      · rw [ite_eq_left hd, ite_eq_left (ha₆.mp hd)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c₁ c₁' hc hc' => ?_⟩
        rw [Except.ok.injEq] at hc hc'
        subst hc; subst hc'
        exact hcong
      · rw [ite_eq_right hd, ite_eq_right fun hc => hd (ha₆.mpr hc)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun c₁ c₁' hc _ => absurd hc (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, rfl⟩

end TateAlgorithm.Step3

end WeierstrassCurve
