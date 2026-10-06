/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep4

/-!
# Finite determination of Step 5 of Tate's algorithm

Step 5 of Tate's algorithm performs no change of variables: it runs Step 4 and, if Step 4 continues
with a curve `c`, tests `ϖ ^ 3 ∣ c.b₆`, continuing with `c` when the test holds and terminating
with Kodaira symbol `IV` otherwise. The local Tamagawa number is then `3` or `1` according as the
quadratic `Y² + (a₃/ϖ)Y - a₆/ϖ²` over the residue field splits or not. We show that Step 5 is
determined by the coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Here `Except.ok c`
means that the algorithm continues with `c`, and `Except.error o` that it terminates with answer
`o`.

## Main results

* `CommRing.mod_div_eq_of_pow_succ_dvd_sub`: if `x` and `y` are both divisible by `ϖ ^ k` and agree
  modulo `ϖ ^ (k + 1)`, then `x / ϖ ^ k` and `y / ϖ ^ k` agree modulo `ϖ`.
* `WeierstrassCurve.CongrDepth.pow_dvd_a₃_sub`, `WeierstrassCurve.CongrDepth.pow_dvd_a₆_sub`,
  `WeierstrassCurve.CongrDepth.pow_dvd_a₃_iff`, `WeierstrassCurve.CongrDepth.pow_dvd_b₆_iff`:
  congruence and divisibility of `a₃`, `a₆` and `b₆` for congruent curves.
* `WeierstrassCurve.TateAlgorithm.quadratic_eq_of_congrDepth`: congruent curves whose `a₃` and `a₆`
  are divisible by `ϖ ^ m` and `ϖ ^ (2 * m)` have the same quadratic `quadratic ϖ · m`, provided
  the congruence has depth at least `2 * m + 1`.
* `WeierstrassCurve.TateAlgorithm.Step5.four_le_multiplicity_Δ`: if Step 4 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 4`.
* `WeierstrassCurve.TateAlgorithm.Step5.run_eq_of_step4_error`,
  `WeierstrassCurve.TateAlgorithm.Step5.run_eq_of_step4_ok`: `Step5.run` in terms of the outcome of
  Step 4.
* `WeierstrassCurve.TateAlgorithm.Step5.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 5 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.

## Implementation notes

`Ideal.span {ϖ}` can be maximal with `ϖ = 0`, namely when `R` is a field; then
`CongrDepth ϖ (v_ϖ(W.Δ) + 1) W W'` says that `W = W'`, and `Step5.finite_determination` holds
trivially in that case.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

namespace CommRing

/-- If `x` and `y` are both divisible by `ϖ ^ k` and agree modulo `ϖ ^ (k + 1)`, then the exact
quotients `x / ϖ ^ k` and `y / ϖ ^ k` agree modulo `ϖ`. -/
theorem mod_div_eq_of_pow_succ_dvd_sub [NoZeroDivisors R] {ϖ x y : R} {k : ℕ} (hϖ : ϖ ≠ 0)
    (hx : ϖ ^ k ∣ x) (hy : ϖ ^ k ∣ y) (hxy : ϖ ^ (k + 1) ∣ x - y) :
    mod ϖ (div x (ϖ ^ k)) = mod ϖ (div y (ϖ ^ k)) := by
  obtain ⟨t, ht⟩ := hxy
  have hk : (ϖ : R) ^ k ≠ 0 := pow_ne_zero k hϖ
  have key : ϖ ^ k * (div x (ϖ ^ k) - div y (ϖ ^ k)) = ϖ ^ k * (ϖ * t) := by
    rw [mul_sub, mul_div hk hx, mul_div hk hy, ht, pow_succ']
    ring
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero, mul_left_cancel₀ hk key]
  exact dvd_mul_right ϖ t

end CommRing

namespace WeierstrassCurve

variable {ϖ : R} {k n : ℕ} {W W' : WeierstrassCurve R}

namespace CongrDepth

/-- Curves congruent to depth `n` have `a₃` congruent to depth `k` for every `k ≤ n`. -/
theorem pow_dvd_a₃_sub (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₃ - W'.a₃ :=
  Ideal.mem_span_singleton.mp ((congrDepth_iff_sub_mem ϖ k W W').mp (h.mono hk)).2.2.1

/-- Curves congruent to depth `n` have `a₆` congruent to depth `k` for every `k ≤ n`. -/
theorem pow_dvd_a₆_sub (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₆ - W'.a₆ :=
  Ideal.mem_span_singleton.mp ((congrDepth_iff_sub_mem ϖ k W W').mp (h.mono hk)).2.2.2.2

/-- Curves congruent to depth `n` pass the divisibility test `ϖ ^ k ∣ a₃` together, for any
`k ≤ n`. -/
theorem pow_dvd_a₃_iff (h : CongrDepth ϖ n W W') (hk : k ≤ n) :
    ϖ ^ k ∣ W.a₃ ↔ ϖ ^ k ∣ W'.a₃ :=
  dvd_iff_dvd_of_dvd_sub (h.pow_dvd_a₃_sub hk)

/-- Curves congruent to depth `n` pass the divisibility test `ϖ ^ k ∣ b₆` together, for any
`k ≤ n`. -/
theorem pow_dvd_b₆_iff (h : CongrDepth ϖ n W W') (hk : k ≤ n) :
    ϖ ^ k ∣ W.b₆ ↔ ϖ ^ k ∣ W'.b₆ :=
  dvd_iff_dvd_of_dvd_sub <| Ideal.mem_span_singleton.mp (h.mono hk).b₆_sub_mem

end CongrDepth

namespace TateAlgorithm

/-! ### The quadratic of Steps 5, 7, 8 and 9 is determined by a congruence

`WeierstrassCurve.TateAlgorithm.quadratic ϖ W n` is the quadratic `Y² + (a₃/ϖ ^ n)Y - a₆/ϖ ^ (2n)`
over the residue field. Its coefficients are determined by the coefficients of `W` modulo
`ϖ ^ (n + 1)` and `ϖ ^ (2n + 1)` respectively. -/

/-- If `ϖ ≠ 0`, two curves congruent to depth `n ≥ 2 * m + 1` whose `a₃` is divisible by `ϖ ^ m`
and whose `a₆` is divisible by `ϖ ^ (2 * m)` have the same quadratic `quadratic ϖ · m`. -/
theorem quadratic_eq_of_congrDepth [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (h : CongrDepth ϖ n W W')
    {m : ℕ} (hm : 2 * m + 1 ≤ n) (ha₃ : ϖ ^ m ∣ W.a₃) (ha₆ : ϖ ^ (2 * m) ∣ W.a₆) :
    quadratic ϖ W m = quadratic ϖ W' m := by
  have ha₃' : ϖ ^ m ∣ W'.a₃ := (h.pow_dvd_a₃_iff (by omega)).mp ha₃
  have ha₆' : ϖ ^ (2 * m) ∣ W'.a₆ := (h.mono (by omega)).dvd_pow_a₆_iff.mp ha₆
  have hc : CommRing.mod ϖ (CommRing.div W.a₃ (ϖ ^ m))
      = CommRing.mod ϖ (CommRing.div W'.a₃ (ϖ ^ m)) :=
    CommRing.mod_div_eq_of_pow_succ_dvd_sub hϖ ha₃ ha₃' (h.pow_dvd_a₃_sub (by omega))
  have hd : CommRing.mod ϖ (CommRing.div W.a₆ (ϖ ^ (2 * m)))
      = CommRing.mod ϖ (CommRing.div W'.a₆ (ϖ ^ (2 * m))) :=
    CommRing.mod_div_eq_of_pow_succ_dvd_sub hϖ ha₆ ha₆' (h.pow_dvd_a₆_sub (by omega))
  unfold quadratic
  rw [hc, hd]

namespace Step5

/-! ### The branch structure of Step 5 -/

variable (ϖ : R) [(Ideal.span {ϖ}).IsMaximal] [PerfectField (R ⧸ Ideal.span {ϖ})]

/-- Unfolding of Step 5 in the case where Step 4 terminates: Step 5 passes the answer through
unchanged. -/
theorem run_eq_of_step4_error {W : WeierstrassCurve R} {o : Output R}
    (h : Step4.run ϖ W = .error o) : run ϖ W = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 5 in the case where Step 4 continues with the curve `c`: Step 5 tests
`ϖ ^ 3 ∣ c.b₆`, continuing (`Except.ok`) with `c` itself when the test succeeds and terminating
(`Except.error`) with Kodaira symbol `IV` and local Tamagawa number `3` or `1` according as the
quadratic `quadratic ϖ c 1` splits or not. -/
theorem run_eq_of_step4_ok {W c : WeierstrassCurve R} (h : Step4.run ϖ W = .ok c) :
    run ϖ W =
      if ϖ ^ 3 ∣ c.b₆ then .ok c
      else .error ⟨c, .IV, if (quadratic ϖ c 1).toPoly.Splits then 3 else 1⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 5 -/

/-- If `ϖ ≠ 0` and Step 4 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 4`. -/
theorem four_le_multiplicity_Δ [IsDomain R] [IsNoetherianRing R] (hϖ : ϖ ≠ 0)
    {W c : WeierstrassCurve R} (hΔ : W.Δ ≠ 0) (h : Step4.run ϖ W = .ok c) :
    4 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step4.run_Δ h]
  exact (Step4.run_hasValuation hϖ h).Δ

/-- **Step 5 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step5.run ϖ W` and `Step5.run ϖ W'` have the same `Except.isOk` flag.
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
  by_cases hϖ : ϖ = 0
  · have hWW' : W = W' := by
      have h5 := (congrDepth_iff_sub_mem ϖ _ W W').mp h
      simp only [hϖ, zero_pow (Nat.succ_ne_zero _), Ideal.mem_span_singleton, zero_dvd_iff,
        sub_eq_zero] at h5
      rw [WeierstrassCurve.ext_iff]
      exact h5
    subst hWW'
    exact ⟨rfl, fun o o' ho ho' => by rw [ho'] at ho; cases ho; exact ⟨rfl, rfl⟩,
      fun c c' hc hc' => by rw [hc'] at hc; cases hc; exact CongrDepth.refl ..⟩
  obtain ⟨hbranch, herror, hcont⟩ := Step4.finite_determination ϖ hΔ h
  cases h₄ : Step4.run ϖ W with
  | error o =>
    cases h₄' : Step4.run ϖ W' with
    | error o' =>
      rw [run_eq_of_step4_error ϖ h₄, run_eq_of_step4_error ϖ h₄']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₄ h₄'
    | ok c' => rw [h₄, h₄'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₄' : Step4.run ϖ W' with
    | error o' => rw [h₄, h₄'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₄ h₄'
      have h4 : 4 ≤ multiplicity ϖ W.Δ := four_le_multiplicity_Δ ϖ hϖ hΔ h₄
      have hval := Step4.run_hasValuation hϖ h₄
      have hquad : quadratic ϖ c 1 = quadratic ϖ c' 1 :=
        quadratic_eq_of_congrDepth hϖ hcong (m := 1) (by omega) hval.a₃ hval.a₆
      rw [run_eq_of_step4_ok ϖ h₄, run_eq_of_step4_ok ϖ h₄']
      by_cases hb₆ : ϖ ^ 3 ∣ c.b₆
      · rw [ite_eq_left hb₆, ite_eq_left ((hcong.pow_dvd_b₆_iff (by omega)).mp hb₆)]
        refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun d d' hd hd' => ?_⟩
        rw [Except.ok.injEq] at hd hd'
        subst hd; subst hd'
        exact hcong
      · rw [ite_eq_right hb₆, ite_eq_right fun hc => hb₆ ((hcong.pow_dvd_b₆_iff (by omega)).mpr hc)]
        refine ⟨rfl, fun o o' ho ho' => ?_, fun d d' hd _ => absurd hd (by simp)⟩
        rw [Except.error.injEq] at ho ho'
        subst ho; subst ho'
        exact ⟨rfl, by rw [hquad]⟩

end Step5

end TateAlgorithm

end WeierstrassCurve
