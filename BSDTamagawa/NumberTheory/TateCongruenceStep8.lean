/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep6

/-!
# Finite determination of Step 8 of Tate's algorithm

Step 8 of Tate's algorithm runs Step 7 and, if Step 7 continues with a curve `c`, applies the
change of variables `Step8.translate` that moves the triple root of the cubic `cubic ϖ · 1 1` to
the origin, and tests whether the quadratic `Y² + (a₃/ϖ ^ 2)Y - a₆/ϖ ^ 4` of the result has a
double root. It continues with the substituted curve when it does, and otherwise terminates with
Kodaira symbol `IV*` and local Tamagawa number `3` or `1` according as that quadratic splits or
not. We show that, given the corresponding statement for Step 7, Step 8 is determined by the
coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Here `Except.ok c` means that the
algorithm continues with `c`, and `Except.error o` that it terminates with answer `o`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step8.r_eq_of_cubic_eq`: the triple root `Step8.r` is a function
  of the cubic `cubic ϖ · 1 1` alone: it is a Frobenius cube root of the constant term in residue
  characteristic three and a third of the `X ^ 2`-coefficient otherwise.
* `WeierstrassCurve.TateAlgorithm.Step8.translate_congrDepth`: Step 8 substitutes congruent curves
  by congruent curves.
* `WeierstrassCurve.TateAlgorithm.Step8.six_le_multiplicity_Δ`: if Step 7 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 6`.
* `WeierstrassCurve.TateAlgorithm.Step8.run_eq_of_step7_error`,
  `WeierstrassCurve.TateAlgorithm.Step8.run_eq_of_step7_ok`: `Step8.run` in terms of the outcome of
  Step 7.
* `WeierstrassCurve.TateAlgorithm.Step8.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1` and Step 7 behaves alike on them, then Step 8 takes the same branch on both,
  returns the same Kodaira symbol and the same local Tamagawa number when it terminates, and
  returns curves congruent to depth `v_ϖ(W.Δ)` when it continues.
-/

@[expose] public section

universe u

open CommRing Ideal

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {n : ℕ} {W W' : WeierstrassCurve R}

namespace TateAlgorithm.Step8

variable [(span {ϖ}).IsMaximal]

/-! ### The change of variables performed by Step 8

Step 8 applies the substitution `(x, y) ↦ (x - ϖ r, y)`, where `r` is the triple root of the cubic
`cubic ϖ · 1 1` over the residue field. -/

/-- `Step8.r` is determined by the cubic `cubic ϖ · 1 1`. In residue characteristic three it is the
Frobenius cube root of that cubic's constant term and otherwise a third of its
`X ^ 2`-coefficient. -/
theorem r_eq_of_cubic_eq (hcub : cubic ϖ W 1 1 = cubic ϖ W' 1 1) : r ϖ W = r ϖ W' := by
  unfold r
  rw [hcub]

/-- If `Step8.r` agrees on two curves congruent to depth `n`, then their images under
`Step8.translate` are congruent to depth `n`. -/
theorem translate_congrDepth (hr : r ϖ W = r ϖ W') (h : CongrDepth ϖ n W W') :
    CongrDepth ϖ n (translate ϖ W) (translate ϖ W') := by
  unfold translate
  rw [hr]
  exact h.smul _

/-! ### The branch structure of Step 8 -/

variable [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]

/-- Unfolding of Step 8 in the case where Step 7 terminates: Step 8 passes the answer through
unchanged. -/
theorem run_eq_of_step7_error (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {o : Output R}
    (h : Step7.run hϖ hΔ = .error o) : run hϖ hΔ = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 8 in the case where Step 7 continues with the curve `c`: Step 8 substitutes
`Step8.translate` and tests whether the quadratic `quadratic ϖ · 2` of the result has a double
root, continuing (`Except.ok`) with the substituted curve when it does and terminating
(`Except.error`) with Kodaira symbol `IV*` and local Tamagawa number `3` or `1` according as that
quadratic splits or not. -/
theorem run_eq_of_step7_ok (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step7.run hϖ hΔ = .ok c) :
    run hϖ hΔ =
      if (quadratic ϖ (translate ϖ c) 2).HasDoubleRoot then .ok (translate ϖ c)
      else .error ⟨translate ϖ c, .IV!,
        if (quadratic ϖ (translate ϖ c) 2).toPoly.Splits then 3 else 1⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 8 -/

/-- If Step 7 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 6`. -/
theorem six_le_multiplicity_Δ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step7.run hϖ hΔ = .ok c) : 6 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step7.run_Δ hϖ hΔ h]
  exact (Step7.run_hasValuation hϖ hΔ h).Δ

/-- **Step 8 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`, and assume the same three statements for Step 7 (the hypothesis `h₇`). Then:

1. `Step8.run hϖ hΔ` and `Step8.run hϖ hΔ'` have the same `Except.isOk` flag.
2. If both terminate (`Except.error`), the two answers have the same Kodaira symbol and the same
   local Tamagawa number.
3. If both continue (`Except.ok`), the two curves returned are congruent to depth `v_ϖ(W.Δ)`. -/
theorem finite_determination (hϖ : ϖ ≠ 0) {W W' : WeierstrassCurve R} (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W')
    (h₇ : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W' →
      ((Step7.run hϖ hΔ).isOk = (Step7.run hϖ hΔ').isOk) ∧
      (∀ o o' : Output R, Step7.run hϖ hΔ = .error o → Step7.run hϖ hΔ' = .error o' →
        o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
      (∀ c c' : WeierstrassCurve R, Step7.run hϖ hΔ = .ok c → Step7.run hϖ hΔ' = .ok c' →
        CongrDepth ϖ (multiplicity ϖ W.Δ) c c')) :
    ((run hϖ hΔ).isOk = (run hϖ hΔ').isOk) ∧
    (∀ o o' : Output R, run hϖ hΔ = .error o → run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve R, run hϖ hΔ = .ok c → run hϖ hΔ' = .ok c' →
      CongrDepth ϖ (multiplicity ϖ W.Δ) c c') := by
  obtain ⟨hbranch, herror, hcont⟩ := h₇ h
  cases h₇ : Step7.run hϖ hΔ with
  | error o =>
    cases h₇' : Step7.run hϖ hΔ' with
    | error o' =>
      rw [run_eq_of_step7_error hϖ hΔ h₇, run_eq_of_step7_error hϖ hΔ' h₇']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₇ h₇'
    | ok c' => rw [h₇, h₇'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₇' : Step7.run hϖ hΔ' with
    | error o' => rw [h₇, h₇'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₇ h₇'
      have hle : 6 ≤ multiplicity ϖ W.Δ := six_le_multiplicity_Δ hϖ hΔ h₇
      have hv := Step7.run_hasValuation hϖ hΔ h₇
      have hcub : cubic ϖ c 1 1 = cubic ϖ c' 1 1 :=
        cubic_eq_of_congrDepth hϖ hcong (m := 1) (by omega) hv.a₂ hv.a₄ hv.a₆
      have hcongV : CongrDepth ϖ (multiplicity ϖ W.Δ) (translate ϖ c) (translate ϖ c') :=
        translate_congrDepth (r_eq_of_cubic_eq hcub) hcong
      have hvV := hasValuation_translate hϖ hv (Step7.run_hasDoubleRoot hϖ hΔ h₇)
        (Step7.run_hasTripleRoot hϖ hΔ h₇)
      have hquad : quadratic ϖ (translate ϖ c) 2 = quadratic ϖ (translate ϖ c') 2 :=
        quadratic_eq_of_congrDepth hϖ hcongV (m := 2) (by omega) hvV.a₃ hvV.a₆
      have hiff : (quadratic ϖ (translate ϖ c) 2).HasDoubleRoot ↔
          (quadratic ϖ (translate ϖ c') 2).HasDoubleRoot := by rw [hquad]
      rw [run_eq_of_step7_ok hϖ hΔ h₇, run_eq_of_step7_ok hϖ hΔ' h₇']
      by_cases hdr : (quadratic ϖ (translate ϖ c) 2).HasDoubleRoot
      · rw [ite_eq_left hdr, ite_eq_left (hiff.mp hdr)]
        refine ⟨rfl, fun p p' hp _ => absurd hp (by simp), fun d d' hd hd' => ?_⟩
        rw [Except.ok.injEq] at hd hd'
        subst hd; subst hd'
        exact hcongV
      · rw [ite_eq_right hdr, ite_eq_right fun hc => hdr (hiff.mpr hc)]
        refine ⟨rfl, fun p p' hp hp' => ?_, fun d d' hd _ => absurd hd (by simp)⟩
        rw [Except.error.injEq] at hp hp'
        subst hp; subst hp'
        exact ⟨rfl, by rw [hquad]⟩

end TateAlgorithm.Step8

end WeierstrassCurve
