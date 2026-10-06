/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep11
public import BSDTamagawa.NumberTheory.TatePositivity

/-!
# Finite determination of Tate's algorithm

Let `R` be a Noetherian domain with `(ϖ)` maximal and perfect residue field. For a Weierstrass
curve `W` over `R` with `W.Δ ≠ 0`, the Kodaira symbol and the local Tamagawa number returned by
Tate's algorithm `WeierstrassCurve.TateAlgorithm.run` depend only on the coefficients of `W` modulo
`ϖ ^ (v_ϖ(W.Δ) + 1)`. Nothing is asserted about the minimal model `(run hϖ hΔ).weierstrassCurve`.

## Main results

* `WeierstrassCurve.TateAlgorithm.run_finite_determination`: two Weierstrass curves congruent to
  depth `v_ϖ(Δ) + 1` have the same Kodaira symbol and the same local Tamagawa number.
-/

@[expose] public section

universe u

open Ideal

namespace WeierstrassCurve.TateAlgorithm

variable {R : Type u} [CommRing R] {ϖ : R} [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})]
  [IsDomain R] [IsNoetherianRing R] {W W' : WeierstrassCurve R}

/-- If Step 11 returns a curve `c` on `W`, then `c.Δ ≠ 0`. -/
theorem Δ_ne_zero_of_step11_ok (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step11.run hϖ hΔ = .ok c) : c.Δ ≠ 0 := fun h₀ =>
  hΔ <| by rw [← Step11.run_Δ hϖ hΔ h, h₀, mul_zero]

/-! ### Finite determination of the whole algorithm -/

/-- For every `n`, Weierstrass curves `W`, `W'` with `v_ϖ(W.Δ) = n` that are congruent to depth
`v_ϖ(W.Δ) + 1` have the same Kodaira symbol and the same local Tamagawa number. -/
private theorem run_finite_determination_aux (hϖ : ϖ ≠ 0) (n : ℕ) :
    ∀ (W W' : WeierstrassCurve R) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0), multiplicity ϖ W.Δ = n →
      CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W' →
      (run hϖ hΔ).kodairaSymbol = (run hϖ hΔ').kodairaSymbol ∧
      (run hϖ hΔ).tamagawaNumber = (run hϖ hΔ').tamagawaNumber := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W W' hΔ hΔ' hn h
    obtain ⟨hbranch, herror, -⟩ := Step11.finite_determination hϖ hΔ hΔ' h
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
        have hdrop : multiplicity ϖ W.Δ = multiplicity ϖ c.Δ + 12 :=
          Step11.multiplicity_Δ_run hϖ hΔ h₁₁
        rw [run_eq_of_step11_ok hϖ hΔ h₁₁ hc, run_eq_of_step11_ok hϖ hΔ' h₁₁' hc']
        exact ih (multiplicity ϖ c.Δ) (by omega) c c' hc hc' rfl
          (Step11.run_congrDepth_recursion hϖ hΔ hΔ' h h₁₁ h₁₁')

/-- **Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.** Let `W` be a
Weierstrass curve over a Noetherian domain `R` with `(ϖ)` maximal and perfect residue field, let
`W.Δ ≠ 0`, and let `W'` be congruent to `W` to depth `v_ϖ(W.Δ) + 1`, that is, the two curves have
the same five Weierstrass coefficients modulo `ϖ ^ (v_ϖ(W.Δ) + 1)`. Then Tate's algorithm returns
the same Kodaira symbol and the same local Tamagawa number on both. -/
theorem run_finite_determination (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W') :
    (run hϖ hΔ).kodairaSymbol = (run hϖ hΔ').kodairaSymbol ∧
    (run hϖ hΔ).tamagawaNumber = (run hϖ hΔ').tamagawaNumber :=
  run_finite_determination_aux hϖ (multiplicity ϖ W.Δ) W W' hΔ hΔ' rfl h

end WeierstrassCurve.TateAlgorithm
