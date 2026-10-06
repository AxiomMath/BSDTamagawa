/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep10

/-!
# Finite determination of Step 11 of Tate's algorithm

Step 11 of Tate's algorithm never terminates: it runs Step 10 and, if Step 10 continues with a
curve `c`, continues with the rescaled curve `Step11.translate ϖ c`, whose coefficients are
`⟨a₁ / ϖ, a₂ / ϖ ^ 2, a₃ / ϖ ^ 3, a₄ / ϖ ^ 4, a₆ / ϖ ^ 6⟩`. This is the substitution
`(X, Y) ↦ (ϖ ^ 2 X, ϖ ^ 3 Y)`, and it divides the discriminant by `ϖ ^ 12`. We show that Step 11 is
determined by the coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`. Unlike the earlier
steps, the rescaling loses congruence depth: dividing `a₆` by `ϖ ^ 6` turns a congruence modulo
`ϖ ^ n` into one modulo `ϖ ^ (n - 6)`, so the curves returned are congruent only to depth
`v_ϖ(Δ) - 6`. Since `v_ϖ(c.Δ) = v_ϖ(W.Δ) - 12`, this is still more than the depth `v_ϖ(c.Δ) + 1`
needed to apply the result again to the rescaled curves. Here `Except.ok c` means that the
algorithm continues with `c`, and `Except.error o` that it terminates with answer `o`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step11.pow_dvd_div_sub_div`: if `ϖ ^ k` divides `x` and `y` and
  `ϖ ^ n ∣ x - y`, then `ϖ ^ m ∣ x / ϖ ^ k - y / ϖ ^ k` whenever `m + k ≤ n`.
* `WeierstrassCurve.TateAlgorithm.Step11.translate_congrDepth`: Step 11's rescaling transports a
  congruence of depth `n` to one of depth `n - 6`.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_of_step10_error`,
  `WeierstrassCurve.TateAlgorithm.Step11.run_eq_of_step10_ok`: `Step11.run` in terms of the outcome
  of Step 10.
* `WeierstrassCurve.TateAlgorithm.Step11.twelve_le_multiplicity_Δ`: if Step 10 continues on `W`,
  then `v_ϖ(W.Δ) ≥ 12`.
* `WeierstrassCurve.TateAlgorithm.Step11.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 11 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ) - 6` when it continues.
* `WeierstrassCurve.TateAlgorithm.Step11.multiplicity_Δ_run`: if Step 11 returns `c`, then
  `v_ϖ(W.Δ) = v_ϖ(c.Δ) + 12`.
* `WeierstrassCurve.TateAlgorithm.Step11.run_congrDepth_recursion`: in the continuing case, the
  curves returned are congruent to depth `v_ϖ(c.Δ) + 1`.
-/

@[expose] public section

universe u

open CommRing Ideal

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {n : ℕ} {W W' : WeierstrassCurve R}

namespace TateAlgorithm.Step11

/-! ### The rescaling performed by Step 11

Step 11 divides the coefficient `aᵢ` by `ϖ ^ i`; dividing by `ϖ ^ k` costs `k` units of congruence
depth. -/

section Translate

variable [IsDomain R]

/-- If `ϖ ^ k` divides both `x` and `y`, and `x` and `y` agree modulo `ϖ ^ n`, then their exact
quotients by `ϖ ^ k` agree modulo `ϖ ^ m` for every `m` with `m + k ≤ n`. -/
theorem pow_dvd_div_sub_div {k m : ℕ} (hϖ : ϖ ≠ 0) (hkm : m + k ≤ n) {x y : R}
    (hx : ϖ ^ k ∣ x) (hy : ϖ ^ k ∣ y) (hxy : ϖ ^ n ∣ x - y) :
    ϖ ^ m ∣ div x (ϖ ^ k) - div y (ϖ ^ k) := by
  refine (mul_dvd_mul_iff_left (pow_ne_zero k hϖ)).mp ?_
  rw [← pow_add, mul_sub, CommRing.mul_div (pow_ne_zero k hϖ) hx,
    CommRing.mul_div (pow_ne_zero k hϖ) hy]
  exact (pow_dvd_pow ϖ (by omega : k + m ≤ n)).trans hxy

/-- **Step 11's rescaling transports a congruence of depth `n` to one of depth `n - 6`.**

Let `ϖ ≠ 0` and `6 ≤ n`, let `W` and `W'` be congruent to depth `n`, and let `ϖ ^ i ∣ W.aᵢ` for
`i = 1, 2, 3, 4, 6`. Then `Step11.translate ϖ W` and `Step11.translate ϖ W'` are congruent to depth
`n - 6`. -/
theorem translate_congrDepth (hϖ : ϖ ≠ 0) (hn : 6 ≤ n) (ha₁ : ϖ ^ 1 ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂)
    (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₄ : ϖ ^ 4 ∣ W.a₄) (ha₆ : ϖ ^ 6 ∣ W.a₆) (h : CongrDepth ϖ n W W') :
    CongrDepth ϖ (n - 6) (translate ϖ W) (translate ϖ W') := by
  have ha₁' : ϖ ^ 1 ∣ W'.a₁ := (dvd_iff_dvd_of_dvd_sub (h.pow_dvd_a₁_sub (by omega))).mp ha₁
  have ha₂' : ϖ ^ 2 ∣ W'.a₂ := (h.pow_dvd_a₂_iff (by omega)).mp ha₂
  have ha₃' : ϖ ^ 3 ∣ W'.a₃ := (h.pow_dvd_a₃_iff (by omega)).mp ha₃
  have ha₄' : ϖ ^ 4 ∣ W'.a₄ := (h.pow_dvd_a₄_iff (by omega)).mp ha₄
  have ha₆' : ϖ ^ 6 ∣ W'.a₆ := ((h.mono hn).dvd_pow_a₆_iff).mp ha₆
  have h₁ : ϖ ^ (n - 6) ∣ div W.a₁ ϖ - div W'.a₁ ϖ := by
    have := pow_dvd_div_sub_div (m := n - 6) hϖ (by omega) ha₁ ha₁' (h.pow_dvd_a₁_sub le_rfl)
    rwa [pow_one] at this
  have h₂ : ϖ ^ (n - 6) ∣ div W.a₂ (ϖ ^ 2) - div W'.a₂ (ϖ ^ 2) :=
    pow_dvd_div_sub_div (m := n - 6) hϖ (by omega) ha₂ ha₂' (h.pow_dvd_a₂_sub le_rfl)
  have h₃ : ϖ ^ (n - 6) ∣ div W.a₃ (ϖ ^ 3) - div W'.a₃ (ϖ ^ 3) :=
    pow_dvd_div_sub_div (m := n - 6) hϖ (by omega) ha₃ ha₃' (h.pow_dvd_a₃_sub le_rfl)
  have h₄ : ϖ ^ (n - 6) ∣ div W.a₄ (ϖ ^ 4) - div W'.a₄ (ϖ ^ 4) :=
    pow_dvd_div_sub_div (m := n - 6) hϖ (by omega) ha₄ ha₄' (h.pow_dvd_a₄_sub le_rfl)
  have h₆ : ϖ ^ (n - 6) ∣ div W.a₆ (ϖ ^ 6) - div W'.a₆ (ϖ ^ 6) :=
    pow_dvd_div_sub_div (m := n - 6) hϖ (by omega) ha₆ ha₆' (h.pow_dvd_a₆_sub le_rfl)
  rw [congrDepth_iff_sub_mem]
  simp only [translate, Ideal.mem_span_singleton]
  exact ⟨h₁, h₂, h₃, h₄, h₆⟩

end Translate

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]

/-! ### The branch structure of Step 11 -/

/-- Unfolding of Step 11 in the case where Step 10 terminates: Step 11 passes the answer through
unchanged. -/
theorem run_eq_of_step10_error (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {o : Output R}
    (h : Step10.run hϖ hΔ = .error o) : run hϖ hΔ = .error o := by
  rw [run.eq_def, h]
  rfl

/-- Unfolding of Step 11 in the case where Step 10 continues with the curve `c`: Step 11 continues
with the rescaled curve `translate ϖ c`. -/
theorem run_eq_of_step10_ok (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step10.run hϖ hΔ = .ok c) : run hϖ hΔ = .ok (translate ϖ c) := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 11 -/

/-- If Step 10 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 12`. -/
theorem twelve_le_multiplicity_Δ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step10.run hϖ hΔ = .ok c) : 12 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step10.run_Δ hϖ hΔ h]
  exact (Step10.run_hasValuation hϖ hΔ h).Δ

/-- **Step 11 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step11.run hϖ hΔ` and `Step11.run hϖ hΔ'` have the same `Except.isOk` flag.
2. If both terminate (`Except.error`), the two answers have the same Kodaira symbol and the same
   local Tamagawa number.
3. If both continue (`Except.ok`), the two curves returned are congruent to depth
   `v_ϖ(W.Δ) - 6`. -/
theorem finite_determination (hϖ : ϖ ≠ 0) {W W' : WeierstrassCurve R} (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W') :
    ((run hϖ hΔ).isOk = (run hϖ hΔ').isOk) ∧
    (∀ o o' : Output R, run hϖ hΔ = .error o → run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve R, run hϖ hΔ = .ok c → run hϖ hΔ' = .ok c' →
      CongrDepth ϖ (multiplicity ϖ W.Δ - 6) c c') := by
  obtain ⟨hbranch, herror, hcont⟩ := Step10.finite_determination hϖ hΔ hΔ' h
  cases h₁₀ : Step10.run hϖ hΔ with
  | error o =>
    cases h₁₀' : Step10.run hϖ hΔ' with
    | error o' =>
      rw [run_eq_of_step10_error hϖ hΔ h₁₀, run_eq_of_step10_error hϖ hΔ' h₁₀']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₁₀ h₁₀'
    | ok c' => rw [h₁₀, h₁₀'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₁₀' : Step10.run hϖ hΔ' with
    | error o' => rw [h₁₀, h₁₀'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₁₀ h₁₀'
      have hv := Step10.run_hasValuation hϖ hΔ h₁₀
      have hle : 12 ≤ multiplicity ϖ W.Δ := twelve_le_multiplicity_Δ hϖ hΔ h₁₀
      rw [run_eq_of_step10_ok hϖ hΔ h₁₀, run_eq_of_step10_ok hϖ hΔ' h₁₀']
      refine ⟨rfl, fun p p' hp _ => absurd hp (by simp), fun d d' hd hd' => ?_⟩
      rw [Except.ok.injEq] at hd hd'
      subst hd; subst hd'
      exact translate_congrDepth hϖ (by omega) hv.a₁ hv.a₂ hv.a₃ hv.a₄ hv.a₆ hcong

/-! ### The discriminant drop and the recursion -/

/-- If Step 11 returns the curve `c` on `W`, then `v_ϖ(W.Δ) = v_ϖ(c.Δ) + 12`. -/
theorem multiplicity_Δ_run (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {c : WeierstrassCurve R}
    (h : run hϖ hΔ = .ok c) : multiplicity ϖ W.Δ = multiplicity ϖ c.Δ + 12 := by
  have hp : Prime ϖ := Ideal.IsMaximal.prime hϖ
  have hfin : FiniteMultiplicity ϖ W.Δ := FiniteMultiplicity.of_span_isMaximal ϖ hΔ
  rw [← run_Δ hϖ hΔ h] at hfin ⊢
  rw [multiplicity_mul hp hfin, multiplicity_pow_self_of_prime hp]
  omega

/-- If `W` and `W'` are congruent to depth `v_ϖ(W.Δ) + 1` and Step 11 returns `c` and `c'`
respectively, then `c` and `c'` are congruent to depth `v_ϖ(c.Δ) + 1`. -/
theorem run_congrDepth_recursion (hϖ : ϖ ≠ 0) {W W' : WeierstrassCurve R} (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W')
    {c c' : WeierstrassCurve R} (hc : run hϖ hΔ = .ok c) (hc' : run hϖ hΔ' = .ok c') :
    CongrDepth ϖ (multiplicity ϖ c.Δ + 1) c c' := by
  have hdrop : multiplicity ϖ W.Δ = multiplicity ϖ c.Δ + 12 := multiplicity_Δ_run hϖ hΔ hc
  exact ((finite_determination hϖ hΔ hΔ' h).2.2 c c' hc hc').mono (by omega)

end TateAlgorithm.Step11

end WeierstrassCurve
