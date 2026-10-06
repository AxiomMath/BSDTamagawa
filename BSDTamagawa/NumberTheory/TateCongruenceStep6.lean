/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep5

/-!
# Finite determination of Step 6 of Tate's algorithm

Step 6 of Tate's algorithm runs Step 5 and, if Step 5 continues with a curve `c`, applies the
substitution `Step6.translate` to `c` and tests whether the cubic `cubic ϖ · 1 1` of the result has
a double root over the residue field. It continues with the substituted curve when it does, and
terminates with Kodaira symbol `I₀*` and local Tamagawa number `1 + #{distinct roots}` otherwise.
We show that Step 6 is determined by the coefficients of the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.
Here `Except.ok c` means that the algorithm continues with `c`, and `Except.error o` that it
terminates with answer `o`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step6.s_eq_of_mod_eq`,
  `WeierstrassCurve.TateAlgorithm.Step6.t_eq_of_mod_div_eq`: the square roots `Step6.s` and
  `Step6.t` defining the substitution are determined by the residues of `a₁`, `a₂` and of `a₃ / ϖ`,
  `a₆ / ϖ ^ 2` respectively, in residue characteristic two and otherwise.
* `WeierstrassCurve.TateAlgorithm.Step6.translate_congrDepth`: Step 6 substitutes congruent curves
  by congruent curves.
* `WeierstrassCurve.TateAlgorithm.cubic_eq_of_congrDepth`: the cubic `cubic ϖ · a m` is determined
  by a congruence of depth `2 * m + 2`.
* `WeierstrassCurve.TateAlgorithm.Step6.five_le_multiplicity_Δ`: if Step 5 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 5`.
* `WeierstrassCurve.TateAlgorithm.Step6.run_eq_of_step5_error`,
  `WeierstrassCurve.TateAlgorithm.Step6.run_eq_of_step5_ok`: `Step6.run` in terms of the outcome of
  Step 5.
* `WeierstrassCurve.TateAlgorithm.Step6.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 6 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.

## Implementation notes

No assumption that `2` is a unit is made: in residue characteristic two, `Step6.s` and `Step6.t`
are Frobenius square roots `CharP.root 2` of residues of `a₂` and `a₆ / ϖ ^ 2`, and otherwise they
are obtained by dividing residues of `a₁` and `a₃ / ϖ` by `2`.
-/

@[expose] public section

universe u

open CommRing Ideal

variable {R : Type u} [CommRing R]

namespace CommRing

/-- Two elements have the same residue modulo `ϖ` exactly when their difference is divisible by
`ϖ`. -/
theorem mod_eq_mod_iff_dvd_sub {ϖ x y : R} : mod ϖ x = mod ϖ y ↔ ϖ ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]

/-- If `x` and `y` are both divisible by `ϖ` and agree modulo `ϖ ^ 2`, then `x / ϖ` and `y / ϖ`
agree modulo `ϖ`. -/
theorem mod_div_self_eq_of_pow_succ_dvd_sub [NoZeroDivisors R] {ϖ x y : R} (hϖ : ϖ ≠ 0)
    (hx : ϖ ^ 1 ∣ x) (hy : ϖ ^ 1 ∣ y) (hxy : ϖ ^ 2 ∣ x - y) :
    mod ϖ (div x ϖ) = mod ϖ (div y ϖ) := by
  have h := mod_div_eq_of_pow_succ_dvd_sub (k := 1) hϖ hx hy (by rwa [show 1 + 1 = 2 from rfl])
  rwa [pow_one] at h

end CommRing

namespace WeierstrassCurve

variable {ϖ : R} {k n : ℕ} {W W' : WeierstrassCurve R}

namespace CongrDepth

/-! ### Coefficientwise divisibility -/

/-- Curves congruent to depth `n` have `a₁` congruent to depth `k` for every `k ≤ n`. -/
theorem pow_dvd_a₁_sub (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₁ - W'.a₁ :=
  Ideal.mem_span_singleton.mp ((congrDepth_iff_sub_mem ϖ k W W').mp (h.mono hk)).1

/-- Curves congruent to depth `n` have `a₂` congruent to depth `k` for every `k ≤ n`. -/
theorem pow_dvd_a₂_sub (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₂ - W'.a₂ :=
  Ideal.mem_span_singleton.mp ((congrDepth_iff_sub_mem ϖ k W W').mp (h.mono hk)).2.1

/-- Curves congruent to depth `n` have `a₄` congruent to depth `k` for every `k ≤ n`. -/
theorem pow_dvd_a₄_sub (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₄ - W'.a₄ :=
  Ideal.mem_span_singleton.mp ((congrDepth_iff_sub_mem ϖ k W W').mp (h.mono hk)).2.2.2.1

/-- Curves congruent to depth `n` pass the divisibility test `ϖ ^ k ∣ a₂` together, for any
`k ≤ n`. -/
theorem pow_dvd_a₂_iff (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₂ ↔ ϖ ^ k ∣ W'.a₂ :=
  dvd_iff_dvd_of_dvd_sub (h.pow_dvd_a₂_sub hk)

/-- Curves congruent to depth `n` pass the divisibility test `ϖ ^ k ∣ a₄` together, for any
`k ≤ n`. -/
theorem pow_dvd_a₄_iff (h : CongrDepth ϖ n W W') (hk : k ≤ n) : ϖ ^ k ∣ W.a₄ ↔ ϖ ^ k ∣ W'.a₄ :=
  dvd_iff_dvd_of_dvd_sub (h.pow_dvd_a₄_sub hk)

/-- At `ϖ = 0` a congruence to any positive depth degenerates to equality of the two curves, since
`0 ^ n = 0`. -/
theorem eq_of_eq_zero (h : CongrDepth ϖ n W W') (hϖ : ϖ = 0) (hn : n ≠ 0) : W = W' := by
  have h₁ := h.pow_dvd_a₁_sub le_rfl
  have h₂ := h.pow_dvd_a₂_sub le_rfl
  have h₃ := h.pow_dvd_a₃_sub le_rfl
  have h₄ := h.pow_dvd_a₄_sub le_rfl
  have h₆ := h.pow_dvd_a₆_sub le_rfl
  subst hϖ
  simp only [zero_pow hn, zero_dvd_iff, sub_eq_zero] at h₁ h₂ h₃ h₄ h₆
  exact WeierstrassCurve.ext h₁ h₂ h₃ h₄ h₆

end CongrDepth

namespace TateAlgorithm

/-! ### The cubic of Steps 6, 7 and 8 is determined by a congruence

`WeierstrassCurve.TateAlgorithm.cubic ϖ W a n` is the cubic
`aX³ + (a₂/ϖ)X² + (a₄/ϖ ^ (n + 1))X + a₆/ϖ ^ (2n + 1)` over the residue field. Its coefficients are
determined by the coefficients of `W` modulo `ϖ ^ 2`, `ϖ ^ (n + 2)` and `ϖ ^ (2n + 2)`
respectively. -/

/-- If `ϖ ≠ 0`, two curves congruent to depth `n ≥ 2 * m + 2` whose `a₂` is divisible by `ϖ`, whose
`a₄` is divisible by `ϖ ^ (m + 1)` and whose `a₆` is divisible by `ϖ ^ (2 * m + 1)` have the same
cubic `cubic ϖ · a m`. -/
theorem cubic_eq_of_congrDepth [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (h : CongrDepth ϖ n W W') {a : R}
    {m : ℕ} (hm : 2 * m + 2 ≤ n) (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₄ : ϖ ^ (m + 1) ∣ W.a₄)
    (ha₆ : ϖ ^ (2 * m + 1) ∣ W.a₆) : cubic ϖ W a m = cubic ϖ W' a m := by
  have ha₂' : ϖ ^ 1 ∣ W'.a₂ := (h.pow_dvd_a₂_iff (by omega)).mp ha₂
  have ha₄' : ϖ ^ (m + 1) ∣ W'.a₄ := (h.pow_dvd_a₄_iff (by omega)).mp ha₄
  have ha₆' : ϖ ^ (2 * m + 1) ∣ W'.a₆ := (h.mono (by omega)).dvd_pow_a₆_iff.mp ha₆
  have h₂ : mod ϖ (div W.a₂ ϖ) = mod ϖ (div W'.a₂ ϖ) :=
    mod_div_self_eq_of_pow_succ_dvd_sub hϖ ha₂ ha₂' (h.pow_dvd_a₂_sub (by omega))
  have h₄ : mod ϖ (div W.a₄ (ϖ ^ (m + 1))) = mod ϖ (div W'.a₄ (ϖ ^ (m + 1))) :=
    mod_div_eq_of_pow_succ_dvd_sub hϖ ha₄ ha₄' (h.pow_dvd_a₄_sub (by omega))
  have h₆ : mod ϖ (div W.a₆ (ϖ ^ (2 * m + 1))) = mod ϖ (div W'.a₆ (ϖ ^ (2 * m + 1))) :=
    mod_div_eq_of_pow_succ_dvd_sub hϖ ha₆ ha₆' (h.pow_dvd_a₆_sub (by omega))
  unfold cubic
  rw [h₂, h₄, h₆]

namespace Step6

variable (ϖ : R) [(span {ϖ}).IsMaximal]

/-! ### The change of variables performed by Step 6

Step 6 applies the substitution `(x, y) ↦ (x, y + s x + ϖ t)`, where `s` and `t` are square roots
of residues of the curve, defined by a case distinction on whether the residue field has
characteristic two. -/

variable {W W' : WeierstrassCurve R}

/-- `Step6.s` is determined by the residues of `a₁` and `a₂`. In residue characteristic two it is
the Frobenius square root of `a₂ mod ϖ`, and otherwise it is `(-a₁ / 2) mod ϖ`. -/
theorem s_eq_of_mod_eq (h₁ : mod ϖ W.a₁ = mod ϖ W'.a₁) (h₂ : mod ϖ W.a₂ = mod ϖ W'.a₂) :
    s ϖ W = s ϖ W' := by
  unfold s
  congr 1
  split_ifs with h2
  · rw [h₂]
  · rw [h₁]

/-- `Step6.t` is determined by the residues of `a₃ / ϖ` and `a₆ / ϖ ^ 2`. In residue characteristic
two it is the Frobenius square root of `(a₆ / ϖ ^ 2) mod ϖ`, and otherwise it is
`(-(a₃ / ϖ) / 2) mod ϖ`. -/
theorem t_eq_of_mod_div_eq (h₃ : mod ϖ (div W.a₃ ϖ) = mod ϖ (div W'.a₃ ϖ))
    (h₆ : mod ϖ (div W.a₆ (ϖ ^ 2)) = mod ϖ (div W'.a₆ (ϖ ^ 2))) : t ϖ W = t ϖ W' := by
  unfold t
  congr 1
  split_ifs with h2
  · rw [h₆]
  · rw [h₃]

/-- If `Step6.s` and `Step6.t` agree on two curves congruent to depth `n`, then their images under
`Step6.translate` are congruent to depth `n`. -/
theorem translate_congrDepth (hs : s ϖ W = s ϖ W') (ht : t ϖ W = t ϖ W')
    (h : CongrDepth ϖ n W W') : CongrDepth ϖ n (translate ϖ W) (translate ϖ W') := by
  unfold translate
  rw [hs, ht]
  exact h.smul _

/-! ### The branch structure of Step 6 -/

variable [PerfectField (R ⧸ span {ϖ})]

/-- Unfolding of Step 6 in the case where Step 5 terminates: Step 6 passes the answer through
unchanged. -/
theorem run_eq_of_step5_error {W : WeierstrassCurve R} {o : Output R}
    (h : Step5.run ϖ W = .error o) : run ϖ W = .error o := by
  rw [run.eq_def, h]
  rfl

open scoped Classical in
/-- Unfolding of Step 6 in the case where Step 5 continues with the curve `c`: Step 6 substitutes
`Step6.translate` and tests whether the cubic `cubic ϖ · 1 1` of the result has a double root,
continuing (`Except.ok`) with the substituted curve when it does and terminating (`Except.error`)
with Kodaira symbol `I₀*` and local Tamagawa number `1 + #{distinct roots}` when it does not. -/
theorem run_eq_of_step5_ok {W c : WeierstrassCurve R} (h : Step5.run ϖ W = .ok c) :
    run ϖ W =
      if (cubic ϖ (translate ϖ c) 1 1).HasDoubleRoot then .ok (translate ϖ c)
      else .error ⟨translate ϖ c, .I! 0,
        1 + (cubic ϖ (translate ϖ c) 1 1).toPoly.roots.toFinset.card⟩ := by
  rw [run.eq_def, h]
  rfl

/-! ### Finite determination of Step 6 -/

/-- If `ϖ ≠ 0` and Step 5 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 5`. -/
theorem five_le_multiplicity_Δ [IsDomain R] [IsNoetherianRing R] {W c : WeierstrassCurve R}
    (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (h : Step5.run ϖ W = .ok c) : 5 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step5.run_Δ h]
  exact (Step5.run_hasValuation hϖ h).Δ

/-- **Step 6 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step6.run ϖ W` and `Step6.run ϖ W'` have the same `Except.isOk` flag.
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
  · obtain rfl : W = W' := h.eq_of_eq_zero hϖ (Nat.succ_ne_zero _)
    refine ⟨rfl, fun o o' ho ho' => ?_, fun c c' hc hc' => ?_⟩
    · rw [ho'] at ho
      simp only [Except.error.injEq] at ho
      subst ho
      exact ⟨rfl, rfl⟩
    · rw [hc'] at hc
      simp only [Except.ok.injEq] at hc
      subst hc
      exact CongrDepth.refl ..
  obtain ⟨hbranch, herror, hcont⟩ := Step5.finite_determination ϖ hΔ h
  cases h₅ : Step5.run ϖ W with
  | error o =>
    cases h₅' : Step5.run ϖ W' with
    | error o' =>
      rw [run_eq_of_step5_error ϖ h₅, run_eq_of_step5_error ϖ h₅']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₅ h₅'
    | ok c' => rw [h₅, h₅'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₅' : Step5.run ϖ W' with
    | error o' => rw [h₅, h₅'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₅ h₅'
      have hle : 5 ≤ multiplicity ϖ W.Δ := five_le_multiplicity_Δ ϖ hϖ hΔ h₅
      have hv := Step5.run_hasValuation hϖ h₅
      have hv' := Step5.run_hasValuation hϖ h₅'
      have hs : s ϖ c = s ϖ c' := s_eq_of_mod_eq ϖ
        (mod_eq_mod_iff_dvd_sub.mpr (hcong.pow_dvd_a₁_sub (by omega) |>.of_pow one_ne_zero))
        (mod_eq_mod_iff_dvd_sub.mpr (hcong.pow_dvd_a₂_sub (by omega) |>.of_pow one_ne_zero))
      have ht : t ϖ c = t ϖ c' := t_eq_of_mod_div_eq ϖ
        (mod_div_self_eq_of_pow_succ_dvd_sub hϖ hv.a₃ hv'.a₃ (hcong.pow_dvd_a₃_sub (by omega)))
        (mod_div_eq_of_pow_succ_dvd_sub (k := 2) hϖ hv.a₆ hv'.a₆
          (hcong.pow_dvd_a₆_sub (by omega)))
      have hcongV : CongrDepth ϖ (multiplicity ϖ W.Δ) (translate ϖ c) (translate ϖ c') :=
        translate_congrDepth ϖ hs ht hcong
      have hvV := hasValuation_translate hϖ hv
      have hcub : cubic ϖ (translate ϖ c) 1 1 = cubic ϖ (translate ϖ c') 1 1 :=
        cubic_eq_of_congrDepth hϖ hcongV (m := 1) (by omega) hvV.a₂ hvV.a₄ hvV.a₆
      have hiff : (cubic ϖ (translate ϖ c) 1 1).HasDoubleRoot ↔
          (cubic ϖ (translate ϖ c') 1 1).HasDoubleRoot := by rw [hcub]
      rw [run_eq_of_step5_ok ϖ h₅, run_eq_of_step5_ok ϖ h₅']
      by_cases hdr : (cubic ϖ (translate ϖ c) 1 1).HasDoubleRoot
      · rw [ite_eq_left hdr, ite_eq_left (hiff.mp hdr)]
        refine ⟨rfl, fun p p' hp _ => absurd hp (by simp), fun d d' hd hd' => ?_⟩
        rw [Except.ok.injEq] at hd hd'
        subst hd; subst hd'
        exact hcongV
      · rw [ite_eq_right hdr, ite_eq_right fun hc => hdr (hiff.mpr hc)]
        refine ⟨rfl, fun p p' hp hp' => ?_, fun d d' hd _ => absurd hd (by simp)⟩
        rw [Except.error.injEq] at hp hp'
        subst hp; subst hp'
        exact ⟨rfl, by rw [hcub]⟩

end Step6

end TateAlgorithm

end WeierstrassCurve
