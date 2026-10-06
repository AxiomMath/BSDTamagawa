/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateTranslateInvariance

/-!
# Cubic double roots

For a cubic `bX² + cX + d` with `a = 0`, `b ≠ 0` and vanishing discriminant over a field with
`2 ≠ 0`, the double root is `-c/2/b`. This file shows that the formula `-c/2/b` moves by `-γ`
under the shift `X ↦ X + γ`.

Applied to the `X`-cubic of Step 7 of Tate's algorithm, whose double root `Step7.rX` lifts, this
shows that the `r`-parameter of a `u = 1` change of variables relating two curves in the
recursion of Step 7 stays divisible by `ϖ ^ n` at stage `n`.

## Main results

* `Cubic.neg_div_shiftBy`: the double-root formula `-c/2/b` moves by `-γ` under `Cubic.shiftBy γ`.
* `WeierstrassCurve.TateAlgorithm.Step7.mod_rX_smul`: the residues of `Step7.rX` on a curve and on
  an integral translate differ by the residue of `r/ϖⁿ`.
* `WeierstrassCurve.TateAlgorithm.Step7.dvd_r_translateX_smul`: the `r`-parameter at stage `n + 1`
  is divisible by `ϖ ^ (n + 1)`.
-/

@[expose] public section

universe u

open CommRing Ideal Polynomial

namespace Cubic

variable {k : Type u} [Field k]

/-- **The double-root formula of an `a = 0` cubic moves by `-γ` under `Cubic.shiftBy γ`**, whether
or not the discriminant vanishes. -/
theorem neg_div_shiftBy (h2 : (2 : k) ≠ 0) {P : Cubic k} (ha : P.a = 0) (hb : P.b ≠ 0) (γ : k) :
    -(P.shiftBy γ).c / 2 / (P.shiftBy γ).b = -P.c / 2 / P.b - γ := by
  simp only [shiftBy_b, shiftBy_c, ha, mul_zero, zero_mul, add_zero]
  field_simp
  ring

end Cubic

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {ϖ : R}

/-- **Two `u = 1` changes of variables compose by adding `r` and `s`.** The `t`-parameters add too,
with the single cross term `r₁s₂`. -/
theorem smulOne_trans (V : WeierstrassCurve R) (r₁ s₁ t₁ r₂ s₂ t₂ : R) :
    (VariableChange.mk 1 r₁ s₁ t₁) • ((VariableChange.mk 1 r₂ s₂ t₂) • V)
      = (VariableChange.mk 1 (r₁ + r₂) (s₁ + s₂) (t₁ + r₁ * s₂ + t₂)) • V := by
  rw [← mul_smul, VariableChange.mul_def]
  congr 1
  ext <;> simp

/-- If `ϖ ^ n ∣ r`, `ϖ ∣ a₁`, and `ϖ ^ (n + 1)` divides `a₃` both of `V` and of its image under the
change of variables `(1, r, s, t)`, then `ϖ ^ (n + 1) ∣ t`. -/
theorem dvd_t_of_dvd_a₃_of_dvd_r (h2 : IsUnit (2 : R)) {n : ℕ} {V : WeierstrassCurve R} {r s t : R}
    (hr : ϖ ^ n ∣ r) (ha₁ : ϖ ∣ V.a₁) (ha₃ : ϖ ^ (n + 1) ∣ V.a₃)
    (ha₃' : ϖ ^ (n + 1) ∣ ((VariableChange.mk 1 r s t) • V).a₃) : ϖ ^ (n + 1) ∣ t :=
  dvd_t_of_dvd_a₃ h2 ha₃ ha₃' (by rw [pow_succ]; exact mul_dvd_mul hr ha₁)

namespace TateAlgorithm

namespace Step7

variable [(span {ϖ}).IsMaximal]

/-- **The residue of `Step7.rX` is the double-root formula of the `X`-cubic.** In residue
characteristic `≠ 2`, `rX` is a lift of `-c/2/b`, where the cubic is written with `a = 0`. -/
theorem mod_rX (V : WeierstrassCurve R) (n : ℕ) (h2 : (2 : R ⧸ span {ϖ}) ≠ 0) :
    mod ϖ (rX ϖ V n) = -(cubic ϖ V 0 n).c / 2 / (cubic ϖ V 0 n).b := by
  rw [rX, dite_eq_right h2]
  exact mod_out _

/-- **The two double roots of the two `X`-cubics differ by exactly the shift.** At stage `n ≥ 2` of
Step 7, for an integral translate by `(1, r, s, t)`, `rX' = rX - r/ϖⁿ` in the residue field. The
hypothesis `¬ ϖ ^ 2 ∣ a₂` makes the leading coefficient `a₂/ϖ` of the `X`-cubic nonzero in the
residue field. -/
theorem mod_rX_smul [IsDomain R] (h2 : IsUnit (2 : R)) (hϖ : ϖ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {V : WeierstrassCurve R} {r s t : R} (hs : ϖ ∣ s) (hr : ϖ ^ n ∣ r) (ht : ϖ ^ (n + 1) ∣ t)
    (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ (n + 1) ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄)
    (ha₆ : ϖ ^ (2 * n + 1) ∣ V.a₆) (ha₂' : ¬ ϖ ^ 2 ∣ V.a₂) :
    mod ϖ (rX ϖ ((VariableChange.mk 1 r s t) • V) n)
      = mod ϖ (rX ϖ V n) - mod ϖ (div r (ϖ ^ n)) := by
  have h2k : (2 : R ⧸ span {ϖ}) ≠ 0 := by
    have h := (h2.map (mod ϖ)).ne_zero
    rwa [map_ofNat] at h
  have hb : (cubic ϖ V 0 n).b ≠ 0 := by
    rw [show (cubic ϖ V 0 n).b = mod ϖ (div V.a₂ ϖ) from rfl, Ne, mod_eq_zero]
    exact fun h ↦ ha₂' (sq_dvd.mpr ⟨ha₂, h⟩)
  rw [mod_rX _ _ h2k, mod_rX _ _ h2k, cubic_smul hϖ hn hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆]
  exact Cubic.neg_div_shiftBy h2k rfl hb _

/-- **`translateY` moves no `r`.** `translateY` of an integral translate by `(1, r, s, t)` is the
translate of `translateY` by `(1, r, s, t')`, where `t'` is `t` plus `ϖⁿ` times the difference of
the two values of `tY`. -/
theorem translateY_smul (V : WeierstrassCurve R) (r s t : R) (n : ℕ) :
    translateY ϖ ((VariableChange.mk 1 r s t) • V) n
      = (VariableChange.mk 1 r s
          (t + ϖ ^ n * (tY ϖ ((VariableChange.mk 1 r s t) • V) n - tY ϖ V n)))
        • translateY ϖ V n := by
  simp only [translateY, smulOne_trans]
  congr 1
  ext <;> first | rfl | ring

/-- **`translateX` of an integral translate is an integral translate of `translateX`**, with
`r`-parameter `r + ϖⁿ(rX' - rX)`. -/
theorem translateX_smul (V : WeierstrassCurve R) (r s t : R) (n : ℕ) :
    translateX ϖ ((VariableChange.mk 1 r s t) • V) n
      = (VariableChange.mk 1
          (r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n)) s
          (t + ϖ ^ n * rX ϖ ((VariableChange.mk 1 r s t) • V) n * s)) • translateX ϖ V n := by
  simp only [translateX, smulOne_trans]
  congr 1
  ext <;> first | rfl | ring

/-- **The `r`-parameter at stage `n + 1` is divisible by `ϖ ^ (n + 1)`**: if `ϖ ^ n ∣ r`, then
`ϖ ^ (n + 1) ∣ r + ϖⁿ(rX' - rX)`. -/
theorem dvd_r_translateX_smul [IsDomain R] (h2 : IsUnit (2 : R)) (hϖ : ϖ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {V : WeierstrassCurve R} {r s t : R} (hs : ϖ ∣ s) (hr : ϖ ^ n ∣ r) (ht : ϖ ^ (n + 1) ∣ t)
    (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ (n + 1) ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄)
    (ha₆ : ϖ ^ (2 * n + 1) ∣ V.a₆) (ha₂' : ¬ ϖ ^ 2 ∣ V.a₂) :
    ϖ ^ (n + 1) ∣ r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n) := by
  have he : r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n)
      = ϖ ^ n * (div r (ϖ ^ n)
        + (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n)) := by
    rw [mul_add, mul_div (pow_ne_zero n hϖ) hr]
  rw [he, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero, map_add, map_sub,
    mod_rX_smul h2 hϖ hn hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆ ha₂']
  ring

end Step7

end TateAlgorithm

end WeierstrassCurve
