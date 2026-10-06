/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateEvenTransport

/-!
# Shifts of quadratics in characteristic `2`, and Steps 2, 5 and 8 of Tate's algorithm at `p = 2`

Under `Y ↦ Y + γ` a monic quadratic `Y² + cY + d` becomes `Y² + (c + 2γ)Y + (d + cγ + γ²)`. In
characteristic `2` the linear coefficient is fixed, and the discriminant `c² - 4d = c²` no longer
detects whether two monic quadratics are shifts of one another. We record the shift formula when
`2 = 0`, show that every element `x` of the residue field of `ℤ_2` satisfies `x² = x`, and use
this to show that, at a prime `ϖ ∣ 2`, the `Splits` tests of Steps 2, 5 and 8 of Tate's algorithm
give the same answer on a Weierstrass curve and on its image under an integral change of variables
with `u = 1`.

## Main results

* `Cubic.shiftBy_eq_of_two_eq_zero`: if `2 = 0`, the monic quadratic `Y² + cY + d'` is the shift of
  `Y² + cY + d` by `γ` when `d' = d + cγ + γ²`.
* `PadicInt.sq_eq_self_residue_of_eq_two`: every element `x` of the residue field of `ℤ_2`
  satisfies `x² = x`.
* `WeierstrassCurve.TateAlgorithm.dvd_a₁_of_dvd_b₂`: for a prime `ϖ ∣ 2`, `ϖ ∣ b₂` implies
  `ϖ ∣ a₁`.
* `WeierstrassCurve.TateAlgorithm.Step2.splitsCubic_smul_of_dvd_two`,
  `WeierstrassCurve.TateAlgorithm.Step2.splits_smul_of_dvd_two`: when `¬ϖ ∣ b₂`, the polynomial
  `X² + a₁X - a₂` tested by Step 2 has the same reduction on both curves.
* `WeierstrassCurve.TateAlgorithm.Step5.quadratic_smul_of_dvd_two`,
  `WeierstrassCurve.TateAlgorithm.Step5.splits_smul_of_dvd_two`: on the terminating branch of Step
  5, the quadratic `Y² + (a₃/ϖ)Y - a₆/ϖ²` of one curve is a shift of that of the other.
* `WeierstrassCurve.TateAlgorithm.Step8.quadratic_smul_of_dvd_two`,
  `WeierstrassCurve.TateAlgorithm.Step8.splits_smul_of_dvd_two`: on the curves reaching Step 8, the
  quadratic `Y² + (a₃/ϖ²)Y - a₆/ϖ⁴` of one curve is the shift of that of the other by `t/ϖ²`.
-/

@[expose] public section

universe u

open CommRing Ideal Polynomial

/-! ### The shift calculus for monic quadratics in characteristic `2` -/

namespace Cubic

variable {k : Type u} [CommRing k]

/-- **A monic quadratic's shift in characteristic `2`.** `Cubic.mk 0 1 c d` is `Y² + cY + d`, and
`Y ↦ Y + γ` sends `c` to `c + 2γ` and `d` to `d + cγ + γ²`. So when `2 = 0`, a monic quadratic `Q`
with `Q.c = P.c` and `Q.d = P.d + P.c γ + γ²` is the shift of `P` by `γ`. -/
theorem shiftBy_eq_of_two_eq_zero (h2 : (2 : k) = 0) {P Q : Cubic k} (hPa : P.a = 0)
    (hPb : P.b = 1) (hQa : Q.a = 0) (hQb : Q.b = 1) {γ : k} (hc : Q.c = P.c)
    (hd : Q.d = P.d + P.c * γ + γ ^ 2) : Q = P.shiftBy γ := by
  refine Cubic.ext (by rw [hQa, shiftBy_a, hPa]) ?_ ?_ ?_
  · rw [hQb, shiftBy_b, hPa, hPb]; ring
  · rw [hc, shiftBy_c, hPa, hPb]; linear_combination (-γ) * h2
  · rw [hd, shiftBy_d, hPa, hPb]; ring

end Cubic

/-! ### `x² = x` in the residue field of `ℤ_2` -/

/-- Squaring is the identity on `ZMod 2`, as a two-element check. -/
private theorem zmod_two_sq_sub_self : ∀ z : ZMod 2, z ^ 2 - z = 0 := by decide

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **The residue field of `ℤ_2` is `𝔽₂`:** every `x` in `ℤ_[2] ⧸ (2)` satisfies `x² = x`. -/
theorem sq_eq_self_residue_of_eq_two (hp2 : p = 2) (x : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) :
    x ^ 2 = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_dvd,
    dvd_iff_toZMod_eq_zero, map_sub, map_pow]
  subst hp2
  exact zmod_two_sq_sub_self _

end PadicInt

namespace WeierstrassCurve.TateAlgorithm

variable {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R} {r s t : R}

/-- If `q ≠ 0` and `x = q * y`, then the exact quotient of `x` by `q` is `y`. -/
private theorem div_eq_of_eq'' [NoZeroDivisors R] {q x y : R} (hq : q ≠ 0) (h : x = q * y) :
    div x q = y :=
  mul_left_cancel₀ hq (by rw [mul_div hq ⟨y, h⟩, h])

/-- If `ϖ ∣ 2`, then `ϖ ∣ 4`. -/
private theorem dvd_four_of_dvd_two (hϖ2 : ϖ ∣ 2) : ϖ ∣ (4 : R) := by
  obtain ⟨c, hc⟩ := hϖ2
  exact ⟨2 * c, by rw [show (4 : R) = 2 * 2 from by norm_num, hc]; ring⟩

/-- If `ϖ ∣ 2`, then `2` vanishes in the residue field `R ⧸ (ϖ)`. -/
private theorem two_residue_eq_zero (hϖ2 : ϖ ∣ 2) : (2 : R ⧸ span {ϖ}) = 0 := by
  rw [← map_ofNat (mod ϖ) 2, mod_eq_zero]; exact hϖ2

/-- **`ϖ ∣ a₁` from `ϖ ∣ b₂` at the even prime.** If `ϖ` is a prime dividing `2` and `ϖ ∣ b₂`, then
`ϖ ∣ a₁`: since `b₂ = a₁² + 4a₂` and `ϖ ∣ 4`, we have `ϖ ∣ a₁²`. -/
theorem dvd_a₁_of_dvd_b₂ (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2) (hb₂ : ϖ ∣ V.b₂) : ϖ ∣ V.a₁ := by
  obtain ⟨c, hc⟩ := dvd_four_of_dvd_two (ϖ := ϖ) hϖ2
  refine hprime.dvd_of_dvd_pow (n := 2) ?_
  have hx := dvd_sub hb₂ (⟨c * V.a₂, by rw [hc]; ring⟩ : ϖ ∣ 4 * V.a₂)
  rwa [show V.b₂ - 4 * V.a₂ = V.a₁ ^ 2 from by rw [WeierstrassCurve.b₂]; ring] at hx

/-! ### Step 2's `Splits` test at the even prime

On the branch `¬ϖ ∣ b₂`, Step 2 reads whether `X² + a₁X - a₂` splits over the residue field. At the
even prime, `¬ϖ ∣ b₂` forces `a₁ ≡ 1`, and then the reductions of this polynomial on a curve and on
an integral translate of it are equal. -/

/-- **Step 2's tested quadratic is the same on an integral translate, at the even prime.** Let `ϖ`
be a prime with `ϖ ∣ 2`, suppose that `x² = x` in `R ⧸ (ϖ)`, that `ϖ ∣ r` and that `¬ϖ ∣ b₂`. Then
the change of variables `(1, r, s, t)` does not change `Step2.splitsCubic ϖ`. Indeed `a₁ ↦ a₁ + 2s`
is invisible modulo `ϖ`, and `a₂` moves by `-sa₁ + 3r - s²`, whose reduction is
`s(a₁ + s) + r = s(1 + 1) = 0` since `a₁ ≡ 1` and `s² ≡ s`. Without `¬ϖ ∣ b₂` this fails: over `𝔽₂`
with `a₁ ≡ 0` the reduction moves by `s`. -/
theorem Step2.splitsCubic_smul_of_dvd_two [IsDomain R] (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2)
    (hsq : ∀ x : R ⧸ span {ϖ}, x ^ 2 = x) (hr : ϖ ∣ r) (hb₂ : ¬ ϖ ∣ V.b₂) :
    Step2.splitsCubic ϖ ((VariableChange.mk 1 r s t) • V) = Step2.splitsCubic ϖ V := by
  have hpr : (span {ϖ}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have h2res : (2 : R ⧸ span {ϖ}) = 0 := two_residue_eq_zero hϖ2
  obtain ⟨c₄, hc₄⟩ := dvd_four_of_dvd_two (ϖ := ϖ) hϖ2
  have ha₁1 : mod ϖ V.a₁ = 1 := by
    have hne : mod ϖ V.a₁ ≠ 0 := by
      intro h
      obtain ⟨α₁, e₁⟩ := (mod_eq_zero _ _).mp h
      exact hb₂ ⟨ϖ * α₁ ^ 2 + c₄ * V.a₂, by rw [WeierstrassCurve.b₂, e₁, hc₄]; ring⟩
    have h0 : mod ϖ V.a₁ * (mod ϖ V.a₁ - 1) = 0 := by linear_combination hsq (mod ϖ V.a₁)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hne)
  refine Cubic.ext rfl rfl ?_ ?_
  · change mod ϖ ((VariableChange.mk 1 r s t) • V).a₁ = mod ϖ V.a₁
    rw [smulOne_a₁, map_add, map_mul, map_ofNat, h2res, zero_mul, add_zero]
  · change -mod ϖ ((VariableChange.mk 1 r s t) • V).a₂ = -mod ϖ V.a₂
    rw [smulOne_a₂]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, (mod_eq_zero ϖ r).mpr hr]
    linear_combination mod ϖ s * ha₁1 + hsq (mod ϖ s) + mod ϖ s * h2res

/-- **Step 2's `Splits` answer agrees on an integral translate, at the even prime.** Under the
hypotheses of `Step2.splitsCubic_smul_of_dvd_two`, the reduction of `X² + a₁X - a₂` splits for the
translated curve if and only if it splits for the original curve. -/
theorem Step2.splits_smul_of_dvd_two [IsDomain R] [(span {ϖ}).IsMaximal] (hprime : Prime ϖ)
    (hϖ2 : ϖ ∣ 2) (hsq : ∀ x : R ⧸ span {ϖ}, x ^ 2 = x) (hr : ϖ ∣ r) (hb₂ : ¬ ϖ ∣ V.b₂) :
    ((X ^ 2 + C ((VariableChange.mk 1 r s t) • V).a₁ * X
        - C ((VariableChange.mk 1 r s t) • V).a₂).map (mod ϖ)).Splits
      ↔ ((X ^ 2 + C V.a₁ * X - C V.a₂).map (mod ϖ)).Splits := by
  rw [← Step2.toPoly_splitsCubic, ← Step2.toPoly_splitsCubic,
    Step2.splitsCubic_smul_of_dvd_two hprime hϖ2 hsq hr hb₂]

/-! ### Step 5's `Splits` test at the even prime

On the branch `¬ϖ³ ∣ b₆`, Step 5 reads whether `Y² + (a₃/ϖ)Y - a₆/ϖ²` splits. At the even prime the
shift relating the quadratics of a curve and of an integral translate of it is `t/ϖ`. -/

/-- **Step 5's quadratic is the shift of the other curve's by `t/ϖ`, at the even prime.**

Write `ρ = r/ϖ`, `τ = t/ϖ`, `α₃ = a₃/ϖ`, `α₄ = a₄/ϖ`, `α₆ = a₆/ϖ²`, and recall `ϖ ∣ a₁`
(`dvd_a₁_of_dvd_b₂`).

* The linear coefficient is `α₃ mod ϖ`, and `a₃ ↦ a₃ + ra₁ + 2t` moves it by `ρa₁ + 2τ ∈ (ϖ)`.
* The constant term is `-α₆ mod ϖ`, and `a₆/ϖ²` moves by `ρα₄ + ρ²a₂ - τα₃ - τ²` modulo `ϖ`. The
  last two terms are `-(cγ + γ²)` at `γ = τ`, so what remains is the residual `ϖ ∣ ρα₄ + ρ²a₂`.

For the residual, `ϖ³ ∣ b₈` gives `a₂α₃² ≡ α₄²`, so over `𝔽₂` `α₄ ≡ a₂α₃`; and `¬ϖ³ ∣ b₆` gives
`¬ϖ ∣ α₃`, hence `α₃ ≡ 1`. Then `ρα₄ + ρ²a₂ ≡ ρa₂(α₃ + 1) = 2ρa₂ = 0`. The hypothesis `¬ϖ³ ∣ b₆`
cannot be dropped: when `α₃ ≡ 0` the residual is `ρa₂`, which need not vanish. -/
theorem Step5.quadratic_smul_of_dvd_two [IsDomain R] (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2)
    (hsq : ∀ x : R ⧸ span {ϖ}, x ^ 2 = x) (hr : ϖ ∣ r) (ht : ϖ ∣ t)
    (ha₃ : ϖ ∣ V.a₃) (ha₄ : ϖ ∣ V.a₄) (ha₆ : ϖ ^ 2 ∣ V.a₆) (hb₂ : ϖ ∣ V.b₂)
    (hb₈ : ϖ ^ 3 ∣ V.b₈) (hb₆ : ¬ ϖ ^ 3 ∣ V.b₆) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) 1 = (quadratic ϖ V 1).shiftBy γ := by
  have hϖ : ϖ ≠ 0 := hprime.ne_zero
  have hpr : (span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ).mpr hprime
  have h2res : (2 : R ⧸ span {ϖ}) = 0 := two_residue_eq_zero hϖ2
  have ha₁ : ϖ ∣ V.a₁ := dvd_a₁_of_dvd_b₂ hprime hϖ2 hb₂
  obtain ⟨c₂, hc₂⟩ := hϖ2
  obtain ⟨c₄, hc₄⟩ := dvd_four_of_dvd_two (ϖ := ϖ) ⟨c₂, hc₂⟩
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  have hX : ϖ ∣ ϖ ^ 2 * α₁ ^ 2 * α₆ + 4 * V.a₂ * α₆ - ϖ * α₁ * α₃ * α₄
      + V.a₂ * α₃ ^ 2 - α₄ ^ 2 := by
    have h : ϖ ^ 3 ∣ ϖ ^ 2 * (ϖ ^ 2 * α₁ ^ 2 * α₆ + 4 * V.a₂ * α₆ - ϖ * α₁ * α₃ * α₄
        + V.a₂ * α₃ ^ 2 - α₄ ^ 2) := by
      rw [show ϖ ^ 2 * (ϖ ^ 2 * α₁ ^ 2 * α₆ + 4 * V.a₂ * α₆ - ϖ * α₁ * α₃ * α₄
          + V.a₂ * α₃ ^ 2 - α₄ ^ 2) = V.b₈ from by
        rw [WeierstrassCurve.b₈, e₁, e₃, e₄, e₆]; ring]
      exact hb₈
    rwa [show (ϖ : R) ^ 3 = ϖ ^ 2 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ)] at h
  have hkey : ϖ ∣ V.a₂ * α₃ ^ 2 - α₄ ^ 2 := by
    have hx := dvd_add (dvd_sub (dvd_sub hX (⟨ϖ * α₁ ^ 2 * α₆, by ring⟩ :
        ϖ ∣ ϖ ^ 2 * α₁ ^ 2 * α₆)) (⟨c₄ * V.a₂ * α₆, by rw [hc₄]; ring⟩ :
        ϖ ∣ 4 * V.a₂ * α₆)) (⟨α₁ * α₃ * α₄, by ring⟩ : ϖ ∣ ϖ * α₁ * α₃ * α₄)
    rwa [show ϖ ^ 2 * α₁ ^ 2 * α₆ + 4 * V.a₂ * α₆ - ϖ * α₁ * α₃ * α₄ + V.a₂ * α₃ ^ 2 - α₄ ^ 2
        - ϖ ^ 2 * α₁ ^ 2 * α₆ - 4 * V.a₂ * α₆ + ϖ * α₁ * α₃ * α₄
        = V.a₂ * α₃ ^ 2 - α₄ ^ 2 from by ring] at hx
  have hα34 : mod ϖ V.a₂ * mod ϖ α₃ = mod ϖ α₄ := by
    have h0 : mod ϖ (V.a₂ * α₃ ^ 2 - α₄ ^ 2) = 0 := (mod_eq_zero _ _).mpr hkey
    rwa [map_sub, map_mul, map_pow, map_pow, hsq (mod ϖ α₃), hsq (mod ϖ α₄), sub_eq_zero] at h0
  have hα3 : mod ϖ α₃ = 1 := by
    have hα₃n : ¬ ϖ ∣ α₃ := by
      rintro ⟨β, hβ⟩
      exact hb₆ ⟨ϖ * β ^ 2 + c₄ * α₆, by rw [WeierstrassCurve.b₆, e₃, e₆, hβ, hc₄]; ring⟩
    have h0 : mod ϖ α₃ * (mod ϖ α₃ - 1) = 0 := by linear_combination hsq (mod ϖ α₃)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left
      fun h => hα₃n ((mod_eq_zero _ _).mp h))
  have hres : mod ϖ ρ * mod ϖ α₄ + mod ϖ ρ ^ 2 * mod ϖ V.a₂ = 0 := by
    rw [← hα34, hα3, mul_one, hsq (mod ϖ ρ)]
    linear_combination (mod ϖ ρ * mod ϖ V.a₂) * h2res
  have d₃ : div V.a₃ (ϖ ^ 1) = α₃ :=
    div_eq_of_eq'' (pow_ne_zero 1 hϖ) (by rw [pow_one]; exact e₃)
  have d₆ : div V.a₆ (ϖ ^ 2) = α₆ := div_eq_of_eq'' (pow_ne_zero 2 hϖ) e₆
  have g₃ : div ((VariableChange.mk 1 r s t) • V).a₃ (ϖ ^ 1) = α₃ + ϖ * ρ * α₁ + 2 * τ :=
    div_eq_of_eq'' (pow_ne_zero 1 hϖ) (by rw [smulOne_a₃, e₁, e₃, hρ, hτ, pow_one]; ring)
  have g₆ : div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 2)
      = α₆ + ρ * α₄ + ρ ^ 2 * V.a₂ + ϖ * ρ ^ 3 - τ * α₃ - τ ^ 2 - ϖ * ρ * τ * α₁ :=
    div_eq_of_eq'' (pow_ne_zero 2 hϖ) (by rw [smulOne_a₆, e₁, e₃, e₄, e₆, hρ, hτ]; ring)
  refine ⟨mod ϖ τ, Cubic.shiftBy_eq_of_two_eq_zero h2res rfl rfl rfl rfl ?_ ?_⟩
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₃ (ϖ ^ 1)) = mod ϖ (div V.a₃ (ϖ ^ 1))
    rw [g₃, d₃, ← sub_eq_zero, ← map_sub, mod_eq_zero]
    exact ⟨ρ * α₁ + c₂ * τ, by rw [hc₂]; ring⟩
  · change -mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 2))
      = -mod ϖ (div V.a₆ (ϖ ^ 2)) + mod ϖ (div V.a₃ (ϖ ^ 1)) * mod ϖ τ + mod ϖ τ ^ 2
    rw [g₆, d₆, d₃]
    simp only [map_add, map_sub, map_mul, map_pow, mod_self]
    linear_combination -hres

/-! ### Step 8's `Splits` test at the even prime

At the even prime, `HasDoubleRoot` of `Y² + (a₃/ϖ²)Y - a₆/ϖ⁴` is `c² = 4d = 0`, so Step 8's branch
test is `ϖ³ ∣ a₃`. Its `Splits` test on the same quadratic needs only `ϖ ∣ 2`. -/

/-- **Step 8's quadratic is the shift of the other curve's by `t/ϖ²`, at the even prime.**

Write `ρ = r/ϖ²`, `τ = t/ϖ²`, `α₃ = a₃/ϖ²`, `α₆ = a₆/ϖ⁴`. The valuations of the curve at Step 8 put
every term by which `a₆` moves into `(ϖ⁵)` except `-ta₃ - t² = -ϖ⁴(τα₃ + τ²)`, which is
`-ϖ⁴(cγ + γ²)` at `γ = τ`; and `a₃ ↦ a₃ + ra₁ + 2t` moves by an element of `(ϖ³)`, so the linear
coefficients agree. This needs only `ϖ ∣ 2`, not that the residue field is `𝔽₂`. -/
theorem Step8.quadratic_smul_of_dvd_two [IsDomain R] (hϖ : ϖ ≠ 0) (hϖ2 : ϖ ∣ 2)
    (hr : ϖ ^ 2 ∣ r) (ht : ϖ ^ 2 ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 3 ∣ V.a₄) (ha₆ : ϖ ^ 4 ∣ V.a₆) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) 2 = (quadratic ϖ V 2).shiftBy γ := by
  have h2res : (2 : R ⧸ span {ϖ}) = 0 := two_residue_eq_zero hϖ2
  obtain ⟨c₂, hc₂⟩ := hϖ2
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  have d₃ : div V.a₃ (ϖ ^ 2) = α₃ := div_eq_of_eq'' (pow_ne_zero 2 hϖ) e₃
  have d₆ : div V.a₆ (ϖ ^ 4) = α₆ := div_eq_of_eq'' (pow_ne_zero 4 hϖ) e₆
  have g₃ : div ((VariableChange.mk 1 r s t) • V).a₃ (ϖ ^ 2) = α₃ + ϖ * ρ * α₁ + 2 * τ :=
    div_eq_of_eq'' (pow_ne_zero 2 hϖ) (by rw [smulOne_a₃, e₁, e₃, hρ, hτ]; ring)
  have g₆ : div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 4)
      = α₆ + ϖ * ρ * α₄ + ϖ * ρ ^ 2 * α₂ + ϖ ^ 2 * ρ ^ 3 - τ * α₃ - τ ^ 2 - ϖ * ρ * τ * α₁ :=
    div_eq_of_eq'' (pow_ne_zero 4 hϖ) (by rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring)
  refine ⟨mod ϖ τ, Cubic.shiftBy_eq_of_two_eq_zero h2res rfl rfl rfl rfl ?_ ?_⟩
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₃ (ϖ ^ 2)) = mod ϖ (div V.a₃ (ϖ ^ 2))
    rw [g₃, d₃, ← sub_eq_zero, ← map_sub, mod_eq_zero]
    exact ⟨ρ * α₁ + c₂ * τ, by rw [hc₂]; ring⟩
  · change -mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 4))
      = -mod ϖ (div V.a₆ (ϖ ^ 4)) + mod ϖ (div V.a₃ (ϖ ^ 2)) * mod ϖ τ + mod ϖ τ ^ 2
    rw [g₆, d₆, d₃]
    simp only [map_add, map_sub, map_mul, map_pow, mod_self]
    ring

/-- **Step 8's `Splits` answer agrees on an integral translate, at the even prime.** The two
quadratics are shifts of one another, and a shift does not change whether a cubic splits. -/
theorem Step8.splits_smul_of_dvd_two [IsDomain R] [(span {ϖ}).IsMaximal] (hϖ : ϖ ≠ 0)
    (hϖ2 : ϖ ∣ 2) (hr : ϖ ^ 2 ∣ r) (ht : ϖ ^ 2 ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂)
    (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₄ : ϖ ^ 3 ∣ V.a₄) (ha₆ : ϖ ^ 4 ∣ V.a₆) :
    (quadratic ϖ ((VariableChange.mk 1 r s t) • V) 2).toPoly.Splits
      ↔ (quadratic ϖ V 2).toPoly.Splits := by
  obtain ⟨γ, hγ⟩ := Step8.quadratic_smul_of_dvd_two hϖ hϖ2 hr ht ha₁ ha₂ ha₃ ha₄ ha₆
  rw [hγ]; exact Cubic.splits_shiftBy _ _

/-- **Step 5's `Splits` answer agrees on an integral translate, at the even prime.** The two
quadratics are shifts of one another, and a shift does not change whether a cubic splits. -/
theorem Step5.splits_smul_of_dvd_two [IsDomain R] [(span {ϖ}).IsMaximal] (hprime : Prime ϖ)
    (hϖ2 : ϖ ∣ 2) (hsq : ∀ x : R ⧸ span {ϖ}, x ^ 2 = x) (hr : ϖ ∣ r) (ht : ϖ ∣ t)
    (ha₃ : ϖ ∣ V.a₃) (ha₄ : ϖ ∣ V.a₄) (ha₆ : ϖ ^ 2 ∣ V.a₆) (hb₂ : ϖ ∣ V.b₂)
    (hb₈ : ϖ ^ 3 ∣ V.b₈) (hb₆ : ¬ ϖ ^ 3 ∣ V.b₆) :
    (quadratic ϖ ((VariableChange.mk 1 r s t) • V) 1).toPoly.Splits
      ↔ (quadratic ϖ V 1).toPoly.Splits := by
  obtain ⟨γ, hγ⟩ :=
    Step5.quadratic_smul_of_dvd_two hprime hϖ2 hsq hr ht ha₃ ha₄ ha₆ hb₂ hb₈ hb₆
  rw [hγ]; exact Cubic.splits_shiftBy _ _

end WeierstrassCurve.TateAlgorithm
