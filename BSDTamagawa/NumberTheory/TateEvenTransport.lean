/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateOddTransport

/-!
# Tate's algorithm along an integral change of variables at the even prime

Let `ϖ` be a prime with `ϖ ∣ 2` in a domain in which `3` is a unit. For two Weierstrass curves
related by an integral change of variables `(1, r, s, t)`, we bound the valuations of `r`, `s` and
`t` by the valuations of the coefficients of the two curves. Each parameter is bounded through a
coefficient in which it appears squared: `r` through `a₃` and `a₄` (via `ϖ ∣ 3r³`), `s` through
`a₂`, and `t` through `a₆`. As a consequence, Steps 1–10 of Tate's algorithm do not terminate on
the dilate `σ(W) = ⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩` of a curve `W`, and the curve returned by Step 11
is an integral translate of `W`. At `p = 2` this shows that
`WeierstrassCurve.StratScaleInvariant 2` follows from
`WeierstrassCurve.RunIntTranslateInvariant 2`.

## Main results

* `WeierstrassCurve.dvd_of_dvd_mul_add_of_dvd`: if `ϖ ^ m ∣ x`, `ϖ ^ (m + 1) ∣ y` and
  `ϖ ^ (2m + 1) ∣ x(x + y)`, then `ϖ ^ (m + 1) ∣ x`.
* `WeierstrassCurve.dvd_r_of_dvd_a₃_a₄`, `WeierstrassCurve.dvd_s_of_dvd_a₂`,
  `WeierstrassCurve.dvd_succ_t_of_dvd_a₆`, `WeierstrassCurve.dvd_t_of_dvd_a₆`,
  `WeierstrassCurve.dvd_sq_t_of_dvd_a₆`, `WeierstrassCurve.dvd_cb_t_of_dvd_a₆`: bounds on the
  parameters `r`, `s`, `t` of the change of variables.
* `PadicInt.isUnit_three_of_eq_two`: `3` is a unit of `ℤ_2`.
* `WeierstrassCurve.TateAlgorithm.Step2.dvd_of_state_of_dvd_two`,
  `WeierstrassCurve.TateAlgorithm.Step6.dvd_of_state_of_dvd_two`: the bounds at the valuations of
  the curves reaching Steps 3 and 6.
* `WeierstrassCurve.TateAlgorithm.Step6.hasDoubleRoot_smul_of_dvd_two`,
  `WeierstrassCurve.TateAlgorithm.Step6.hasTripleRoot_smul_of_dvd_two`,
  `WeierstrassCurve.TateAlgorithm.Step6.card_roots_smul_of_dvd_two`: the branch conditions of Steps
  6 and 7, and the Tamagawa number of Step 6, agree on the two curves.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_scaleUp_of_dvd_two`: Step 11 returns a curve
  on the dilate `σ(W)`.
* `WeierstrassCurve.TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp_of_dvd_two`: the curve
  returned by Step 11 on `σ(W)` is an integral translate of `W`.
* `WeierstrassCurve.stratScaleInvariant_of_runIntTranslateInvariant_two`:
  `RunIntTranslateInvariant 2` implies `StratScaleInvariant 2`.
-/

@[expose] public section

universe u

open CommRing Ideal

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R} {r s t : R}

/-! ### Divisibility of a square -/

/-- Let `ϖ` be prime. If `ϖ ^ m ∣ x`, `ϖ ^ (m + 1) ∣ y` and `ϖ ^ (2m + 1) ∣ x(x + y)`, then
`ϖ ^ (m + 1) ∣ x`: writing `x = ϖ ^ m ξ` and `y = ϖ ^ (m + 1) η` the product is
`ϖ ^ (2m) ξ(ξ + ϖη)`, so `ϖ ∣ ξ²` and hence `ϖ ∣ ξ`. -/
theorem dvd_of_dvd_mul_add_of_dvd [IsDomain R] (hprime : Prime ϖ) {m : ℕ} {x y : R}
    (hx : ϖ ^ m ∣ x) (hy : ϖ ^ (m + 1) ∣ y) (h : ϖ ^ (2 * m + 1) ∣ x * (x + y)) :
    ϖ ^ (m + 1) ∣ x := by
  obtain ⟨ξ, rfl⟩ := hx
  obtain ⟨η, rfl⟩ := hy
  have hsq : ϖ ^ m * ξ * (ϖ ^ m * ξ + ϖ ^ (m + 1) * η)
      = ϖ ^ (2 * m) * (ξ * (ξ + ϖ * η)) := by
    rw [two_mul, pow_add, pow_succ]; ring
  rw [hsq, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero (2 * m) hprime.ne_zero)] at h
  have hξ : ϖ ∣ ξ := by
    refine hprime.dvd_of_dvd_pow (n := 2) ?_
    have hx := dvd_sub h (Dvd.intro (ξ * η) (by ring) : ϖ ∣ ϖ * (ξ * η))
    rwa [show ξ * (ξ + ϖ * η) - ϖ * (ξ * η) = ξ ^ 2 from by ring] at hx
  obtain ⟨ξ', rfl⟩ := hξ
  exact ⟨ξ', by rw [pow_succ]; ring⟩

/-! ### Bounds on the parameters at the even prime -/

/-- **`ϖ ∣ r` from `ϖ ∣ a₃` and `ϖ ∣ a₄` on both curves, at the even prime.** Let `ϖ` be a prime
with `ϖ ∣ 2`, and let `3` be a unit. If `ϖ` divides `a₃` and `a₄` of both `V` and
`(1, r, s, t) • V`, then `ϖ ∣ r`.

Indeed `a₃ ↦ a₃ + ra₁ + 2t` gives `ϖ ∣ ra₁`; then `a₄ ↦ a₄ - sa₃ + 2ra₂ - (t + rs)a₁ + 3r² - 2st`
gives `ϖ ∣ 3r² - ta₁`; and `r(3r² - ta₁) + t(ra₁) = 3r³`. -/
theorem dvd_r_of_dvd_a₃_a₄ [IsDomain R] (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2) (h3 : IsUnit (3 : R))
    (ha₃ : ϖ ∣ V.a₃) (ha₄ : ϖ ∣ V.a₄)
    (ha₃' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₄) : ϖ ∣ r := by
  have hra₁ : ϖ ∣ r * V.a₁ := by
    have hx := dvd_sub (dvd_sub ha₃' ha₃) (hϖ2.mul_right t)
    rwa [smulOne_a₃, show V.a₃ + r * V.a₁ + 2 * t - V.a₃ - 2 * t = r * V.a₁ from by ring] at hx
  have hkey : ϖ ∣ 3 * r ^ 2 - t * V.a₁ := by
    have hx := dvd_add (dvd_add (dvd_sub (dvd_add (dvd_sub ha₄' ha₄) (ha₃.mul_left s))
      (hϖ2.mul_right (r * V.a₂))) (hra₁.mul_left s)) (hϖ2.mul_right (s * t))
    rwa [smulOne_a₄, show V.a₄ - s * V.a₃ + 2 * r * V.a₂ - (t + r * s) * V.a₁ + 3 * r ^ 2
        - 2 * s * t - V.a₄ + s * V.a₃ - 2 * (r * V.a₂) + s * (r * V.a₁) + 2 * (s * t)
        = 3 * r ^ 2 - t * V.a₁ from by ring] at hx
  refine hprime.dvd_of_dvd_pow (n := 3) ?_
  have hx := dvd_add (hkey.mul_left r) (hra₁.mul_left t)
  rw [show r * (3 * r ^ 2 - t * V.a₁) + t * (r * V.a₁) = 3 * r ^ 3 from by ring] at hx
  rwa [h3.dvd_mul_left] at hx

/-- **`ϖ ∣ s` from `ϖ ∣ a₂` on both curves.** Let `ϖ` be prime, `ϖ ∣ a₁` and `ϖ ∣ r`. If `ϖ`
divides `a₂` of both `V` and `(1, r, s, t) • V`, then `ϖ ∣ s`, since `a₂ ↦ a₂ - sa₁ + 3r - s²`. -/
theorem dvd_s_of_dvd_a₂ [IsDomain R] (hprime : Prime ϖ) (ha₁ : ϖ ∣ V.a₁) (hr : ϖ ∣ r)
    (ha₂ : ϖ ∣ V.a₂) (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂) : ϖ ∣ s := by
  refine hprime.dvd_of_dvd_pow (n := 2) ?_
  have hx := dvd_add (dvd_sub (dvd_sub ha₂ ha₂') (ha₁.mul_left s)) (hr.mul_left 3)
  rwa [smulOne_a₂, show V.a₂ - (V.a₂ - s * V.a₁ + 3 * r - s ^ 2) - s * V.a₁ + 3 * r = s ^ 2 from by
    ring] at hx

/-- **`ϖ ^ (m + 1) ∣ t` from `ϖ ^ (2m + 1) ∣ a₆` on both curves.** Let `ϖ` be prime, and suppose
`ϖ ^ m ∣ t`, `ϖ ^ (m + 1) ∣ u` and `ϖ ^ (2m + 1) ∣ X`, where `u = a₃ + ra₁` and
`X = ra₄ + r²a₂ + r³`. If `ϖ ^ (2m + 1)` divides `a₆` of both `V` and `(1, r, s, t) • V`, then
`ϖ ^ (m + 1) ∣ t`, since the change of variables moves `a₆` by `X - t(t + u)`. -/
theorem dvd_succ_t_of_dvd_a₆ [IsDomain R] (hprime : Prime ϖ) {m : ℕ} (ht : ϖ ^ m ∣ t)
    (hu : ϖ ^ (m + 1) ∣ V.a₃ + r * V.a₁)
    (hX : ϖ ^ (2 * m + 1) ∣ r * V.a₄ + r ^ 2 * V.a₂ + r ^ 3)
    (ha₆ : ϖ ^ (2 * m + 1) ∣ V.a₆)
    (ha₆' : ϖ ^ (2 * m + 1) ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ^ (m + 1) ∣ t := by
  refine dvd_of_dvd_mul_add_of_dvd hprime ht hu ?_
  have hx := dvd_sub (dvd_add ha₆ hX) ha₆'
  rwa [smulOne_a₆, show V.a₆ + (r * V.a₄ + r ^ 2 * V.a₂ + r ^ 3)
      - (V.a₆ + r * V.a₄ + r ^ 2 * V.a₂ + r ^ 3 - t * V.a₃ - t ^ 2 - r * t * V.a₁)
      = t * (t + (V.a₃ + r * V.a₁)) from by ring] at hx

/-- **`ϖ ∣ t`.** Let `ϖ` be prime, `ϖ ∣ r` and `ϖ ∣ a₃`. If `ϖ` divides `a₆` of both `V` and
`(1, r, s, t) • V`, then `ϖ ∣ t`. -/
theorem dvd_t_of_dvd_a₆ [IsDomain R] (hprime : Prime ϖ) (hr : ϖ ∣ r) (ha₃ : ϖ ∣ V.a₃)
    (ha₆ : ϖ ∣ V.a₆) (ha₆' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ∣ t := by
  obtain ⟨ρ, e⟩ := hr
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨β, hβ⟩ := ha₆
  obtain ⟨β', hβ'⟩ := ha₆'
  obtain ⟨τ, hτ⟩ := dvd_succ_t_of_dvd_a₆ (V := V) (r := r) (s := s) (t := t) (m := 0) hprime
    ⟨t, by ring⟩
    ⟨α₃ + ρ * V.a₁, by rw [e, e₃]; ring⟩
    ⟨ρ * V.a₄ + ϖ * ρ ^ 2 * V.a₂ + ϖ ^ 2 * ρ ^ 3, by rw [e]; ring⟩
    ⟨β, by rw [hβ]; ring⟩ ⟨β', by rw [hβ']; ring⟩
  exact ⟨τ, by rw [hτ]; ring⟩

/-- **`ϖ² ∣ t`.** Let `ϖ` be prime, `ϖ ∣ r`, `ϖ ∣ t`, and let `V` have valuations at least
`⟨1, 1, 2, 2, 3⟩`. If `ϖ³` divides the `a₆` of `(1, r, s, t) • V`, then `ϖ² ∣ t`. -/
theorem dvd_sq_t_of_dvd_a₆ [IsDomain R] (hprime : Prime ϖ) (hr : ϖ ∣ r) (ha₁ : ϖ ∣ V.a₁)
    (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₄ : ϖ ^ 2 ∣ V.a₄) (ht : ϖ ∣ t)
    (ha₆ : ϖ ^ 3 ∣ V.a₆) (ha₆' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ^ 2 ∣ t := by
  obtain ⟨ρ, e⟩ := hr
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨τ₀, eτ⟩ := ht
  obtain ⟨β, hβ⟩ := ha₆
  obtain ⟨β', hβ'⟩ := ha₆'
  obtain ⟨τ, hτ⟩ := dvd_succ_t_of_dvd_a₆ (V := V) (r := r) (s := s) (t := t) (m := 1) hprime
    ⟨τ₀, by rw [eτ]; ring⟩
    ⟨α₃ + ρ * α₁, by rw [e, e₁, e₃]; ring⟩
    ⟨ρ * α₄ + ρ ^ 2 * α₂ + ρ ^ 3, by rw [e, e₂, e₄]; ring⟩
    ⟨β, by rw [hβ]⟩ ⟨β', by rw [hβ']⟩
  exact ⟨τ, by rw [hτ]⟩

/-- **`ϖ³ ∣ t`.** Let `ϖ` be prime, `ϖ² ∣ r`, `ϖ² ∣ t`, and let `V` have valuations at least
`⟨1, 1, 3, 3, 5⟩`. If `ϖ⁵` divides the `a₆` of `(1, r, s, t) • V`, then `ϖ³ ∣ t`. -/
theorem dvd_cb_t_of_dvd_a₆ [IsDomain R] (hprime : Prime ϖ) (hr : ϖ ^ 2 ∣ r) (ha₁ : ϖ ∣ V.a₁)
    (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 3 ∣ V.a₃) (ha₄ : ϖ ^ 3 ∣ V.a₄) (ht : ϖ ^ 2 ∣ t)
    (ha₆ : ϖ ^ 5 ∣ V.a₆) (ha₆' : ϖ ^ 5 ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ^ 3 ∣ t := by
  obtain ⟨ρ, e⟩ := hr
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨τ₀, eτ⟩ := ht
  obtain ⟨β, hβ⟩ := ha₆
  obtain ⟨β', hβ'⟩ := ha₆'
  obtain ⟨τ, hτ⟩ := dvd_succ_t_of_dvd_a₆ (V := V) (r := r) (s := s) (t := t) (m := 2) hprime
    ⟨τ₀, by rw [eτ]⟩
    ⟨α₃ + ρ * α₁, by rw [e, e₁, e₃]; ring⟩
    ⟨ρ * α₄ + ρ ^ 2 * α₂ + ϖ * ρ ^ 3, by rw [e, e₂, e₄]; ring⟩
    ⟨β, by rw [hβ]⟩ ⟨β', by rw [hβ']⟩
  exact ⟨τ, by rw [hτ]⟩

end WeierstrassCurve

/-! ### `3` is a unit at the even prime -/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **`3` is a unit of `ℤ_2`.** -/
theorem isUnit_three_of_eq_two (hp2 : p = 2) : IsUnit (3 : ℤ_[p]) := by
  subst hp2
  rw [isUnit_iff]
  rcases lt_or_eq_of_le (norm_le_one (3 : ℤ_[2])) with hlt | heq
  · exfalso
    have hn : ‖((3 : ℕ) : ℤ_[2])‖ < 1 := by push_cast; simpa using hlt
    rw [norm_natCast_lt_one_iff] at hn
    omega
  · exact heq

end PadicInt

namespace WeierstrassCurve.TateAlgorithm

variable {R : Type u} [CommRing R] {ϖ : R}

/-! ### The bounds at the valuations of Steps 2 and 6 -/

section Pinning

variable {V : WeierstrassCurve R} {r s t : R}

/-- **The bounds at Step 2's valuations, at the even prime.** Let `ϖ` be a prime with `ϖ ∣ 2`, and
let `3` be a unit. If `V` and `(1, r, s, t) • V` both satisfy `ϖ ∣ a₃`, `ϖ ∣ a₄`, `ϖ ∣ a₆`, then
`ϖ ∣ r` and `ϖ ∣ t`. -/
theorem Step2.dvd_of_state_of_dvd_two [IsDomain R] (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2)
    (h3 : IsUnit (3 : R)) (ha₃ : ϖ ∣ V.a₃) (ha₄ : ϖ ∣ V.a₄) (ha₆ : ϖ ∣ V.a₆)
    (ha₃' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ∣ r ∧ ϖ ∣ t := by
  have hr : ϖ ∣ r := WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 ha₃ ha₄ ha₃' ha₄'
  exact ⟨hr, WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr ha₃ ha₆ ha₆'⟩

/-- **The bounds at Step 6's valuations, at the even prime.** Let `ϖ` be a prime with `ϖ ∣ 2`, and
let `3` be a unit. If `V` and `(1, r, s, t) • V` both satisfy `ϖ ∣ a₂`, `ϖ² ∣ a₃`, `ϖ² ∣ a₄`,
`ϖ³ ∣ a₆`, and `ϖ ∣ V.a₁`, then `ϖ ∣ s`, `ϖ ∣ r` and `ϖ² ∣ t`. -/
theorem Step6.dvd_of_state_of_dvd_two [IsDomain R] (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2)
    (h3 : IsUnit (3 : R)) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ϖ ∣ s ∧ ϖ ∣ r ∧ ϖ ^ 2 ∣ t := by
  have ha₃1 : ϖ ∣ V.a₃ := (dvd_pow_self ϖ two_ne_zero).trans ha₃
  have ha₆1 : ϖ ∣ V.a₆ := (dvd_pow_self ϖ three_ne_zero).trans ha₆
  have hr : ϖ ∣ r :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 ha₃1
      ((dvd_pow_self ϖ two_ne_zero).trans ha₄)
      ((dvd_pow_self ϖ two_ne_zero).trans ha₃') ((dvd_pow_self ϖ two_ne_zero).trans ha₄')
  have hs : ϖ ∣ s := WeierstrassCurve.dvd_s_of_dvd_a₂ hprime ha₁ hr ha₂ ha₂'
  have ht1 : ϖ ∣ t :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr ha₃1 ha₆1
      ((dvd_pow_self ϖ three_ne_zero).trans ha₆')
  exact ⟨hs, hr, WeierstrassCurve.dvd_sq_t_of_dvd_a₆ hprime hr ha₁ ha₂ ha₃ ha₄ ht1 ha₆ ha₆'⟩

/-- **Step 6's branch condition agrees on an integral translate, at the even prime.** Under the
hypotheses of `Step6.dvd_of_state_of_dvd_two`, the cubic `cubic ϖ · 1 1` has a double root for
`(1, r, s, t) • V` if and only if it has one for `V`. -/
theorem Step6.hasDoubleRoot_smul_of_dvd_two [IsDomain R] (hϖ : ϖ ≠ 0) (hprime : Prime ϖ)
    (hϖ2 : ϖ ∣ 2) (h3 : IsUnit (3 : R)) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).HasDoubleRoot
      ↔ (cubic ϖ V 1 1).HasDoubleRoot := by
  obtain ⟨hs, hr, ht⟩ :=
    Step6.dvd_of_state_of_dvd_two hprime hϖ2 h3 ha₁ ha₂ ha₃ ha₄ ha₆ ha₂' ha₃' ha₄' ha₆'
  exact Step6.hasDoubleRoot_smul_of_dvd hϖ hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆

/-- **Step 7's branch condition agrees on an integral translate, at the even prime.** Under the
hypotheses of `Step6.dvd_of_state_of_dvd_two`, the cubic `cubic ϖ · 1 1` has a triple root for
`(1, r, s, t) • V` if and only if it has one for `V`. -/
theorem Step6.hasTripleRoot_smul_of_dvd_two [IsDomain R] (hϖ : ϖ ≠ 0) (hprime : Prime ϖ)
    (hϖ2 : ϖ ∣ 2) (h3 : IsUnit (3 : R)) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).HasTripleRoot
      ↔ (cubic ϖ V 1 1).HasTripleRoot := by
  obtain ⟨hs, hr, ht⟩ :=
    Step6.dvd_of_state_of_dvd_two hprime hϖ2 h3 ha₁ ha₂ ha₃ ha₄ ha₆ ha₂' ha₃' ha₄' ha₆'
  exact Step6.hasTripleRoot_smul_of_dvd hϖ hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆

open scoped Classical in
/-- **Step 6's Tamagawa number agrees on an integral translate, at the even prime.** Under the
hypotheses of `Step6.dvd_of_state_of_dvd_two`, the cubics `cubic ϖ · 1 1` of `(1, r, s, t) • V` and
of `V` have the same number of distinct roots. -/
theorem Step6.card_roots_smul_of_dvd_two [IsDomain R] [(span {ϖ}).IsMaximal] (hϖ : ϖ ≠ 0)
    (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2) (h3 : IsUnit (3 : R)) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂)
    (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).toPoly.roots.toFinset.card
      = (cubic ϖ V 1 1).toPoly.roots.toFinset.card := by
  obtain ⟨hs, hr, ht⟩ :=
    Step6.dvd_of_state_of_dvd_two hprime hϖ2 h3 ha₁ ha₂ ha₃ ha₄ ha₆ ha₂' ha₃' ha₄' ha₆'
  exact Step6.card_roots_smul_of_dvd hϖ hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆

end Pinning

/-! ### Steps 1–10 do not terminate on a dilate, at the even prime

The dilate `σ(W) = ⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩` satisfies every valuation condition of the ten
branch tests, and the curve that reaches each step is an integral translate of it. -/

section Dilate

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsNoetherianRing R] [IsDomain R]

/-- **Steps 1–10 of Tate's algorithm do not terminate on a dilate, at the even prime.** Let `ϖ ≠ 0`
be a prime with `ϖ ∣ 2`, and let `3` be a unit. For every curve `W` with `Δ(σ W) ≠ 0`, Step 11
returns a curve on `σ W`. -/
theorem Step11.run_eq_ok_of_scaleUp_of_dvd_two (hϖ : ϖ ≠ 0) (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2)
    (h3 : IsUnit (3 : R)) {W : WeierstrassCurve R} (hΔ : (scaleUp ϖ W).Δ ≠ 0) :
    ∃ V, Step11.run hϖ hΔ = Except.ok V := by
  have h2res : (2 : R ⧸ span {ϖ}) = 0 := by
    rwa [← map_ofNat (mod ϖ) 2, mod_eq_zero]
  have h4res : (4 : R ⧸ span {ϖ}) = 0 := by
    rw [show (4 : R ⧸ span {ϖ}) = 2 * 2 by norm_num, h2res, mul_zero]
  have hSa₁ : ϖ ∣ (scaleUp ϖ W).a₁ := ⟨W.a₁, rfl⟩
  have hSa₂2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₂ := ⟨W.a₂, rfl⟩
  have hSa₃3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₃ := ⟨W.a₃, rfl⟩
  have hSa₄4 : ϖ ^ 4 ∣ (scaleUp ϖ W).a₄ := ⟨W.a₄, rfl⟩
  have hSa₆6 : ϖ ^ 6 ∣ (scaleUp ϖ W).a₆ := ⟨W.a₆, rfl⟩
  have hSa₂1 : ϖ ∣ (scaleUp ϖ W).a₂ := (dvd_pow_self ϖ two_ne_zero).trans hSa₂2
  have hSa₃1 : ϖ ∣ (scaleUp ϖ W).a₃ := (dvd_pow_self ϖ three_ne_zero).trans hSa₃3
  have hSa₃2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₃ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₃3
  have hSa₄1 : ϖ ∣ (scaleUp ϖ W).a₄ := (dvd_pow_self ϖ (by norm_num)).trans hSa₄4
  have hSa₄2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₄4
  have hSa₄3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₄4
  have hSa₆1 : ϖ ∣ (scaleUp ϖ W).a₆ := (dvd_pow_self ϖ (by norm_num)).trans hSa₆6
  have hSa₆2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSa₆3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSa₆5 : ϖ ^ 5 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSb₂2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₂ := by rw [scaleUp_b₂]; exact Dvd.intro _ rfl
  have hSb₄4 : ϖ ^ 4 ∣ (scaleUp ϖ W).b₄ := by rw [scaleUp_b₄]; exact Dvd.intro _ rfl
  have hSb₆6 : ϖ ^ 6 ∣ (scaleUp ϖ W).b₆ := by rw [scaleUp_b₆]; exact Dvd.intro _ rfl
  have hSb₈3 : ϖ ^ 3 ∣ (scaleUp ϖ W).b₈ := by
    rw [scaleUp_b₈]; exact ⟨ϖ ^ 5 * W.b₈, by ring⟩
  have hSb₂1 : ϖ ∣ (scaleUp ϖ W).b₂ := (dvd_pow_self ϖ two_ne_zero).trans hSb₂2
  have hSb₄1 : ϖ ∣ (scaleUp ϖ W).b₄ := (dvd_pow_self ϖ (by norm_num)).trans hSb₄4
  have hSb₄2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₄4
  have hSb₆2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₆6
  have hSb₆3 : ϖ ^ 3 ∣ (scaleUp ϖ W).b₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₆6
  have hdΔ : ϖ ∣ (scaleUp ϖ W).Δ := by rw [scaleUp_Δ]; exact ⟨ϖ ^ 11 * W.Δ, by ring⟩
  have hc₄ : ϖ ∣ (scaleUp ϖ W).c₄ := by rw [scaleUp_c₄]; exact ⟨ϖ ^ 3 * W.c₄, by ring⟩
  have h2run : Step2.run ϖ (scaleUp ϖ W) = Except.ok (Step2.translate ϖ (scaleUp ϖ W)) :=
    Step2.run_eq_ok_of_dvd_c₄ hdΔ hc₄
  obtain ⟨r₂, s₂, t₂, hrel₂⟩ := Step2.isIntTranslate_translate (ϖ := ϖ) (scaleUp ϖ W)
  have hv2 := Step2.run_hasValuation h2run
  have hr₂ : ϖ ∣ r₂ :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 hSa₃1 hSa₄1
      (by rw [← hrel₂]; simpa using hv2.a₃) (by rw [← hrel₂]; simpa using hv2.a₄)
  have ht₂ : ϖ ∣ t₂ :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr₂ hSa₃1 hSa₆1
      (by rw [← hrel₂]; simpa using hv2.a₆)
  have hA₆ : ϖ ^ 2 ∣ (Step2.translate ϖ (scaleUp ϖ W)).a₆ := by
    rw [hrel₂]
    exact (dvd_iff_of_dvd_sub
      (WeierstrassCurve.sq_dvd_sub_a₆_smulOne hr₂ ht₂ hSa₃1 hSa₄1)).mpr hSa₆2
  have h3run : Step3.run ϖ (scaleUp ϖ W) = Except.ok (Step2.translate ϖ (scaleUp ϖ W)) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left hA₆
  have hB₈ : ϖ ^ 3 ∣ (Step2.translate ϖ (scaleUp ϖ W)).b₈ := by
    rw [hrel₂]
    exact (dvd_iff_of_dvd_sub
      (WeierstrassCurve.cb_dvd_sub_b₈_smulOne hr₂ hSb₂1 hSb₄1 hSb₆2)).mpr hSb₈3
  have h4run : Step4.run ϖ (scaleUp ϖ W) = Except.ok (Step2.translate ϖ (scaleUp ϖ W)) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    exact ite_eq_left hB₈
  have hB₆ : ϖ ^ 3 ∣ (Step2.translate ϖ (scaleUp ϖ W)).b₆ := by
    rw [hrel₂]
    exact (dvd_iff_of_dvd_sub
      (WeierstrassCurve.cb_dvd_sub_b₆_smulOne hr₂ hSb₂1 hSb₄2)).mpr hSb₆3
  have h5run : Step5.run ϖ (scaleUp ϖ W) = Except.ok (Step2.translate ϖ (scaleUp ϖ W)) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    exact ite_eq_left hB₆
  have hval5 := Step5.run_hasValuation hϖ h5run
  have hval6 := Step6.hasValuation_translate hϖ hval5
  obtain ⟨r₆, s₆, t₆, hrel₆⟩ :
      IsIntTranslate (scaleUp ϖ W) (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W))) :=
    (Step2.isIntTranslate_translate (scaleUp ϖ W)).trans ⟨0, _, _, rfl⟩
  have hr₆ : ϖ ∣ r₆ :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 hSa₃1 hSa₄1
      (by rw [← hrel₆]; exact (dvd_pow_self ϖ two_ne_zero).trans hval6.a₃)
      (by rw [← hrel₆]; exact (dvd_pow_self ϖ two_ne_zero).trans hval6.a₄)
  have hs₆ : ϖ ∣ s₆ :=
    WeierstrassCurve.dvd_s_of_dvd_a₂ hprime hSa₁ hr₆ hSa₂1
      (by rw [← hrel₆]; simpa using hval6.a₂)
  have ht₆1 : ϖ ∣ t₆ :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr₆ hSa₃1 hSa₆1
      (by rw [← hrel₆]; exact (dvd_pow_self ϖ three_ne_zero).trans hval6.a₆)
  have ht₆ : ϖ ^ 2 ∣ t₆ :=
    WeierstrassCurve.dvd_sq_t_of_dvd_a₆ hprime hr₆ hSa₁ hSa₂1 hSa₃2 hSa₄2 ht₆1 hSa₆3
      (by rw [← hrel₆]; exact hval6.a₆)
  have hdouble : (cubic ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W))) 1 1).HasDoubleRoot := by
    rw [hrel₆]
    exact (Step6.hasDoubleRoot_smul_of_dvd hϖ hs₆ hr₆ ht₆ hSa₁ hSa₂1 hSa₃2 hSa₄2 hSa₆3).mpr
      (hasDoubleRoot_cubic_scaleUp hϖ W)
  have htriple : (cubic ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W))) 1 1).HasTripleRoot := by
    rw [hrel₆]
    exact (Step6.hasTripleRoot_smul_of_dvd hϖ hs₆ hr₆ ht₆ hSa₁ hSa₂1 hSa₃2 hSa₄2 hSa₆3).mpr
      (hasTripleRoot_cubic_scaleUp hϖ W)
  have h6run : Step6.run ϖ (scaleUp ϖ W)
      = Except.ok (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W))) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    exact ite_eq_left hdouble
  have h7run : Step7.run hϖ hΔ
      = Except.ok (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W))) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W)) :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  have hval7 := Step7.run_hasValuation hϖ hΔ h7run
  have hval8 := Step8.hasValuation_translate hϖ hval7 hdouble htriple
  obtain ⟨r₈, s₈, t₈, hrel₈⟩ :
      IsIntTranslate (scaleUp ϖ W)
        (Step8.translate ϖ (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W)))) :=
    IsIntTranslate.trans ⟨r₆, s₆, t₆, hrel₆⟩ ⟨_, 0, 0, rfl⟩
  have hr₈1 : ϖ ∣ r₈ :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 hSa₃1 hSa₄1
      (by rw [← hrel₈]; exact (dvd_pow_self ϖ two_ne_zero).trans hval8.a₃)
      (by rw [← hrel₈]; exact (dvd_pow_self ϖ three_ne_zero).trans hval8.a₄)
  have hs₈ : ϖ ∣ s₈ :=
    WeierstrassCurve.dvd_s_of_dvd_a₂ hprime hSa₁ hr₈1 hSa₂1
      (by rw [← hrel₈]; exact (dvd_pow_self ϖ two_ne_zero).trans hval8.a₂)
  have hr₈ : ϖ ^ 2 ∣ r₈ :=
    WeierstrassCurve.dvd_r_of_dvd_a₂ h3 hSa₂2 (by rw [← hrel₈]; exact hval8.a₂)
      (by rw [pow_two]; exact mul_dvd_mul hs₈ hSa₁)
      (by rw [pow_two ϖ, pow_two s₈]; exact mul_dvd_mul hs₈ hs₈)
  have ht₈1 : ϖ ∣ t₈ :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr₈1 hSa₃1 hSa₆1
      (by rw [← hrel₈]; exact (dvd_pow_self ϖ (by norm_num)).trans hval8.a₆)
  have ht₈ : ϖ ^ 2 ∣ t₈ :=
    WeierstrassCurve.dvd_sq_t_of_dvd_a₆ hprime hr₈1 hSa₁ hSa₂1 hSa₃2 hSa₄2 ht₈1 hSa₆3
      (by rw [← hrel₈]; exact (pow_dvd_pow ϖ (by norm_num : 3 ≤ 4)).trans hval8.a₆)
  have ha₃T : ϖ ^ 3 ∣ (Step8.translate ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W)))).a₃ := by
    rw [hrel₈, smulOne_a₃]
    refine dvd_add (dvd_add hSa₃3 ?_) ?_
    · rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]; exact mul_dvd_mul hr₈ hSa₁
    · rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]; exact mul_dvd_mul hϖ2 ht₈
  have hq : (quadratic ϖ (Step8.translate ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W)))) 2).HasDoubleRoot := by
    have hc : (quadratic ϖ (Step8.translate ϖ (Step6.translate ϖ
        (Step2.translate ϖ (scaleUp ϖ W)))) 2).c = 0 := by
      change mod ϖ (div _ (ϖ ^ 2)) = 0
      exact (mod_eq_zero _ _).mpr ((CommRing.pow_succ_dvd two_ne_zero).mp ha₃T).2
    rw [Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) (by simp [quadratic]), hc, h4res]
    ring
  have h8run : Step8.run hϖ hΔ = Except.ok (Step8.translate ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W)))) := by
    rw [Step8.run.eq_def, h7run]
    simp only [except_ok_bind]
    exact ite_eq_left hq
  have hval9 := Step9.hasValuation_translate hϖ hval8 hq
  obtain ⟨r₉, s₉, t₉, hrel₉⟩ :
      IsIntTranslate (scaleUp ϖ W) (Step9.translate ϖ (Step8.translate ϖ
        (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W))))) :=
    IsIntTranslate.trans ⟨r₈, s₈, t₈, hrel₈⟩ ⟨0, 0, _, rfl⟩
  have hr₉1 : ϖ ∣ r₉ :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 hSa₃1 hSa₄1
      (by rw [← hrel₉]; exact (dvd_pow_self ϖ three_ne_zero).trans hval9.a₃)
      (by rw [← hrel₉]; exact (dvd_pow_self ϖ (by norm_num)).trans hval9.a₄)
  have hs₉ : ϖ ∣ s₉ :=
    WeierstrassCurve.dvd_s_of_dvd_a₂ hprime hSa₁ hr₉1 hSa₂1
      (by rw [← hrel₉]; exact (dvd_pow_self ϖ two_ne_zero).trans hval9.a₂)
  have hr₉ : ϖ ^ 2 ∣ r₉ :=
    WeierstrassCurve.dvd_r_of_dvd_a₂ h3 hSa₂2 (by rw [← hrel₉]; exact hval9.a₂)
      (by rw [pow_two]; exact mul_dvd_mul hs₉ hSa₁)
      (by rw [pow_two ϖ, pow_two s₉]; exact mul_dvd_mul hs₉ hs₉)
  have ht₉1 : ϖ ∣ t₉ :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr₉1 hSa₃1 hSa₆1
      (by rw [← hrel₉]; exact (dvd_pow_self ϖ (by norm_num)).trans hval9.a₆)
  have ht₉2 : ϖ ^ 2 ∣ t₉ :=
    WeierstrassCurve.dvd_sq_t_of_dvd_a₆ hprime hr₉1 hSa₁ hSa₂1 hSa₃2 hSa₄2 ht₉1 hSa₆3
      (by rw [← hrel₉]; exact (pow_dvd_pow ϖ (by norm_num : 3 ≤ 5)).trans hval9.a₆)
  have ht₉ : ϖ ^ 3 ∣ t₉ :=
    WeierstrassCurve.dvd_cb_t_of_dvd_a₆ hprime hr₉ hSa₁ hSa₂1 hSa₃3 hSa₄3 ht₉2 hSa₆5
      (by rw [← hrel₉]; exact hval9.a₆)
  have h9cond : ϖ ^ 4 ∣ (Step9.translate ϖ (Step8.translate ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W))))).a₄ := by
    rw [hrel₉]
    exact (dvd_iff_of_dvd_sub (WeierstrassCurve.pow_four_dvd_sub_a₄_smulOne hs₉ hr₉ ht₉ hSa₁
      hSa₂2 hSa₃3)).mpr hSa₄4
  have h9run : Step9.run hϖ hΔ = Except.ok (Step9.translate ϖ (Step8.translate ϖ
      (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W))))) := by
    rw [Step9.run.eq_def, h8run]
    simp only [except_ok_bind]
    exact ite_eq_left h9cond
  have h10cond : ϖ ^ 6 ∣ (Step9.translate ϖ (Step8.translate ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W))))).a₆ := by
    rw [hrel₉]
    exact (dvd_iff_of_dvd_sub (WeierstrassCurve.pow_six_dvd_sub_a₆_smulOne hr₉ ht₉ hSa₁ hSa₂2
      hSa₃3 hSa₄4)).mpr hSa₆6
  have h10run : Step10.run hϖ hΔ = Except.ok (Step9.translate ϖ (Step8.translate ϖ
      (Step6.translate ϖ (Step2.translate ϖ (scaleUp ϖ W))))) := by
    rw [Step10.run.eq_def, h9run]
    simp only [except_ok_bind]
    exact ite_eq_left h10cond
  exact ⟨Step11.translate ϖ (Step9.translate ϖ (Step8.translate ϖ (Step6.translate ϖ
    (Step2.translate ϖ (scaleUp ϖ W))))), by rw [Step11.run.eq_def, h10run]; rfl⟩

/-- **What Step 11 returns on a dilate, at the even prime.** Let `ϖ ≠ 0` be a prime with `ϖ ∣ 2`,
and let `3` be a unit. If Step 11 returns `c` on `σ W`, then `c` is an integral translate of
`W`. -/
theorem Step11.isIntTranslate_of_run_ok_scaleUp_of_dvd_two (hϖ : ϖ ≠ 0) (hprime : Prime ϖ)
    (hϖ2 : ϖ ∣ 2) (h3 : IsUnit (3 : R)) {W : WeierstrassCurve R}
    (hΔ : (scaleUp ϖ W).Δ ≠ 0) {c : WeierstrassCurve R} (h : Step11.run hϖ hΔ = .ok c) :
    IsIntTranslate W c := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, hc⟩
  obtain rfl : c = Step11.translate ϖ V := (Except.ok.inj hc).symm
  obtain ⟨r, s, t, rfl⟩ := Step10.isIntTranslate_of_run_ok hϖ hΔ hV
  have hval := Step10.run_hasValuation hϖ hΔ hV
  have hSa₁ : ϖ ∣ (scaleUp ϖ W).a₁ := ⟨W.a₁, rfl⟩
  have hSa₂2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₂ := ⟨W.a₂, rfl⟩
  have hSa₃3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₃ := ⟨W.a₃, rfl⟩
  have hSa₄4 : ϖ ^ 4 ∣ (scaleUp ϖ W).a₄ := ⟨W.a₄, rfl⟩
  have hSa₆6 : ϖ ^ 6 ∣ (scaleUp ϖ W).a₆ := ⟨W.a₆, rfl⟩
  have hSa₂1 : ϖ ∣ (scaleUp ϖ W).a₂ := (dvd_pow_self ϖ two_ne_zero).trans hSa₂2
  have hSa₃1 : ϖ ∣ (scaleUp ϖ W).a₃ := (dvd_pow_self ϖ three_ne_zero).trans hSa₃3
  have hSa₃2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₃ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₃3
  have hSa₄1 : ϖ ∣ (scaleUp ϖ W).a₄ := (dvd_pow_self ϖ (by norm_num)).trans hSa₄4
  have hSa₄2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₄4
  have hSa₄3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₄4
  have hSa₆1 : ϖ ∣ (scaleUp ϖ W).a₆ := (dvd_pow_self ϖ (by norm_num)).trans hSa₆6
  have hSa₆3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSa₆5 : ϖ ^ 5 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hr1 : ϖ ∣ r :=
    WeierstrassCurve.dvd_r_of_dvd_a₃_a₄ hprime hϖ2 h3 hSa₃1 hSa₄1
      ((dvd_pow_self ϖ three_ne_zero).trans hval.a₃)
      ((dvd_pow_self ϖ (by norm_num)).trans hval.a₄)
  have hs : ϖ ∣ s :=
    WeierstrassCurve.dvd_s_of_dvd_a₂ hprime hSa₁ hr1 hSa₂1
      ((dvd_pow_self ϖ two_ne_zero).trans hval.a₂)
  have hr : ϖ ^ 2 ∣ r :=
    WeierstrassCurve.dvd_r_of_dvd_a₂ h3 hSa₂2 hval.a₂
      (by rw [pow_two]; exact mul_dvd_mul hs hSa₁)
      (by rw [pow_two ϖ, pow_two s]; exact mul_dvd_mul hs hs)
  have ht1 : ϖ ∣ t :=
    WeierstrassCurve.dvd_t_of_dvd_a₆ hprime hr1 hSa₃1 hSa₆1
      ((dvd_pow_self ϖ (by norm_num)).trans hval.a₆)
  have ht2 : ϖ ^ 2 ∣ t :=
    WeierstrassCurve.dvd_sq_t_of_dvd_a₆ hprime hr1 hSa₁ hSa₂1 hSa₃2 hSa₄2 ht1 hSa₆3
      ((pow_dvd_pow ϖ (by norm_num : 3 ≤ 6)).trans hval.a₆)
  have ht : ϖ ^ 3 ∣ t :=
    WeierstrassCurve.dvd_cb_t_of_dvd_a₆ hprime hr hSa₁ hSa₂1 hSa₃3 hSa₄3 ht2 hSa₆5
      ((pow_dvd_pow ϖ (by norm_num : 5 ≤ 6)).trans hval.a₆)
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨τ, rfl⟩ := ht
  exact ⟨ρ, σ, τ, Step11.translate_smul_scaleUp hϖ W ρ σ τ⟩

end Dilate

end WeierstrassCurve.TateAlgorithm

/-! ### `StratScaleInvariant 2` is `RunIntTranslateInvariant 2` -/

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy

/-- **`StratScaleInvariant 2` follows from `RunIntTranslateInvariant 2`.** Step 11 returns a curve
on the dilate (`TateAlgorithm.Step11.run_eq_ok_of_scaleUp_of_dvd_two`), that curve is an integral
translate of the base model (`TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp_of_dvd_two`),
and the hypothesis identifies the two reduction data. -/
theorem stratScaleInvariant_of_runIntTranslateInvariant_two (hp2 : p = 2)
    (h : RunIntTranslateInvariant p) : StratScaleInvariant p := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hϖ2 : (p : ℤ_[p]) ∣ 2 := by subst hp2; norm_num
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three_of_eq_two hp2
  have hrun : ∀ (W₁ W₂ : WeierstrassCurve ℤ_[p]), W₁ = W₂ → ∀ (h₁ : W₁.Δ ≠ 0) (h₂ : W₂.Δ ≠ 0),
      TateAlgorithm.run hϖ h₁ = TateAlgorithm.run hϖ h₂ := by
    intro W₁ W₂ e h₁ h₂; subst e; rfl
  intro x hx hσx
  have heq : ofShortNF (PadicInt.scaleProdByPPow 4 6 x).1 (PadicInt.scaleProdByPPow 4 6 x).2
      = scaleUp (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    rw [scaleUp_ofShortNF]; rfl
  have hΔσ : (scaleUp (p : ℤ_[p]) (ofShortNF x.1 x.2)).Δ ≠ 0 := by rw [← heq]; exact hσx
  obtain ⟨V, hV⟩ := TateAlgorithm.Step11.run_eq_ok_of_scaleUp_of_dvd_two hϖ PadicInt.prime_p
    hϖ2 h3 hΔσ
  have hVΔ : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔσ hV
  have hIT : IsIntTranslate (ofShortNF x.1 x.2) V :=
    TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp_of_dvd_two hϖ PadicInt.prime_p hϖ2 h3
      hΔσ hV
  obtain ⟨hk, ht⟩ := h (ofShortNF x.1 x.2) V hx hVΔ hIT
  simp only [strat, Prod.mk.injEq]
  rw [hrun _ _ heq hσx hΔσ, TateAlgorithm.run_eq_of_step11_ok hϖ hΔσ hV hVΔ]
  exact ⟨hk.symm, ht.symm⟩

end WeierstrassCurve
