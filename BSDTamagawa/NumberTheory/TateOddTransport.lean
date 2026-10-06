/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateRunInvariance

/-!
# Tate's algorithm along an integral change of variables at an odd prime

Let `ϖ` be a prime in a domain in which `2` is a unit. For two Weierstrass curves related by an
integral change of variables `(1, r, s, t)` whose parameters satisfy suitable divisibilities, the
coefficients tested by Steps 3, 4, 5, 9 and 10 of Tate's algorithm differ by elements of the ideal
the test reads, and the residue-field polynomials tested by Steps 5–8 are shifts of one another. We
prove `ϖ² ∣ r` from `ϖ⁴ ∣ b₆` on both curves, using that `b₆` moves by `2rb₄ + r²b₂ + 4r³`. As a
consequence, Steps 1–10 of Tate's algorithm do not terminate on the dilate
`σ(W) = ⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩` of a curve `W`, and the curve returned by Step 11 is an
integral translate of `W`. No division by `3` is used.

## Main results

* `WeierstrassCurve.smulOne_b₈`: `b₈` moves by `3rb₆ + 3r²b₄ + r³b₂ + 3r⁴`.
* `WeierstrassCurve.dvd_sq_r_of_dvd_b₆`: `ϖ² ∣ r` from `ϖ⁴ ∣ b₆` on both curves.
* `WeierstrassCurve.sq_dvd_sub_a₆_smulOne`, `WeierstrassCurve.cb_dvd_sub_b₈_smulOne`,
  `WeierstrassCurve.cb_dvd_sub_b₆_smulOne`, `WeierstrassCurve.pow_four_dvd_sub_a₄_smulOne`,
  `WeierstrassCurve.pow_six_dvd_sub_a₆_smulOne`: the coefficients tested by Steps 3, 4, 5, 9 and 10
  move by elements of the ideal the test reads.
* `WeierstrassCurve.TateAlgorithm.Step5.quadratic_smul_of_dvd`,
  `WeierstrassCurve.TateAlgorithm.Step6.cubic_smul_of_dvd`,
  `WeierstrassCurve.TateAlgorithm.Step8.quadratic_smul_of_dvd`: the polynomials tested by Steps 5,
  6 and 8 on the two curves are shifts of one another.
* `WeierstrassCurve.TateAlgorithm.Step6.card_roots_smul_of_dvd`,
  `WeierstrassCurve.TateAlgorithm.Step6.hasDoubleRoot_smul_of_dvd`,
  `WeierstrassCurve.TateAlgorithm.Step6.hasTripleRoot_smul_of_dvd`: the tests of Steps 6 and 7, and
  the Tamagawa number of Step 6, agree on the two curves.
* `WeierstrassCurve.TateAlgorithm.Step7.dvd_sq_r_of_state_of_dvd_b`: the loop invariant `ϖ ∣ s`,
  `ϖ² ∣ r` of Step 7 holds on entry.
* `WeierstrassCurve.TateAlgorithm.Step11.isIntTranslate_translate_of_dvd_b`: Step 11's rescaling
  carries an integral translate to an integral translate.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_scaleUp`: Step 11 returns a curve on the
  dilate `σ(W)`.
* `WeierstrassCurve.TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp_of_prime`: the curve
  returned by Step 11 on `σ(W)` is an integral translate of `W`.
-/

@[expose] public section

universe u

open CommRing Ideal Polynomial

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R} {r s t : R}

/-! ### `b₈` and the dilation's `b`-invariants -/

/-- **`b₈` under an integral translation:** `b₈ ↦ b₈ + 3rb₆ + 3r²b₄ + r³b₂ + 3r⁴`. -/
theorem smulOne_b₈ (V : WeierstrassCurve R) (r s t : R) :
    ((VariableChange.mk 1 r s t) • V).b₈
      = V.b₈ + 3 * r * V.b₆ + 3 * r ^ 2 * V.b₄ + r ^ 3 * V.b₂ + 3 * r ^ 4 := by
  simp [variableChange_b₈]

/-- The dilation multiplies `b₂` by `ϖ²`. -/
theorem scaleUp_b₂ (ϖ : R) (V : WeierstrassCurve R) : (scaleUp ϖ V).b₂ = ϖ ^ 2 * V.b₂ := by
  simp only [WeierstrassCurve.b₂, scaleUp]; ring

/-- The dilation multiplies `b₄` by `ϖ⁴`. -/
theorem scaleUp_b₄ (ϖ : R) (V : WeierstrassCurve R) : (scaleUp ϖ V).b₄ = ϖ ^ 4 * V.b₄ := by
  simp only [WeierstrassCurve.b₄, scaleUp]; ring

/-- The dilation multiplies `b₆` by `ϖ⁶`. -/
theorem scaleUp_b₆ (ϖ : R) (V : WeierstrassCurve R) : (scaleUp ϖ V).b₆ = ϖ ^ 6 * V.b₆ := by
  simp only [WeierstrassCurve.b₆, scaleUp]; ring

/-- The dilation multiplies `b₈` by `ϖ⁸`. -/
theorem scaleUp_b₈ (ϖ : R) (V : WeierstrassCurve R) : (scaleUp ϖ V).b₈ = ϖ ^ 8 * V.b₈ := by
  simp only [WeierstrassCurve.b₈, scaleUp]; ring

/-! ### `ϖ² ∣ r` from `b₆` -/

/-- **`ϖ² ∣ r` from `ϖ⁴ ∣ b₆` on both curves.** Let `ϖ` be prime, `2` a unit, `ϖ ∣ r`, `ϖ² ∣ b₂`
and `ϖ³ ∣ b₄`. If `ϖ⁴` divides `b₆` of both `V` and `(1, r, s, t) • V`, then `ϖ² ∣ r`.

Indeed `b₆` moves by `2rb₄ + r²b₂ + 4r³`. Writing `r = ϖρ`, the first two terms lie in `(ϖ⁴)`, so
`ϖ⁴ ∣ 4ϖ³ρ³`, i.e. `ϖ ∣ 4ρ³`, and `4` is a unit. -/
theorem dvd_sq_r_of_dvd_b₆ [IsDomain R] (hprime : Prime ϖ) (h2 : IsUnit (2 : R))
    (hb₂ : ϖ ^ 2 ∣ V.b₂) (hb₄ : ϖ ^ 3 ∣ V.b₄) (hb₆ : ϖ ^ 4 ∣ V.b₆)
    (hb₆' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).b₆) (hr : ϖ ∣ r) : ϖ ^ 2 ∣ r := by
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨B₄, hB₄⟩ := hb₄
  obtain ⟨B₆, hB₆⟩ := hb₆
  have h4 : IsUnit (4 : R) := by simpa [show (4 : R) = 2 * 2 by norm_num] using h2.mul h2
  have hsub : ϖ ^ 4 ∣ ϖ ^ 3 * (4 * ρ ^ 3) := by
    have hrest : ϖ ^ 4 ∣ V.b₆ + 2 * (ϖ * ρ) * V.b₄ + (ϖ * ρ) ^ 2 * V.b₂ :=
      ⟨B₆ + 2 * ρ * B₄ + ρ ^ 2 * B₂, by rw [hB₂, hB₄, hB₆]; ring⟩
    have h := dvd_sub hb₆' hrest
    rwa [smulOne_b₆, show V.b₆ + 2 * (ϖ * ρ) * V.b₄ + (ϖ * ρ) ^ 2 * V.b₂ + 4 * (ϖ * ρ) ^ 3
        - (V.b₆ + 2 * (ϖ * ρ) * V.b₄ + (ϖ * ρ) ^ 2 * V.b₂) = ϖ ^ 3 * (4 * ρ ^ 3) from by
      ring] at h
  rw [show (ϖ : R) ^ 4 = ϖ ^ 3 * ϖ from by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 3 hprime.ne_zero)] at hsub
  obtain ⟨ρ', rfl⟩ := hprime.dvd_of_dvd_pow (h4.dvd_mul_left.mp hsub)
  exact ⟨ρ', by ring⟩

/-! ### The five divisibility branch conditions

Each lemma below says that the coefficient a step tests moves by an element of the ideal the test
reads, so the test gives the same answer on the two curves. -/

/-- **Step 3's branch condition transports.** If `ϖ ∣ r`, `ϖ ∣ t`, `ϖ ∣ a₃` and `ϖ ∣ a₄`, then
every one of the six terms by which `a₆` moves lies in `(ϖ²)`. -/
theorem sq_dvd_sub_a₆_smulOne (hr : ϖ ∣ r) (ht : ϖ ∣ t) (ha₃ : ϖ ∣ V.a₃) (ha₄ : ϖ ∣ V.a₄) :
    ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₆ - V.a₆ := by
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  refine ⟨ρ * α₄ + ρ ^ 2 * V.a₂ + ϖ * ρ ^ 3 - τ * α₃ - τ ^ 2 - ρ * τ * V.a₁, ?_⟩
  rw [smulOne_a₆, hρ, hτ, e₃, e₄]
  ring

/-- **Step 4's branch condition transports.** If `ϖ ∣ r`, `ϖ ∣ b₂`, `ϖ ∣ b₄` and `ϖ² ∣ b₆`, then
the four terms `3rb₆`, `3r²b₄`, `r³b₂`, `3r⁴` by which `b₈` moves lie in `(ϖ³)`. -/
theorem cb_dvd_sub_b₈_smulOne (hr : ϖ ∣ r) (hb₂ : ϖ ∣ V.b₂) (hb₄ : ϖ ∣ V.b₄) (hb₆ : ϖ ^ 2 ∣ V.b₆) :
    ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).b₈ - V.b₈ := by
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨β₂, e₂⟩ := hb₂
  obtain ⟨β₄, e₄⟩ := hb₄
  obtain ⟨β₆, e₆⟩ := hb₆
  refine ⟨3 * ρ * β₆ + 3 * ρ ^ 2 * β₄ + ϖ * ρ ^ 3 * β₂ + 3 * ϖ * ρ ^ 4, ?_⟩
  rw [smulOne_b₈, hρ, e₂, e₄, e₆]
  ring

/-- **Step 5's branch condition transports.** If `ϖ ∣ r`, `ϖ ∣ b₂` and `ϖ² ∣ b₄`, then the three
terms `2rb₄`, `r²b₂`, `4r³` by which `b₆` moves lie in `(ϖ³)`. -/
theorem cb_dvd_sub_b₆_smulOne (hr : ϖ ∣ r) (hb₂ : ϖ ∣ V.b₂) (hb₄ : ϖ ^ 2 ∣ V.b₄) :
    ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).b₆ - V.b₆ := by
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨β₂, e₂⟩ := hb₂
  obtain ⟨β₄, e₄⟩ := hb₄
  refine ⟨2 * ρ * β₄ + ρ ^ 2 * β₂ + 4 * ρ ^ 3, ?_⟩
  rw [smulOne_b₆, hρ, e₂, e₄]
  ring

/-- **Step 9's branch condition transports.** If `ϖ ∣ s`, `ϖ² ∣ r`, `ϖ³ ∣ t`, `ϖ ∣ a₁`, `ϖ² ∣ a₂`
and `ϖ³ ∣ a₃`, then every term by which `a₄` moves lies in `(ϖ⁴)`. -/
theorem pow_four_dvd_sub_a₄_smulOne (hs : ϖ ∣ s) (hr : ϖ ^ 2 ∣ r) (ht : ϖ ^ 3 ∣ t)
    (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ^ 2 ∣ V.a₂) (ha₃ : ϖ ^ 3 ∣ V.a₃) :
    ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).a₄ - V.a₄ := by
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  refine ⟨-(σ * α₃) + 2 * ρ * α₂ - τ * α₁ - ρ * σ * α₁ + 3 * ρ ^ 2 - 2 * σ * τ, ?_⟩
  rw [smulOne_a₄, hσ, hρ, hτ, e₁, e₂, e₃]
  ring

/-- **Step 10's branch condition transports.** If `ϖ² ∣ r`, `ϖ³ ∣ t`, `ϖ ∣ a₁`, `ϖ² ∣ a₂`,
`ϖ³ ∣ a₃` and `ϖ⁴ ∣ a₄`, then every term by which `a₆` moves lies in `(ϖ⁶)`. -/
theorem pow_six_dvd_sub_a₆_smulOne (hr : ϖ ^ 2 ∣ r) (ht : ϖ ^ 3 ∣ t) (ha₁ : ϖ ∣ V.a₁)
    (ha₂ : ϖ ^ 2 ∣ V.a₂) (ha₃ : ϖ ^ 3 ∣ V.a₃) (ha₄ : ϖ ^ 4 ∣ V.a₄) :
    ϖ ^ 6 ∣ ((VariableChange.mk 1 r s t) • V).a₆ - V.a₆ := by
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  refine ⟨ρ * α₄ + ρ ^ 2 * α₂ + ρ ^ 3 - τ * α₃ - τ ^ 2 - ρ * τ * α₁, ?_⟩
  rw [smulOne_a₆, hρ, hτ, e₁, e₂, e₃, e₄]
  ring

/-! ### Valuations of the `b`-invariants from those of the `a`-coefficients -/

/-- If `ϖ ∣ a₁` and `ϖ² ∣ a₂`, then `ϖ² ∣ b₂`. -/
theorem sq_dvd_b₂_of (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ^ 2 ∣ V.a₂) : ϖ ^ 2 ∣ V.b₂ := by
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  exact ⟨α₁ ^ 2 + 4 * α₂, by rw [WeierstrassCurve.b₂, e₁, e₂]; ring⟩

/-- If `ϖ ∣ a₁`, `ϖ ^ i ∣ a₃` and `ϖ ^ j ∣ a₄`, then `ϖ ^ k ∣ b₄` whenever `k ≤ i + 1` and
`k ≤ j`. -/
theorem dvd_b₄_of {i j : ℕ} (ha₁ : ϖ ∣ V.a₁) (ha₃ : ϖ ^ i ∣ V.a₃) (ha₄ : ϖ ^ j ∣ V.a₄)
    {k : ℕ} (hik : k ≤ i + 1) (hjk : k ≤ j) : ϖ ^ k ∣ V.b₄ := by
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  refine dvd_add ((pow_dvd_pow ϖ hjk).trans ⟨2 * α₄, by rw [e₄]; ring⟩)
    ((pow_dvd_pow ϖ hik).trans ⟨α₁ * α₃, by rw [e₁, e₃, pow_succ]; ring⟩)

/-- If `ϖ ^ i ∣ a₃` and `ϖ ^ j ∣ a₆`, then `ϖ ^ k ∣ b₆` whenever `k ≤ 2i` and `k ≤ j`. -/
theorem dvd_b₆_of {i j : ℕ} (ha₃ : ϖ ^ i ∣ V.a₃) (ha₆ : ϖ ^ j ∣ V.a₆) {k : ℕ} (hik : k ≤ 2 * i)
    (hjk : k ≤ j) : ϖ ^ k ∣ V.b₆ := by
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₆, e₆⟩ := ha₆
  refine dvd_add ((pow_dvd_pow ϖ hik).trans ⟨α₃ ^ 2, by rw [e₃, two_mul, pow_add]; ring⟩)
    ((pow_dvd_pow ϖ hjk).trans ⟨4 * α₆, by rw [e₆]; ring⟩)

end WeierstrassCurve

namespace WeierstrassCurve.TateAlgorithm

variable {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R} {r s t : R}

/-- If `d ∣ y - x`, then `d ∣ y ↔ d ∣ x`. -/
theorem dvd_iff_of_dvd_sub {d x y : R} (h : d ∣ y - x) : d ∣ y ↔ d ∣ x :=
  ⟨fun hy => by simpa using dvd_sub hy h, fun hx => by simpa using dvd_add hx h⟩

/-- If `q ≠ 0` and `x = q * y`, then the exact quotient of `x` by `q` is `y`. -/
private theorem div_eq_of_eq' [NoZeroDivisors R] {q x y : R} (hq : q ≠ 0) (h : x = q * y) :
    div x q = y :=
  mul_left_cancel₀ hq (by rw [mul_div hq ⟨y, h⟩, h])

/-- Two elements divisible by `ϖ ^ n` and congruent modulo `ϖ ^ (n + 1)` have the same
`ϖ ^ n`-quotient modulo `ϖ`. -/
private theorem mod_div_eq_of_dvd_sub' [NoZeroDivisors R] (hϖ : ϖ ≠ 0) {x y : R} {n : ℕ}
    (hx : ϖ ^ n ∣ x) (hy : ϖ ^ n ∣ y) (h : ϖ ^ (n + 1) ∣ y - x) :
    mod ϖ (div y (ϖ ^ n)) = mod ϖ (div x (ϖ ^ n)) := by
  obtain ⟨c, hc⟩ := h
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero, ← div_sub (pow_ne_zero n hϖ) hy hx,
    div_eq_of_eq' (pow_ne_zero n hϖ) (show y - x = ϖ ^ n * (ϖ * c) from by rw [hc]; ring)]
  exact dvd_mul_right _ _

/-! ### The polynomials of Steps 5, 6 and 8 under an integral translation -/

/-- **Step 5's quadratic is a shift of the other curve's.** Let `2` be a unit, `ϖ ≠ 0` and `ϖ ∣ r`.
If `ϖ ∣ b₂`, `ϖ² ∣ b₄`, and both `V` and `(1, r, s, t) • V` satisfy `ϖ ∣ a₃` and `ϖ² ∣ a₆`, then
`quadratic ϖ · 1` of the translated curve is a shift of that of `V`. -/
theorem Step5.quadratic_smul_of_dvd [IsDomain R] (h2 : IsUnit (2 : R)) (hϖ : ϖ ≠ 0) (hr : ϖ ∣ r)
    (ha₃ : ϖ ∣ V.a₃) (ha₆ : ϖ ^ 2 ∣ V.a₆) (hb₂ : ϖ ∣ V.b₂) (hb₄ : ϖ ^ 2 ∣ V.b₄)
    (ha₃' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₆' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) 1 = (quadratic ϖ V 1).shiftBy γ := by
  refine Cubic.exists_shiftBy_of_discr_eq ?_ rfl rfl rfl rfl ?_
  · have hu := h2.map (mod ϖ)
    rwa [map_ofNat] at hu
  · rw [quadratic_discr hϖ (n := 1) (m := 2) (by norm_num) (by simpa using ha₃') ha₆',
      quadratic_discr hϖ (n := 1) (m := 2) (by norm_num) (by simpa using ha₃) ha₆]
    refine mod_div_eq_of_dvd_sub' hϖ
      (WeierstrassCurve.dvd_b₆_of (i := 1) (j := 2) (by simpa using ha₃) ha₆ (by norm_num)
        (by norm_num))
      (WeierstrassCurve.dvd_b₆_of (i := 1) (j := 2) (by simpa using ha₃') ha₆' (by norm_num)
        (by norm_num))
      (WeierstrassCurve.cb_dvd_sub_b₆_smulOne hr hb₂ hb₄)

/-- **Step 8's quadratic is a shift of the other curve's.** Let `2` be a unit, `ϖ ≠ 0` and
`ϖ² ∣ r`. If `ϖ² ∣ b₂`, `ϖ³ ∣ b₄`, and both `V` and `(1, r, s, t) • V` satisfy `ϖ² ∣ a₃` and
`ϖ⁴ ∣ a₆`, then `quadratic ϖ · 2` of the translated curve is a shift of that of `V`. -/
theorem Step8.quadratic_smul_of_dvd [IsDomain R] (h2 : IsUnit (2 : R)) (hϖ : ϖ ≠ 0)
    (hr : ϖ ^ 2 ∣ r) (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₆ : ϖ ^ 4 ∣ V.a₆) (hb₂ : ϖ ^ 2 ∣ V.b₂)
    (hb₄ : ϖ ^ 3 ∣ V.b₄) (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₆' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) 2 = (quadratic ϖ V 2).shiftBy γ := by
  have hdiff : ϖ ^ 5 ∣ ((VariableChange.mk 1 r s t) • V).b₆ - V.b₆ := by
    obtain ⟨ρ, hρ⟩ := hr
    obtain ⟨u₄, hu₄⟩ := hb₄
    obtain ⟨u₂, hu₂⟩ := hb₂
    exact ⟨2 * ρ * u₄ + ϖ * ρ ^ 2 * u₂ + 4 * ϖ * ρ ^ 3, by rw [smulOne_b₆, hρ, hu₄, hu₂]; ring⟩
  refine Cubic.exists_shiftBy_of_discr_eq ?_ rfl rfl rfl rfl ?_
  · have hu := h2.map (mod ϖ)
    rwa [map_ofNat] at hu
  · rw [quadratic_discr hϖ (n := 2) (m := 4) (by norm_num) ha₃' ha₆',
      quadratic_discr hϖ (n := 2) (m := 4) (by norm_num) ha₃ ha₆]
    exact mod_div_eq_of_dvd_sub' hϖ
      (WeierstrassCurve.dvd_b₆_of (i := 2) (j := 4) ha₃ ha₆ (by norm_num) (by norm_num))
      (WeierstrassCurve.dvd_b₆_of (i := 2) (j := 4) ha₃' ha₆' (by norm_num) (by norm_num)) hdiff

/-- **Step 6's cubic on an integral translate is the shift by `r/ϖ`.** If `ϖ ≠ 0`, `ϖ ∣ s`,
`ϖ ∣ r`, `ϖ² ∣ t`, and `V` has valuations at least `⟨1, 1, 2, 2, 3⟩`, then `cubic ϖ · 1 1` of
`(1, r, s, t) • V` is the shift of that of `V` by the residue of `r/ϖ`. -/
theorem Step6.cubic_smul_of_dvd [IsDomain R] (hϖ : ϖ ≠ 0) (hs : ϖ ∣ s) (hr : ϖ ∣ r)
    (ht : ϖ ^ 2 ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆) :
    cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1
      = (cubic ϖ V 1 1).shiftBy (mod ϖ (div r ϖ)) := by
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht
  have dr : div r ϖ = ρ := div_eq_of_eq' hϖ hρ
  have d₂ : div V.a₂ ϖ = α₂ := div_eq_of_eq' hϖ e₂
  have d₄ : div V.a₄ (ϖ ^ 2) = α₄ := div_eq_of_eq' (pow_ne_zero 2 hϖ) e₄
  have d₆ : div V.a₆ (ϖ ^ 3) = α₆ := div_eq_of_eq' (pow_ne_zero 3 hϖ) e₆
  have g₂ : div ((VariableChange.mk 1 r s t) • V).a₂ ϖ
      = α₂ - ϖ * σ * α₁ + 3 * ρ - ϖ * σ ^ 2 :=
    div_eq_of_eq' hϖ (by rw [smulOne_a₂, e₁, e₂, hρ, hσ]; ring)
  have g₄ : div ((VariableChange.mk 1 r s t) • V).a₄ (ϖ ^ 2)
      = α₄ - ϖ * σ * α₃ + 2 * ρ * α₂ - ϖ * (τ + ρ * σ) * α₁ + 3 * ρ ^ 2 - 2 * ϖ * σ * τ :=
    div_eq_of_eq' (pow_ne_zero 2 hϖ) (by rw [smulOne_a₄, e₁, e₂, e₃, e₄, hρ, hσ, hτ]; ring)
  have g₆ : div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 3)
      = α₆ + ρ * α₄ + ρ ^ 2 * α₂ + ρ ^ 3 - ϖ * τ * α₃ - ϖ * τ ^ 2 - ϖ * ρ * τ * α₁ :=
    div_eq_of_eq' (pow_ne_zero 3 hϖ) (by rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring)
  refine Cubic.ext rfl ?_ ?_ ?_
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₂ ϖ)
      = mod ϖ (div V.a₂ ϖ) + 3 * 1 * mod ϖ (div r ϖ)
    rw [g₂, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mod_self]
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₄ (ϖ ^ 2))
      = mod ϖ (div V.a₄ (ϖ ^ 2)) + 2 * mod ϖ (div V.a₂ ϖ) * mod ϖ (div r ϖ)
        + 3 * 1 * mod ϖ (div r ϖ) ^ 2
    rw [g₄, d₄, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mod_self]
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 3))
      = mod ϖ (div V.a₆ (ϖ ^ 3)) + mod ϖ (div V.a₄ (ϖ ^ 2)) * mod ϖ (div r ϖ)
        + mod ϖ (div V.a₂ ϖ) * mod ϖ (div r ϖ) ^ 2 + 1 * mod ϖ (div r ϖ) ^ 3
    rw [g₆, d₆, d₄, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, mod_self]
    ring

open scoped Classical in
/-- **Step 6's Tamagawa number agrees on an integral translate.** Under the hypotheses of
`Step6.cubic_smul_of_dvd`, the two cubics have the same number of distinct roots. -/
theorem Step6.card_roots_smul_of_dvd [IsDomain R] [(span {ϖ}).IsMaximal] (hϖ : ϖ ≠ 0) (hs : ϖ ∣ s)
    (hr : ϖ ∣ r) (ht : ϖ ^ 2 ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).toPoly.roots.toFinset.card
      = (cubic ϖ V 1 1).toPoly.roots.toFinset.card := by
  rw [Step6.cubic_smul_of_dvd hϖ hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆, Cubic.card_toFinset_roots_shiftBy]

/-- **Step 6's branch condition agrees on an integral translate.** Under the hypotheses of
`Step6.cubic_smul_of_dvd`, one cubic has a double root if and only if the other does. -/
theorem Step6.hasDoubleRoot_smul_of_dvd [IsDomain R] (hϖ : ϖ ≠ 0) (hs : ϖ ∣ s) (hr : ϖ ∣ r)
    (ht : ϖ ^ 2 ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).HasDoubleRoot
      ↔ (cubic ϖ V 1 1).HasDoubleRoot := by
  rw [Step6.cubic_smul_of_dvd hϖ hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆, Cubic.hasDoubleRoot_shiftBy]

/-- **Step 7's branch condition agrees on an integral translate.** Under the hypotheses of
`Step6.cubic_smul_of_dvd`, one cubic has a triple root if and only if the other does. -/
theorem Step6.hasTripleRoot_smul_of_dvd [IsDomain R] (hϖ : ϖ ≠ 0) (hs : ϖ ∣ s) (hr : ϖ ∣ r)
    (ht : ϖ ^ 2 ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).HasTripleRoot
      ↔ (cubic ϖ V 1 1).HasTripleRoot := by
  rw [Step6.cubic_smul_of_dvd hϖ hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆, Cubic.hasTripleRoot_shiftBy rfl]


/-! ### Step 7's subprocedure enters with `ϖ ∣ s` and `ϖ² ∣ r` -/

/-- **The subprocedure's parameter invariant holds on entry, at every odd prime.** Let `ϖ` be prime
and `2` a unit. If `V` has valuations at least `⟨1, 1, 2, 3, 4⟩` with `¬ϖ² ∣ a₂`, and
`(1, r, s, t) • V` satisfies `ϖ ∣ a₁`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄`, `ϖ⁴ ∣ a₆`, then `ϖ ∣ s` and `ϖ² ∣ r`.

Given `ϖ ∣ r`, write `r = ϖρ` and `α₂ = a₂/ϖ`: the `a₄`-bound gives `ϖ ∣ ρ(2α₂ + 3ρ)` and the
`a₆`-bound `ϖ ∣ ρ²(α₂ + ρ)`, and if `ϖ ∤ ρ` then `(2α₂ + 3ρ) - 3(α₂ + ρ) = -α₂` puts `a₂` in
`(ϖ²)`. -/
theorem Step7.dvd_sq_r_of_state_of_dvd_b [IsDomain R] (hprime : Prime ϖ) (h2 : IsUnit (2 : R))
    (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₄ : ϖ ^ 3 ∣ V.a₄)
    (ha₆ : ϖ ^ 4 ∣ V.a₆) (ha₂n : ¬ ϖ ^ 2 ∣ V.a₂)
    (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₁)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ϖ ∣ s ∧ ϖ ^ 2 ∣ r := by
  have hϖ : ϖ ≠ 0 := hprime.ne_zero
  have hs : ϖ ∣ s := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using ha₁) (by simpa using ha₁')
  have hr1 : ϖ ∣ r :=
    dvd_r_of_dvd_b₄_b₆ hprime h2
      (by simpa using WeierstrassCurve.dvd_b₄_of ha₁ ha₃ ha₄ (k := 1) (by norm_num) (by norm_num))
      (by
        simpa using WeierstrassCurve.dvd_b₄_of ha₁' ha₃' ha₄' (k := 1) (by norm_num) (by norm_num))
      (by simpa using WeierstrassCurve.dvd_b₆_of ha₃ ha₆ (k := 1) (by norm_num) (by norm_num))
      (by simpa using WeierstrassCurve.dvd_b₆_of ha₃' ha₆' (k := 1) (by norm_num) (by norm_num))
  have ht2 : ϖ ^ 2 ∣ t :=
    dvd_t_of_dvd_a₃ h2 ha₃ ha₃' (by rw [pow_two]; exact mul_dvd_mul hr1 ha₁)
  refine ⟨hs, ?_⟩
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr1
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht2
  have k4 : ϖ ∣ ρ * (2 * α₂ + 3 * ρ) := by
    have hsub : ϖ ^ 3 ∣ ϖ ^ 2 * (ρ * (2 * α₂ + 3 * ρ)) := by
      have hx := dvd_sub ha₄' (dvd_mul_right (ϖ ^ 3)
        (α₄ - σ * α₃ - τ * α₁ - ρ * σ * α₁ - 2 * σ * τ))
      rwa [show ((VariableChange.mk 1 r s t) • V).a₄
          - ϖ ^ 3 * (α₄ - σ * α₃ - τ * α₁ - ρ * σ * α₁ - 2 * σ * τ)
          = ϖ ^ 2 * (ρ * (2 * α₂ + 3 * ρ)) from by
        rw [smulOne_a₄, e₁, e₂, e₃, e₄, hρ, hσ, hτ]; ring] at hx
    rwa [show (ϖ : R) ^ 3 = ϖ ^ 2 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ)] at hsub
  have k6 : ϖ ∣ ρ * (ρ * (α₂ + ρ)) := by
    have hsub : ϖ ^ 4 ∣ ϖ ^ 3 * (ρ * (ρ * (α₂ + ρ))) := by
      have hx := dvd_sub ha₆' (dvd_mul_right (ϖ ^ 4)
        (α₆ + ρ * α₄ - τ * α₃ - τ ^ 2 - ρ * τ * α₁))
      rwa [show ((VariableChange.mk 1 r s t) • V).a₆
          - ϖ ^ 4 * (α₆ + ρ * α₄ - τ * α₃ - τ ^ 2 - ρ * τ * α₁)
          = ϖ ^ 3 * (ρ * (ρ * (α₂ + ρ))) from by
        rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring] at hx
    rwa [show (ϖ : R) ^ 4 = ϖ ^ 3 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 3 hϖ)] at hsub
  by_contra hcon
  have hρnd : ¬ ϖ ∣ ρ := by
    rintro ⟨ρ', hρ'⟩
    exact hcon ⟨ρ', by rw [hρ, hρ']; ring⟩
  have hk1 : ϖ ∣ 2 * α₂ + 3 * ρ := (hprime.dvd_mul.mp k4).resolve_left hρnd
  have hk2 : ϖ ∣ α₂ + ρ :=
    (hprime.dvd_mul.mp ((hprime.dvd_mul.mp k6).resolve_left hρnd)).resolve_left hρnd
  have hα₂ : ϖ ∣ α₂ := by
    have hx := dvd_sub hk1 (hk2.mul_left 3)
    rw [show 2 * α₂ + 3 * ρ - 3 * (α₂ + ρ) = -α₂ from by ring] at hx
    exact dvd_neg.mp hx
  obtain ⟨α₂', hα₂'⟩ := hα₂
  exact ha₂n ⟨α₂', by rw [e₂, hα₂']; ring⟩

/-! ### Step 11's rescaling, at every odd prime -/

/-- **Step 11's rescaling carries an integral translate to an integral translate**, at every odd
prime. Let `ϖ` be prime and `2` a unit. If `W` has valuations at least `⟨1, 2, 3, 4, 6⟩` and
`(1, r, s, t) • W` satisfies `ϖ ∣ a₁`, `ϖ³ ∣ a₃`, `ϖ⁴ ∣ a₄`, `ϖ⁶ ∣ a₆`, then the rescalings of the
two curves by Step 11 are integral translates of one another. -/
theorem Step11.isIntTranslate_translate_of_dvd_b [(span {ϖ}).IsMaximal] [IsDomain R]
    (hprime : Prime ϖ) (h2 : IsUnit (2 : R)) {W : WeierstrassCurve R} {r s t : R}
    (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₄ : ϖ ^ 4 ∣ W.a₄)
    (ha₆ : ϖ ^ 6 ∣ W.a₆) (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • W).a₁)
    (ha₃' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • W).a₃)
    (ha₄' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • W).a₄)
    (ha₆' : ϖ ^ 6 ∣ ((VariableChange.mk 1 r s t) • W).a₆) :
    IsIntTranslate (Step11.translate ϖ W)
      (Step11.translate ϖ ((VariableChange.mk 1 r s t) • W)) := by
  have hϖ : ϖ ≠ 0 := hprime.ne_zero
  have hb₂ : ϖ ^ 2 ∣ W.b₂ := WeierstrassCurve.sq_dvd_b₂_of ha₁ ha₂
  have hb₄ : ϖ ^ 4 ∣ W.b₄ := WeierstrassCurve.dvd_b₄_of ha₁ ha₃ ha₄ (by norm_num) (by norm_num)
  have hb₆ : ϖ ^ 6 ∣ W.b₆ := WeierstrassCurve.dvd_b₆_of ha₃ ha₆ (by norm_num) (by norm_num)
  have hb₄' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • W).b₄ :=
    WeierstrassCurve.dvd_b₄_of ha₁' ha₃' ha₄' (by norm_num) (by norm_num)
  have hb₆' : ϖ ^ 6 ∣ ((VariableChange.mk 1 r s t) • W).b₆ :=
    WeierstrassCurve.dvd_b₆_of ha₃' ha₆' (by norm_num) (by norm_num)
  have hs : ϖ ∣ s := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using ha₁) (by simpa using ha₁')
  have hr1 : ϖ ∣ r :=
    dvd_r_of_dvd_b₄_b₆ hprime h2 ((dvd_pow_self ϖ (by norm_num)).trans hb₄)
      ((dvd_pow_self ϖ (by norm_num)).trans hb₄') ((dvd_pow_self ϖ (by norm_num)).trans hb₆)
      ((dvd_pow_self ϖ (by norm_num)).trans hb₆')
  have hr : ϖ ^ 2 ∣ r :=
    WeierstrassCurve.dvd_sq_r_of_dvd_b₆ hprime h2 hb₂
      ((pow_dvd_pow ϖ (by norm_num : 3 ≤ 4)).trans hb₄)
      ((pow_dvd_pow ϖ (by norm_num : 4 ≤ 6)).trans hb₆)
      ((pow_dvd_pow ϖ (by norm_num : 4 ≤ 6)).trans hb₆') hr1
  have ht : ϖ ^ 3 ∣ t :=
    dvd_t_of_dvd_a₃ h2 ha₃ ha₃'
      (by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]; exact mul_dvd_mul hr ha₁)
  have hbase : scaleUp ϖ (Step11.translate ϖ W) = W :=
    Step11.scaleUp_translate hϖ ha₁ ha₂ ha₃ ha₄ ha₆
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨τ, rfl⟩ := ht
  refine ⟨ρ, σ, τ, ?_⟩
  have key := Step11.translate_smul_scaleUp hϖ (Step11.translate ϖ W) ρ σ τ
  rw [hbase] at key
  exact key

/-! ### Steps 1–10 do not terminate on a dilate, at every odd prime

The dilate `σ(W) = ⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩` satisfies every valuation condition of the ten
branch tests, and the curve that reaches each step is an integral translate of it. On `σ(W)` the
Step-6 cubic is `X³` and the Step-8 quadratic is `Y²`. -/

/-- `ϖ ^ k` divides `ϖ ^ j * x` whenever `k ≤ j`. -/
private theorem pow_dvd_pow_mul' {k j : ℕ} (hjk : k ≤ j) (x : R) : ϖ ^ k ∣ ϖ ^ j * x :=
  ⟨ϖ ^ (j - k) * x, by rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjk]⟩

/-- Dividing `ϖ ^ k x` by a strictly smaller power of `ϖ` leaves something in `(ϖ)`. -/
private theorem mod_div_pow_mul_eq_zero [IsDomain R] (hϖ : ϖ ≠ 0) {k j : ℕ} (hjk : j < k) (x : R) :
    mod ϖ (div (ϖ ^ k * x) (ϖ ^ j)) = 0 := by
  rw [div_eq_of_eq' (pow_ne_zero j hϖ)
      (show ϖ ^ k * x = ϖ ^ j * (ϖ ^ (k - j) * x) from by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjk.le]),
    mod_eq_zero]
  exact (dvd_pow_self ϖ (by omega)).mul_right x

/-- Dividing `ϖ ^ k x` by `ϖ` leaves something in `(ϖ)`, for `k ≥ 2`. -/
private theorem mod_div_pow_mul_eq_zero_one [IsDomain R] (hϖ : ϖ ≠ 0) {k : ℕ} (hk : 1 < k) (x : R) :
    mod ϖ (div (ϖ ^ k * x) ϖ) = 0 := by
  simpa using mod_div_pow_mul_eq_zero hϖ (j := 1) hk x

/-- **Step 6's double-root test passes on a dilate.** The Step-6 cubic of `σ(W)` is `X³`: each of
`a₂/ϖ`, `a₄/ϖ²`, `a₆/ϖ³` still carries a factor of `ϖ` on the dilate, so all three vanish in the
residue field, and the discriminant of `X³` is `0`. -/
theorem hasDoubleRoot_cubic_scaleUp [IsDomain R] (hϖ : ϖ ≠ 0) (W : WeierstrassCurve R) :
    (cubic ϖ (scaleUp ϖ W) 1 1).HasDoubleRoot := by
  have hb : (cubic ϖ (scaleUp ϖ W) 1 1).b = 0 := by
    change mod ϖ (div (ϖ ^ 2 * W.a₂) ϖ) = 0
    exact mod_div_pow_mul_eq_zero_one hϖ (by norm_num) W.a₂
  have hc : (cubic ϖ (scaleUp ϖ W) 1 1).c = 0 := by
    change mod ϖ (div (ϖ ^ 4 * W.a₄) (ϖ ^ 2)) = 0
    exact mod_div_pow_mul_eq_zero hϖ (by norm_num) W.a₄
  have hd : (cubic ϖ (scaleUp ϖ W) 1 1).d = 0 := by
    change mod ϖ (div (ϖ ^ 6 * W.a₆) (ϖ ^ 3)) = 0
    exact mod_div_pow_mul_eq_zero hϖ (by norm_num) W.a₆
  rw [Cubic.hasDoubleRoot_of_a_eq_one (by simp [cubic]), hb, hc, hd]
  ring

/-- **Step 7's triple-root test passes on a dilate.** `HasTripleRoot` is `b² = 3c`, and the Step-6
cubic of `σ(W)` has `b = c = 0`. -/
theorem hasTripleRoot_cubic_scaleUp [IsDomain R] (hϖ : ϖ ≠ 0) (W : WeierstrassCurve R) :
    (cubic ϖ (scaleUp ϖ W) 1 1).HasTripleRoot := by
  have hb : (cubic ϖ (scaleUp ϖ W) 1 1).b = 0 := by
    change mod ϖ (div (ϖ ^ 2 * W.a₂) ϖ) = 0
    exact mod_div_pow_mul_eq_zero_one hϖ (by norm_num) W.a₂
  have hc : (cubic ϖ (scaleUp ϖ W) 1 1).c = 0 := by
    change mod ϖ (div (ϖ ^ 4 * W.a₄) (ϖ ^ 2)) = 0
    exact mod_div_pow_mul_eq_zero hϖ (by norm_num) W.a₄
  rw [Cubic.HasTripleRoot, hb, hc]
  ring

/-- **Step 8's double-root test passes on a dilate.** The Step-8 quadratic of `σ(W)` is `Y²`: both
`a₃/ϖ²` and `a₆/ϖ⁴` still carry a factor of `ϖ`. -/
theorem hasDoubleRoot_quadratic_scaleUp [IsDomain R] (hϖ : ϖ ≠ 0) (W : WeierstrassCurve R) :
    (quadratic ϖ (scaleUp ϖ W) 2).HasDoubleRoot := by
  have hc : (quadratic ϖ (scaleUp ϖ W) 2).c = 0 := by
    change mod ϖ (div (ϖ ^ 3 * W.a₃) (ϖ ^ 2)) = 0
    exact mod_div_pow_mul_eq_zero hϖ (by norm_num) W.a₃
  have hd : (quadratic ϖ (scaleUp ϖ W) 2).d = 0 := by
    change -mod ϖ (div (ϖ ^ 6 * W.a₆) (ϖ ^ 4)) = 0
    rw [mod_div_pow_mul_eq_zero hϖ (by norm_num) W.a₆, neg_zero]
  rw [Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) (by simp [quadratic]), hc, hd]
  ring


/-- `ϖ` divides `ϖ ^ j * x` for `j ≠ 0`. -/
private theorem dvd_pow_mul' {j : ℕ} (hj : j ≠ 0) (x : R) : ϖ ∣ ϖ ^ j * x :=
  (dvd_pow_self ϖ hj).mul_right x

section Dilate

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsNoetherianRing R] [IsDomain R]

/-- **Steps 1–10 of Tate's algorithm do not terminate on a dilate, at every odd prime.** Let
`ϖ ≠ 0` be prime, and let `2` be a unit. For every curve `W` with `Δ(σ W) ≠ 0`, Step 11 returns a
curve on `σ W = ⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩`. -/
theorem Step11.run_eq_ok_of_scaleUp (hϖ : ϖ ≠ 0) (hprime : Prime ϖ) (h2 : IsUnit (2 : R))
    {W : WeierstrassCurve R} (hΔ : (scaleUp ϖ W).Δ ≠ 0) :
    ∃ V, Step11.run hϖ hΔ = Except.ok V := by
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
  have hSa₆2 : ϖ ^ 2 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSa₆3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSa₆4 : ϖ ^ 4 ∣ (scaleUp ϖ W).a₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSa₆6
  have hSb₂2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₂ := by rw [scaleUp_b₂]; exact Dvd.intro _ rfl
  have hSb₄4 : ϖ ^ 4 ∣ (scaleUp ϖ W).b₄ := by rw [scaleUp_b₄]; exact Dvd.intro _ rfl
  have hSb₆6 : ϖ ^ 6 ∣ (scaleUp ϖ W).b₆ := by rw [scaleUp_b₆]; exact Dvd.intro _ rfl
  have hSb₈3 : ϖ ^ 3 ∣ (scaleUp ϖ W).b₈ := by
    rw [scaleUp_b₈]; exact pow_dvd_pow_mul' (by norm_num) _
  have hSb₂1 : ϖ ∣ (scaleUp ϖ W).b₂ := (dvd_pow_self ϖ two_ne_zero).trans hSb₂2
  have hSb₄1 : ϖ ∣ (scaleUp ϖ W).b₄ := (dvd_pow_self ϖ (by norm_num)).trans hSb₄4
  have hSb₄2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₄4
  have hSb₄3 : ϖ ^ 3 ∣ (scaleUp ϖ W).b₄ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₄4
  have hSb₆1 : ϖ ∣ (scaleUp ϖ W).b₆ := (dvd_pow_self ϖ (by norm_num)).trans hSb₆6
  have hSb₆2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₆6
  have hSb₆3 : ϖ ^ 3 ∣ (scaleUp ϖ W).b₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₆6
  have hSb₆4 : ϖ ^ 4 ∣ (scaleUp ϖ W).b₆ := (pow_dvd_pow ϖ (by norm_num)).trans hSb₆6
  have hdΔ : ϖ ∣ (scaleUp ϖ W).Δ := by rw [scaleUp_Δ]; exact dvd_pow_mul' (by norm_num) _
  have hc₄ : ϖ ∣ (scaleUp ϖ W).c₄ := by rw [scaleUp_c₄]; exact dvd_pow_mul' (by norm_num) _
  have h2run : Step2.run ϖ (scaleUp ϖ W) = Except.ok (Step2.translate ϖ (scaleUp ϖ W)) :=
    Step2.run_eq_ok_of_dvd_c₄ hdΔ hc₄
  obtain ⟨r₂, s₂, t₂, hrel₂⟩ := Step2.isIntTranslate_translate (ϖ := ϖ) (scaleUp ϖ W)
  have hv2 := Step2.run_hasValuation h2run
  have hr₂ : ϖ ∣ r₂ :=
    dvd_r_of_dvd_b₄_b₆ hprime h2 hSb₄1 (by rw [← hrel₂]; simpa using hv2.b₄) hSb₆1
      (by rw [← hrel₂]; simpa using hv2.b₆)
  have ht₂ : ϖ ∣ t₂ := by
    have h := dvd_t_of_dvd_a₃ (m := 1) (V := scaleUp ϖ W) (r := r₂) (s := s₂) (t := t₂) h2
      (by simpa using hSa₃1) (by rw [← hrel₂]; simpa using hv2.a₃)
      (by simpa using hr₂.mul_right (scaleUp ϖ W).a₁)
    simpa using h
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
  have hs₆ : ϖ ∣ s₆ := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using hSa₁)
      (by rw [← hrel₆]; simpa using hval6.a₁)
  have hr₆ : ϖ ∣ r₆ :=
    dvd_r_of_dvd_b₄_b₆ hprime h2 hSb₄1
      (by rw [← hrel₆]; exact (dvd_pow_self ϖ two_ne_zero).trans hval6.b₄) hSb₆1
      (by rw [← hrel₆]; exact (dvd_pow_self ϖ three_ne_zero).trans hval6.b₆)
  have ht₆ : ϖ ^ 2 ∣ t₆ :=
    dvd_t_of_dvd_a₃ h2 hSa₃2 (by rw [← hrel₆]; exact hval6.a₃)
      (by rw [pow_two]; exact mul_dvd_mul hr₆ hSa₁)
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
    dvd_r_of_dvd_b₄_b₆ hprime h2 hSb₄1
      (by rw [← hrel₈]; exact (dvd_pow_self ϖ three_ne_zero).trans hval8.b₄) hSb₆1
      (by rw [← hrel₈]; exact (dvd_pow_self ϖ (by norm_num)).trans hval8.b₆)
  have hr₈ : ϖ ^ 2 ∣ r₈ :=
    WeierstrassCurve.dvd_sq_r_of_dvd_b₆ hprime h2 hSb₂2 hSb₄3 hSb₆4
      (by rw [← hrel₈]; exact hval8.b₆) hr₈1
  have hq : (quadratic ϖ (Step8.translate ϖ (Step6.translate ϖ
      (Step2.translate ϖ (scaleUp ϖ W)))) 2).HasDoubleRoot := by
    obtain ⟨γ, hγ⟩ : ∃ γ, quadratic ϖ (Step8.translate ϖ (Step6.translate ϖ
        (Step2.translate ϖ (scaleUp ϖ W)))) 2 = (quadratic ϖ (scaleUp ϖ W) 2).shiftBy γ := by
      rw [hrel₈]
      exact Step8.quadratic_smul_of_dvd h2 hϖ hr₈ hSa₃2 hSa₆4 hSb₂2 hSb₄3
        (by rw [← hrel₈]; exact hval8.a₃) (by rw [← hrel₈]; exact hval8.a₆)
    rw [hγ]
    exact (Cubic.hasDoubleRoot_shiftBy _ _).mpr (hasDoubleRoot_quadratic_scaleUp hϖ W)
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
  have hs₉ : ϖ ∣ s₉ := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using hSa₁)
      (by rw [← hrel₉]; simpa using hval9.a₁)
  have hr₉1 : ϖ ∣ r₉ :=
    dvd_r_of_dvd_b₄_b₆ hprime h2 hSb₄1
      (by rw [← hrel₉]; exact (dvd_pow_self ϖ three_ne_zero).trans hval9.b₄) hSb₆1
      (by rw [← hrel₉]; exact (dvd_pow_self ϖ (by norm_num)).trans hval9.b₆)
  have hr₉ : ϖ ^ 2 ∣ r₉ :=
    WeierstrassCurve.dvd_sq_r_of_dvd_b₆ hprime h2 hSb₂2 hSb₄3 hSb₆4
      (by rw [← hrel₉]; exact (pow_dvd_pow ϖ (by norm_num : 4 ≤ 5)).trans hval9.b₆) hr₉1
  have ht₉ : ϖ ^ 3 ∣ t₉ :=
    dvd_t_of_dvd_a₃ h2 hSa₃3 (by rw [← hrel₉]; exact hval9.a₃)
      (by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]; exact mul_dvd_mul hr₉ hSa₁)
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


/-- **What Step 11 returns on a dilate, at every odd prime.** Let `ϖ ≠ 0` be prime, and let `2` be
a unit. If Step 11 returns `c` on `σ W`, then `c` is an integral translate of `W`. -/
theorem Step11.isIntTranslate_of_run_ok_scaleUp_of_prime (hϖ : ϖ ≠ 0) (hprime : Prime ϖ)
    (h2 : IsUnit (2 : R)) {W : WeierstrassCurve R} (hΔ : (scaleUp ϖ W).Δ ≠ 0)
    {c : WeierstrassCurve R} (h : Step11.run hϖ hΔ = .ok c) : IsIntTranslate W c := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, hc⟩
  obtain rfl : c = Step11.translate ϖ V := (Except.ok.inj hc).symm
  obtain ⟨r, s, t, rfl⟩ := Step10.isIntTranslate_of_run_ok hϖ hΔ hV
  have hval := Step10.run_hasValuation hϖ hΔ hV
  have hSa₁ : ϖ ∣ (scaleUp ϖ W).a₁ := ⟨W.a₁, rfl⟩
  have hSa₃3 : ϖ ^ 3 ∣ (scaleUp ϖ W).a₃ := ⟨W.a₃, rfl⟩
  have hSb₂2 : ϖ ^ 2 ∣ (scaleUp ϖ W).b₂ := by rw [scaleUp_b₂]; exact Dvd.intro _ rfl
  have hSb₄4 : ϖ ^ 4 ∣ (scaleUp ϖ W).b₄ := by rw [scaleUp_b₄]; exact Dvd.intro _ rfl
  have hSb₆6 : ϖ ^ 6 ∣ (scaleUp ϖ W).b₆ := by rw [scaleUp_b₆]; exact Dvd.intro _ rfl
  have hs : ϖ ∣ s := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using hSa₁) (by simpa using hval.a₁)
  have hr1 : ϖ ∣ r :=
    dvd_r_of_dvd_b₄_b₆ hprime h2 ((dvd_pow_self ϖ (by norm_num)).trans hSb₄4)
      ((dvd_pow_self ϖ (by norm_num)).trans hval.b₄)
      ((dvd_pow_self ϖ (by norm_num)).trans hSb₆6)
      ((dvd_pow_self ϖ (by norm_num)).trans hval.b₆)
  have hr : ϖ ^ 2 ∣ r :=
    WeierstrassCurve.dvd_sq_r_of_dvd_b₆ hprime h2 hSb₂2
      ((pow_dvd_pow ϖ (by norm_num : 3 ≤ 4)).trans hSb₄4)
      ((pow_dvd_pow ϖ (by norm_num : 4 ≤ 6)).trans hSb₆6)
      ((pow_dvd_pow ϖ (by norm_num : 4 ≤ 6)).trans hval.b₆) hr1
  have ht : ϖ ^ 3 ∣ t :=
    dvd_t_of_dvd_a₃ h2 hSa₃3 hval.a₃
      (by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]; exact mul_dvd_mul hr hSa₁)
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨τ, rfl⟩ := ht
  exact ⟨ρ, σ, τ, Step11.translate_smul_scaleUp hϖ W ρ σ τ⟩

end Dilate

end WeierstrassCurve.TateAlgorithm
