/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.SmallPrimeStratum

/-!
# Step 11 of Tate's algorithm fires at `p = 3`

Over `ℤ_3`, on a short model `y² = x³ + a₄x + a₆` with `3³ ∣ a₄`, `3³ ∣ a₆` and `3¹⁴ ∣ Δ`, Tate's
algorithm passes Steps 1–10 without answering, so Step 11 fires. By
`WeierstrassCurve.exists_emultiplicity_of_mem_stratFibre_three`, every point of the
split-multiplicative stratum `τ_3⁻¹((I_t, t))` with `t ≥ 5` satisfies these hypotheses.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step5.run_eq_ok_of_cb_dvd_three`: Steps 1–5 pass on a short model
  over `ℤ_3` with `3³ ∣ a₄` and `3³ ∣ a₆`, handing on the Step-2 translate.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_three`: Steps 1–10 do not answer on a short
  model over `ℤ_3` with `3³ ∣ a₄`, `3³ ∣ a₆` and `3¹⁴ ∣ Δ`, so Step 11 fires.

## Implementation notes

At `p ≥ 5` the branch conditions of Steps 3–10 are usually expressed through `c₄`, `c₆` and `Δ`,
via identities involving `24`, `48`, `216`, `864` or `1728`, all divisible by `3`. At `p = 3` the
conditions of Steps 3–5 are checked directly on the Step-2 translate; in residue characteristic `3`
the cubic tests of Steps 6 and 7 reduce to `3² ∣ a₂` and `3³ ∣ a₄`; and the conditions of Steps
8–10 are read off `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆`, whose coefficients `27` and `9` are powers
of `3`.
-/

@[expose] public section

open CommRing Ideal

namespace WeierstrassCurve.TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Units, the residue field, and exact division at `p = 3` -/

/-- `2` is a unit of `ℤ_3`. -/
private theorem isUnit_two_three (hp3 : p = 3) : IsUnit (2 : ℤ_[p]) := by
  have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 2) (by rw [hp3]; norm_num)
  simpa using h

/-- `8` is a unit of `ℤ_3`. -/
private theorem isUnit_eight_three (hp3 : p = 3) : IsUnit (8 : ℤ_[p]) := by
  have h := (isUnit_two_three hp3).pow 3
  simpa [show (2 : ℤ_[p]) ^ 3 = 8 by norm_num] using h

/-- `3` does not divide `2` in `ℤ_3`. -/
private theorem not_dvd_two_three (hp3 : p = 3) : ¬ ((p : ℤ_[p]) ∣ 2) := fun h =>
  PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit h (isUnit_two_three hp3))

/-- `2 ≠ 0` in the residue field `𝔽_3`. -/
private theorem residue_two_ne_zero (hp3 : p = 3) :
    (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ 0 := by
  rw [← map_ofNat (mod (p : ℤ_[p])) 2, Ne, mod_eq_zero]
  exact not_dvd_two_three hp3

/-- `27 = 0` in the residue field `𝔽_3`. -/
private theorem residue_twentySeven_eq_zero (hp3 : p = 3) :
    (27 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
  rw [← map_ofNat (mod (p : ℤ_[p])) 27, mod_eq_zero]
  exact ⟨9, by subst hp3; push_cast; norm_num⟩

/-- Division by the exact power that divides is exact. -/
private theorem div_pow_mul (k : ℕ) (a : ℤ_[p]) :
    div ((p : ℤ_[p]) ^ k * a) ((p : ℤ_[p]) ^ k) = a :=
  mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-! ### The Step-2 translation at `p = 3` on a deep short model -/

/-- The `a₃`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₃_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 2 * t := by
  simp [variableChange_a₃]

/-- The `a₁`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₁_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
  simp [variableChange_a₁]

/-- The `a₂`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₂_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
  simp [variableChange_a₂]

/-- The `a₄`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₄_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = a₄ + 3 * r ^ 2 := by
  simp [variableChange_a₄]

/-- The `a₆`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₆_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
  simp [variableChange_a₆]

/-- The `b₆`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_b₆_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₆ = 4 * (a₆ + r * a₄ + r ^ 3) := by
  simp [WeierstrassCurve.b₆, variableChange_a₃, variableChange_a₆]; ring

/-- The `b₈`-coefficient of an integral translate with `s = 0` of a short model:
`12r(a₆ + ra₄ + r³) - (a₄ + 3r²)²`. -/
private theorem smulOne_b₈_ofShortNF (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₈
      = 12 * r * (a₆ + r * a₄ + r ^ 3) - (a₄ + 3 * r ^ 2) ^ 2 := by
  simp [WeierstrassCurve.b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring

/-- **At `p = 3`, the Step-2 translation of a deep short model is divisible by `3`.** On
`ofShortNF a₄ a₆` with `3 ∣ a₄` and `3 ∣ a₆`, an integral translate `⟨1, r, 0, t⟩ • W` whose `a₃`
and `a₆` are divisible by `3` has `3 ∣ r` and `3 ∣ t`. -/
theorem dvd_params_of_dvd_three (hp3 : p = 3) {a₄ a₆ r t : ℤ_[p]}
    (h₄ : (p : ℤ_[p]) ∣ a₄) (h₆ : (p : ℤ_[p]) ∣ a₆)
    (ha₃ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃)
    (ha₆ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆) :
    (p : ℤ_[p]) ∣ r ∧ (p : ℤ_[p]) ∣ t := by
  rw [smulOne_a₃_ofShortNF] at ha₃
  rw [smulOne_a₆_ofShortNF] at ha₆
  have ht : (p : ℤ_[p]) ∣ t := (isUnit_two_three hp3).dvd_mul_left.mp ha₃
  refine ⟨?_, ht⟩
  have ht2 : (p : ℤ_[p]) ∣ t ^ 2 := ht.trans (dvd_pow_self t two_ne_zero)
  have hcube : (p : ℤ_[p]) ∣ r ^ 3 := by
    have h := dvd_add (dvd_sub (dvd_sub ha₆ h₆) (h₄.mul_left r)) ht2
    have e : a₆ + r * a₄ + r ^ 3 - t ^ 2 - a₆ - r * a₄ + t ^ 2 = r ^ 3 := by ring
    rwa [e] at h
  exact PadicInt.prime_p.dvd_of_dvd_pow hcube

/-! ### Steps 1–5 at `p = 3` -/

/-- **The Step-2 translate of a deep short model at `p = 3`.** If `3³ ∣ a₄`, `3³ ∣ a₆` and `3 ∣ Δ`,
then the Step-2 translate of `ofShortNF a₄ a₆` has `a₁ = 0`, `3² ∣ a₂`, `3³ ∣ a₄`, `3² ∣ a₆`,
`3³ ∣ b₆` and `3³ ∣ b₈`. -/
theorem step2_translate_data_three (hp3 : p = 3) {a₄ a₆ : ℤ_[p]}
    (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄) (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆)
    (hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ) :
    (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₁ = 0 ∧
      (∃ A₂, (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₂ = (p : ℤ_[p]) ^ 2 * A₂) ∧
      (∃ A₄, (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₄ = (p : ℤ_[p]) ^ 3 * A₄) ∧
      (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₆ ∧
      (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).b₆ ∧
      (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).b₈ := by
  have h₄1 : (p : ℤ_[p]) ∣ a₄ := (dvd_pow_self _ three_ne_zero).trans h₄
  have h₆1 : (p : ℤ_[p]) ∣ a₆ := (dvd_pow_self _ three_ne_zero).trans h₆
  obtain ⟨α, hα⟩ := h₄
  obtain ⟨β, hβ⟩ := h₆
  obtain ⟨r, t, hT⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔ⟩
  have hval := Step2.hasValuation_translate hΔ
  have ha₃ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ := by
    rw [← hT]; simpa using hval.a₃
  have ha₆ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ := by
    rw [← hT]; simpa using hval.a₆
  obtain ⟨hr, ht⟩ := dvd_params_of_dvd_three hp3 h₄1 h₆1 ha₃ ha₆
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  refine ⟨by rw [hT, smulOne_a₁_ofShortNF], ⟨ρ, ?_⟩, ⟨α + ρ ^ 2, ?_⟩, ?_, ?_, ?_⟩
  · rw [hT, smulOne_a₂_ofShortNF, hρ]; subst hp3; push_cast; ring
  · rw [hT, smulOne_a₄_ofShortNF, hα, hρ]; subst hp3; push_cast; ring
  · rw [hT, smulOne_a₆_ofShortNF]
    refine ⟨(p : ℤ_[p]) * β + (p : ℤ_[p]) ^ 2 * ρ * α + (p : ℤ_[p]) * ρ ^ 3 - τ ^ 2, ?_⟩
    rw [hα, hβ, hρ, hτ]; ring
  · rw [hT, smulOne_b₆_ofShortNF]
    refine ⟨4 * (β + (p : ℤ_[p]) * ρ * α + ρ ^ 3), ?_⟩
    rw [hα, hβ, hρ]; ring
  · rw [hT, smulOne_b₈_ofShortNF]
    refine ⟨12 * (p : ℤ_[p]) * ρ * (β + (p : ℤ_[p]) * ρ * α + ρ ^ 3)
      - (p : ℤ_[p]) ^ 3 * (α + ρ ^ 2) ^ 2, ?_⟩
    rw [hα, hβ, hρ]; subst hp3; push_cast; ring

/-- `3 ∣ Δ` on a short model over `ℤ_3` with `3³ ∣ a₄` and `3³ ∣ a₆`. -/
private theorem dvd_Δ_ofShortNF_three (hp3 : p = 3) {a₄ a₆ : ℤ_[p]}
    (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄) (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆) :
    (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨α, hα⟩ := h₄
  obtain ⟨β, hβ⟩ := h₆
  refine ⟨(p : ℤ_[p]) ^ 8 * (-16) * (4 * α ^ 3 + β ^ 2), ?_⟩
  rw [ofShortNF_Δ, hα, hβ]; subst hp3; push_cast; ring

/-- **At `p = 3`, Steps 1–5 all pass on a short model with `3³ ∣ a₄` and `3³ ∣ a₆`**, and the curve
they hand on is the Step-2 translate of the input. -/
theorem Step5.run_eq_ok_of_cb_dvd_three (hp3 : p = 3) {a₄ a₆ : ℤ_[p]}
    (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄) (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆) :
    Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
  have hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := dvd_Δ_ofShortNF_three hp3 h₄ h₆
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
    dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inr hp3) a₄ a₆
  obtain ⟨-, -, -, hA6, hB6, hB8⟩ := step2_translate_data_three hp3 h₄ h₆ hΔ
  have h2 : Step2.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔ hc₄
  have h3 : Step3.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, h2]
    simp only [except_ok_bind]
    exact ite_eq_left hA6
  have h4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, h3]
    simp only [except_ok_bind]
    exact ite_eq_left hB8
  rw [Step5.run.eq_def, h4]
  simp only [except_ok_bind]
  exact ite_eq_left hB6

/-! ### Steps 6 and 7 at `p = 3` -/

/-- Step 6/7's cubic has `b = 0` when `ϖ² ∣ a₂`. -/
private theorem cubic_b_eq_zero {V : WeierstrassCurve ℤ_[p]} {A₂ : ℤ_[p]}
    (hA₂ : V.a₂ = (p : ℤ_[p]) ^ 2 * A₂) (a : ℤ_[p]) (n : ℕ) :
    (cubic (p : ℤ_[p]) V a n).b = 0 := by
  have h : div V.a₂ (p : ℤ_[p]) = (p : ℤ_[p]) * A₂ := by
    rw [hA₂, show (p : ℤ_[p]) ^ 2 * A₂ = (p : ℤ_[p]) ^ 1 * ((p : ℤ_[p]) * A₂) by ring, pow_one]
    simpa using div_pow_mul 1 ((p : ℤ_[p]) * A₂)
  simp only [cubic, h]
  exact (mod_eq_zero _ _).2 (dvd_mul_right _ _)

/-- Step 6/7's cubic has `c = 0` when `ϖ³ ∣ a₄`. -/
private theorem cubic_c_eq_zero {V : WeierstrassCurve ℤ_[p]} {A₄ : ℤ_[p]}
    (hA₄ : V.a₄ = (p : ℤ_[p]) ^ 3 * A₄) (a : ℤ_[p]) :
    (cubic (p : ℤ_[p]) V a 1).c = 0 := by
  have h : div V.a₄ ((p : ℤ_[p]) ^ 2) = (p : ℤ_[p]) * A₄ := by
    rw [hA₄, show (p : ℤ_[p]) ^ 3 * A₄ = (p : ℤ_[p]) ^ 2 * ((p : ℤ_[p]) * A₄) by ring]
    exact div_pow_mul 2 ((p : ℤ_[p]) * A₄)
  simp only [cubic, h]
  exact (mod_eq_zero _ _).2 (dvd_mul_right _ _)

/-- **Step 6's branch condition at `p = 3`.** If `ϖ² ∣ a₂` and `ϖ³ ∣ a₄`, the cubic of Step 6 has a
double root. -/
theorem hasDoubleRoot_of_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]} {A₂ A₄ : ℤ_[p]}
    (hA₂ : V.a₂ = (p : ℤ_[p]) ^ 2 * A₂) (hA₄ : V.a₄ = (p : ℤ_[p]) ^ 3 * A₄) :
    (cubic (p : ℤ_[p]) V 1 1).HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_one (by simp [cubic]), cubic_b_eq_zero hA₂ 1 1,
    cubic_c_eq_zero hA₄ 1]
  rw [residue_twentySeven_eq_zero hp3]
  ring

/-- **Step 7's branch condition at `p = 3`.** If `ϖ² ∣ a₂`, the cubic of Step 7 has a triple root.
-/
theorem hasTripleRoot_of_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]} {A₂ : ℤ_[p]}
    (hA₂ : V.a₂ = (p : ℤ_[p]) ^ 2 * A₂) : (cubic (p : ℤ_[p]) V 1 1).HasTripleRoot := by
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
    rw [← map_ofNat (mod (p : ℤ_[p])) 3, mod_eq_zero]
    exact ⟨1, by subst hp3; push_cast; ring⟩
  rw [Cubic.HasTripleRoot, cubic_b_eq_zero hA₂ 1 1, h3]
  ring

/-! ### The Step-6 translation at `p = 3` -/

/-- **The Step-6 shift `s` vanishes modulo `3` on a curve with `a₁ = 0`.** -/
theorem dvd_step6_s (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]} (ha₁ : V.a₁ = 0) :
    (p : ℤ_[p]) ∣ Step6.s (p : ℤ_[p]) V := by
  rw [← mod_eq_zero]
  simp only [Step6.s, mod_out, dite_eq_right (residue_two_ne_zero hp3), ha₁, map_zero, neg_zero,
    zero_div]

/-- The Step-6 translation of a curve with `a₁ = 0` has `a₂ = a₂ - s²`. -/
theorem step6_translate_a₂ (V : WeierstrassCurve ℤ_[p]) (ha₁ : V.a₁ = 0) :
    (Step6.translate (p : ℤ_[p]) V).a₂ = V.a₂ - Step6.s (p : ℤ_[p]) V ^ 2 := by
  simp [Step6.translate, variableChange_a₂, ha₁]

/-- The Step-6 translation of a curve with `a₁ = 0` has `a₄ = a₄ - s · a₃'`, where `a₃'` is the
translated `a₃`. -/
theorem step6_translate_a₄ (V : WeierstrassCurve ℤ_[p]) (ha₁ : V.a₁ = 0) :
    (Step6.translate (p : ℤ_[p]) V).a₄
      = V.a₄ - Step6.s (p : ℤ_[p]) V * (Step6.translate (p : ℤ_[p]) V).a₃ := by
  simp [Step6.translate, variableChange_a₄, variableChange_a₃, ha₁]
  ring

/-! ### Steps 8, 9 and 10 at `p = 3` -/

/-- Cancel a common power of `3` from a divisibility. -/
private theorem dvd_of_pow_dvd_pow_mul {k j : ℕ} {x : ℤ_[p]}
    (h : (p : ℤ_[p]) ^ (k + j) ∣ (p : ℤ_[p]) ^ k * x) : (p : ℤ_[p]) ^ j ∣ x := by
  rwa [pow_add, mul_dvd_mul_iff_left (pow_ne_zero k PadicInt.uniformizer_ne_zero)] at h

/-- **Step 9's branch condition at `p = 3`: `3⁴ ∣ a₄`.** If `3² ∣ b₂`, `3³ ∣ b₄`, `3⁵ ∣ b₆`,
`3⁶ ∣ b₈`, `3 ∣ a₁`, `3³ ∣ a₃` and `3¹⁰ ∣ Δ`, then `3⁴ ∣ a₄`. -/
theorem pow_four_dvd_a₄_of_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    {B₂ B₄ B₆ B₈ : ℤ_[p]}
    (hb₂ : V.b₂ = (p : ℤ_[p]) ^ 2 * B₂) (hb₄ : V.b₄ = (p : ℤ_[p]) ^ 3 * B₄)
    (hb₆ : V.b₆ = (p : ℤ_[p]) ^ 5 * B₆) (hb₈ : V.b₈ = (p : ℤ_[p]) ^ 6 * B₈)
    (ha₁ : (p : ℤ_[p]) ∣ V.a₁) (ha₃ : (p : ℤ_[p]) ^ 3 ∣ V.a₃)
    (hΔ : (p : ℤ_[p]) ^ 10 ∣ V.Δ) : (p : ℤ_[p]) ^ 4 ∣ V.a₄ := by
  have key : V.Δ = (p : ℤ_[p]) ^ 9 * (-(8 * B₄ ^ 3) + (p : ℤ_[p]) * (-(B₂ ^ 2 * B₈)
      - (p : ℤ_[p]) ^ 3 * B₆ ^ 2 + (p : ℤ_[p]) ^ 2 * (B₂ * B₄ * B₆))) := by
    rw [WeierstrassCurve.Δ, hb₂, hb₄, hb₆, hb₈]; subst hp3; push_cast; ring
  obtain ⟨y, hy⟩ := dvd_of_pow_dvd_pow_mul (k := 9) (j := 1) (by rw [← key]; exact hΔ)
  rw [pow_one] at hy
  have h8 : (p : ℤ_[p]) ∣ 8 * B₄ ^ 3 := by
    refine ⟨-y - B₂ ^ 2 * B₈ - (p : ℤ_[p]) ^ 3 * B₆ ^ 2 + (p : ℤ_[p]) ^ 2 * (B₂ * B₄ * B₆), ?_⟩
    linear_combination -hy
  have hB₄ : (p : ℤ_[p]) ∣ B₄ :=
    PadicInt.prime_p.dvd_of_dvd_pow ((isUnit_eight_three hp3).dvd_mul_left.mp h8)
  obtain ⟨C₄, hC₄⟩ := hB₄
  have hb₄' : (p : ℤ_[p]) ^ 4 ∣ V.b₄ := ⟨C₄, by rw [hb₄, hC₄]; ring⟩
  have h13 : (p : ℤ_[p]) ^ 4 ∣ V.a₁ * V.a₃ := by
    obtain ⟨u, hu⟩ := ha₁
    obtain ⟨v, hv⟩ := ha₃
    exact ⟨u * v, by rw [hu, hv]; ring⟩
  have h2a₄ : (p : ℤ_[p]) ^ 4 ∣ 2 * V.a₄ := by
    have e : 2 * V.a₄ = V.b₄ - V.a₁ * V.a₃ := by rw [WeierstrassCurve.b₄]; ring
    rw [e]; exact dvd_sub hb₄' h13
  exact (isUnit_two_three hp3).dvd_mul_left.mp h2a₄

/-- Cancel `3²` against `3` in a divisibility. -/
private theorem dvd_of_sq_dvd_mul {x : ℤ_[p]} (h : (p : ℤ_[p]) ^ 2 ∣ (p : ℤ_[p]) * x) :
    (p : ℤ_[p]) ∣ x := by
  rwa [pow_two, mul_dvd_mul_iff_left PadicInt.uniformizer_ne_zero] at h

/-- Cancel `3³` against `3²` in a divisibility. -/
private theorem dvd_of_cb_dvd_sq_mul {x : ℤ_[p]} (h : (p : ℤ_[p]) ^ 3 ∣ (p : ℤ_[p]) ^ 2 * x) :
    (p : ℤ_[p]) ∣ x := by
  rwa [show ((p : ℤ_[p])) ^ 3 = (p : ℤ_[p]) ^ 2 * (p : ℤ_[p]) by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)] at h

/-- `4` is a unit of `ℤ_3`. -/
private theorem isUnit_four_three (hp3 : p = 3) : IsUnit (4 : ℤ_[p]) := by
  have h := (isUnit_two_three hp3).pow 2
  simpa [show (2 : ℤ_[p]) ^ 2 = 4 by norm_num] using h

/-- **Step 8's `b₆`-condition at `p = 3`.** If `b₂ = 3²B₂`, `b₄ = 3³B₄`, `b₆ = 3⁴B₆`, `b₈ = 3⁶B₈`
and `3¹² ∣ Δ`, then `3 ∣ B₆`. -/
theorem dvd_B₆_of_three_step8 (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    {B₂ B₄ B₆ B₈ : ℤ_[p]}
    (hb₂ : V.b₂ = (p : ℤ_[p]) ^ 2 * B₂) (hb₄ : V.b₄ = (p : ℤ_[p]) ^ 3 * B₄)
    (hb₆ : V.b₆ = (p : ℤ_[p]) ^ 4 * B₆) (hb₈ : V.b₈ = (p : ℤ_[p]) ^ 6 * B₈)
    (hΔ : (p : ℤ_[p]) ^ 12 ∣ V.Δ) : (p : ℤ_[p]) ∣ B₆ := by
  have hrel : 4 * B₈ = B₂ * B₆ - B₄ ^ 2 := by
    have h := V.b_relation
    rw [hb₂, hb₄, hb₆, hb₈] at h
    refine mul_left_cancel₀ (pow_ne_zero 6 PadicInt.uniformizer_ne_zero) ?_
    linear_combination h
  have key : V.Δ = (p : ℤ_[p]) ^ 9 * (-(8 * B₄ ^ 3) - (p : ℤ_[p]) * (B₂ ^ 2 * B₈)
      + (p : ℤ_[p]) ^ 2 * (-(B₆ ^ 2) + B₂ * B₄ * B₆)) := by
    rw [WeierstrassCurve.Δ, hb₂, hb₄, hb₆, hb₈]; subst hp3; push_cast; ring
  obtain ⟨y, hy⟩ := dvd_of_pow_dvd_pow_mul (k := 9) (j := 3) (by rw [← key]; exact hΔ)
  have h8 : (p : ℤ_[p]) ∣ 8 * B₄ ^ 3 := by
    refine ⟨-((p : ℤ_[p]) ^ 2 * y) - B₂ ^ 2 * B₈
      + (p : ℤ_[p]) * (-(B₆ ^ 2) + B₂ * B₄ * B₆), ?_⟩
    linear_combination -hy
  obtain ⟨C₄, rfl⟩ : (p : ℤ_[p]) ∣ B₄ :=
    PadicInt.prime_p.dvd_of_dvd_pow ((isUnit_eight_three hp3).dvd_mul_left.mp h8)
  have hB₂₈ : (p : ℤ_[p]) ∣ B₂ ^ 2 * B₈ := by
    refine dvd_of_sq_dvd_mul ⟨-((p : ℤ_[p]) * y) - 8 * (p : ℤ_[p]) * C₄ ^ 3 - B₆ ^ 2
      + (p : ℤ_[p]) * B₂ * C₄ * B₆, ?_⟩
    linear_combination -hy
  by_cases hB₂ : (p : ℤ_[p]) ∣ B₂
  · obtain ⟨D₂, rfl⟩ := hB₂
    have h4B₈ : (p : ℤ_[p]) ∣ 4 * B₈ :=
      ⟨D₂ * B₆ - (p : ℤ_[p]) * C₄ ^ 2, by linear_combination hrel⟩
    obtain ⟨F₈, rfl⟩ : (p : ℤ_[p]) ∣ B₈ := (isUnit_four_three hp3).dvd_mul_left.mp h4B₈
    refine PadicInt.prime_p.dvd_of_dvd_pow (dvd_of_cb_dvd_sq_mul (x := B₆ ^ 2) ?_)
    exact ⟨-(8 * C₄ ^ 3) - (p : ℤ_[p]) * D₂ ^ 2 * F₈ + (p : ℤ_[p]) * D₂ * C₄ * B₆ - y, by
      linear_combination -hy⟩
  · have hB₈ : (p : ℤ_[p]) ∣ B₈ := by
      rcases PadicInt.prime_p.dvd_mul.mp hB₂₈ with h | h
      · exact absurd (PadicInt.prime_p.dvd_of_dvd_pow h) hB₂
      · exact h
    obtain ⟨F₈, rfl⟩ := hB₈
    have h2 : (p : ℤ_[p]) ∣ B₂ * B₆ :=
      ⟨4 * F₈ + (p : ℤ_[p]) * C₄ ^ 2, by linear_combination -hrel⟩
    rcases PadicInt.prime_p.dvd_mul.mp h2 with h | h
    · exact absurd h hB₂
    · exact h

/-- **Step 8's branch condition at `p = 3`.** If `b₂ = 3²B₂`, `b₄ = 3³B₄`, `b₈ = 3⁶B₈`,
`a₃ = 3²A₃`, `a₆ = 3⁴A₆` and `3¹² ∣ Δ`, then the Step-8 quadratic `Y² + A₃Y - A₆` has a double
root. -/
theorem quadratic_hasDoubleRoot_of_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    {B₂ B₄ B₈ A₃ A₆ : ℤ_[p]}
    (hb₂ : V.b₂ = (p : ℤ_[p]) ^ 2 * B₂) (hb₄ : V.b₄ = (p : ℤ_[p]) ^ 3 * B₄)
    (hb₈ : V.b₈ = (p : ℤ_[p]) ^ 6 * B₈) (ha₃ : V.a₃ = (p : ℤ_[p]) ^ 2 * A₃)
    (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 4 * A₆) (hΔ : (p : ℤ_[p]) ^ 12 ∣ V.Δ) :
    (quadratic (p : ℤ_[p]) V 2).HasDoubleRoot := by
  have hb₆ : V.b₆ = (p : ℤ_[p]) ^ 4 * (A₃ ^ 2 + 4 * A₆) := by
    rw [WeierstrassCurve.b₆, ha₃, ha₆]; ring
  have hB₆ : (p : ℤ_[p]) ∣ A₃ ^ 2 + 4 * A₆ := dvd_B₆_of_three_step8 hp3 hb₂ hb₄ hb₆ hb₈ hΔ
  have hdiv₃ : div V.a₃ ((p : ℤ_[p]) ^ 2) = A₃ := by rw [ha₃]; exact div_pow_mul 2 A₃
  have hdiv₆ : div V.a₆ ((p : ℤ_[p]) ^ 4) = A₆ := by rw [ha₆]; exact div_pow_mul 4 A₆
  rw [Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) (by simp [quadratic]), quadratic]
  norm_num only [hdiv₃, hdiv₆]
  rw [← sub_eq_zero,
    show (mod (p : ℤ_[p])) A₃ ^ 2 - 4 * -(mod (p : ℤ_[p])) A₆
        = (mod (p : ℤ_[p])) (A₃ ^ 2 + 4 * A₆) by
      rw [map_add, map_mul, map_pow, map_ofNat]; ring,
    mod_eq_zero]
  exact hB₆

/-- **Step 10's branch condition at `p = 3`: `3⁶ ∣ a₆`.** If `b₂ = 3²B₂`, `b₄ = 3⁴B₄`, `b₈ = 3⁷B₈`,
`a₃ = 3³A₃`, `a₆ = 3⁵A₆` and `3¹⁴ ∣ Δ`, then `3⁶ ∣ a₆`. -/
theorem pow_six_dvd_a₆_of_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    {B₂ B₄ B₈ A₃ A₆ : ℤ_[p]}
    (hb₂ : V.b₂ = (p : ℤ_[p]) ^ 2 * B₂) (hb₄ : V.b₄ = (p : ℤ_[p]) ^ 4 * B₄)
    (hb₈ : V.b₈ = (p : ℤ_[p]) ^ 7 * B₈) (ha₃ : V.a₃ = (p : ℤ_[p]) ^ 3 * A₃)
    (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 5 * A₆) (hΔ : (p : ℤ_[p]) ^ 14 ∣ V.Δ) :
    (p : ℤ_[p]) ^ 6 ∣ V.a₆ := by
  have hb₆ : V.b₆ = (p : ℤ_[p]) ^ 5 * ((p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆) := by
    rw [WeierstrassCurve.b₆, ha₃, ha₆]; ring
  have hA₆ : (p : ℤ_[p]) ∣ A₆ := by
    have hB₆ : (p : ℤ_[p]) ∣ (p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆ := by
      generalize hB₆def : (p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆ = B₆ at hb₆ ⊢
      have hrel : 4 * B₈ = B₂ * B₆ - (p : ℤ_[p]) * B₄ ^ 2 := by
        have h := V.b_relation
        rw [hb₂, hb₄, hb₆, hb₈] at h
        refine mul_left_cancel₀ (pow_ne_zero 7 PadicInt.uniformizer_ne_zero) ?_
        linear_combination h
      have key : V.Δ = (p : ℤ_[p]) ^ 11 * (-(B₂ ^ 2 * B₈) - (p : ℤ_[p]) * (8 * B₄ ^ 3)
          + (p : ℤ_[p]) ^ 2 * (-(B₆ ^ 2) + B₂ * B₄ * B₆)) := by
        rw [WeierstrassCurve.Δ, hb₂, hb₄, hb₆, hb₈]; subst hp3; push_cast; ring
      obtain ⟨y, hy⟩ := dvd_of_pow_dvd_pow_mul (k := 11) (j := 3) (by rw [← key]; exact hΔ)
      have hB₂₈ : (p : ℤ_[p]) ∣ B₂ ^ 2 * B₈ := by
        refine ⟨-((p : ℤ_[p]) ^ 2 * y) - 8 * B₄ ^ 3
          + (p : ℤ_[p]) * (-(B₆ ^ 2) + B₂ * B₄ * B₆), ?_⟩
        linear_combination -hy
      by_cases hB₂ : (p : ℤ_[p]) ∣ B₂
      · obtain ⟨D₂, rfl⟩ := hB₂
        have h4B₈ : (p : ℤ_[p]) ∣ 4 * B₈ := ⟨D₂ * B₆ - B₄ ^ 2, by linear_combination hrel⟩
        obtain ⟨F₈, rfl⟩ : (p : ℤ_[p]) ∣ B₈ := (isUnit_four_three hp3).dvd_mul_left.mp h4B₈
        obtain ⟨C₄, rfl⟩ : (p : ℤ_[p]) ∣ B₄ := by
          have h8 : (p : ℤ_[p]) ∣ 8 * B₄ ^ 3 := dvd_of_sq_dvd_mul
            ⟨-((p : ℤ_[p]) * D₂ ^ 2 * F₈) - B₆ ^ 2 + (p : ℤ_[p]) * D₂ * B₄ * B₆
              - (p : ℤ_[p]) * y, by linear_combination -hy⟩
          exact PadicInt.prime_p.dvd_of_dvd_pow ((isUnit_eight_three hp3).dvd_mul_left.mp h8)
        refine PadicInt.prime_p.dvd_of_dvd_pow (dvd_of_cb_dvd_sq_mul (x := B₆ ^ 2) ?_)
        exact ⟨-(D₂ ^ 2 * F₈) - 8 * (p : ℤ_[p]) * C₄ ^ 3 + (p : ℤ_[p]) * D₂ * C₄ * B₆ - y, by
          linear_combination -hy⟩
      · have hB₈ : (p : ℤ_[p]) ∣ B₈ := by
          rcases PadicInt.prime_p.dvd_mul.mp hB₂₈ with h | h
          · exact absurd (PadicInt.prime_p.dvd_of_dvd_pow h) hB₂
          · exact h
        obtain ⟨F₈, rfl⟩ := hB₈
        have h2 : (p : ℤ_[p]) ∣ B₂ * B₆ := ⟨4 * F₈ + B₄ ^ 2, by linear_combination -hrel⟩
        rcases PadicInt.prime_p.dvd_mul.mp h2 with h | h
        · exact absurd h hB₂
        · exact h
    have h := dvd_sub hB₆ (Dvd.intro (A₃ ^ 2) rfl)
    rw [show (p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆ - (p : ℤ_[p]) * A₃ ^ 2 = 4 * A₆ by ring] at h
    exact (isUnit_four_three hp3).dvd_mul_left.mp h
  obtain ⟨G₆, hG₆⟩ := hA₆
  exact ⟨G₆, by rw [ha₆, hG₆]; ring⟩

/-! ### Step 11 fires at `p = 3` -/

/-- **Steps 1–10 do not answer on a short model over `ℤ_3` with `3³ ∣ a₄`, `3³ ∣ a₆` and `3¹⁴ ∣ Δ`,
so Step 11 fires.** -/
theorem Step11.run_eq_ok_of_three (hp3 : p = 3) {a₄ a₆ : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄) (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆)
    (hΔ14 : (p : ℤ_[p]) ^ 14 ∣ (ofShortNF a₄ a₆).Δ) :
    ∃ V, Step11.run PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := dvd_Δ_ofShortNF_three hp3 h₄ h₆
  obtain ⟨ha₁0, ⟨A₂, hA₂⟩, ⟨A₄, hA₄⟩, -, -, -⟩ := step2_translate_data_three hp3 h₄ h₆ hΔd
  have h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) :=
    Step5.run_eq_ok_of_cb_dvd_three hp3 h₄ h₆
  have hval5 := Step5.run_hasValuation hϖ h5
  have hval6 := Step6.hasValuation_translate hϖ hval5
  obtain ⟨σ, hσ⟩ := dvd_step6_s hp3 ha₁0
  obtain ⟨A₃', hA₃'⟩ := hval6.a₃
  have hW2a₂ : (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))).a₂ = (p : ℤ_[p]) ^ 2 * (A₂ - σ ^ 2) := by
    rw [step6_translate_a₂ _ ha₁0, hA₂, hσ]; ring
  have hW2a₄ : (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))).a₄
        = (p : ℤ_[p]) ^ 3 * (A₄ - σ * A₃') := by
    rw [step6_translate_a₄ _ ha₁0, hA₄, hσ, hA₃']; ring
  have hdouble := hasDoubleRoot_of_three hp3 hW2a₂ hW2a₄
  have htriple := hasTripleRoot_of_three hp3 hW2a₂
  have h6 : Step6.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) := by
    rw [Step6.run.eq_def, h5]; simp only [except_ok_bind]; exact ite_eq_left hdouble
  have h7 : Step7.run hϖ hΔ0 = Except.ok (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = Step6.translate (p : ℤ_[p])
            (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := Except.ok.inj (heq.symm.trans h6)
        exact dite_eq_left htriple
  have hval7 := Step7.run_hasValuation hϖ hΔ0 h7
  have hval8 := Step8.hasValuation_translate hϖ hval7 hdouble htriple
  obtain ⟨B₂, hB₂⟩ := hval8.b₂
  obtain ⟨B₄, hB₄⟩ := hval8.b₄
  obtain ⟨B₈, hB₈⟩ := hval8.b₈
  obtain ⟨A₃₈, hA₃₈⟩ := hval8.a₃
  obtain ⟨A₆₈, hA₆₈⟩ := hval8.a₆
  have hΔ8 : (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)))).Δ = (ofShortNF a₄ a₆).Δ := by
    rw [Step8.translate_Δ, Step7.run_Δ hϖ hΔ0 h7]
  have hq := quadratic_hasDoubleRoot_of_three hp3 hB₂ hB₄ hB₈ hA₃₈ hA₆₈
    (by rw [hΔ8]; exact (pow_dvd_pow _ (by norm_num : 12 ≤ 14)).trans hΔ14)
  have h8 : Step8.run hϖ hΔ0 = Except.ok (Step8.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)))) := by
    rw [Step8.run.eq_def, h7]; simp only [except_ok_bind]; exact ite_eq_left hq
  have hval9 := Step9.hasValuation_translate hϖ hval8 hq
  obtain ⟨C₂, hC₂⟩ := hval9.b₂
  obtain ⟨C₄, hC₄⟩ := hval9.b₄
  obtain ⟨C₆, hC₆⟩ := hval9.b₆
  obtain ⟨C₈, hC₈⟩ := hval9.b₈
  have hΔ9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))))).Δ
        = (ofShortNF a₄ a₆).Δ := by
    rw [Step9.translate, Step7.translateY_Δ, Step8.run_Δ hϖ hΔ0 h8]
  have h9cond := pow_four_dvd_a₄_of_three hp3 hC₂ hC₄ hC₆ hC₈ (by simpa using hval9.a₁) hval9.a₃
    (by rw [hΔ9]; exact (pow_dvd_pow _ (by norm_num : 10 ≤ 14)).trans hΔ14)
  have h9 : Step9.run hϖ hΔ0 = Except.ok (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))))) := by
    rw [Step9.run.eq_def, h8]; simp only [except_ok_bind]; exact ite_eq_left h9cond
  have hval9' := Step9.run_hasValuation hϖ hΔ0 h9
  obtain ⟨D₂, hD₂⟩ := hval9'.b₂
  obtain ⟨D₄, hD₄⟩ := hval9'.b₄
  obtain ⟨D₈, hD₈⟩ := hval9'.b₈
  obtain ⟨E₃, hE₃⟩ := hval9'.a₃
  obtain ⟨E₆, hE₆⟩ := hval9'.a₆
  have h10cond := pow_six_dvd_a₆_of_three hp3 hD₂ hD₄ hD₈ hE₃ hE₆
    (by rw [Step9.run_Δ hϖ hΔ0 h9]; exact hΔ14)
  have h10 : Step10.run hϖ hΔ0 = Except.ok (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))))) := by
    rw [Step10.run.eq_def, h9]; simp only [except_ok_bind]; exact ite_eq_left h10cond
  exact ⟨Step11.translate (p : ℤ_[p]) (Step9.translate (p : ℤ_[p])
    (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))))),
    by rw [Step11.run.eq_def, h10]; rfl⟩

end WeierstrassCurve.TateAlgorithm
