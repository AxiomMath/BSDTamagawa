/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildIZeroStarAtThree

/-!
# The `(I₀*, 1)` and `(I₀*, 2)` loci at `p = 3`

Tate's algorithm exits at Step 6 with `(I₀*, 1 + n)`, where `n` is the number of distinct roots of
the cubic `X³ + bX² + cX + d` over the residue field. This file identifies the parts of the
coefficient plane over `ℤ_3` on which that cubic has no root (`c = 1`) and exactly one root
(`c = 2`), computes their masses, and places them in the minimal parts of the rows `t = 1` and
`t = 2`.

On a short model with `a₄ = 9A` and `a₆ = 27C` the Step-6 cubic is `X³ + ĀX + (C̄ + ρ̄(Ā + 1))`,
where `ρ` is the Step-2 translation parameter, which the algorithm is free to choose. Fermat over
`ℤ_3` makes `x³ = x` in the residue field, so the whole root count is linear:

* `Ā = -1`: the cubic is `X³ - X + C̄`, which evaluates to `C̄` at every point. So it has three
  roots when `C̄ = 0` and no root when `C̄ ≠ 0`. The `ρ̄` term drops out because `ρ̄(Ā + 1) = 0`.
* `Ā = 1`: the cubic is `X³ + X + d`, which evaluates to `d - x` at `x`. So it has exactly one
  root, namely `d`, whatever `ρ̄` and `C̄` are.

Since the count does not depend on `ρ̄`, the two loci are residue cylinders:

    stratum     locus                                          mass
    (I₀*, 1)    `a₄ ≡ 18 (mod 27)`, `a₆ ≡ 27, 54 (mod 81)`      2/2187
    (I₀*, 2)    `a₄ ≡ 9 (mod 27)`, `27 ∣ a₆`                    1/729

## Main definitions

* `WeierstrassCurve.iZeroStarOne3Locus`, `WeierstrassCurve.iZeroStarTwo3Locus`: the two loci in
  `ℤ_3 × ℤ_3`.

## Main results

* `WeierstrassCurve.residue_cube_eq_self_at_three`: `x³ = x` in the residue field of `ℤ_3`.
* `WeierstrassCurve.card_roots_eq_zero_at_three`, `WeierstrassCurve.card_roots_eq_one_at_three`:
  the two root counts, and `WeierstrassCurve.not_hasDoubleRoot_of_one_at_three` and
  `WeierstrassCurve.not_hasDoubleRoot_of_neg_one_at_three'`: separability in both cases.
* `WeierstrassCurve.Step5.run_eq_ok_izeroStarOneTwo_three`: Steps 1–5 pass on `a₄ = 9A`,
  `a₆ = 27C`.
* `WeierstrassCurve.cubic_data_izeroStarOneTwo_three`: the Step-6 cubic on that locus, in full.
* `WeierstrassCurve.run_eq_I0star_one_three` and `WeierstrassCurve.run_eq_I0star_two_three`: the
  two forward runs, `(I₀*, 1)` and `(I₀*, 2)`.
* `WeierstrassCurve.volume_iZeroStarOne3Locus`, `WeierstrassCurve.volume_iZeroStarTwo3Locus`: the
  two loci have masses `2/2187` and `1/729`.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadSumThree
open CommRing Ideal TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Fermat in the residue field of `ℤ_3`

In the residue field, `x³ = x` makes every monic cubic with `b = 0` an affine function. -/

/-- **`x³ = x` in the residue field of `ℤ_3`.** -/
theorem residue_cube_eq_self_at_three (hp3 : p = 3) (x : ℤ_[p] ⧸ span {(p : ℤ_[p])}) :
    x ^ 3 = x := by
  rcases residue_cases_at_three hp3 x with h | h | h <;> rw [h] <;> ring

/-! ### The two root counts over `𝔽₃`

With `b = 0` and `x³ = x`, the cubic `X³ + cX + d` evaluates to `(1 + c)x + d`. At `c = -1` that is
the constant `d`, and at `c = 1` it is `2x + d = d - x`. So the count is `0` or `3` in the first
case according as `d ≠ 0` or `d = 0`, and always exactly `1` in the second. -/

open scoped Classical in
/-- **`X³ - X + d` has no root over the residue field of `ℤ_3` when `d ≠ 0`.** It is the constant
function `d`. -/
theorem card_roots_eq_zero_at_three (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b = 0) (hc : P.c = -1) (hd : P.d ≠ 0) :
    P.toPoly.roots.toFinset.card = 0 := by
  refine card_roots_toFinset_eq_zero (by simp [ha]) fun x hx => hd ?_
  rw [ha, hb, hc] at hx
  linear_combination hx - residue_cube_eq_self_at_three hp3 x

open scoped Classical in
/-- **`X³ + X + d` has exactly one root over the residue field of `ℤ_3`**, namely `d`. It is the
affine function `d - x`. -/
theorem card_roots_eq_one_at_three (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b = 0) (hc : P.c = 1) :
    P.toPoly.roots.toFinset.card = 1 := by
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  refine card_roots_toFinset_eq_one (by simp [ha]) (x₀ := P.d) ?_ fun x hx => ?_
  · rw [ha, hb, hc]
    linear_combination residue_cube_eq_self_at_three hp3 P.d + P.d * h3
  · rw [ha, hb, hc] at hx
    linear_combination -hx + residue_cube_eq_self_at_three hp3 x + x * h3

/-- **`X³ + X + d` is separable over the residue field of `ℤ_3`.** With `b = 0` the discriminant
condition reads `4c³ + 27d² = 0`, and in characteristic `3` that is `c³ = 0`; here `c³ = 1`. -/
theorem not_hasDoubleRoot_of_one_at_three (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b = 0) (hc : P.c = 1) :
    ¬ P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha, hb, hc]
  intro h
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  refine residue_zero_ne_one_at_three hp3 ?_
  linear_combination h + (1 + 9 * P.d ^ 2) * h3

/-- **`X³ - X + d` is separable over the residue field of `ℤ_3`, for every `d`.** The discriminant
condition is `4c³ + 27d² = 0`, which in characteristic `3` does not see `d` at all; here
`c³ = -1`. -/
theorem not_hasDoubleRoot_of_neg_one_at_three' (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b = 0) (hc : P.c = -1) :
    ¬ P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha, hb, hc]
  intro h
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  refine residue_zero_ne_one_at_three hp3 ?_
  linear_combination -h + (1 - 9 * P.d ^ 2) * h3

/-! ### The cubic's `d`, as the residue of `a₆ / 27` -/

/-- The cubic's `d` is the residue of `a₆ / ϖ³`. -/
theorem cubic_d_eq_mod_of_eq {V : WeierstrassCurve ℤ_[p]} {X : ℤ_[p]}
    (hV : V.a₆ = (p : ℤ_[p]) ^ 3 * X) :
    (cubic (p : ℤ_[p]) V 1 1).d = mod (p : ℤ_[p]) X := by
  change mod (p : ℤ_[p]) (div V.a₆ ((p : ℤ_[p]) ^ 3)) = _
  rw [show div V.a₆ ((p : ℤ_[p]) ^ 3) = X from
    mul_left_cancel₀ (pow_ne_zero 3 PadicInt.uniformizer_ne_zero)
      (by rw [CommRing.mul_div (pow_ne_zero 3 PadicInt.uniformizer_ne_zero) ⟨X, hV⟩, hV])]

/-! ### Steps 1–5 on `a₄ = 9A`, `a₆ = 27C`

The three branch conditions on the Step-2 translate are `3² ∣ a₆`, `3³ ∣ b₈` and `3³ ∣ b₆`. At
`a₆ = 27C` the translate has `a₆ = 27(C + ρA + ρ³) - 9τ²`, `b₆ = 108(C + ρA + ρ³)` and
`b₈ = 972ρ(C + ρA + ρ³) - 81(A + 3ρ²)²`, which satisfy all three. -/

/-- **Steps 1–5 pass on a short model with `a₄ = 3²A` and `a₆ = 3³C` at `p = 3`.** -/
theorem Step5.run_eq_ok_izeroStarOneTwo_three (hp3 : p = 3) {A C : ℤ_[p]} :
    Step5.run (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))
      = Except.ok (Step2.translate (p : ℤ_[p])
          (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))) := by
  obtain ⟨a₄, ha4⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * A := ⟨_, rfl⟩
  obtain ⟨a₆, ha6⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 3 * C := ⟨_, rfl⟩
  rw [← ha4, ← ha6]
  have hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := by
    refine ⟨(-16) * (972 * A ^ 3 + 6561 * C ^ 2), ?_⟩
    rw [ofShortNF_Δ, ha4, ha6]; subst hp3; push_cast; ring
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
    dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inr hp3) a₄ a₆
  have h₄1 : (p : ℤ_[p]) ∣ a₄ := ⟨(p : ℤ_[p]) * A, by rw [ha4]; ring⟩
  have h₆1 : (p : ℤ_[p]) ∣ a₆ := ⟨(p : ℤ_[p]) ^ 2 * C, by rw [ha6]; ring⟩
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
  have hA6 : (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₆ := by
    rw [hT, smul_ofShortNF_a₆, ha4, ha6, hρ, hτ]
    refine ⟨(p : ℤ_[p]) * C + (p : ℤ_[p]) * ρ * A + (p : ℤ_[p]) * ρ ^ 3 - τ ^ 2, ?_⟩
    subst hp3; push_cast; ring
  have hB6 : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).b₆ := by
    rw [hT, WeierstrassCurve.b₆, smul_ofShortNF_a₃, smul_ofShortNF_a₆, ha4, ha6, hρ, hτ]
    refine ⟨4 * (C + ρ * A + ρ ^ 3), ?_⟩
    subst hp3; push_cast; ring
  have hB8 : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hT, WeierstrassCurve.b₈, smul_ofShortNF_a₁, smul_ofShortNF_a₂, smul_ofShortNF_a₃,
      smul_ofShortNF_a₄, smul_ofShortNF_a₆, ha4, ha6, hρ, hτ]
    refine ⟨36 * C * ρ + 18 * ρ ^ 2 * A + 9 * ρ ^ 4 - 3 * A ^ 2, ?_⟩
    subst hp3; push_cast; ring
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

/-- **The Step-2 translate of the `a₄ = 3²A`, `a₆ = 3³C` locus at `p = 3`, in full.** -/
theorem step2_translate_data_izeroStarOneTwo_three (hp3 : p = 3) {A C : ℤ_[p]} :
    ∃ ρ τ : ℤ_[p],
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 3 * C))).a₁ = 0 ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 3 * C))).a₂ = (p : ℤ_[p]) ^ 2 * ρ ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 3 * C))).a₃ = 2 * ((p : ℤ_[p]) * τ) ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 3 * C))).a₄ = (p : ℤ_[p]) ^ 2 * (A + (p : ℤ_[p]) * ρ ^ 2) ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 3 * C))).a₆ = (p : ℤ_[p]) ^ 3 * C + (p : ℤ_[p]) ^ 3 * ρ * A
          + (p : ℤ_[p]) ^ 3 * ρ ^ 3 - (p : ℤ_[p]) ^ 2 * τ ^ 2 := by
  obtain ⟨a₄, ha4⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * A := ⟨_, rfl⟩
  obtain ⟨a₆, ha6⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 3 * C := ⟨_, rfl⟩
  rw [← ha4, ← ha6]
  have hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := by
    refine ⟨(-16) * (972 * A ^ 3 + 6561 * C ^ 2), ?_⟩
    rw [ofShortNF_Δ, ha4, ha6]; subst hp3; push_cast; ring
  have h₄1 : (p : ℤ_[p]) ∣ a₄ := ⟨(p : ℤ_[p]) * A, by rw [ha4]; ring⟩
  have h₆1 : (p : ℤ_[p]) ∣ a₆ := ⟨(p : ℤ_[p]) ^ 2 * C, by rw [ha6]; ring⟩
  obtain ⟨r, t, hT⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔ⟩
  have hval := Step2.hasValuation_translate hΔ
  have ha₃ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ := by
    rw [← hT]; simpa using hval.a₃
  have ha₆d : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ := by
    rw [← hT]; simpa using hval.a₆
  obtain ⟨hr, ht⟩ := dvd_params_of_dvd_three hp3 h₄1 h₆1 ha₃ ha₆d
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  refine ⟨ρ, τ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, smul_ofShortNF_a₁]; ring
  · rw [hT, smul_ofShortNF_a₂, hρ]; subst hp3; push_cast; ring
  · rw [hT, smul_ofShortNF_a₃, hτ]
  · rw [hT, smul_ofShortNF_a₄, ha4, hρ]; subst hp3; push_cast; ring
  · rw [hT, smul_ofShortNF_a₆, ha4, ha6, hρ, hτ]; subst hp3; push_cast; ring

/-- **The `a₆`-coefficient of the Step-6 translate, on the `a₄ = 9A`, `a₆ = 27C` locus.** -/
theorem step6_translate_a₆_izeroStarOneTwo_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    {A C ρ τ : ℤ_[p]} (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 2 * ((p : ℤ_[p]) * τ))
    (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 3 * C + (p : ℤ_[p]) ^ 3 * ρ * A + (p : ℤ_[p]) ^ 3 * ρ ^ 3
      - (p : ℤ_[p]) ^ 2 * τ ^ 2) :
    ∃ y : ℤ_[p], (Step6.translate (p : ℤ_[p]) V).a₆
      = (p : ℤ_[p]) ^ 3 * (C + ρ * A + ρ ^ 3 - (p : ℤ_[p]) * y ^ 2) := by
  obtain ⟨γ, hγ⟩ := sq_dvd_step6_translate_a₃_at_three hp3 ⟨2 * τ, by rw [ha₃]; ring⟩
  have h23 : 2 * (τ + Step6.t (p : ℤ_[p]) V) = (p : ℤ_[p]) * γ := by
    have he : (Step6.translate (p : ℤ_[p]) V).a₃
        = (p : ℤ_[p]) * (2 * (τ + Step6.t (p : ℤ_[p]) V)) := by
      rw [show (Step6.translate (p : ℤ_[p]) V).a₃
          = V.a₃ + 2 * ((p : ℤ_[p]) * Step6.t (p : ℤ_[p]) V) from by
        simp [Step6.translate, variableChange_a₃], ha₃]
      ring
    exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero
      (by linear_combination he.symm.trans hγ)
  obtain ⟨y, hy⟩ := dvd_of_two_mul_eq_three_mul hp3 h23
  refine ⟨y, ?_⟩
  rw [step6_translate_a₆ ha₁, ha₆, ha₃,
    show Step6.t (p : ℤ_[p]) V = (p : ℤ_[p]) * y - τ from by linear_combination hy]
  subst hp3
  push_cast
  ring

/-- **The Step-6 cubic on the `a₄ = 9A`, `a₆ = 27C` locus at `p = 3`, in full.** It is
`X³ + ĀX + (C̄ + ρ̄(Ā + 1))`: the `b`-coefficient vanishes because `a₂` is `3²`-deep, the
`c`-coefficient is `Ā` because the Step-6 shift `s` and the deepened `a₃` contribute `3³` to `a₄`,
and the `d`-coefficient is where `ρ̄` enters, through `ρ̄³ = ρ̄`. -/
theorem cubic_data_izeroStarOneTwo_three (hp3 : p = 3) {A C : ℤ_[p]} :
    ∃ V : WeierstrassCurve ℤ_[p], ∃ ρ : ℤ_[p],
      Step5.run (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))
          = Except.ok V ∧
        (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).b = 0 ∧
        (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).c = mod (p : ℤ_[p]) A ∧
        (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).d
          = mod (p : ℤ_[p]) C + mod (p : ℤ_[p]) ρ * (mod (p : ℤ_[p]) A + 1) := by
  obtain ⟨ρ, τ, h1, h2, h3, h4, h6⟩ :=
    step2_translate_data_izeroStarOneTwo_three (A := A) (C := C) hp3
  obtain ⟨V, hV⟩ : ∃ W : WeierstrassCurve ℤ_[p], W = Step2.translate (p : ℤ_[p])
    (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C)) := ⟨_, rfl⟩
  rw [← hV] at h1 h2 h3 h4 h6
  refine ⟨V, ρ, by rw [hV]; exact Step5.run_eq_ok_izeroStarOneTwo_three hp3, ?_, ?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := dvd_step6_s hp3 h1
    refine cubic_b_eq_zero_of_sq_dvd ?_
    rw [step6_translate_a₂ V h1, h2]
    exact ⟨ρ - σ ^ 2, by rw [hσ]; ring⟩
  · obtain ⟨σ, hσ⟩ := dvd_step6_s hp3 h1
    obtain ⟨γ, hγ⟩ := sq_dvd_step6_translate_a₃_at_three hp3 (V := V) ⟨2 * τ, by rw [h3]; ring⟩
    rw [cubic_c_eq_mod_of_eq (X := A + (p : ℤ_[p]) * ρ ^ 2 - (p : ℤ_[p]) * σ * γ) ?_]
    · rw [map_sub, map_add, map_mul, map_mul, map_mul,
        show mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 from by rw [mod_eq_zero]]
      ring
    · rw [step6_translate_a₄ V h1, h4, hσ, hγ]; ring
  · obtain ⟨y, hy⟩ := step6_translate_a₆_izeroStarOneTwo_three hp3 h1 h3 h6
    rw [cubic_d_eq_mod_of_eq hy, map_sub, map_add, map_add, map_mul, map_mul, map_pow,
      show mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 from by rw [mod_eq_zero]]
    linear_combination residue_cube_eq_self_at_three hp3 (mod (p : ℤ_[p]) ρ)

/-! ### The two forward runs -/

open scoped Classical in
/-- **The forward run at `(I₀*, 1)`, at the prime `3`.** A short model over `ℤ_3` with `a₄ = 9A`,
`A ≡ -1 (mod 3)`, `a₆ = 27C` and `3 ∤ C` has reduction datum exactly `(I₀*, 1)`.

The cubic is `X³ - X + C̄`, whose value at every point of `𝔽₃` is `C̄ ≠ 0`, so it has no root and
Step 6 exits with `1 + 0 = 1`. -/
theorem run_eq_I0star_one_three (hp3 : p = 3) {A C k : ℤ_[p]}
    (hA : A = -1 + (p : ℤ_[p]) * k) (hC : ¬ (p : ℤ_[p]) ∣ C)
    (hΔ : (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C)).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  obtain ⟨V, ρ, h5, hb, hc, hd⟩ := cubic_data_izeroStarOneTwo_three (A := A) (C := C) hp3
  have hAres : mod (p : ℤ_[p]) A = -1 := by
    rw [hA, map_add, map_mul, map_neg, map_one,
      show mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 from by rw [mod_eq_zero]]
    ring
  rw [hAres] at hc hd
  have hd' : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).d ≠ 0 := by
    rw [hd, show mod (p : ℤ_[p]) ρ * (-1 + 1) = 0 from by ring, add_zero, Ne, mod_eq_zero]
    exact hC
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_step5 hΔ h5
    (not_hasDoubleRoot_of_neg_one_at_three' hp3 rfl hb hc)
  exact ⟨hk, by rw [ht, card_roots_eq_zero_at_three hp3 rfl hb hc hd']⟩

open scoped Classical in
/-- **The forward run at `(I₀*, 2)`, at the prime `3`.** A short model over `ℤ_3` with `a₄ = 9A`,
`A ≡ 1 (mod 3)` and `27 ∣ a₆` has reduction datum exactly `(I₀*, 2)`.

The cubic is `X³ + X + d`, whose value at `x` is `d - x`, so it has the single root `d` whatever
`a₆` and the Step-2 parameter `ρ` are, and Step 6 exits with `1 + 1 = 2`. -/
theorem run_eq_I0star_two_three (hp3 : p = 3) {A C k : ℤ_[p]}
    (hA : A = 1 + (p : ℤ_[p]) * k)
    (hΔ : (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C)).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 3 * C))
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  obtain ⟨V, ρ, h5, hb, hc, hd⟩ := cubic_data_izeroStarOneTwo_three (A := A) (C := C) hp3
  have hAres : mod (p : ℤ_[p]) A = 1 := by
    rw [hA, map_add, map_mul, map_one,
      show mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 from by rw [mod_eq_zero]]
    ring
  rw [hAres] at hc
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_step5 hΔ h5
    (not_hasDoubleRoot_of_one_at_three hp3 rfl hb hc)
  exact ⟨hk, by rw [ht, card_roots_eq_one_at_three hp3 rfl hb hc]⟩

/-! ### The two loci and their masses

Both are cut modulo `81`. The `(I₀*, 1)` locus is `{a₄ ≡ 18, 45, 72} × {a₆ ≡ 27, 54}`, six of the
`6561` pairs, of mass `6/6561 = 2/2187`; the `(I₀*, 2)` locus is
`{a₄ ≡ 9, 36, 63} × {a₆ ≡ 0, 27, 54}`, nine pairs, of mass `9/6561 = 1/729`. On both,
`a₄ ≢ 0 (mod 81)`, so no point is a `(3⁴, 3⁶)`-dilate. -/

/-- **The residue condition cutting out the `(I₀*, 1)` locus at `3`**: `a₄ ≡ 18, 45, 72` and
`a₆ ≡ 27, 54` modulo `81`. Every class has `9 ∣ a₄`, `a₄/9 ≡ -1 (mod 3)`, `27 ∣ a₆` and
`81 ∤ a₆`. -/
abbrev HeadResIZeroStarOneThree (A E : ZMod (3 ^ 4)) : Prop :=
  (A = 18 ∨ A = 45 ∨ A = 72) ∧ (E = 27 ∨ E = 54)

/-- **The residue condition cutting out the `(I₀*, 2)` locus at `3`**: `a₄ ≡ 9, 36, 63` and
`a₆ ≡ 0, 27, 54` modulo `81`. Every class has `9 ∣ a₄`, `a₄/9 ≡ 1 (mod 3)` and `27 ∣ a₆`. -/
abbrev HeadResIZeroStarTwoThree (A E : ZMod (3 ^ 4)) : Prop :=
  (A = 9 ∨ A = 36 ∨ A = 63) ∧ (E = 0 ∨ E = 27 ∨ E = 54)

-- The nine statements below unfold an `abbrev` over all `6561` pairs modulo `81`, which outruns
-- the default recursion depth.
set_option maxRecDepth 100000 in
/-- `9 ∣ a₄` on the `(I₀*, 1)` locus. -/
theorem headResIZeroStarOneThree_cast_two :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarOneThree c.1 c.2 →
      (ZMod.cast c.1 : ZMod (3 ^ 2)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `27 ∣ a₄ + 9` on the `(I₀*, 1)` locus, so that `a₄ / 9 ≡ -1 (mod 3)`. -/
theorem headResIZeroStarOneThree_cast_three :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarOneThree c.1 c.2 →
      (ZMod.cast (c.1 + 9) : ZMod (3 ^ 3)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `27 ∣ a₆` on the `(I₀*, 1)` locus. -/
theorem headResIZeroStarOneThree_snd :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarOneThree c.1 c.2 →
      (ZMod.cast c.2 : ZMod (3 ^ 3)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `81 ∤ a₆` on the `(I₀*, 1)` locus. -/
theorem headResIZeroStarOneThree_snd_ne :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarOneThree c.1 c.2 → c.2 ≠ 0 := by decide

set_option maxRecDepth 100000 in
/-- The zero class modulo `81` is not on the `(I₀*, 1)` locus. -/
theorem not_headResIZeroStarOneThree_zero : ¬ HeadResIZeroStarOneThree 0 0 := by decide

set_option maxRecDepth 100000 in
/-- `9 ∣ a₄` on the `(I₀*, 2)` locus. -/
theorem headResIZeroStarTwoThree_cast_two :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarTwoThree c.1 c.2 →
      (ZMod.cast c.1 : ZMod (3 ^ 2)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `27 ∣ a₄ - 9` on the `(I₀*, 2)` locus, so that `a₄ / 9 ≡ 1 (mod 3)`. -/
theorem headResIZeroStarTwoThree_cast_three :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarTwoThree c.1 c.2 →
      (ZMod.cast (c.1 - 9) : ZMod (3 ^ 3)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `27 ∣ a₆` on the `(I₀*, 2)` locus. -/
theorem headResIZeroStarTwoThree_snd :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarTwoThree c.1 c.2 →
      (ZMod.cast c.2 : ZMod (3 ^ 3)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- The zero class modulo `81` is not on the `(I₀*, 2)` locus. -/
theorem not_headResIZeroStarTwoThree_zero : ¬ HeadResIZeroStarTwoThree 0 0 := by decide

/-- The six residue pairs of `HeadResIZeroStarOneThree`, as a `Finset`. -/
def headResiduesIZeroStarOneThree : Finset (ZMod (3 ^ 4) × ZMod (3 ^ 4)) :=
  {(18, 27), (18, 54), (45, 27), (45, 54), (72, 27), (72, 54)}

/-- `headResiduesIZeroStarOneThree` has six elements. -/
theorem card_headResiduesIZeroStarOneThree : headResiduesIZeroStarOneThree.card = 6 := by decide

/-- A residue pair lies in `headResiduesIZeroStarOneThree` iff it satisfies
`HeadResIZeroStarOneThree`. -/
theorem mem_headResiduesIZeroStarOneThree_iff {c : ZMod (3 ^ 4) × ZMod (3 ^ 4)} :
    c ∈ headResiduesIZeroStarOneThree ↔ HeadResIZeroStarOneThree c.1 c.2 := by
  simp [headResiduesIZeroStarOneThree, HeadResIZeroStarOneThree, Prod.ext_iff]
  tauto

/-- The nine residue pairs of `HeadResIZeroStarTwoThree`, as a `Finset`. -/
def headResiduesIZeroStarTwoThree : Finset (ZMod (3 ^ 4) × ZMod (3 ^ 4)) :=
  {(9, 0), (9, 27), (9, 54), (36, 0), (36, 27), (36, 54), (63, 0), (63, 27), (63, 54)}

/-- `headResiduesIZeroStarTwoThree` has nine elements. -/
theorem card_headResiduesIZeroStarTwoThree : headResiduesIZeroStarTwoThree.card = 9 := by decide

/-- A residue pair lies in `headResiduesIZeroStarTwoThree` iff it satisfies
`HeadResIZeroStarTwoThree`. -/
theorem mem_headResiduesIZeroStarTwoThree_iff {c : ZMod (3 ^ 4) × ZMod (3 ^ 4)} :
    c ∈ headResiduesIZeroStarTwoThree ↔ HeadResIZeroStarTwoThree c.1 c.2 := by
  simp [headResiduesIZeroStarTwoThree, HeadResIZeroStarTwoThree, Prod.ext_iff]
  tauto

/-- The **`(I₀*, 1)` locus** of the coefficient plane at `3`: the six residue classes with
`a₄ ≡ 18, 45, 72` and `a₆ ≡ 27, 54` modulo `81`. On it Tate's algorithm returns `(I₀*, 1)`. -/
noncomputable def iZeroStarOne3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 4 ⁻¹'
    (headResiduesIZeroStarOneThree : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4)))

/-- A pair lies in `iZeroStarOne3Locus` iff its reduction modulo `81` satisfies
`HeadResIZeroStarOneThree`. -/
theorem mem_iZeroStarOne3Locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ iZeroStarOne3Locus ↔
      HeadResIZeroStarOneThree (PadicInt.toZModPow 4 x.1) (PadicInt.toZModPow 4 x.2) := by
  rw [iZeroStarOne3Locus, mem_preimage, Finset.mem_coe,
    mem_headResiduesIZeroStarOneThree_iff, PadicInt.redPairPow]

/-- `iZeroStarOne3Locus` is measurable. -/
theorem measurableSet_iZeroStarOne3Locus : MeasurableSet iZeroStarOne3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 4 headResiduesIZeroStarOneThree

/-- The **`(I₀*, 2)` locus** of the coefficient plane at `3`: the nine residue classes with
`a₄ ≡ 9, 36, 63` and `a₆ ≡ 0, 27, 54` modulo `81`. On it Tate's algorithm returns `(I₀*, 2)`. -/
noncomputable def iZeroStarTwo3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 4 ⁻¹'
    (headResiduesIZeroStarTwoThree : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4)))

/-- A pair lies in `iZeroStarTwo3Locus` iff its reduction modulo `81` satisfies
`HeadResIZeroStarTwoThree`. -/
theorem mem_iZeroStarTwo3Locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ iZeroStarTwo3Locus ↔
      HeadResIZeroStarTwoThree (PadicInt.toZModPow 4 x.1) (PadicInt.toZModPow 4 x.2) := by
  rw [iZeroStarTwo3Locus, mem_preimage, Finset.mem_coe,
    mem_headResiduesIZeroStarTwoThree_iff, PadicInt.redPairPow]

/-- `iZeroStarTwo3Locus` is measurable. -/
theorem measurableSet_iZeroStarTwo3Locus : MeasurableSet iZeroStarTwo3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 4 headResiduesIZeroStarTwoThree

/-- `6 · 3⁻⁸ = 6/6561 = 2/2187` in `ℝ≥0∞`. -/
theorem six_mul_inv_pow_eight_div_eq :
    ((6 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 4) = 2 / 2187 := by
  rw [show ((6 : ℕ) : ℝ≥0∞) = 6 by norm_num, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 4) = 6561 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the `(I₀*, 1)` locus at `3` is `6/6561 = 2/2187`.** -/
theorem volume_iZeroStarOne3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iZeroStarOne3Locus = 2 / 2187 := by
  rw [iZeroStarOne3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResiduesIZeroStarOneThree, six_mul_inv_pow_eight_div_eq]

/-- `9 · 3⁻⁸ = 9/6561 = 1/729` in `ℝ≥0∞`. -/
theorem nine_mul_inv_pow_eight_div_eq :
    ((9 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 4) = 1 / 729 := by
  rw [show ((9 : ℕ) : ℝ≥0∞) = 9 by norm_num, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 4) = 6561 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the `(I₀*, 2)` locus at `3` is `9/6561 = 1/729`.** -/
theorem volume_iZeroStarTwo3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iZeroStarTwo3Locus = 1 / 729 := by
  rw [iZeroStarTwo3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResiduesIZeroStarTwoThree, nine_mul_inv_pow_eight_div_eq]

/-! ### Points of the two loci -/

/-- **Points of the `(I₀*, 1)` locus at `3`**: `a₄ = 9A` with `A ≡ -1 (mod 3)`, and `a₆ = 27C` with
`3 ∤ C`. -/
theorem exists_form_of_mem_iZeroStarOne3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ iZeroStarOne3Locus) :
    ∃ A C k : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 2 * A ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * C ∧
      A = -1 + ((3 : ℕ) : ℤ_[3]) * k ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ C := by
  have h := mem_iZeroStarOne3Locus_iff.1 hx
  obtain ⟨A, hA⟩ : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ x.1 :=
    pow_dvd_of_cast_toZModPow_eq_zero (m := 2) (n := 4) (by norm_num)
      (headResIZeroStarOneThree_cast_two (PadicInt.redPairPow 3 4 x) h)
  obtain ⟨C, hC⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.2 :=
    pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 4) (by norm_num)
      (headResIZeroStarOneThree_snd (PadicInt.redPairPow 3 4 x) h)
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1 + 9 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 4) (by norm_num) ?_
    have hs := headResIZeroStarOneThree_cast_three (PadicInt.redPairPow 3 4 x) h
    rwa [show PadicInt.toZModPow 4 (x.1 + 9) = PadicInt.toZModPow 4 x.1 + 9 from by
      rw [map_add, map_ofNat]]
  refine ⟨A, C, c, hA, hC, ?_, ?_⟩
  · have h9 : ((3 : ℕ) : ℤ_[3]) ^ 2 * (A + 1)
        = ((3 : ℕ) : ℤ_[3]) ^ 2 * (((3 : ℕ) : ℤ_[3]) * c) := by
      rw [show ((3 : ℕ) : ℤ_[3]) ^ 2 * (A + 1) = x.1 + 9 from by
        rw [hA, show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]; ring, hc]
      rw [show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]; ring
    linear_combination mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero) h9
  · intro ⟨e, he⟩
    refine headResIZeroStarOneThree_snd_ne (PadicInt.redPairPow 3 4 x) h ?_
    refine PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp ⟨e, ?_⟩
    rw [hC, he]; ring

/-- **Points of the `(I₀*, 2)` locus at `3`**: `a₄ = 9A` with `A ≡ 1 (mod 3)`, and `a₆ = 27C`. -/
theorem exists_form_of_mem_iZeroStarTwo3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ iZeroStarTwo3Locus) :
    ∃ A C k : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 2 * A ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * C ∧
      A = 1 + ((3 : ℕ) : ℤ_[3]) * k := by
  have h := mem_iZeroStarTwo3Locus_iff.1 hx
  obtain ⟨A, hA⟩ : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ x.1 :=
    pow_dvd_of_cast_toZModPow_eq_zero (m := 2) (n := 4) (by norm_num)
      (headResIZeroStarTwoThree_cast_two (PadicInt.redPairPow 3 4 x) h)
  obtain ⟨C, hC⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.2 :=
    pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 4) (by norm_num)
      (headResIZeroStarTwoThree_snd (PadicInt.redPairPow 3 4 x) h)
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1 - 9 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 4) (by norm_num) ?_
    have hs := headResIZeroStarTwoThree_cast_three (PadicInt.redPairPow 3 4 x) h
    rwa [show PadicInt.toZModPow 4 (x.1 - 9) = PadicInt.toZModPow 4 x.1 - 9 from by
      rw [map_sub, map_ofNat]]
  refine ⟨A, C, c, hA, hC, ?_⟩
  have h9 : ((3 : ℕ) : ℤ_[3]) ^ 2 * (A - 1)
      = ((3 : ℕ) : ℤ_[3]) ^ 2 * (((3 : ℕ) : ℤ_[3]) * c) := by
    rw [show ((3 : ℕ) : ℤ_[3]) ^ 2 * (A - 1) = x.1 - 9 from by
      rw [hA, show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]; ring, hc]
    rw [show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]; ring
  linear_combination mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero) h9

/-- **Nonsingularity on both loci.** With `a₄ = 9A` and `a₆ = 27C`, dividing `Δ` by `3⁶` leaves
`4A³ + 27C² = 0`, and `A` is a unit on both loci, so `3 ∣ 4A³` is impossible. -/
theorem ofShortNF_Δ_ne_zero_izeroStarOneTwo_three {A C : ℤ_[3]}
    (hA : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A) :
    (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 2 * A) (((3 : ℕ) : ℤ_[3]) ^ 3 * C)).Δ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h729 : (729 : ℤ_[3]) ≠ 0 := by
    rw [show (729 : ℤ_[3]) = 3 ^ 6 by norm_num]; exact pow_ne_zero 6 h3
  intro hzero
  rw [ofShortNF_Δ, hcast] at hzero
  have hD : (4 : ℤ_[3]) * (3 ^ 2 * A) ^ 3 + 27 * (3 ^ 3 * C) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left isUnit_neg_sixteen_three.ne_zero
  have hE : (729 : ℤ_[3]) * (4 * A ^ 3 + 27 * C ^ 2) = 0 := by linear_combination hD
  have hE' : (4 : ℤ_[3]) * A ^ 3 + 27 * C ^ 2 = 0 := (mul_eq_zero.mp hE).resolve_left h729
  refine hA (PadicInt.prime_p.dvd_of_dvd_pow (n := 3) ?_)
  refine (PadicInt.prime_p.dvd_or_dvd (a := (4 : ℤ_[3])) (b := A ^ 3) ?_).resolve_left
    not_three_dvd_four
  exact ⟨-(9 * C ^ 2), by rw [hcast]; linear_combination hE'⟩

/-- In `ℤ_3`, `A = u + 3k` with `u = ±1` is not divisible by `3`. -/
theorem not_dvd_of_eq_add_mul_three {A k : ℤ_[3]} {u : ℤ_[3]} (hu : u = 1 ∨ u = -1)
    (hA : A = u + ((3 : ℕ) : ℤ_[3]) * k) : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, hA, map_add, map_mul,
    show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by rw [← PadicInt.dvd_iff_toZMod_eq_zero],
    zero_mul, add_zero]
  rcases hu with h | h <;> rw [h]
  · rw [map_one]; decide
  · rw [map_neg, map_one]; decide

/-! ### The two loci lie in the minimal parts of rows `t = 1` and `t = 2` -/

open scoped Classical in
/-- **The `(I₀*, 1)` locus at `3` lies in the strata over `t = 1`.** -/
theorem iZeroStarOne3Locus_subset_iUnion_stratFibre :
    iZeroStarOne3Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1) := by
  intro x hx
  obtain ⟨A, C, k, hA, hC, hk, hCu⟩ := exists_form_of_mem_iZeroStarOne3Locus hx
  have hAu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A := not_dvd_of_eq_add_mul_three (Or.inr rfl) hk
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hA, hC]; exact ofShortNF_Δ_ne_zero_izeroStarOneTwo_three hAu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_I0star_one_three (p := 3) rfl (A := A) (C := C) (k := k) hk hCu
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 2 * A) (((3 : ℕ) : ℤ_[3]) ^ 3 * C)).Δ ≠ 0 from by
      rw [← hA, ← hC]; exact hΔ)
  refine Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0, (mem_stratFibre_iff hUp).2 ?_⟩
  rw [strat]
  refine Prod.ext ?_ ?_
  · simp only [hA, hC]; exact hks
  · simp only [hA, hC]; exact hts

open scoped Classical in
/-- **The `(I₀*, 2)` locus at `3` lies in the strata over `t = 2`.** -/
theorem iZeroStarTwo3Locus_subset_iUnion_stratFibre :
    iZeroStarTwo3Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2) := by
  intro x hx
  obtain ⟨A, C, k, hA, hC, hk⟩ := exists_form_of_mem_iZeroStarTwo3Locus hx
  have hAu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A := not_dvd_of_eq_add_mul_three (Or.inl rfl) hk
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hA, hC]; exact ofShortNF_Δ_ne_zero_izeroStarOneTwo_three hAu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_I0star_two_three (p := 3) rfl (A := A) (C := C) (k := k) hk
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 2 * A) (((3 : ℕ) : ℤ_[3]) ^ 3 * C)).Δ ≠ 0 from by
      rw [← hA, ← hC]; exact hΔ)
  refine Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0, (mem_stratFibre_iff hUp).2 ?_⟩
  rw [strat]
  refine Prod.ext ?_ ?_
  · simp only [hA, hC]; exact hks
  · simp only [hA, hC]; exact hts

/-- **The `(I₀*, 1)` locus at `3` lies in the minimal part of the `t = 1` row.** -/
theorem iZeroStarOne3Locus_subset_headMinimal :
    iZeroStarOne3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun x hx => ⟨iZeroStarOne3Locus_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three (k := 4) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_iZeroStarOne3Locus_iff.1 hx
  rw [h1, h2] at h
  exact not_headResIZeroStarOneThree_zero h

/-- **The `(I₀*, 2)` locus at `3` lies in the minimal part of the `t = 2` row.** -/
theorem iZeroStarTwo3Locus_subset_headMinimal :
    iZeroStarTwo3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun x hx => ⟨iZeroStarTwo3Locus_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three (k := 4) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_iZeroStarTwo3Locus_iff.1 hx
  rw [h1, h2] at h
  exact not_headResIZeroStarTwoThree_zero h

end WeierstrassCurve

end
