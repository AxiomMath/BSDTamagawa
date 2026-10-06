/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildIZeroStarAtTwo
public import BSDTamagawa.GOTTable.WildShallowAtThree

/-!
# The `(I₀*, 4)` locus at `p = 3`

Tate's algorithm exits at Step 6 with `(I₀*, 1 + n)`, where `n` is the number of distinct roots of
the cubic `X³ + bX² + cX + d` over the residue field. Over `𝔽₃` a monic cubic with three distinct
roots must have root set `{0, 1, -1}`, so it is `X³ - X` and nothing else: three roots forces
`(b, c, d) = (0, -1, 0)`. This file identifies the locus of the coefficient plane over `ℤ_3` where
that happens.

The locus is one residue cylinder: `a₄ ≡ 9 · (-1) (mod 27)` and `81 ∣ a₆`, i.e. `a₄ = 9A` with
`A ≡ -1 (mod 3)` and `a₆ = 81B`, of mass `1/27 · 1/81 = 1/2187`. On it the Step-6 cubic is
`X³ - X` for every choice of lifts, so `c = 4` throughout.

## Main definitions

* `WeierstrassCurve.iZeroStarFour3Locus`: the set of `(a₄, a₆) ∈ ℤ_3²` with
  `(a₄, a₆) ≡ (18, 0), (45, 0)` or `(72, 0)` modulo `81`.

## Main results

* `WeierstrassCurve.card_roots_eq_three_at_three` and
  `WeierstrassCurve.not_hasDoubleRoot_of_neg_one_at_three`: over the residue field of `ℤ_3`, the
  cubic `X³ - X` has exactly three distinct roots and no double root.
* `WeierstrassCurve.sq_dvd_step6_translate_a₃_at_three`: the Step-6 translation deepens `3 ∣ a₃`
  to `3² ∣ a₃`.
* `WeierstrassCurve.Step5.run_eq_ok_izeroStar_three`: Steps 1–5 all pass on `a₄ = 9A`, `a₆ = 81B`.
* `WeierstrassCurve.run_eq_I0star_four_three`: on this locus Tate's algorithm returns `(I₀*, 4)`.
* `WeierstrassCurve.volume_iZeroStarFour3Locus`: the locus has mass `1/2187`.

## Implementation notes

Over `𝔽₃` the count of roots is a `decide` over `ZMod 3` transported along `residueEquiv`, and
separability is automatic: in characteristic `3` the discriminant of `X³ - X` is
`-4c³ = 4 = 1 ≠ 0`. Since `2 ≠ 0` in `𝔽₃`, the Step-6 shifts `s` and `t` are lifts of `-a₁/2 = 0`
and `-(a₃/ϖ)/2`, both determined modulo `3`.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadSumThree
open CommRing Ideal TateAlgorithm

/-! ### The residue field of `ℤ_3`, as three elements

Every statement below is a `decide` over `ZMod 3` transported along
`BSDTamagawa.HeadSumThree.residueEquiv`. The residue field carries no `DecidableEq`, so the
statements over `ZMod 3` are stated separately. -/

/-- Every element of `ZMod 3` is `0`, `1` or `-1`. -/
theorem zmod_three_cases : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = -1 := by decide

/-- `0 ≠ 1` in `ZMod 3`. -/
theorem zmod_three_zero_ne_one : (0 : ZMod 3) ≠ 1 := by decide

/-- `1 ≠ -1` in `ZMod 3`. -/
theorem zmod_three_one_ne_neg_one : (1 : ZMod 3) ≠ -1 := by decide

/-- `0 ≠ -1` in `ZMod 3`. -/
theorem zmod_three_zero_ne_neg_one : (0 : ZMod 3) ≠ -1 := by decide

/-- `2 ≠ 0` in `ZMod 3`. -/
theorem zmod_three_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

variable {p : ℕ} [Fact p.Prime]

/-- `2 ≠ 0` in the residue field of `ℤ_3`. -/
theorem residue_two_ne_zero_at_three (hp3 : p = 3) :
    (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ 0 := by
  rw [← map_ofNat (mod ((p : ℕ) : ℤ_[p])) 2, Ne, mod_eq_zero]
  subst hp3
  intro h
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat] at h
  exact zmod_three_two_ne_zero h

/-- **The residue field of `ℤ_3` is `{0, 1, -1}`.** -/
theorem residue_cases_at_three (hp3 : p = 3) (x : ℤ_[p] ⧸ span {(p : ℤ_[p])}) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  subst hp3
  have h := (residueEquiv 3).symm_apply_apply x
  rcases zmod_three_cases (residueEquiv 3 x) with h0 | h1 | h2
  · left; rw [← h, h0, map_zero]
  · right; left; rw [← h, h1, map_one]
  · right; right; rw [← h, h2, map_neg, map_one]

/-- `0 ≠ 1` in the residue field of `ℤ_3`. -/
theorem residue_zero_ne_one_at_three (hp3 : p = 3) :
    (0 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ 1 := by
  subst hp3
  intro h
  have he := congrArg (residueEquiv 3) h
  rw [map_zero, map_one] at he
  exact zmod_three_zero_ne_one he

/-- `1 ≠ -1` in the residue field of `ℤ_3`. -/
theorem residue_one_ne_neg_one_at_three (hp3 : p = 3) :
    (1 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ -1 := by
  subst hp3
  intro h
  have he := congrArg (residueEquiv 3) h
  rw [map_one, map_neg, map_one] at he
  exact zmod_three_one_ne_neg_one he

/-- `0 ≠ -1` in the residue field of `ℤ_3`. -/
theorem residue_zero_ne_neg_one_at_three (hp3 : p = 3) :
    (0 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ -1 := by
  subst hp3
  intro h
  have he := congrArg (residueEquiv 3) h
  rw [map_zero, map_neg, map_one] at he
  exact zmod_three_zero_ne_neg_one he

/-- `3 = 0` in the residue field of `ℤ_3`. -/
theorem residue_three_eq_zero_at_three (hp3 : p = 3) :
    (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
  subst hp3
  rw [← map_ofNat (mod (((3 : ℕ)) : ℤ_[3])) 3, mod_eq_zero]
  norm_num

/-! ### The cubic `X³ - X` over `𝔽₃`

This is the only monic cubic over `𝔽₃` with three distinct roots: three roots exhaust the field, so
the cubic is `X(X - 1)(X + 1)`. -/

open scoped Classical in
/-- **`X³ - X` has exactly three distinct roots over the residue field of `ℤ_3`.** -/
theorem card_roots_eq_three_at_three (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b = 0) (hc : P.c = -1) (hd : P.d = 0) :
    P.toPoly.roots.toFinset.card = 3 := by
  rw [roots_toFinset_eq_of_forall (by simp [ha]) {0, 1, -1} ?_]
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using residue_one_ne_neg_one_at_three hp3
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim (residue_zero_ne_one_at_three hp3)
        (residue_zero_ne_neg_one_at_three hp3)
  · intro x
    rw [ha, hb, hc, hd]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun _ => residue_cases_at_three hp3 x, ?_⟩
    rintro (h | h | h) <;> rw [h] <;> ring

/-- **`X³ - X` is separable over the residue field of `ℤ_3`.** -/
theorem not_hasDoubleRoot_of_neg_one_at_three (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b = 0) (hc : P.c = -1) (hd : P.d = 0) :
    ¬ P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha, hb, hc, hd]
  intro h
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  have h4 : (4 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 1 := by linear_combination h3
  refine residue_zero_ne_one_at_three hp3 ?_
  linear_combination -h - h4 + 2 * h3

/-! ### The Step-6 translation at `p = 3`

`Step6.s` and `Step6.t` are `Quot.out` lifts, so only their residues are pinned. At `p = 3` the
`if 2 = 0` guard is false, so `s` lifts `-a₁/2` and `t` lifts `-(a₃/ϖ)/2`. -/

/-- **The Step-6 translation deepens `3 ∣ a₃` to `3² ∣ a₃`.** -/
theorem sq_dvd_step6_translate_a₃_at_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    (ha₃ : (p : ℤ_[p]) ∣ V.a₃) :
    (p : ℤ_[p]) ^ 2 ∣ (Step6.translate (p : ℤ_[p]) V).a₃ := by
  obtain ⟨c, hc⟩ := ha₃
  have heq : (Step6.translate (p : ℤ_[p]) V).a₃
      = (p : ℤ_[p]) * (c + 2 * Step6.t (p : ℤ_[p]) V) := by
    rw [show (Step6.translate (p : ℤ_[p]) V).a₃
        = V.a₃ + 2 * ((p : ℤ_[p]) * Step6.t (p : ℤ_[p]) V) from by
      simp [Step6.translate, variableChange_a₃], hc]
    ring
  rw [heq, pow_two]
  refine mul_dvd_mul_left _ ?_
  rw [← mod_eq_zero, map_add, map_mul, map_ofNat]
  have hdiv : div V.a₃ (p : ℤ_[p]) = c :=
    mul_left_cancel₀ PadicInt.uniformizer_ne_zero
      (by rw [CommRing.mul_div PadicInt.uniformizer_ne_zero ⟨c, hc⟩, hc])
  rw [show mod (p : ℤ_[p]) (Step6.t (p : ℤ_[p]) V)
      = -mod (p : ℤ_[p]) (div V.a₃ (p : ℤ_[p])) / 2 from by
    rw [Step6.t, mod_out, dite_eq_right (residue_two_ne_zero_at_three hp3)], hdiv,
    mul_div_cancel₀ _ (residue_two_ne_zero_at_three hp3), add_neg_cancel]

/-! ### Steps 1–5 on the `(I₀*, 4)` locus

With `a₄` exactly `3²`-deep, the cubic's `c` is a unit and Step 6 exits. The branch conditions of
Steps 3–5 are checked on the Step-2 translate, whose parameters `r` and `t` are divisible by
`3`. -/

/-- **Steps 1–5 pass on a short model with `a₄ = 3²A` and `a₆ = 3⁴B` at `p = 3`.** -/
theorem Step5.run_eq_ok_izeroStar_three (hp3 : p = 3) {A B : ℤ_[p]} :
    Step5.run (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B))
      = Except.ok (Step2.translate (p : ℤ_[p])
          (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B))) := by
  obtain ⟨a₄, ha4⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * A := ⟨_, rfl⟩
  obtain ⟨a₆, ha6⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 4 * B := ⟨_, rfl⟩
  rw [← ha4, ← ha6]
  have hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := by
    refine ⟨(-16) * (972 * A ^ 3 + 59049 * B ^ 2), ?_⟩
    rw [ofShortNF_Δ, ha4, ha6]; subst hp3; push_cast; ring
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
    dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inr hp3) a₄ a₆
  have h₄1 : (p : ℤ_[p]) ∣ a₄ := ⟨(p : ℤ_[p]) * A, by rw [ha4]; ring⟩
  have h₆1 : (p : ℤ_[p]) ∣ a₆ := ⟨(p : ℤ_[p]) ^ 3 * B, by rw [ha6]; ring⟩
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
    refine ⟨(p : ℤ_[p]) ^ 2 * B + (p : ℤ_[p]) * ρ * A + (p : ℤ_[p]) * ρ ^ 3 - τ ^ 2, ?_⟩
    subst hp3; push_cast; ring
  have hB6 : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).b₆ := by
    rw [hT, WeierstrassCurve.b₆, smul_ofShortNF_a₃, smul_ofShortNF_a₆, ha4, ha6, hρ, hτ]
    refine ⟨4 * ((p : ℤ_[p]) * B + ρ * A + ρ ^ 3), ?_⟩
    subst hp3; push_cast; ring
  have hB8 : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hT, WeierstrassCurve.b₈, smul_ofShortNF_a₁, smul_ofShortNF_a₂, smul_ofShortNF_a₃,
      smul_ofShortNF_a₄, smul_ofShortNF_a₆, ha4, ha6, hρ, hτ]
    refine ⟨108 * B * ρ + 18 * ρ ^ 2 * A + 9 * ρ ^ 4 - 3 * A ^ 2, ?_⟩
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

/-! ### The cubic components, and the depths the Step-6 translate reaches

`cubic ϖ V 1 1` is `⟨1, (a₂/ϖ)‾, (a₄/ϖ²)‾, (a₆/ϖ³)‾⟩`. So `b = 0` needs `ϖ² ∣ a₂`, `d = 0` needs
`ϖ⁴ ∣ a₆`, and `c = -1` needs `a₄ = ϖ² X` with `X ≡ -1`. The first follows from `a₂(V) = 3r`
with `3 ∣ r`; the third from `step6_translate_a₄` together with `3 ∣ s` and `3² ∣ a₃(W)`; the
second rests on Fermat's little theorem over `ℤ_3`. -/

/-- The cubic's `b` vanishes when `ϖ² ∣ a₂`. -/
theorem cubic_b_eq_zero_of_sq_dvd {V : WeierstrassCurve ℤ_[p]} (hV : (p : ℤ_[p]) ^ 2 ∣ V.a₂) :
    (cubic (p : ℤ_[p]) V 1 1).b = 0 := by
  obtain ⟨c, hc⟩ := hV
  change mod (p : ℤ_[p]) (div V.a₂ (p : ℤ_[p])) = 0
  rw [show div V.a₂ (p : ℤ_[p]) = (p : ℤ_[p]) * c from
    mul_left_cancel₀ PadicInt.uniformizer_ne_zero
      (by rw [CommRing.mul_div PadicInt.uniformizer_ne_zero
        ⟨(p : ℤ_[p]) * c, by rw [hc]; ring⟩, hc]; ring), mod_eq_zero]
  exact Dvd.intro c rfl

/-- The cubic's `d` vanishes when `ϖ⁴ ∣ a₆`. -/
theorem cubic_d_eq_zero_of_pow_four_dvd {V : WeierstrassCurve ℤ_[p]}
    (hV : (p : ℤ_[p]) ^ 4 ∣ V.a₆) :
    (cubic (p : ℤ_[p]) V 1 1).d = 0 := by
  obtain ⟨c, hc⟩ := hV
  change mod (p : ℤ_[p]) (div V.a₆ ((p : ℤ_[p]) ^ 3)) = 0
  rw [show div V.a₆ ((p : ℤ_[p]) ^ 3) = (p : ℤ_[p]) * c from
    mul_left_cancel₀ (pow_ne_zero 3 PadicInt.uniformizer_ne_zero)
      (by rw [CommRing.mul_div (pow_ne_zero 3 PadicInt.uniformizer_ne_zero)
        ⟨(p : ℤ_[p]) * c, by rw [hc]; ring⟩, hc]; ring), mod_eq_zero]
  exact Dvd.intro c rfl

/-- The cubic's `c` is the residue of `a₄ / ϖ²`. -/
theorem cubic_c_eq_mod_of_eq {V : WeierstrassCurve ℤ_[p]} {X : ℤ_[p]}
    (hV : V.a₄ = (p : ℤ_[p]) ^ 2 * X) :
    (cubic (p : ℤ_[p]) V 1 1).c = mod (p : ℤ_[p]) X := by
  change mod (p : ℤ_[p]) (div V.a₄ ((p : ℤ_[p]) ^ 2)) = _
  rw [show div V.a₄ ((p : ℤ_[p]) ^ 2) = X from
    mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [CommRing.mul_div (pow_ne_zero 2 PadicInt.uniformizer_ne_zero) ⟨X, hV⟩, hV])]

/-- **Fermat's little theorem over `ℤ_3`**: `3 ∣ x³ - x`. -/
theorem three_dvd_cube_sub_self (hp3 : p = 3) (x : ℤ_[p]) : (p : ℤ_[p]) ∣ x ^ 3 - x := by
  rw [← mod_eq_zero, map_sub, map_pow]
  rcases residue_cases_at_three hp3 (mod ((p : ℕ) : ℤ_[p]) x) with h0 | h1 | h2
  · rw [h0]; ring
  · rw [h1]; ring
  · rw [h2]; ring

/-- In `ℤ_3`, `2y = 3γ` implies `3 ∣ y`. -/
theorem dvd_of_two_mul_eq_three_mul (hp3 : p = 3) {y γ : ℤ_[p]}
    (h : 2 * y = (p : ℤ_[p]) * γ) : (p : ℤ_[p]) ∣ y := by
  rw [← mod_eq_zero]
  have hm := congrArg (mod (p : ℤ_[p])) h
  rw [map_mul, map_mul, map_ofNat, show mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 from by rw [mod_eq_zero],
    zero_mul] at hm
  exact (mul_eq_zero.mp hm).resolve_left (residue_two_ne_zero_at_three hp3)

/-- The `a₆`-coefficient of the Step-6 translation of a curve with `a₁ = 0`. -/
theorem step6_translate_a₆ {V : WeierstrassCurve ℤ_[p]} (ha₁ : V.a₁ = 0) :
    (Step6.translate (p : ℤ_[p]) V).a₆
      = V.a₆ - (p : ℤ_[p]) * Step6.t (p : ℤ_[p]) V * V.a₃
        - ((p : ℤ_[p]) * Step6.t (p : ℤ_[p]) V) ^ 2 := by
  simp [Step6.translate, variableChange_a₆, ha₁]

/-- **`3⁴ ∣ a₆` after the Step-6 translation, on the `(I₀*, 4)` locus.** -/
theorem pow_four_dvd_step6_translate_a₆_at_three (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]}
    {A B ρ τ k : ℤ_[p]} (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 2 * ((p : ℤ_[p]) * τ))
    (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 4 * B + (p : ℤ_[p]) ^ 3 * ρ * A + (p : ℤ_[p]) ^ 3 * ρ ^ 3
      - (p : ℤ_[p]) ^ 2 * τ ^ 2)
    (hA : A = -1 + (p : ℤ_[p]) * k) :
    (p : ℤ_[p]) ^ 4 ∣ (Step6.translate (p : ℤ_[p]) V).a₆ := by
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
  obtain ⟨f, hf⟩ := three_dvd_cube_sub_self hp3 ρ
  refine ⟨B + f + ρ * k - y ^ 2, ?_⟩
  rw [step6_translate_a₆ ha₁, ha₆, ha₃, hA,
    show Step6.t (p : ℤ_[p]) V = (p : ℤ_[p]) * y - τ from by linear_combination hy]
  subst hp3
  push_cast
  linear_combination (27 : ℤ_[3]) * hf

/-! ### The Step-2 translate on the locus, in full

The translate `Step2.translate 3 (ofShortNF 9A 81B)` has `a₁ = 0`, and its remaining coefficients
are explicit polynomials in the Step-2 parameters `r = 3ρ` and `t = 3τ`. -/

/-- **The Step-2 translate of the `(I₀*, 4)` locus at `p = 3`, in full.** -/
theorem step2_translate_data_izeroStar_three (hp3 : p = 3) {A B : ℤ_[p]} :
    ∃ ρ τ : ℤ_[p],
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 4 * B))).a₁ = 0 ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 4 * B))).a₂ = (p : ℤ_[p]) ^ 2 * ρ ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 4 * B))).a₃ = 2 * ((p : ℤ_[p]) * τ) ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 4 * B))).a₄ = (p : ℤ_[p]) ^ 2 * (A + (p : ℤ_[p]) * ρ ^ 2) ∧
      (Step2.translate (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A)
        ((p : ℤ_[p]) ^ 4 * B))).a₆ = (p : ℤ_[p]) ^ 4 * B + (p : ℤ_[p]) ^ 3 * ρ * A
          + (p : ℤ_[p]) ^ 3 * ρ ^ 3 - (p : ℤ_[p]) ^ 2 * τ ^ 2 := by
  obtain ⟨a₄, ha4⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * A := ⟨_, rfl⟩
  obtain ⟨a₆, ha6⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 4 * B := ⟨_, rfl⟩
  rw [← ha4, ← ha6]
  have hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := by
    refine ⟨(-16) * (972 * A ^ 3 + 59049 * B ^ 2), ?_⟩
    rw [ofShortNF_Δ, ha4, ha6]; subst hp3; push_cast; ring
  have h₄1 : (p : ℤ_[p]) ∣ a₄ := ⟨(p : ℤ_[p]) * A, by rw [ha4]; ring⟩
  have h₆1 : (p : ℤ_[p]) ∣ a₆ := ⟨(p : ℤ_[p]) ^ 3 * B, by rw [ha6]; ring⟩
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

/-! ### The forward run -/

open scoped Classical in
/-- **The forward run at `(I₀*, 4)`, at the prime `3`.** A short model over `ℤ_3` with
`a₄ = 9A`, `A ≡ -1 (mod 3)` and `a₆ = 81B` has reduction datum exactly `(I₀*, 4)`. -/
theorem run_eq_I0star_four_three (hp3 : p = 3) {A B k : ℤ_[p]}
    (hA : A = -1 + (p : ℤ_[p]) * k)
    (hΔ : (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B)).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B))
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B))
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 4 := by
  obtain ⟨ρ, τ, h1, h2, h3, h4, h6⟩ := step2_translate_data_izeroStar_three (A := A) (B := B) hp3
  obtain ⟨V, hV⟩ : ∃ W : WeierstrassCurve ℤ_[p], W = Step2.translate (p : ℤ_[p])
    (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B)) := ⟨_, rfl⟩
  rw [← hV] at h1 h2 h3 h4 h6
  have h5 : Step5.run (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * A) ((p : ℤ_[p]) ^ 4 * B))
      = Except.ok V := by rw [hV]; exact Step5.run_eq_ok_izeroStar_three hp3
  obtain ⟨σ, hσ⟩ := dvd_step6_s hp3 h1
  obtain ⟨γ, hγ⟩ := sq_dvd_step6_translate_a₃_at_three hp3 (V := V) ⟨2 * τ, by rw [h3]; ring⟩
  have hb : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).b = 0 := by
    refine cubic_b_eq_zero_of_sq_dvd ?_
    rw [step6_translate_a₂ V h1, h2]
    exact ⟨ρ - σ ^ 2, by rw [hσ]; ring⟩
  have hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).d = 0 :=
    cubic_d_eq_zero_of_pow_four_dvd
      (pow_four_dvd_step6_translate_a₆_at_three hp3 h1 h3 h6 hA)
  have hc : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).c = -1 := by
    rw [cubic_c_eq_mod_of_eq (X := A + (p : ℤ_[p]) * ρ ^ 2 - (p : ℤ_[p]) * σ * γ) ?_, hA]
    · rw [map_sub, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
        show mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 from by rw [mod_eq_zero], map_neg, map_one]
      ring
    · rw [step6_translate_a₄ V h1, h4, hσ, hγ]; ring
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_step5 hΔ h5
    (not_hasDoubleRoot_of_neg_one_at_three hp3 rfl hb hc hd)
  exact ⟨hk, by rw [ht, card_roots_eq_three_at_three hp3 rfl hb hc hd]⟩

/-! ### The locus, its mass, and the `t = 4` row

The locus is `{a₄ ≡ 18, 45, 72 (mod 81)} × {81 ∣ a₆}`, three of the `6561` residue classes modulo
`81`, of mass `3/6561 = 1/2187`. Since `81 ∤ a₄` on all three, no point is a
`(3⁴, 3⁶)`-dilate. -/

/-- **The residue condition cutting out the `(I₀*, 4)` locus at `3`**: `a₄ ≡ 18, 45, 72` and
`a₆ ≡ 0` modulo `81`. Every class has `9 ∣ a₄`, `27 ∤ a₄` and `81 ∣ a₆`. -/
abbrev HeadResIZeroStarFourThree (A E : ZMod (3 ^ 4)) : Prop :=
  (A = 18 ∨ A = 45 ∨ A = 72) ∧ E = 0

set_option maxRecDepth 100000 in
/-- `9 ∣ a₄` on the locus. -/
theorem headResIZeroStarFourThree_cast_two :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarFourThree c.1 c.2 →
      (ZMod.cast c.1 : ZMod (3 ^ 2)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `27 ∣ a₄ + 9` on the locus, which is what makes `a₄ / 9 ≡ -1 (mod 3)`. -/
theorem headResIZeroStarFourThree_cast_three :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarFourThree c.1 c.2 →
      (ZMod.cast (c.1 + 9) : ZMod (3 ^ 3)) = 0 := by decide

set_option maxRecDepth 100000 in
/-- `81 ∣ a₆` on the locus. -/
theorem headResIZeroStarFourThree_snd :
    ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), HeadResIZeroStarFourThree c.1 c.2 → c.2 = 0 := by decide

set_option maxRecDepth 100000 in
/-- The zero class modulo `81` does not satisfy `HeadResIZeroStarFourThree`. -/
theorem not_headResIZeroStarFourThree_zero : ¬ HeadResIZeroStarFourThree 0 0 := by decide

/-- The three residue pairs of `HeadResIZeroStarFourThree`, as a `Finset`. -/
def headResiduesIZeroStarFourThree : Finset (ZMod (3 ^ 4) × ZMod (3 ^ 4)) :=
  {(18, 0), (45, 0), (72, 0)}

/-- `headResiduesIZeroStarFourThree` has three elements. -/
theorem card_headResiduesIZeroStarFourThree : headResiduesIZeroStarFourThree.card = 3 := by decide

/-- A residue pair lies in `headResiduesIZeroStarFourThree` iff it satisfies
`HeadResIZeroStarFourThree`. -/
theorem mem_headResiduesIZeroStarFourThree_iff {c : ZMod (3 ^ 4) × ZMod (3 ^ 4)} :
    c ∈ headResiduesIZeroStarFourThree ↔ HeadResIZeroStarFourThree c.1 c.2 := by
  simp [headResiduesIZeroStarFourThree, HeadResIZeroStarFourThree, Prod.ext_iff]
  tauto

/-- The **`(I₀*, 4)` locus** of the coefficient plane at `3`: the three residue classes
`(a₄, a₆) ≡ (18, 0), (45, 0), (72, 0)` modulo `81`. On it Tate's algorithm returns `(I₀*, 4)`. -/
noncomputable def iZeroStarFour3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 4 ⁻¹' (headResiduesIZeroStarFourThree : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4)))

/-- A pair lies in `iZeroStarFour3Locus` iff its reduction modulo `81` satisfies
`HeadResIZeroStarFourThree`. -/
theorem mem_iZeroStarFour3Locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ iZeroStarFour3Locus ↔
      HeadResIZeroStarFourThree (PadicInt.toZModPow 4 x.1) (PadicInt.toZModPow 4 x.2) := by
  rw [iZeroStarFour3Locus, mem_preimage, Finset.mem_coe,
    mem_headResiduesIZeroStarFourThree_iff, PadicInt.redPairPow]

/-- `3 · 3⁻⁸ = 3/6561 = 1/2187` in `ℝ≥0∞`. -/
theorem three_mul_inv_pow_eight_div_eq :
    ((3 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 4) = 1 / 2187 := by
  rw [show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num, ← ENNReal.inv_pow,
    show ((3 : ℝ≥0∞)) ^ (2 * 4) = 6561 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the `(I₀*, 4)` locus at `3` is `3/6561 = 1/2187`.** -/
theorem volume_iZeroStarFour3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iZeroStarFour3Locus = 1 / 2187 := by
  rw [iZeroStarFour3Locus, PadicInt.volume_preimage_redPairPow,
    card_headResiduesIZeroStarFourThree, three_mul_inv_pow_eight_div_eq]

/-- **Points of the `(I₀*, 4)` locus at `3`**: `a₄ = 9A` with `A ≡ -1 (mod 3)`
and `a₆ = 81B`. -/
theorem exists_form_of_mem_iZeroStarFour3Locus {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ iZeroStarFour3Locus) :
    ∃ A B k : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 2 * A ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 4 * B ∧
      A = -1 + ((3 : ℕ) : ℤ_[3]) * k := by
  have h := mem_iZeroStarFour3Locus_iff.1 hx
  obtain ⟨A, hA⟩ : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ x.1 :=
    pow_dvd_of_cast_toZModPow_eq_zero (m := 2) (n := 4) (by norm_num)
      (headResIZeroStarFourThree_cast_two (PadicInt.redPairPow 3 4 x) h)
  obtain ⟨B, hB⟩ : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 :=
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.mpr
      (headResIZeroStarFourThree_snd (PadicInt.redPairPow 3 4 x) h)
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1 + 9 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 4) (by norm_num) ?_
    have hs := headResIZeroStarFourThree_cast_three (PadicInt.redPairPow 3 4 x) h
    rwa [show PadicInt.toZModPow 4 (x.1 + 9) = PadicInt.toZModPow 4 x.1 + 9 from by
      rw [map_add, map_ofNat]]
  refine ⟨A, B, c, hA, hB, ?_⟩
  have h9 : ((3 : ℕ) : ℤ_[3]) ^ 2 * (A + 1)
      = ((3 : ℕ) : ℤ_[3]) ^ 2 * (((3 : ℕ) : ℤ_[3]) * c) := by
    rw [show ((3 : ℕ) : ℤ_[3]) ^ 2 * (A + 1) = x.1 + 9 from by
      rw [hA, show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]; ring, hc]
    rw [show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]; ring
  linear_combination mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero) h9

/-- **The `(I₀*, 4)` locus at `3` consists of nonsingular models.** -/
theorem ofShortNF_Δ_ne_zero_izeroStarFour_three {x : ℤ_[3] × ℤ_[3]}
    (hx : x ∈ iZeroStarFour3Locus) : (ofShortNF x.1 x.2).Δ ≠ 0 := by
  obtain ⟨A, B, k, hA, hB, hk⟩ := exists_form_of_mem_iZeroStarFour3Locus hx
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h729 : (729 : ℤ_[3]) ≠ 0 := by
    rw [show (729 : ℤ_[3]) = 3 ^ 6 by norm_num]; exact pow_ne_zero 6 h3
  intro hzero
  rw [ofShortNF_Δ, hA, hB, hcast] at hzero
  have hD : (4 : ℤ_[3]) * (3 ^ 2 * A) ^ 3 + 27 * (3 ^ 4 * B) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left isUnit_neg_sixteen_three.ne_zero
  have hE : (729 : ℤ_[3]) * (4 * A ^ 3 + 243 * B ^ 2) = 0 := by linear_combination hD
  have hE' : (4 : ℤ_[3]) * A ^ 3 + 243 * B ^ 2 = 0 := (mul_eq_zero.mp hE).resolve_left h729
  have hAu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ A := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, hk, map_add, map_mul, map_neg, map_one,
      show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by
        rw [← PadicInt.dvd_iff_toZMod_eq_zero],
      zero_mul, add_zero]
    decide
  refine hAu (PadicInt.prime_p.dvd_of_dvd_pow (n := 3) ?_)
  refine (PadicInt.prime_p.dvd_or_dvd (a := (4 : ℤ_[3])) (b := A ^ 3) ?_).resolve_left
    not_three_dvd_four
  exact ⟨-(81 * B ^ 2), by rw [hcast]; linear_combination hE'⟩

open scoped Classical in
/-- **The `(I₀*, 4)` locus at `3` lies in the strata over `t = 4`.** -/
theorem iZeroStarFour3Locus_subset_iUnion_stratFibre :
    iZeroStarFour3Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 4) := by
  intro x hx
  obtain ⟨A, B, k, hA, hB, hk⟩ := exists_form_of_mem_iZeroStarFour3Locus hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_izeroStarFour_three hx
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_I0star_four_three (p := 3) rfl (A := A) (B := B) (k := k) hk
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 2 * A) (((3 : ℕ) : ℤ_[3]) ^ 4 * B)).Δ ≠ 0 from by
      rw [← hA, ← hB]; exact hΔ)
  refine Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0, (mem_stratFibre_iff hUp).2 ?_⟩
  rw [strat]
  refine Prod.ext ?_ ?_
  · simp only [hA, hB]; exact hks
  · simp only [hA, hB]; exact hts

/-- **The `(I₀*, 4)` locus at `3` lies in the minimal part of the `t = 4` row.** -/
theorem iZeroStarFour3Locus_subset_headMinimal :
    iZeroStarFour3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine fun x hx => ⟨iZeroStarFour3Locus_subset_iUnion_stratFibre hx, ?_⟩
  refine notMem_range_scaleProdByPPow_of_toZModPow_ne_zero_at_three (k := 4) (by norm_num) ?_
  rintro ⟨h1, h2⟩
  have h := mem_iZeroStarFour3Locus_iff.1 hx
  rw [h1, h2] at h
  exact not_headResIZeroStarFourThree_zero h

end WeierstrassCurve

end
