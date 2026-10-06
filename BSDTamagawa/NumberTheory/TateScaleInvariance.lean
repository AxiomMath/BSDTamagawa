/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateTailLaw

/-!
# Reducing `StratScaleInvariant` to invariance under integral translation

For a prime `p ≥ 5`, the dilation `σ(W) = ⟨pa₁, p²a₂, p³a₃, p⁴a₄, p⁶a₆⟩` of a Weierstrass curve
over `ℤ_p` has `p⁴ ∣ c₄` and `p⁶ ∣ c₆`, so Tate's algorithm passes through Steps 1–10 without
answering and Step 11 rescales. Steps 1–10 move the curve only by changes of variables
`⟨1, r, s, t⟩`, and Step 11's rescaling conjugates such a change into another one, so the curve on
which the algorithm restarts is an integral translate of `W`. Hence
`WeierstrassCurve.StratScaleInvariant p` follows from
`WeierstrassCurve.RunIntTranslateInvariant p`, the invariance of Tate's algorithm under changes of
variables with `u = 1`. On the way, every branch condition of Steps 6–10 is rewritten as a
divisibility condition on `c₄`, `c₆` or `Δ`.

## Main definitions

* `WeierstrassCurve.IsIntTranslate`: two curves differ by a change of variables with `u = 1`.
* `WeierstrassCurve.scaleUp`: the dilation `⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩`.
* `WeierstrassCurve.RunIntTranslateInvariant`: Tate's algorithm over `ℤ_p` returns the same Kodaira
  symbol and Tamagawa number on two curves that differ by a change of variables with `u = 1`.

## Main results

* `WeierstrassCurve.TateAlgorithm.hasDoubleRoot_iff_pow_dvd_Δ`,
  `WeierstrassCurve.TateAlgorithm.hasTripleRoot_iff_cb_dvd_c₄`,
  `WeierstrassCurve.TateAlgorithm.quadratic_hasDoubleRoot_iff`,
  `WeierstrassCurve.TateAlgorithm.pow_four_dvd_a₄_iff`,
  `WeierstrassCurve.TateAlgorithm.pow_six_dvd_a₆_iff`: the branch conditions of Steps 6–10 in terms
  of `c₄`, `c₆` and `Δ`, for `p ≥ 5`.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_pow_dvd_c₄_c₆`: at `p ≥ 5`, on a model with
  `p⁴ ∣ c₄` and `p⁶ ∣ c₆` Steps 1–10 do not answer, so Step 11 rescales.
* `WeierstrassCurve.TateAlgorithm.Step10.isIntTranslate_of_run_ok`: the curve reaching Step 11 is
  an integral translate of the input.
* `WeierstrassCurve.TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp`: on a dilate `σ(W)`, the
  curve handed back by Step 11 is an integral translate of `W`.
* `WeierstrassCurve.stratScaleInvariant_of_runIntTranslateInvariant`:
  `5 ≤ p → RunIntTranslateInvariant p → StratScaleInvariant p`.
-/

@[expose] public section

universe u

open CommRing Ideal

namespace WeierstrassCurve

/-! ### Integral translates: differing by a change of variables with `u = 1` -/

variable {R : Type u} [CommRing R]

/-- **Two curves differ by an integral translation.** `W'` is obtained from `W` by an admissible
change of variables `(X, Y) ↦ (X + r, Y + sX + t)` with `u = 1`. -/
def IsIntTranslate (W W' : WeierstrassCurve R) : Prop :=
  ∃ r s t : R, W' = (VariableChange.mk 1 r s t) • W

/-- `IsIntTranslate` is reflexive: the identity change of variables is `⟨1, 0, 0, 0⟩`. -/
theorem IsIntTranslate.refl (W : WeierstrassCurve R) : IsIntTranslate W W :=
  ⟨0, 0, 0, by rw [show (VariableChange.mk 1 0 0 0 : VariableChange R) = 1 from rfl, one_smul]⟩

/-- `IsIntTranslate` is transitive: the composite of two `u = 1` changes of variables is one, the
`u`-component of a product being the product of the `u`-components. -/
theorem IsIntTranslate.trans {W W' W'' : WeierstrassCurve R} (h : IsIntTranslate W W')
    (h' : IsIntTranslate W' W'') : IsIntTranslate W W'' := by
  obtain ⟨r, s, t, rfl⟩ := h
  obtain ⟨r', s', t', rfl⟩ := h'
  refine ⟨r' + r, s' + s, t' + r' * s + t, ?_⟩
  rw [← mul_smul]
  congr 1
  rw [VariableChange.mul_def]
  ext <;> simp

/-! ### The dilation, on an arbitrary curve -/

/-- **The dilation `σ` of an arbitrary Weierstrass curve**: the weight-`(1, 2, 3, 4, 6)` scaling
`⟨ϖa₁, ϖ²a₂, ϖ³a₃, ϖ⁴a₄, ϖ⁶a₆⟩`. -/
def scaleUp (ϖ : R) (W : WeierstrassCurve R) : WeierstrassCurve R :=
  ⟨ϖ * W.a₁, ϖ ^ 2 * W.a₂, ϖ ^ 3 * W.a₃, ϖ ^ 4 * W.a₄, ϖ ^ 6 * W.a₆⟩

/-- On a short model the dilation is `⟨0, 0, 0, ϖ⁴a₄, ϖ⁶a₆⟩`. -/
theorem scaleUp_ofShortNF (ϖ a₄ a₆ : R) :
    scaleUp ϖ (ofShortNF a₄ a₆) = ofShortNF (ϖ ^ 4 * a₄) (ϖ ^ 6 * a₆) := by
  ext <;> simp [scaleUp]

/-- **The dilation conjugates an integral translation into an integral translation with weighted
parameters.** Dilating after translating by `(r, s, t)` is translating by `(ϖ²r, ϖs, ϖ³t)` after
dilating. -/
theorem scaleUp_smul (ϖ : R) (W : WeierstrassCurve R) (r s t : R) :
    scaleUp ϖ ((VariableChange.mk 1 r s t) • W)
      = (VariableChange.mk 1 (ϖ ^ 2 * r) (ϖ * s) (ϖ ^ 3 * t)) • scaleUp ϖ W := by
  ext <;> simp [scaleUp, variableChange_def] <;> ring

/-! ### Step 11's rescaling inverts the dilation, translations and all -/

namespace TateAlgorithm.Step11

variable [IsDomain R]

/-- `ϖ ^ k` divides `ϖ ^ k * a` exactly. -/
private theorem div_pow_mul_self' {ϖ : R} (hϖ : ϖ ≠ 0) (k : ℕ) (a : R) :
    CommRing.div (ϖ ^ k * a) (ϖ ^ k) = a :=
  mul_left_cancel₀ (pow_ne_zero k hϖ)
    (CommRing.mul_div (pow_ne_zero k hϖ) (Dvd.intro a rfl))

/-- **Step 11's rescaling undoes the dilation**, for an arbitrary curve. -/
theorem translate_scaleUp {ϖ : R} (hϖ : ϖ ≠ 0) (W : WeierstrassCurve R) :
    translate ϖ (scaleUp ϖ W) = W := by
  have h1 : CommRing.div (ϖ * W.a₁) ϖ = W.a₁ := by simpa using div_pow_mul_self' hϖ 1 W.a₁
  ext <;>
    simp only [translate, scaleUp, h1, div_pow_mul_self' hϖ 2, div_pow_mul_self' hϖ 3,
      div_pow_mul_self' hϖ 4, div_pow_mul_self' hϖ 6]

/-- **The descent conjugates the translation.** Step 11's rescaling, applied to a dilate that has
been translated by `(ϖ²r, ϖs, ϖ³t)`, returns the base curve translated by `(r, s, t)`. -/
theorem translate_smul_scaleUp {ϖ : R} (hϖ : ϖ ≠ 0) (W : WeierstrassCurve R) (r s t : R) :
    translate ϖ ((VariableChange.mk 1 (ϖ ^ 2 * r) (ϖ * s) (ϖ ^ 3 * t)) • scaleUp ϖ W)
      = (VariableChange.mk 1 r s t) • W := by
  rw [← scaleUp_smul, translate_scaleUp hϖ]

end TateAlgorithm.Step11

/-- **Step 10's valuation bound pins the translation parameters of a translated dilate.** If
`⟨1, r, s, t⟩ • σ(W)` has `ϖ ∣ a₁`, `ϖ² ∣ a₂` and `ϖ³ ∣ a₃`, and `2` and `3` are units, then
`ϖ ∣ s`, `ϖ² ∣ r` and `ϖ³ ∣ t`. -/
theorem dvd_of_smul_scaleUp {ϖ : R} (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (W : WeierstrassCurve R) {r s t : R}
    (ha₁ : ϖ ∣ ((VariableChange.mk 1 r s t) • scaleUp ϖ W).a₁)
    (ha₂ : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • scaleUp ϖ W).a₂)
    (ha₃ : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • scaleUp ϖ W).a₃) :
    ϖ ∣ s ∧ ϖ ^ 2 ∣ r ∧ ϖ ^ 3 ∣ t := by
  simp only [variableChange_def, scaleUp, inv_one, Units.val_one, one_pow, one_mul] at ha₁ ha₂ ha₃
  have hs : ϖ ∣ s := by
    have h2s : ϖ ∣ 2 * s := by
      have h := dvd_sub ha₁ (Dvd.intro W.a₁ rfl)
      rwa [show ϖ * W.a₁ + 2 * s - ϖ * W.a₁ = 2 * s by ring] at h
    rwa [h2.dvd_mul_left] at h2s
  obtain ⟨σ, hσ⟩ := hs
  have hr : ϖ ^ 2 ∣ r := by
    have hkey : ϖ ^ 2 ∣ 3 * r := by
      have hrest : ϖ ^ 2 ∣ ϖ ^ 2 * W.a₂ - s * (ϖ * W.a₁) - s ^ 2 := by
        refine dvd_sub (dvd_sub (Dvd.intro W.a₂ rfl) ⟨σ * W.a₁, by rw [hσ]; ring⟩)
          ⟨σ ^ 2, by rw [hσ]; ring⟩
      have h := dvd_sub ha₂ hrest
      rwa [show ϖ ^ 2 * W.a₂ - s * (ϖ * W.a₁) + 3 * r - s ^ 2
        - (ϖ ^ 2 * W.a₂ - s * (ϖ * W.a₁) - s ^ 2) = 3 * r by ring] at h
    rwa [h3.dvd_mul_left] at hkey
  obtain ⟨ρ, hρ⟩ := hr
  refine ⟨⟨σ, hσ⟩, ⟨ρ, hρ⟩, ?_⟩
  have hkey : ϖ ^ 3 ∣ 2 * t := by
    have hrest : ϖ ^ 3 ∣ ϖ ^ 3 * W.a₃ + r * (ϖ * W.a₁) :=
      dvd_add (Dvd.intro W.a₃ rfl) ⟨ρ * W.a₁, by rw [hρ]; ring⟩
    have h := dvd_sub ha₃ hrest
    rwa [show ϖ ^ 3 * W.a₃ + r * (ϖ * W.a₁) + 2 * t - (ϖ ^ 3 * W.a₃ + r * (ϖ * W.a₁))
      = 2 * t by ring] at h
  rwa [h2.dvd_mul_left] at hkey

/-! ### Steps 1–10 move the curve only by a `u = 1` change of variables

Each of the algorithm's four translations — Step 2's move of the singular point to the origin, Step
6's `(X, Y) ↦ (X, Y + sX + ϖt)`, Step 8's `X ↦ X - ϖr` and Step 9's `Y ↦ Y + ϖ²t` — is a
`VariableChange.mk 1 _ _ _`. Steps 1, 3, 4, 5, 7 and 10 pass the curve through unchanged. -/

namespace TateAlgorithm

variable {ϖ : R} [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] {W W' : WeierstrassCurve R}

/-- Step 2's translation is a `u = 1` change of variables (or the identity, off the discriminant
locus): its parameters are the `Quotient.out` lifts of the singular point's coordinates. -/
theorem Step2.isIntTranslate_translate (W : WeierstrassCurve R) :
    IsIntTranslate W (Step2.translate ϖ W) := by
  rw [Step2.translate]
  split_ifs with h
  · exact ⟨_, 0, _, rfl⟩
  · exact IsIntTranslate.refl W

omit [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] in
/-- Step 1 passes the curve through unchanged. -/
theorem Step1.isIntTranslate_of_run_ok (h : Step1.run ϖ W = .ok W') : IsIntTranslate W W' := by
  rw [Step1.run_weierstrassCurve h]; exact IsIntTranslate.refl W

/-- Step 2 hands on the Step-2 translate of the input. -/
theorem Step2.isIntTranslate_of_run_ok (h : Step2.run ϖ W = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'
  cases h'
  obtain rfl := Step1.run_weierstrassCurve hV
  exact Step2.isIntTranslate_translate _

/-- Step 3 passes the curve through unchanged. -/
theorem Step3.isIntTranslate_of_run_ok (h : Step3.run ϖ W = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'; exact Step2.isIntTranslate_of_run_ok hV

/-- Step 4 passes the curve through unchanged. -/
theorem Step4.isIntTranslate_of_run_ok (h : Step4.run ϖ W = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'; exact Step3.isIntTranslate_of_run_ok hV

/-- Step 5 passes the curve through unchanged. -/
theorem Step5.isIntTranslate_of_run_ok (h : Step5.run ϖ W = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'; exact Step4.isIntTranslate_of_run_ok hV

/-- Step 6 hands on `(X, Y) ↦ (X, Y + sX + ϖt)` applied to Step 5's curve. -/
theorem Step6.isIntTranslate_of_run_ok (h : Step6.run ϖ W = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'
  exact (Step5.isIntTranslate_of_run_ok hV).trans ⟨0, _, _, rfl⟩

variable [IsNoetherianRing R] [IsDomain R] (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- Step 7 passes the curve through unchanged when it succeeds: its own translations happen only in
the subprocedure, which is reached on the `error` branch. -/
theorem Step7.isIntTranslate_of_run_ok (h : Step7.run hϖ hΔ = .ok W') : IsIntTranslate W W' := by
  rw [Step7.run] at h
  split at h
  · contradiction
  · split_ifs at h; cases h; exact Step6.isIntTranslate_of_run_ok <| by assumption

/-- Step 8 hands on `X ↦ X - ϖr` applied to Step 7's curve. -/
theorem Step8.isIntTranslate_of_run_ok (h : Step8.run hϖ hΔ = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'
  exact (Step7.isIntTranslate_of_run_ok hϖ hΔ hV).trans ⟨_, 0, 0, rfl⟩

/-- Step 9 hands on `Y ↦ Y + ϖ²t` applied to Step 8's curve. -/
theorem Step9.isIntTranslate_of_run_ok (h : Step9.run hϖ hΔ = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'
  exact (Step8.isIntTranslate_of_run_ok hϖ hΔ hV).trans ⟨0, 0, _, rfl⟩

/-- **The curve reaching Step 11 is an integral translate of the input.** -/
theorem Step10.isIntTranslate_of_run_ok (h : Step10.run hϖ hΔ = .ok W') : IsIntTranslate W W' := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, h'⟩
  split_ifs at h'; cases h'; exact Step9.isIntTranslate_of_run_ok hϖ hΔ hV

end TateAlgorithm

end WeierstrassCurve

/-! ### The ten branch conditions of Steps 1–10, in `c₄`, `c₆` and `Δ`

All statements are at `p ≥ 5`, where `2`, `3`, `16`, `24`, `48`, `216`, `864` and `1728` are units
of `ℤ_p`. -/

namespace WeierstrassCurve.TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-- `ϖ ^ k` divides `ϖ ^ k * a` exactly, over `ℤ_p`. -/
private theorem div_mul_left (k : ℕ) (a : ℤ_[p]) :
    div ((p : ℤ_[p]) ^ k * a) ((p : ℤ_[p]) ^ k) = a :=
  mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-- `48 = 2⁴ · 3` is a unit of `ℤ_p` for `p ≥ 5`. -/
private theorem isUnit_fortyEightP (hp : 5 ≤ p) : IsUnit (48 : ℤ_[p]) := by
  simpa using (isUnit_neg_fortyEight hp).neg

/-- `864 = 2⁵ · 27` is a unit of `ℤ_p` for `p ≥ 5`. -/
private theorem isUnit_eightSixFourP (hp : 5 ≤ p) : IsUnit (864 : ℤ_[p]) := by
  simpa using (isUnit_neg_eightSixFour hp).neg

/-- `1728 = 2⁶ · 27` is a unit of `ℤ_p` for `p ≥ 5`. -/
private theorem isUnit_seventeenTwentyEight (hp : 5 ≤ p) : IsUnit (1728 : ℤ_[p]) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h : IsUnit ((2 : ℤ_[p]) ^ 6 * 27) :=
    ((PadicInt.isUnit_two hodd).pow 6).mul (isUnit_twentySeven hp)
  simpa [show (2 : ℤ_[p]) ^ 6 * 27 = 1728 by norm_num] using h

/-- **`p⁴ ∣ c₄` and `p⁶ ∣ c₆` force `p¹² ∣ Δ`**, for `p ≥ 5`. Mathlib's `c_relation` is
`1728 Δ = c₄³ - c₆²`, and `1728` is a unit at `p ≥ 5`, so `Δ` inherits the divisibility of `c₄³`
and `c₆²`. -/
theorem pow_dvd_Δ_of_pow_dvd_c₄_c₆ (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    (hc₄ : (p : ℤ_[p]) ^ 4 ∣ W.c₄) (hc₆ : (p : ℤ_[p]) ^ 6 ∣ W.c₆) :
    (p : ℤ_[p]) ^ 12 ∣ W.Δ := by
  have h : (p : ℤ_[p]) ^ 12 ∣ 1728 * W.Δ := by
    rw [W.c_relation]
    refine dvd_sub ?_ ?_
    · rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul]; exact pow_dvd_pow_of_dvd hc₄ 3
    · rw [show (12 : ℕ) = 6 * 2 from rfl, pow_mul]; exact pow_dvd_pow_of_dvd hc₆ 2
  rwa [(isUnit_seventeenTwentyEight hp).dvd_mul_left] at h

/-- **Steps 1–5 all pass on a model with `p ∣ Δ`, `p² ∣ c₄` and `p³ ∣ c₆`**, for `p ≥ 5`, and the
curve they hand on is the Step-2 translate of the input. -/
theorem Step5.run_eq_ok_of_pow_dvd_c₄_c₆ (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (hd : (p : ℤ_[p]) ∣ V.Δ) (hc₄ : (p : ℤ_[p]) ^ 2 ∣ V.c₄) (hc₆ : (p : ℤ_[p]) ^ 3 ∣ V.c₆) :
    Step5.run (p : ℤ_[p]) V = Except.ok (Step2.translate (p : ℤ_[p]) V) := by
  have hc₄1 : (p : ℤ_[p]) ∣ V.c₄ := (dvd_pow_self _ two_ne_zero).trans hc₄
  have hc₆2 : (p : ℤ_[p]) ^ 2 ∣ V.c₆ := (pow_dvd_pow _ (by norm_num)).trans hc₆
  have hb₂ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) V).b₂ :=
    Step2.dvd_translate_b₂_of_dvd_c₄ hd hc₄1
  have h2 : Step2.run (p : ℤ_[p]) V = Except.ok (Step2.translate (p : ℤ_[p]) V) :=
    Step2.run_eq_ok_of_dvd_c₄ hd hc₄1
  have h3 : Step3.run (p : ℤ_[p]) V = Except.ok (Step2.translate (p : ℤ_[p]) V) := by
    rw [Step3.run.eq_def, h2]
    simp only [except_ok_bind]
    exact ite_eq_left ((sq_dvd_translate_a₆_iff_sq_dvd_c₆ hp hd hc₄1).mpr hc₆2)
  have hval3 := Step3.run_hasValuation h3
  have h4 : Step4.run (p : ℤ_[p]) V = Except.ok (Step2.translate (p : ℤ_[p]) V) := by
    rw [Step4.run.eq_def, h3]
    simp only [except_ok_bind]
    refine ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hval3.b₂) hval3.b₆).mpr ?_)
    rwa [Step2.translate_c₄]
  have hval4 := Step4.run_hasValuation PadicInt.uniformizer_ne_zero h4
  rw [Step5.run.eq_def, h4]
  simp only [except_ok_bind]
  refine ite_eq_left ((cb_dvd_b₆_iff_cb_dvd_c₆ hp hb₂ hval4.b₄).mpr ?_)
  rwa [Step2.translate_c₆]

/-- **Step 6's branch condition, in invariant form: `ϖ⁷ ∣ Δ`.** For `p ≥ 5`, on a curve in the
state `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆`, the Step-6 cubic `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` has a
double root iff `ϖ⁷ ∣ Δ`. Indeed `Δ = ϖ⁶ D` with `D ≡ 16 · disc(cubic) (mod ϖ)`. -/
theorem hasDoubleRoot_iff_pow_dvd_Δ (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (ha₁ : (p : ℤ_[p]) ∣ V.a₁) (ha₂ : (p : ℤ_[p]) ∣ V.a₂)
    (ha₃ : (p : ℤ_[p]) ^ 2 ∣ V.a₃) (ha₄ : (p : ℤ_[p]) ^ 2 ∣ V.a₄)
    (ha₆ : (p : ℤ_[p]) ^ 3 ∣ V.a₆) :
    (cubic (p : ℤ_[p]) V 1 1).HasDoubleRoot ↔ (p : ℤ_[p]) ^ 7 ∣ V.Δ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  have d₂ : div V.a₂ (p : ℤ_[p]) = α₂ := by rw [e₂]; simpa using div_mul_left 1 α₂
  have d₄ : div V.a₄ ((p : ℤ_[p]) ^ 2) = α₄ := by rw [e₄]; exact div_mul_left 2 α₄
  have d₆ : div V.a₆ ((p : ℤ_[p]) ^ 3) = α₆ := by rw [e₆]; exact div_mul_left 3 α₆
  set ϖ : ℤ_[p] := (p : ℤ_[p])
  have key : V.Δ = ϖ ^ 6 *
      (-(4 * α₂ + ϖ * α₁ ^ 2) ^ 2 * (4 * α₂ * α₆ - α₄ ^ 2
          + ϖ * (α₁ ^ 2 * α₆ - α₁ * α₃ * α₄ + α₂ * α₃ ^ 2))
        - 8 * (2 * α₄ + ϖ * α₁ * α₃) ^ 3 - 27 * (4 * α₆ + ϖ * α₃ ^ 2) ^ 2
        + 9 * (4 * α₂ + ϖ * α₁ ^ 2) * (2 * α₄ + ϖ * α₁ * α₃) * (4 * α₆ + ϖ * α₃ ^ 2)) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, e₁, e₂, e₃, e₄, e₆]
    ring
  have hcancel : ϖ ^ 7 ∣ V.Δ ↔ ϖ ∣ (-(4 * α₂ + ϖ * α₁ ^ 2) ^ 2 * (4 * α₂ * α₆ - α₄ ^ 2
          + ϖ * (α₁ ^ 2 * α₆ - α₁ * α₃ * α₄ + α₂ * α₃ ^ 2))
        - 8 * (2 * α₄ + ϖ * α₁ * α₃) ^ 3 - 27 * (4 * α₆ + ϖ * α₃ ^ 2) ^ 2
        + 9 * (4 * α₂ + ϖ * α₁ ^ 2) * (2 * α₄ + ϖ * α₁ * α₃) * (4 * α₆ + ϖ * α₃ ^ 2)) := by
    rw [key, show (ϖ : ℤ_[p]) ^ 7 = ϖ ^ 6 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 6 hϖ)]
  rw [hcancel, ← mod_eq_zero]
  have hmod : (mod ϖ) (-(4 * α₂ + ϖ * α₁ ^ 2) ^ 2 * (4 * α₂ * α₆ - α₄ ^ 2
          + ϖ * (α₁ ^ 2 * α₆ - α₁ * α₃ * α₄ + α₂ * α₃ ^ 2))
        - 8 * (2 * α₄ + ϖ * α₁ * α₃) ^ 3 - 27 * (4 * α₆ + ϖ * α₃ ^ 2) ^ 2
        + 9 * (4 * α₂ + ϖ * α₁ ^ 2) * (2 * α₄ + ϖ * α₁ * α₃) * (4 * α₆ + ϖ * α₃ ^ 2))
      = 16 * ((mod ϖ α₂) ^ 2 * (mod ϖ α₄) ^ 2 - 4 * (mod ϖ α₄) ^ 3
          - 4 * (mod ϖ α₂) ^ 3 * (mod ϖ α₆) - 27 * (mod ϖ α₆) ^ 2
          + 18 * (mod ϖ α₂) * (mod ϖ α₄) * (mod ϖ α₆)) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mod_self, zero_mul, add_zero]
    ring
  rw [hmod, Cubic.hasDoubleRoot_of_a_eq_one (by simp [cubic]), cubic]
  norm_num only [d₂, d₄, d₆]
  have h16 : IsUnit (16 : ℤ_[p] ⧸ span {ϖ}) := by
    have h := (isUnit_sixteen hp).map (mod ϖ)
    rwa [map_ofNat] at h
  rw [h16.mul_right_eq_zero]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Step 7's branch condition, in invariant form: `ϖ³ ∣ c₄`.** For `p ≥ 5`, on a curve with
`ϖ ∣ a₁, a₂` and `ϖ² ∣ a₃, a₄`, the Step-6 cubic has a *triple* root iff `ϖ³ ∣ c₄`.

Writing `a₂ = ϖα₂` and `a₄ = ϖ²α₄`, the triple-root condition is `ϖ ∣ α₂² - 3α₄`, and
`c₄ = ϖ²(16(α₂² - 3α₄) + ϖ · …)`. -/
theorem hasTripleRoot_iff_cb_dvd_c₄ (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (ha₁ : (p : ℤ_[p]) ∣ V.a₁) (ha₂ : (p : ℤ_[p]) ∣ V.a₂)
    (ha₃ : (p : ℤ_[p]) ^ 2 ∣ V.a₃) (ha₄ : (p : ℤ_[p]) ^ 2 ∣ V.a₄) :
    (cubic (p : ℤ_[p]) V 1 1).HasTripleRoot ↔ (p : ℤ_[p]) ^ 3 ∣ V.c₄ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  have d₂ : div V.a₂ (p : ℤ_[p]) = α₂ := by rw [e₂]; simpa using div_mul_left 1 α₂
  have d₄ : div V.a₄ ((p : ℤ_[p]) ^ 2) = α₄ := by rw [e₄]; exact div_mul_left 2 α₄
  set ϖ : ℤ_[p] := (p : ℤ_[p])
  have key : V.c₄ = ϖ ^ 2 * (16 * (α₂ ^ 2 - 3 * α₄)
      + ϖ * (8 * α₁ ^ 2 * α₂ - 24 * α₁ * α₃ + ϖ * α₁ ^ 4)) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, e₁, e₂, e₃, e₄]
    ring
  have hcancel : ϖ ^ 3 ∣ V.c₄ ↔ ϖ ∣ α₂ ^ 2 - 3 * α₄ := by
    rw [key, show (ϖ : ℤ_[p]) ^ 3 = ϖ ^ 2 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ)]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hs := dvd_sub h (dvd_mul_right (ϖ : ℤ_[p])
        (8 * α₁ ^ 2 * α₂ - 24 * α₁ * α₃ + ϖ * α₁ ^ 4))
      rwa [add_sub_cancel_right, (isUnit_sixteen hp).dvd_mul_left] at hs
    · exact dvd_add ((isUnit_sixteen hp).dvd_mul_left.mpr h) (dvd_mul_right _ _)
  rw [hcancel, Cubic.HasTripleRoot, cubic]
  norm_num only [d₂, d₄]
  rw [← map_pow, ← map_ofNat (mod (ϖ : ℤ_[p])) 3, ← map_mul, ← sub_eq_zero, ← map_sub, mod_eq_zero]

/-- **Step 8's branch condition, in invariant form: `ϖ⁵ ∣ c₆`.** For `p ≥ 5`, on a curve in the
state `ϖ² ∣ a₃`, `ϖ⁴ ∣ a₆`, `ϖ² ∣ b₂`, `ϖ³ ∣ b₄`, the quadratic `Y² + a₃Y/ϖ² - a₆/ϖ⁴` has a double
root iff `ϖ⁵ ∣ c₆`.

Its discriminant is `b₆/ϖ⁴`, so the test is `ϖ⁵ ∣ b₆`; and `c₆ + 216 b₆ = -b₂³ + 36 b₂b₄` lies in
`(ϖ⁵)`, with `216` a unit. -/
theorem quadratic_hasDoubleRoot_iff (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (ha₃ : (p : ℤ_[p]) ^ 2 ∣ V.a₃) (ha₆ : (p : ℤ_[p]) ^ 4 ∣ V.a₆)
    (hb₂ : (p : ℤ_[p]) ^ 2 ∣ V.b₂) (hb₄ : (p : ℤ_[p]) ^ 3 ∣ V.b₄) :
    (quadratic (p : ℤ_[p]) V 2).HasDoubleRoot ↔ (p : ℤ_[p]) ^ 5 ∣ V.c₆ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨β₃, e₃⟩ := ha₃
  obtain ⟨β₆, e₆⟩ := ha₆
  obtain ⟨u₂, hu₂⟩ := hb₂
  obtain ⟨u₄, hu₄⟩ := hb₄
  have d₃ : div V.a₃ ((p : ℤ_[p]) ^ 2) = β₃ := by rw [e₃]; exact div_mul_left 2 β₃
  have d₆ : div V.a₆ ((p : ℤ_[p]) ^ 4) = β₆ := by rw [e₆]; exact div_mul_left 4 β₆
  set ϖ : ℤ_[p] := (p : ℤ_[p])
  have hb₆ : ϖ ^ 5 ∣ V.b₆ ↔ ϖ ∣ β₃ ^ 2 + 4 * β₆ := by
    have key : V.b₆ = ϖ ^ 4 * (β₃ ^ 2 + 4 * β₆) := by
      simp only [WeierstrassCurve.b₆, e₃, e₆]; ring
    rw [key, show (ϖ : ℤ_[p]) ^ 5 = ϖ ^ 4 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 4 hϖ)]
  have hc₆ : ϖ ^ 5 ∣ V.c₆ ↔ ϖ ^ 5 ∣ V.b₆ := by
    have key : V.c₆ + 216 * V.b₆ = -V.b₂ ^ 3 + 36 * V.b₂ * V.b₄ := by
      simp only [WeierstrassCurve.c₆]; ring
    have hrest : ϖ ^ 5 ∣ -V.b₂ ^ 3 + 36 * V.b₂ * V.b₄ :=
      ⟨-(ϖ * u₂ ^ 3) + 36 * u₂ * u₄, by rw [hu₂, hu₄]; ring⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hs := dvd_sub hrest h
      rwa [← key, add_sub_cancel_left, (isUnit_twoHundredSixteen hp).dvd_mul_left] at hs
    · have hs := dvd_sub hrest (h.mul_left 216)
      rwa [← key, add_sub_cancel_right] at hs
  rw [hc₆, hb₆, Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) (by simp [quadratic]),
    quadratic]
  norm_num only [d₃, d₆]
  rw [← sub_eq_zero, ← mod_eq_zero (ϖ) (β₃ ^ 2 + 4 * β₆)]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Step 9's branch condition, in invariant form: `ϖ⁴ ∣ c₄`.** For `p ≥ 5`, on a curve with
`ϖ ∣ a₁`, `ϖ³ ∣ a₃` and `ϖ² ∣ b₂`, one has `ϖ⁴ ∣ a₄ ↔ ϖ⁴ ∣ c₄`, because `c₄ + 48a₄ = b₂² - 24a₁a₃`
lies in `(ϖ⁴)` and `48` is a unit. -/
theorem pow_four_dvd_a₄_iff (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (ha₁ : (p : ℤ_[p]) ∣ V.a₁) (ha₃ : (p : ℤ_[p]) ^ 3 ∣ V.a₃) (hb₂ : (p : ℤ_[p]) ^ 2 ∣ V.b₂) :
    (p : ℤ_[p]) ^ 4 ∣ V.a₄ ↔ (p : ℤ_[p]) ^ 4 ∣ V.c₄ := by
  obtain ⟨v₁, hv₁⟩ := ha₁
  obtain ⟨v₃, hv₃⟩ := ha₃
  obtain ⟨u₂, hu₂⟩ := hb₂
  set ϖ : ℤ_[p] := (p : ℤ_[p])
  have key : V.c₄ + 48 * V.a₄ = V.b₂ ^ 2 - 24 * (V.a₁ * V.a₃) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
  have hrest : ϖ ^ 4 ∣ V.b₂ ^ 2 - 24 * (V.a₁ * V.a₃) :=
    ⟨u₂ ^ 2 - 24 * (v₁ * v₃), by rw [hu₂, hv₁, hv₃]; ring⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := dvd_sub hrest (h.mul_left 48)
    rwa [← key, add_sub_cancel_right] at hs
  · have hs := dvd_sub hrest h
    rwa [← key, add_sub_cancel_left, (isUnit_fortyEightP hp).dvd_mul_left] at hs

/-- **Step 10's branch condition, in invariant form: `ϖ⁶ ∣ c₆`.** For `p ≥ 5`, on a curve with
`ϖ³ ∣ a₃`, `ϖ² ∣ b₂` and `ϖ⁴ ∣ b₄`, one has `ϖ⁶ ∣ a₆ ↔ ϖ⁶ ∣ c₆`, because
`c₆ + 864a₆ = -b₂³ + 36b₂b₄ - 216a₃²` lies in `(ϖ⁶)` and `864` is a unit. -/
theorem pow_six_dvd_a₆_iff (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (ha₃ : (p : ℤ_[p]) ^ 3 ∣ V.a₃) (hb₂ : (p : ℤ_[p]) ^ 2 ∣ V.b₂)
    (hb₄ : (p : ℤ_[p]) ^ 4 ∣ V.b₄) :
    (p : ℤ_[p]) ^ 6 ∣ V.a₆ ↔ (p : ℤ_[p]) ^ 6 ∣ V.c₆ := by
  obtain ⟨v₃, hv₃⟩ := ha₃
  obtain ⟨u₂, hu₂⟩ := hb₂
  obtain ⟨u₄, hu₄⟩ := hb₄
  set ϖ : ℤ_[p] := (p : ℤ_[p])
  have key : V.c₆ + 864 * V.a₆ = -V.b₂ ^ 3 + 36 * (V.b₂ * V.b₄) - 216 * V.a₃ ^ 2 := by
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₆]; ring
  have hrest : ϖ ^ 6 ∣ -V.b₂ ^ 3 + 36 * (V.b₂ * V.b₄) - 216 * V.a₃ ^ 2 :=
    ⟨-u₂ ^ 3 + 36 * (u₂ * u₄) - 216 * v₃ ^ 2, by rw [hu₂, hu₄, hv₃]; ring⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := dvd_sub hrest (h.mul_left 864)
    rwa [← key, add_sub_cancel_right] at hs
  · have hs := dvd_sub hrest h
    rwa [← key, add_sub_cancel_left, (isUnit_eightSixFourP hp).dvd_mul_left] at hs

/-! ### The non-minimality criterion -/

/-- **Steps 1–10 cannot answer on a model with `p⁴ ∣ c₄` and `p⁶ ∣ c₆`, so Step 11 fires.** For
every prime `p ≥ 5` and every curve over `ℤ_p` with `Δ ≠ 0`, `p⁴ ∣ c₄` and `p⁶ ∣ c₆`, Tate's
algorithm traverses the whole first pass and hands a curve back to the top-level recursion. This is
the classical non-minimality criterion. -/
theorem Step11.run_eq_ok_of_pow_dvd_c₄_c₆ (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    (hΔ : W.Δ ≠ 0) (hc₄ : (p : ℤ_[p]) ^ 4 ∣ W.c₄) (hc₆ : (p : ℤ_[p]) ^ 6 ∣ W.c₆) :
    ∃ V, Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.ok V := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hΔ12 : (p : ℤ_[p]) ^ 12 ∣ W.Δ := pow_dvd_Δ_of_pow_dvd_c₄_c₆ hp hc₄ hc₆
  have h5 : Step5.run (p : ℤ_[p]) W = Except.ok (Step2.translate (p : ℤ_[p]) W) :=
    Step5.run_eq_ok_of_pow_dvd_c₄_c₆ hp ((dvd_pow_self _ (by norm_num)).trans hΔ12)
      ((pow_dvd_pow _ (by norm_num)).trans hc₄) ((pow_dvd_pow _ (by norm_num)).trans hc₆)
  have hval6 := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ h5)
  have hdouble := (hasDoubleRoot_iff_pow_dvd_Δ hp (by simpa using hval6.a₁)
    (by simpa using hval6.a₂) hval6.a₃ hval6.a₄ hval6.a₆).mpr
      (by rw [Step6.translate_Δ, Step5.run_Δ h5]; exact (pow_dvd_pow _ (by norm_num)).trans hΔ12)
  have h6 : Step6.run (p : ℤ_[p]) W
      = Except.ok (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)) := by
    rw [Step6.run.eq_def, h5]
    exact ite_eq_left hdouble
  have htriple := (hasTripleRoot_iff_cb_dvd_c₄ hp (by simpa using hval6.a₁)
    (by simpa using hval6.a₂) hval6.a₃ hval6.a₄).mpr
      (by rw [Step6.translate_c₄, Step5.run_c₄ h5]; exact (pow_dvd_pow _ (by norm_num)).trans hc₄)
  have h7 : Step7.run hϖ hΔ
      = Except.ok (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W) :=
          Except.ok.inj (heq.symm.trans h6)
        exact dite_eq_left htriple
  have hval7 := Step7.run_hasValuation hϖ hΔ h7
  have hval8 := Step8.hasValuation_translate hϖ hval7 hdouble htriple
  have hq := (quadratic_hasDoubleRoot_iff hp hval8.a₃ hval8.a₆ hval8.b₂ hval8.b₄).mpr
    (by
      rw [Step8.translate_c₆, Step7.run_c₆ hϖ hΔ h7]
      exact (pow_dvd_pow _ (by norm_num)).trans hc₆)
  have h8 : Step8.run hϖ hΔ = Except.ok (Step8.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W))) := by
    rw [Step8.run.eq_def, h7]
    exact ite_eq_left hq
  have hval9 := Step9.hasValuation_translate hϖ hval8 hq
  have h9cond := (pow_four_dvd_a₄_iff hp (by simpa using hval9.a₁) hval9.a₃ hval9.b₂).mpr
    (by rwa [Step9.translate, Step7.translateY_c₄, Step8.run_c₄ hϖ hΔ h8])
  have h9 : Step9.run hϖ hΔ = Except.ok (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)))) := by
    rw [Step9.run.eq_def, h8]
    exact ite_eq_left h9cond
  have hval9' := Step9.run_hasValuation hϖ hΔ h9
  have h10cond := (pow_six_dvd_a₆_iff hp hval9'.a₃ hval9'.b₂ hval9'.b₄).mpr
    (by rwa [Step9.run_c₆ hϖ hΔ h9])
  have h10 : Step10.run hϖ hΔ = Except.ok (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)))) := by
    rw [Step10.run.eq_def, h9]
    exact ite_eq_left h10cond
  exact ⟨Step11.translate (p : ℤ_[p]) (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p])
    (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)))),
    by rw [Step11.run.eq_def, h10]; rfl⟩

end WeierstrassCurve.TateAlgorithm

/-! ### What Step 11 hands back, and the reduction of `StratScaleInvariant` -/

namespace WeierstrassCurve

variable {R : Type u} [CommRing R]

/-- The dilation multiplies `c₄` by `ϖ⁴`: `b₂ ↦ ϖ²b₂` and `b₄ ↦ ϖ⁴b₄`. -/
theorem scaleUp_c₄ (ϖ : R) (W : WeierstrassCurve R) : (scaleUp ϖ W).c₄ = ϖ ^ 4 * W.c₄ := by
  simp only [c₄, b₂, b₄, scaleUp]; ring

/-- The dilation multiplies `c₆` by `ϖ⁶`: `b₂ ↦ ϖ²b₂`, `b₄ ↦ ϖ⁴b₄`, `b₆ ↦ ϖ⁶b₆`. -/
theorem scaleUp_c₆ (ϖ : R) (W : WeierstrassCurve R) : (scaleUp ϖ W).c₆ = ϖ ^ 6 * W.c₆ := by
  simp only [c₆, b₂, b₄, b₆, scaleUp]; ring

/-- The dilation multiplies `Δ` by `ϖ¹²`, for an arbitrary curve. -/
theorem scaleUp_Δ (ϖ : R) (W : WeierstrassCurve R) : (scaleUp ϖ W).Δ = ϖ ^ 12 * W.Δ := by
  simp only [Δ, b₂, b₄, b₆, b₈, scaleUp]; ring

namespace TateAlgorithm.Step11

/-- **The curve Step 11 hands back on a dilate is an integral translate of the base curve.** If
Tate's algorithm reaches Step 11 on `σ(W)` and returns the curve `c`, then `IsIntTranslate W c`. -/
theorem isIntTranslate_of_run_ok_scaleUp {ϖ : R}
    [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] [IsNoetherianRing R] [IsDomain R]
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (hϖ : ϖ ≠ 0) {W : WeierstrassCurve R}
    (hΔ : (scaleUp ϖ W).Δ ≠ 0) {c : WeierstrassCurve R}
    (h : Step11.run hϖ hΔ = .ok c) : IsIntTranslate W c := by
  rcases Except.bind_eq_ok_iff.mp h with ⟨V, hV, hc⟩
  obtain rfl : c = translate ϖ V := (Except.ok.inj hc).symm
  obtain ⟨r, s, t, rfl⟩ := Step10.isIntTranslate_of_run_ok hϖ hΔ hV
  have hval := Step10.run_hasValuation hϖ hΔ hV
  obtain ⟨hs, hr, ht⟩ := dvd_of_smul_scaleUp h2 h3 W (by simpa using hval.a₁) hval.a₂ hval.a₃
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨ρ, rfl⟩ := hr
  obtain ⟨τ, rfl⟩ := ht
  exact ⟨ρ, σ, τ, translate_smul_scaleUp hϖ W ρ σ τ⟩

end TateAlgorithm.Step11

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy

variable (p) in
/-- Tate's algorithm returns the same Kodaira symbol and the same local Tamagawa number on any two
curves over `ℤ_p` with nonzero discriminant that differ by a change of variables with `u = 1`. -/
def RunIntTranslateInvariant : Prop :=
  ∀ (W W' : WeierstrassCurve ℤ_[p]) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0), IsIntTranslate W W' →
    (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ').kodairaSymbol ∧
      (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ').tamagawaNumber

/-- **`StratScaleInvariant p` follows from `RunIntTranslateInvariant p`, for every `p ≥ 5`.** -/
theorem stratScaleInvariant_of_runIntTranslateInvariant (hp : 5 ≤ p)
    (h : RunIntTranslateInvariant p) : StratScaleInvariant p := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  have hrun : ∀ (W₁ W₂ : WeierstrassCurve ℤ_[p]), W₁ = W₂ → ∀ (h₁ : W₁.Δ ≠ 0) (h₂ : W₂.Δ ≠ 0),
      TateAlgorithm.run hϖ h₁ = TateAlgorithm.run hϖ h₂ := by
    intro W₁ W₂ e h₁ h₂; subst e; rfl
  intro x hx hσx
  have heq : ofShortNF (PadicInt.scaleProdByPPow 4 6 x).1 (PadicInt.scaleProdByPPow 4 6 x).2
      = scaleUp (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    rw [scaleUp_ofShortNF]; rfl
  have hΔσ : (scaleUp (p : ℤ_[p]) (ofShortNF x.1 x.2)).Δ ≠ 0 := by rw [← heq]; exact hσx
  obtain ⟨V, hV⟩ := TateAlgorithm.Step11.run_eq_ok_of_pow_dvd_c₄_c₆ hp hΔσ
    (by rw [scaleUp_c₄]; exact dvd_mul_right _ _) (by rw [scaleUp_c₆]; exact dvd_mul_right _ _)
  have hVΔ : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔσ hV
  have hIT : IsIntTranslate (ofShortNF x.1 x.2) V :=
    TateAlgorithm.Step11.isIntTranslate_of_run_ok_scaleUp h2 h3 hϖ hΔσ hV
  obtain ⟨hk, ht⟩ := h (ofShortNF x.1 x.2) V hx hVΔ hIT
  simp only [strat, Prod.mk.injEq]
  rw [hrun _ _ heq hσx hΔσ, TateAlgorithm.run_eq_of_step11_ok hϖ hΔσ hV hVΔ]
  exact ⟨hk.symm, ht.symm⟩

end WeierstrassCurve
