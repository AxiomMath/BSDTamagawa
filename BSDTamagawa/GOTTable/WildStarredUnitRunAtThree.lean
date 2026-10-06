/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildStarredAtThree

/-!
# Tate's algorithm on the starred strata at `p = 3` over a unit `a₆/3³`

For short models over `ℤ_3` with `a₄ = 27α` and `a₆ = 27β`, `3 ∤ β`, the `b`-invariants of the
curve Step 8 hands on, and Tate's algorithm on the three branches `IV*`, `III*` and `II*`.

## Main results

* `WeierstrassCurve.StarredUnitThree.step8_bInvariants_unit_three`: the three `b`-invariants of
  the Step-8 translate at `a₆ = 3³β`.
* `WeierstrassCurve.StarredUnitThree.run_eq_IVstar_unit_three`,
  `WeierstrassCurve.StarredUnitThree.run_eq_IIIstar_unit_three`,
  `WeierstrassCurve.StarredUnitThree.run_eq_IIstar_unit_three`: Tate's algorithm on the three
  branches.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

namespace StarredUnitThree

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadSumThree TateAlgorithm
open StarredThree

variable {p : ℕ} [Fact p.Prime]

/-- If `x = p ^ k * a`, then dividing `x` by `p ^ k` gives `a`. -/
private theorem div_pow_eq_of_eq_pow_mul {k : ℕ} {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) ^ k * a) :
    div x ((p : ℤ_[p]) ^ k) = a := by
  subst h
  exact mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-- Two elements congruent modulo `p` have the same residue. -/
private theorem mod_eq_mod_of_dvd_sub {x y : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x - y) :
    mod (p : ℤ_[p]) x = mod (p : ℤ_[p]) y := by
  rwa [← sub_eq_zero, ← map_sub, mod_eq_zero]

/-! ### The `b`-invariants of the Step-8 translate at `a₆ = 3³β`

Steps 1 through 7 run as in `StarredThree.step7_run_eq_ok`, which asks only for `3³ ∣ a₄` and
`3³ ∣ a₆`. The Step-6 cubic's constant term is `β + ρ³ ≡ β + ρ`, so the total shift is
`3(-β + 3j)` with `-β` a unit. -/

/-- **The Step-8 translate of a short model with `v₃(a₆) = 3`, with its shift and all three
`b`-invariants.** On `y² = x³ + 3³αx + 3³β` over `ℤ_3` the curve `V` that Step 8 hands to Step 9
satisfies the valuation conditions of Step 9 and has

    `b₂(V) = 3²·4μ`,    `b₄(V) = 3³·2(α + μ²)`,    `b₆(V) = 3³·4(β + 3μα + μ³)`

with `μ = -β + 3j` for some `j`. -/
theorem step8_bInvariants_unit_three (hp3 : p = 3) {a₄ a₆ α β : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 3 * β) :
    ∃ (W' : WeierstrassCurve ℤ_[p]) (j : ℤ_[p]),
      Step7.run (PadicInt.uniformizer_ne_zero (p := p)) hΔ0 = Except.ok W' ∧
      HasValuation (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')
        ⟨1, 2, 2, 3, 4, 2, 3, 4, 6, 3, 4, 8⟩ ∧
      (Step8.translate (p : ℤ_[p]) W').b₂
        = (p : ℤ_[p]) ^ 2 * (4 * (-β + (p : ℤ_[p]) * j)) ∧
      (Step8.translate (p : ℤ_[p]) W').b₄
        = (p : ℤ_[p]) ^ 3 * (2 * (α + (-β + (p : ℤ_[p]) * j) ^ 2)) ∧
      (Step8.translate (p : ℤ_[p]) W').b₆
        = (p : ℤ_[p]) ^ 3 * (4 * (β + (p : ℤ_[p]) * (-β + (p : ℤ_[p]) * j) * α
          + (-β + (p : ℤ_[p]) * j) ^ 3)) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h₄3 : (p : ℤ_[p]) ^ 3 ∣ a₄ := ⟨α, h₄⟩
  have h₆3 : (p : ℤ_[p]) ^ 3 ∣ a₆ := ⟨β, h₆⟩
  have hΔd := dvd_Δ_of_cb_dvd hp3 h₄3 h₆3
  have h7 := step7_run_eq_ok hp3 hΔ0 h₄3 h₆3
  obtain ⟨r, t, hT2⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔd⟩
  have hval2 := Step2.hasValuation_translate hΔd
  rw [hT2] at hval2
  obtain ⟨hr, -⟩ := dvd_params_of_dvd_three hp3
    ((dvd_pow_self _ three_ne_zero).trans h₄3) ((dvd_pow_self _ three_ne_zero).trans h₆3)
    (by simpa using hval2.a₃) (by simpa using hval2.a₆)
  obtain ⟨ρ, hρ⟩ := hr
  set V₁ := Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆) with hV₁
  set s := Step6.s (p : ℤ_[p]) V₁ with hs
  set t₆ := Step6.t (p : ℤ_[p]) V₁ with ht₆
  have hW6 : Step6.translate (p : ℤ_[p]) V₁
      = (VariableChange.mk 1 r s ((p : ℤ_[p]) * t₆ + t)) • ofShortNF a₄ a₆ := by
    rw [show Step6.translate (p : ℤ_[p]) V₁
        = (VariableChange.mk 1 0 s ((p : ℤ_[p]) * t₆)) • V₁ from rfl, hT2]
    exact smul_smul_eq _ (by ring) (by ring) (by ring)
  have hval6 := Step6.hasValuation_translate hϖ
    (Step5.run_hasValuation hϖ (Step5.run_eq_ok_of_cb_dvd_three hp3 h₄3 h₆3))
  have h2u : IsUnit (2 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 2) (by rw [hp3]; norm_num)
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ_[p], (p : ℤ_[p]) * t₆ + t = (p : ℤ_[p]) ^ 2 * σ := by
    obtain ⟨A₃, hA₃⟩ := hval6.a₃
    rw [hW6, smul_ofShortNF_a₃] at hA₃
    exact h2u.dvd_mul_left.mp ⟨A₃, hA₃⟩
  set r₈ := Step8.r (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁) with hr₈
  have ha₆W6 : (Step6.translate (p : ℤ_[p]) V₁).a₆
      = (p : ℤ_[p]) ^ 3 * (β + (p : ℤ_[p]) * ρ * α + ρ ^ 3 - (p : ℤ_[p]) * σ ^ 2) := by
    rw [hW6, smul_ofShortNF_a₆, h₄, h₆, hρ, hσ]; ring
  have hdiv₆ : div (Step6.translate (p : ℤ_[p]) V₁).a₆ ((p : ℤ_[p]) ^ (2 * 1 + 1))
      = β + (p : ℤ_[p]) * ρ * α + ρ ^ 3 - (p : ℤ_[p]) * σ ^ 2 :=
    div_pow_eq_of_eq_pow_mul (by simpa using ha₆W6)
  have hcubicd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁) 1 1).d
      = mod (p : ℤ_[p]) (β + ρ ^ 3) := by
    rw [cubic]
    dsimp only
    rw [hdiv₆]
    exact mod_eq_mod_of_dvd_sub ⟨ρ * α - σ ^ 2, by ring⟩
  obtain ⟨j, hj⟩ : (p : ℤ_[p]) ∣ ρ - r₈ + β := by
    rw [← mod_eq_zero, map_add, map_sub, hr₈,
      mod_r_three hp3 (Step6.translate (p : ℤ_[p]) V₁), hcubicd, map_add, map_pow,
      residue_cube_self hp3]
    ring
  have hshift : r - (p : ℤ_[p]) * r₈ = (p : ℤ_[p]) * (-β + (p : ℤ_[p]) * j) := by
    rw [hρ]; linear_combination (p : ℤ_[p]) * hj
  have hV8 : Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁)
      = (VariableChange.mk 1 ((p : ℤ_[p]) * (-β + (p : ℤ_[p]) * j)) s
        (-(p : ℤ_[p]) * r₈ * s + ((p : ℤ_[p]) * t₆ + t))) • ofShortNF a₄ a₆ := by
    rw [show Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁)
        = (VariableChange.mk 1 (-(p : ℤ_[p]) * r₈) 0 0)
          • Step6.translate (p : ℤ_[p]) V₁ from rfl, hW6]
    refine smul_smul_eq _ ?_ (by ring) (by ring)
    rw [← hshift]; ring
  obtain ⟨hb₂, hb₄, hb₆⟩ := smul_ofShortNF_b (p := p) a₄ a₆
    ((p : ℤ_[p]) * (-β + (p : ℤ_[p]) * j)) s
    (-(p : ℤ_[p]) * r₈ * s + ((p : ℤ_[p]) * t₆ + t))
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, V₁.a₂ = (p : ℤ_[p]) ^ 2 * A₂ :=
    (step2_translate_data_three hp3 h₄3 h₆3 hΔd).2.1
  obtain ⟨A₄, hA₄⟩ : ∃ A₄, V₁.a₄ = (p : ℤ_[p]) ^ 3 * A₄ :=
    (step2_translate_data_three hp3 h₄3 h₆3 hΔd).2.2.1
  obtain ⟨σ₆, hσ₆⟩ := dvd_step6_s hp3 (step2_translate_data_three hp3 h₄3 h₆3 hΔd).1
  obtain ⟨A₃', hA₃'⟩ := hval6.a₃
  have hW6a₂ : (Step6.translate (p : ℤ_[p]) V₁).a₂ = (p : ℤ_[p]) ^ 2 * (A₂ - σ₆ ^ 2) := by
    rw [step6_translate_a₂ _ (step2_translate_data_three hp3 h₄3 h₆3 hΔd).1, hA₂, hσ₆]; ring
  have hW6a₄ : (Step6.translate (p : ℤ_[p]) V₁).a₄ = (p : ℤ_[p]) ^ 3 * (A₄ - σ₆ * A₃') := by
    rw [step6_translate_a₄ _ (step2_translate_data_three hp3 h₄3 h₆3 hΔd).1, hA₄, hσ₆, hA₃']
    ring
  refine ⟨Step6.translate (p : ℤ_[p]) V₁, j, h7,
    Step8.hasValuation_translate hϖ hval6 (hasDoubleRoot_of_three hp3 hW6a₂ hW6a₄)
      (hasTripleRoot_of_three hp3 hW6a₂), ?_, ?_, ?_⟩
  · rw [hV8, hb₂]; subst hp3; push_cast; ring
  · rw [hV8, hb₄, h₄]; subst hp3; push_cast; ring
  · rw [hV8, hb₆, h₄, h₆]; subst hp3; push_cast; ring

/-! ### The `b₆` factorisation

`b₆(V)/3³ = 4(β + 3μα + μ³)` with `μ = -β + 3j`, and the bracket is divisible by `3` on the whole
region, because `β³ ≡ β` modulo `3` and `β² + 3α - 1 = 3w`. Substituting `μ` and using both facts,

    `β + 3μα + μ³ = 3(-βw + 3(jα + jβ² - 3βj² + 3j³))`,

so `b₆(V) = 3⁴·4(-βw + 3(…))` and Step 8's test `3 ∣ b₆/3⁴` is `3 ∣ βw`, i.e. `3 ∣ w`. -/

/-- **The `b₆` bracket at `v₃(a₆) = 3`, factorised.** If `3w = β² + 3α - 1`, then
`β + 3μα + μ³ = 3(-βw + 3(jα + jβ² - 3βj² + 3j³))` with `μ = -β + 3j`. -/
theorem bracket_eq_three_mul {α β w j : ℤ_[p]} (hp3 : p = 3)
    (hw : (p : ℤ_[p]) * w = β ^ 2 + (p : ℤ_[p]) * α - 1) :
    β + (p : ℤ_[p]) * (-β + (p : ℤ_[p]) * j) * α + (-β + (p : ℤ_[p]) * j) ^ 3
      = (p : ℤ_[p]) * (-(β * w) + (p : ℤ_[p]) * (j * α + j * β ^ 2 - (p : ℤ_[p]) * β * j ^ 2
        + (p : ℤ_[p]) * j ^ 3)) := by
  subst hp3
  push_cast at hw ⊢
  linear_combination β * hw

/-! ### The three forward runs

Step 8's test is `3 ∣ b₆/3⁴`, which the factorisation turns into `3 ∣ w`; Step 9's is `3 ∣ b₄/3³`,
i.e. `3 ∣ α + β²` since `b₄/3³ = 2(α + β² + 3(…))`; and Step 10's is `9 ∣ b₆/3⁴`, which on the
`II*` branch is `3 ∣ w/3`. -/

open scoped Classical in
/-- **The forward run at `IV*` at `p = 3` over a unit `β`.** A short model over `ℤ_3` with
`a₄ = 27α` and `a₆ = 27β`, `3 ∤ β`, on which `3 ∤ w`, has reduction datum `(IV*, 3)` or `(IV*, 1)`
according as the residue of `-4βw` is a square in `𝔽₃`. -/
theorem run_eq_IVstar_unit_three (hp3 : p = 3) {a₄ a₆ α β w : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 3 * β) (hβ : ¬ (p : ℤ_[p]) ∣ β)
    (hw : (p : ℤ_[p]) * w = β ^ 2 + (p : ℤ_[p]) * α - 1) (hwu : ¬ (p : ℤ_[p]) ∣ w) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.IV! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber
        = if IsSquare (PadicInt.toZMod (-(4 * (β * w)))) then 3 else 1 := by
  obtain ⟨W', j, h7, hval8, -, -, hb₆⟩ := step8_bInvariants_unit_three hp3 hΔ0 h₄ h₆
  obtain ⟨A₃, hA₃⟩ := hval8.a₃
  obtain ⟨A₆, hA₆⟩ := hval8.a₆
  set J : ℤ_[p] := j * α + j * β ^ 2 - (p : ℤ_[p]) * β * j ^ 2 + (p : ℤ_[p]) * j ^ 3 with hJ
  have hb₆' : (Step8.translate (p : ℤ_[p]) W').b₆
      = (p : ℤ_[p]) ^ 4 * (4 * (-(β * w) + (p : ℤ_[p]) * J)) := by
    rw [hb₆, bracket_eq_three_mul hp3 hw, hJ]; ring
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  have hnd : ¬ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff_dvd hA₃ hA₆ hb₆']
    refine fun h => hwu ?_
    obtain ⟨c, hc⟩ := h4u.dvd_mul_left.mp h
    exact (PadicInt.prime_p.dvd_or_dvd (show (p : ℤ_[p]) ∣ β * w from
      ⟨J - c, by linear_combination -hc⟩)).resolve_left hβ
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step8 hΔ0 (step8_run_eq_error_of_not_hasDoubleRoot hΔ0 h7 hnd))]
  refine ⟨rfl, ?_⟩
  rw [show (TateAlgorithm.Output.mk (Step8.translate (p : ℤ_[p]) W') KodairaSymbol.IV!
      (if (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).toPoly.Splits then 3
        else 1)).tamagawaNumber
      = if (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).toPoly.Splits then 3
        else 1 from rfl,
    splits_quadratic_two_iff hp3 hA₃ hA₆ hb₆']
  congr 1
  refine propext (Iff.of_eq (congrArg _ ?_))
  rw [show (4 : ℤ_[p]) * (-(β * w) + (p : ℤ_[p]) * J)
      = -(4 * (β * w)) + (p : ℤ_[p]) * (4 * J) from by ring, map_add,
    show PadicInt.toZMod ((p : ℤ_[p]) * (4 * J)) = 0 from by
      rw [← PadicInt.dvd_iff_toZMod_eq_zero]; exact Dvd.intro _ rfl,
    add_zero]

open scoped Classical in
/-- **The forward run at `III*` at `p = 3` over a unit `β`.** A short model over `ℤ_3` with
`a₄ = 27α`, `a₆ = 27β`, `3 ∤ β`, on which `3 ∣ w` but `3 ∤ α + β²`, has reduction datum
`(III*, 2)`: Step 8 hands on because `3 ∣ b₆/3⁴ = 4(-βw + 3J)`, and Step 9 answers because
`3 ∤ b₄/3³ = 2(α + β² + 3(…))`. -/
theorem run_eq_IIIstar_unit_three (hp3 : p = 3) {a₄ a₆ α β w : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 3 * β)
    (hw : (p : ℤ_[p]) * w = β ^ 2 + (p : ℤ_[p]) * α - 1) (hwd : (p : ℤ_[p]) ∣ w)
    (hαβ : ¬ (p : ℤ_[p]) ∣ α + β ^ 2) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.III! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 2 := by
  obtain ⟨W', j, h7, hval8, -, hb₄, hb₆⟩ := step8_bInvariants_unit_three hp3 hΔ0 h₄ h₆
  obtain ⟨A₃, hA₃⟩ := hval8.a₃
  obtain ⟨A₆, hA₆⟩ := hval8.a₆
  obtain ⟨g, hg⟩ := hwd
  have h2u : IsUnit (2 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 2) (by rw [hp3]; norm_num)
  have hb₆' : (Step8.translate (p : ℤ_[p]) W').b₆
      = (p : ℤ_[p]) ^ 4 * (4 * (-(β * w) + (p : ℤ_[p]) * (j * α + j * β ^ 2
        - (p : ℤ_[p]) * β * j ^ 2 + (p : ℤ_[p]) * j ^ 3))) := by
    rw [hb₆, bracket_eq_three_mul hp3 hw]; ring
  have hd : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff_dvd hA₃ hA₆ hb₆']
    exact ⟨4 * (-(β * g) + (j * α + j * β ^ 2 - (p : ℤ_[p]) * β * j ^ 2
      + (p : ℤ_[p]) * j ^ 3)), by rw [hg]; ring⟩
  have h8 := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7 hd
  have hval9 := Step9.hasValuation_translate PadicInt.uniformizer_ne_zero hval8 hd
  have hb₄9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).b₄
      = (p : ℤ_[p]) ^ 3 * (2 * (α + β ^ 2)
        + (p : ℤ_[p]) * (2 * (-2 * β * j + (p : ℤ_[p]) * j ^ 2))) := by
    rw [Step9.translate, Step7.translateY_b₄, hb₄]; ring
  have ha₄ : ¬ (p : ℤ_[p]) ^ 4
      ∣ (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).a₄ := by
    rw [pow_four_dvd_a₄_iff_dvd_B₄ hp3 hb₄9 (by simpa using hval9.a₁)
      (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 3)) hval9.a₃)]
    refine fun h => hαβ ?_
    obtain ⟨d, hd'⟩ := h2u.dvd_mul_left.mp ((dvd_add_right
      (Dvd.intro (2 * (-2 * β * j + (p : ℤ_[p]) * j ^ 2)) rfl)).mp
      (by rwa [add_comm] at h))
    exact ⟨d, hd'⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step9 hΔ0 (step9_run_eq_error_of_not_dvd hΔ0 h8 ha₄))]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **The forward run at `II*` at `p = 3` over a unit `β`.** A short model over `ℤ_3` with
`a₄ = 27α`, `a₆ = 27β`, `3 ∤ β`, on which `w = 3g` and `α + β² = 3k` but `3 ∤ g`, has reduction
datum `(II*, 1)`: Step 8 hands on, Step 9 hands on because `3 ∣ α + β²`, and Step 10 answers
because `b₆/3⁴ = 3·4(-βg + 3(…))` is not divisible by `9` once `3 ∤ βg`. -/
theorem run_eq_IIstar_unit_three (hp3 : p = 3) {a₄ a₆ α β g k : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 3 * β) (hβ : ¬ (p : ℤ_[p]) ∣ β)
    (hw : (p : ℤ_[p]) * ((p : ℤ_[p]) * g) = β ^ 2 + (p : ℤ_[p]) * α - 1)
    (hk : α + β ^ 2 = (p : ℤ_[p]) * k) (hgu : ¬ (p : ℤ_[p]) ∣ g) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.II! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1 := by
  obtain ⟨W', j, h7, hval8, -, hb₄, hb₆⟩ := step8_bInvariants_unit_three hp3 hΔ0 h₄ h₆
  obtain ⟨A₃, hA₃⟩ := hval8.a₃
  obtain ⟨A₆, hA₆⟩ := hval8.a₆
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  set K : ℤ_[p] := j * k - β * j ^ 2 + j ^ 3 with hK
  have hb₆' : (Step8.translate (p : ℤ_[p]) W').b₆
      = (p : ℤ_[p]) ^ 4 * ((p : ℤ_[p]) * (4 * (-(β * g) + (p : ℤ_[p]) * K))) := by
    rw [hb₆, bracket_eq_three_mul hp3 hw, hK]
    subst hp3
    push_cast at hk ⊢
    linear_combination (972 : ℤ_[3]) * j * hk
  have hd : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff_dvd hA₃ hA₆ hb₆']
    exact ⟨4 * (-(β * g) + (p : ℤ_[p]) * K), by ring⟩
  have h8 := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7 hd
  have hval9 := Step9.hasValuation_translate PadicInt.uniformizer_ne_zero hval8 hd
  have hb₄9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).b₄
      = (p : ℤ_[p]) ^ 3 * ((p : ℤ_[p]) * (2 * k)
        + (p : ℤ_[p]) * (2 * (-2 * β * j + (p : ℤ_[p]) * j ^ 2))) := by
    rw [Step9.translate, Step7.translateY_b₄, hb₄]
    linear_combination (2 : ℤ_[p]) * (p : ℤ_[p]) ^ 3 * hk
  have ha₄ : (p : ℤ_[p]) ^ 4
      ∣ (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).a₄ := by
    rw [pow_four_dvd_a₄_iff_dvd_B₄ hp3 hb₄9 (by simpa using hval9.a₁)
      (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 3)) hval9.a₃)]
    exact ⟨2 * k + 2 * (-2 * β * j + (p : ℤ_[p]) * j ^ 2), by ring⟩
  have h9 := step9_run_eq_ok_of_dvd hΔ0 h8 ha₄
  have hb₆9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).b₆
      = (p : ℤ_[p]) ^ 4 * ((p : ℤ_[p]) * (4 * (-(β * g) + (p : ℤ_[p]) * K))) := by
    rw [Step9.translate, Step7.translateY_b₆, hb₆']
  have ha₆ : ¬ (p : ℤ_[p]) ^ 6
      ∣ (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).a₆ := by
    rw [pow_six_dvd_a₆_iff_sq_dvd_B₆ hp3 hb₆9
      (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 3)) hval9.a₃)]
    intro ⟨d, hd'⟩
    refine hgu ((PadicInt.prime_p.dvd_or_dvd (show (p : ℤ_[p]) ∣ β * g from ?_)).resolve_left hβ)
    obtain ⟨e, he⟩ := h4u.dvd_mul_left.mp
      (show (p : ℤ_[p]) ∣ 4 * (-(β * g) + (p : ℤ_[p]) * K) from ⟨d, by
        refine mul_left_cancel₀ (PadicInt.uniformizer_ne_zero (p := p)) ?_
        linear_combination hd'⟩)
    exact ⟨K - e, by linear_combination -he⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step10 hΔ0 (step10_run_eq_error_of_not_dvd hΔ0 h9 ha₆))]
  exact ⟨rfl, rfl⟩

/-! ### Nonsingularity

Here `4a₄³ + 27a₆² = 3⁹(4α³ + β²)`, and `4α³ + β²` vanishes at `(α, β) = (-1, 2)`: the point
`a₄ = -27`, `a₆ = 54` has `Δ = 0` with `β = 2` a unit. Each of the four loci avoids the singular
points by its own branch condition. If `4α³ + β² = 0` then modulo `3` Fermat gives
`α ≡ α³ ≡ -β² ≡ -1`, so `α = -1 + 3e`; substituting `β² = -4α³` into `3w = β² + 3α - 1` gives
`3w = -4α³ + 3α - 1 = 27(-e + 4e² - 4e³)`, whence `9 ∣ w`. This excludes all four loci: `IV*`
asks `3 ∤ w`, `II*` asks `3 ∤ w/3`, and `III*` asks `3 ∤ α + β²`, which is `3 ∤ α + 1`. -/

/-- **On a singular point of this region, `9 ∣ w` and `3 ∣ α + 1`.** -/
theorem pow_two_dvd_w_of_Δ_eq_zero (hp3 : p = 3) {a₄ a₆ α β w : ℤ_[p]}
    (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α) (h₆ : a₆ = (p : ℤ_[p]) ^ 3 * β)
    (hw : (p : ℤ_[p]) * w = β ^ 2 + (p : ℤ_[p]) * α - 1)
    (hzero : (ofShortNF a₄ a₆).Δ = 0) : (p : ℤ_[p]) ^ 2 ∣ w ∧ (p : ℤ_[p]) ∣ α + 1 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h16 : IsUnit (-16 : ℤ_[p]) := PadicInt.isUnit_neg_sixteen (hp3 ▸ (by decide : Odd 3))
  rw [ofShortNF_Δ, h₄, h₆] at hzero
  have hbr : (4 : ℤ_[p]) * ((p : ℤ_[p]) ^ 3 * α) ^ 3
      + 27 * ((p : ℤ_[p]) ^ 3 * β) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left h16.ne_zero
  have h9 : (p : ℤ_[p]) ^ 9 * (4 * α ^ 3 + β ^ 2) = 0 := by
    subst hp3; push_cast at hbr ⊢; linear_combination hbr
  have hsum : (4 : ℤ_[p]) * α ^ 3 + β ^ 2 = 0 :=
    (mul_eq_zero.mp h9).resolve_left (pow_ne_zero 9 hϖ)
  obtain ⟨f, hf⟩ : ∃ f, α ^ 3 - α = (p : ℤ_[p]) * f := by
    obtain ⟨f, hf⟩ : (p : ℤ_[p]) ∣ α ^ 3 - α := by
      rw [← mod_eq_zero, map_sub, map_pow, residue_cube_self hp3, sub_self]
    exact ⟨f, hf⟩
  obtain ⟨e, he⟩ : ∃ e, α = -1 + (p : ℤ_[p]) * e := by
    refine ⟨-w - 4 * f, ?_⟩
    subst hp3
    push_cast at hw hf hsum ⊢
    linear_combination hw + hsum - 4 * hf
  refine ⟨⟨-e + 4 * e ^ 2 - 4 * e ^ 3, ?_⟩, ⟨e, by rw [he]; ring⟩⟩
  refine mul_left_cancel₀ hϖ ?_
  subst hp3
  rw [he] at hw hsum
  push_cast at hw hsum ⊢
  linear_combination hw + hsum

end StarredUnitThree

end WeierstrassCurve

end
