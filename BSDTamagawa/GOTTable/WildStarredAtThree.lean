/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.StarredThreeAtThree
public import BSDTamagawa.NumberTheory.HeadDensityOne
public import BSDTamagawa.NumberTheory.SplitStoreyDescentTwo
public import BSDTamagawa.NumberTheory.HeadDensityTwo

/-!
# The starred strata `IV*`, `III*` and `II*` at `p = 3`

On a short model over `ℤ_3` with `3³ ∣ a₄`, `3³ ∣ a₆` and `Δ ≠ 0`, Steps 1–7 of Tate's algorithm
pass, and the three starred strata are distinguished by which of Steps 8, 9 and 10 first answers.
This file decides that on four residue loci of the coefficient plane:

    (IV*,  3)   `27 ∣ a₄`, `a₆ ≡ 81  (mod 243)`         mass `1/6561`    -> row `t = 3`
    (IV*,  1)   `27 ∣ a₄`, `a₆ ≡ 162 (mod 243)`         mass `1/6561`    -> row `t = 1`
    (III*, 2)   `a₄ ≡ 27, 54 (mod 81)`, `243 ∣ a₆`      mass `2/19683`   -> row `t = 2`
    (II*,  1)   `81 ∣ a₄`, `a₆ ≡ 243, 486 (mod 729)`    mass `2/59049`   -> row `t = 1`

The variable changes of Steps 6 and 9 have `r = 0`, and the `b`-invariants depend on a variable
change only through `r`. So on a short model `y² = x³ + 3³αx + 3⁴b`, with `3²m` the total `x`-shift
of Steps 2 and 8, the curve `V` handed on by Step 8 has

    `b₂(V) = 3³·4m`,     `b₄(V) = 3³·2(α + 3²m²)`,     `b₆(V) = 3⁴·4(b + 3mα + 3²m³)`,

and the remaining branch conditions are conditions on these:

* Step 8 passes iff `3 ∣ b₆(V)/3⁴`, since Step 8's quadratic is `Y² + (a₃/3²)Y - a₆/3⁴` and its
  discriminant `(a₃/3²)² + 4(a₆/3⁴)` is exactly `b₆(V)/3⁴`;
* Step 9 passes iff `3 ∣ b₄(V)/3³`, since `2a₄ = b₄ - a₁a₃` and `3⁴ ∣ a₁a₃` at that stage;
* Step 10 passes iff `3² ∣ b₆(V)/3⁴`, since `4a₆ = b₆ - a₃²` and `3³ ∣ a₃` there.

The shift of Step 8 is the cube root of the constant term of the Step-6 cubic, and cubing is the
identity on `𝔽₃`. On a short model with `3⁴ ∣ a₆` this makes the shifts of Steps 2 and 8 cancel
modulo `3`, so the total shift is divisible by `9`. On the rest of each stratum, where
`v₃(a₆) = 3`, the shift is a unit multiple of `3`; this is why each locus above is one third of its
stratum.

## Main definitions

* `WeierstrassCurve.ivStarThree3Locus`, `WeierstrassCurve.ivStarOne3Locus`,
  `WeierstrassCurve.iiiStar3Locus`, `WeierstrassCurve.iiStar3Locus`: the four loci.

## Main results

* `WeierstrassCurve.StarredThree.step8_bInvariants_three`: the three `b`-invariants of the Step-8
  translate in terms of `α`, `b` and the shift.
* `WeierstrassCurve.StarredThree.hasDoubleRoot_quadratic_two_iff_dvd` and
  `WeierstrassCurve.StarredThree.splits_quadratic_two_iff`: Step 8's two tests, in terms of `b₆`.
* `WeierstrassCurve.StarredThree.pow_four_dvd_a₄_iff_dvd_B₄` and
  `WeierstrassCurve.StarredThree.pow_six_dvd_a₆_iff_sq_dvd_B₆`: the tests of Steps 9 and 10, in
  terms of `b₄` and `b₆`.
* `WeierstrassCurve.StarredThree.run_eq_IVstar_three`,
  `WeierstrassCurve.StarredThree.run_eq_IIIstar_three`,
  `WeierstrassCurve.StarredThree.run_eq_IIstar_three`: the reduction data on the three families.
* `WeierstrassCurve.volume_ivStarThree3Locus`, `WeierstrassCurve.volume_ivStarOne3Locus`,
  `WeierstrassCurve.volume_iiiStar3Locus`, `WeierstrassCurve.volume_iiStar3Locus`: the masses
  `1/6561`, `1/6561`, `2/19683`, `2/59049`.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

namespace StarredThree

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadSumThree TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Exact division, residues, and cubing on `𝔽₃` -/

/-- Division by the exact power that divides is exact. -/
private theorem div_pow_eq_of_eq_mul {k : ℕ} {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) ^ k * a) :
    div x ((p : ℤ_[p]) ^ k) = a := by
  subst h
  exact mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-- Two elements congruent modulo `ϖ` have the same residue. -/
private theorem mod_eq_mod_of_dvd_sub {x y : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x - y) :
    mod (p : ℤ_[p]) x = mod (p : ℤ_[p]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-- **Cubing is the identity on the residue field of `ℤ_3`**, which is Fermat's little theorem over
`𝔽₃`. -/
theorem residue_cube_self (hp3 : p = 3) (x : ℤ_[p] ⧸ span {(p : ℤ_[p])}) : x ^ 3 = x := by
  rw [show (3 : ℕ) = p from hp3.symm]
  exact residue_pow_self x

/-! ### The `b`-invariants of the Step-8 translate, free of every lift

Step 6's variable change is `⟨1, 0, s, ϖt⟩` and Step 9's is `⟨1, 0, 0, ϖ²tY⟩`, both with `r = 0`,
and the `b`-invariants depend on a variable change only through `r`. So the three `b`-invariants
see only the total `x`-shift of Steps 2 and 8. -/

/-- **The three `b`-invariants of a `u = 1` translate of a short model see only the `x`-shift.** -/
theorem smul_ofShortNF_b (a₄ a₆ R S T : ℤ_[p]) :
    ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).b₂ = 12 * R ∧
      ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).b₄ = 2 * a₄ + 6 * R ^ 2 ∧
      ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).b₆
        = 4 * a₆ + 4 * R * a₄ + 4 * R ^ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.b₂, smul_ofShortNF_a₁, smul_ofShortNF_a₂]; ring
  · rw [WeierstrassCurve.b₄, smul_ofShortNF_a₁, smul_ofShortNF_a₃, smul_ofShortNF_a₄]; ring
  · rw [WeierstrassCurve.b₆, smul_ofShortNF_a₃, smul_ofShortNF_a₆]; ring

/-- **If `ϖ² ∣ a₃` and `ϖ⁴ ∣ a₆`, then `(a₃/ϖ²)² + 4(a₆/ϖ⁴) = b₆/ϖ⁴`.** -/
theorem quadratic_two_disc_eq {V : WeierstrassCurve ℤ_[p]} {A₃ A₆ B₆ : ℤ_[p]}
    (ha₃ : V.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 4 * A₆)
    (hb₆ : V.b₆ = (p : ℤ_[p]) ^ 4 * B₆) : A₃ ^ 2 + 4 * A₆ = B₆ := by
  refine mul_left_cancel₀ (pow_ne_zero 4 (PadicInt.uniformizer_ne_zero (p := p))) ?_
  rw [← hb₆, WeierstrassCurve.b₆, ha₃, ha₆]
  ring

/-- **Step 8's quadratic has a double root iff `ϖ ∣ b₆/ϖ⁴`.** Its `c` and `d` are the residues of
`a₃/ϖ²` and `-a₆/ϖ⁴`, and the double-root condition is `c² = 4d`. -/
theorem hasDoubleRoot_quadratic_two_iff_dvd {V : WeierstrassCurve ℤ_[p]} {A₃ A₆ B₆ : ℤ_[p]}
    (ha₃ : V.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 4 * A₆)
    (hb₆ : V.b₆ = (p : ℤ_[p]) ^ 4 * B₆) :
    (quadratic (p : ℤ_[p]) V 2).HasDoubleRoot ↔ (p : ℤ_[p]) ∣ B₆ := by
  have hdisc := quadratic_two_disc_eq ha₃ ha₆ hb₆
  have h3 : div V.a₃ ((p : ℤ_[p]) ^ 2) = A₃ := div_pow_eq_of_eq_mul ha₃
  have h6 : div V.a₆ ((p : ℤ_[p]) ^ (2 * 2)) = A₆ := div_pow_eq_of_eq_mul (by simpa using ha₆)
  rw [Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) (by simp [quadratic]), quadratic]
  norm_num only [h3, h6]
  rw [← sub_eq_zero,
    show mod (p : ℤ_[p]) A₃ ^ 2 - 4 * -mod (p : ℤ_[p]) A₆ = mod (p : ℤ_[p]) B₆ from by
      rw [← hdisc, map_add, map_mul, map_pow, map_ofNat]; ring,
    mod_eq_zero]

/-- **Step 8's split test, in terms of `b₆`.** The quadratic `Y² + cY - d` splits exactly when its
discriminant `c² + 4d = b₆/ϖ⁴` is a square in the residue field. -/
theorem splits_quadratic_two_iff {V : WeierstrassCurve ℤ_[p]} (hp3 : p = 3) {A₃ A₆ B₆ : ℤ_[p]}
    (ha₃ : V.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (ha₆ : V.a₆ = (p : ℤ_[p]) ^ 4 * A₆)
    (hb₆ : V.b₆ = (p : ℤ_[p]) ^ 4 * B₆) :
    (quadratic (p : ℤ_[p]) V 2).toPoly.Splits ↔ IsSquare (PadicInt.toZMod B₆) := by
  have hdisc := quadratic_two_disc_eq ha₃ ha₆ hb₆
  have h3 : div V.a₃ ((p : ℤ_[p]) ^ 2) = A₃ := div_pow_eq_of_eq_mul ha₃
  have h6 : div V.a₆ ((p : ℤ_[p]) ^ (2 * 2)) = A₆ := div_pow_eq_of_eq_mul (by simpa using ha₆)
  have h2 : (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ 0 := by
    rw [show (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = mod (p : ℤ_[p]) 2 from by simp only [map_ofNat],
      Ne, mod_eq_zero]
    exact fun h => PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit h (by
      simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 2) (by rw [hp3]; norm_num)))
  rw [quadratic, Cubic.of_a_eq_zero rfl]
  norm_num only [h3, h6]
  rw [splits_quadratic_iff_isSquare h2 (mod (p : ℤ_[p]) A₃) (mod (p : ℤ_[p]) A₆),
    show mod (p : ℤ_[p]) A₃ ^ 2 + 4 * mod (p : ℤ_[p]) A₆ = mod (p : ℤ_[p]) B₆ from by
      rw [← hdisc, map_add, map_mul, map_pow, map_ofNat],
    isSquare_mod_iff_isSquare_toZMod]

/-! ### The Step-8 translate on the deep branch

The composite of the changes of variables of Steps 2, 6 and 8, `⟨1, r, 0, t⟩`, `⟨1, 0, s, ϖt₆⟩` and
`⟨1, -ϖr₈, 0, 0⟩`, is a single change `⟨1, r - ϖr₈, s, …⟩`. With `r = 3ρ` the total shift is
`3(ρ - r₈)`, and `r₈` is congruent modulo `3` to the constant term of the Step-6 cubic, which on a
short model with `3⁴ ∣ a₆` is `ρ`; so the shift is divisible by `9`. -/

/-- **The Step-8 translate of a deep short model, with its shift and all three `b`-invariants.** On
`y² = x³ + 3³αx + 3⁴b` over `ℤ_3` the curve `V` that Step 8 hands to Step 9 has

    `b₂(V) = 3³·4m`,    `b₄(V) = 3³·2(α + 3²m²)`,    `b₆(V) = 3⁴·4(b + 3mα + 3²m³)`

for some `m`. -/
theorem step8_bInvariants_three (hp3 : p = 3) {a₄ a₆ α b : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 4 * b) :
    ∃ (W' : WeierstrassCurve ℤ_[p]) (m : ℤ_[p]),
      Step7.run (PadicInt.uniformizer_ne_zero (p := p)) hΔ0 = Except.ok W' ∧
      HasValuation (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')
        ⟨1, 2, 2, 3, 4, 2, 3, 4, 6, 3, 4, 8⟩ ∧
      (Step8.translate (p : ℤ_[p]) W').b₂ = (p : ℤ_[p]) ^ 3 * (4 * m) ∧
      (Step8.translate (p : ℤ_[p]) W').b₄
        = (p : ℤ_[p]) ^ 3 * (2 * (α + (p : ℤ_[p]) ^ 2 * m ^ 2)) ∧
      (Step8.translate (p : ℤ_[p]) W').b₆
        = (p : ℤ_[p]) ^ 4 * (4 * (b + (p : ℤ_[p]) * m * α + (p : ℤ_[p]) ^ 2 * m ^ 3)) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h₄3 : (p : ℤ_[p]) ^ 3 ∣ a₄ := ⟨α, h₄⟩
  have h₆3 : (p : ℤ_[p]) ^ 3 ∣ a₆ := ⟨(p : ℤ_[p]) * b, by rw [h₆]; ring⟩
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
      = (p : ℤ_[p]) ^ 3 * ((p : ℤ_[p]) * b + (p : ℤ_[p]) * ρ * α + ρ ^ 3
        - (p : ℤ_[p]) * σ ^ 2) := by
    rw [hW6, smul_ofShortNF_a₆, h₄, h₆, hρ, hσ]; ring
  have hdiv₆ : div (Step6.translate (p : ℤ_[p]) V₁).a₆ ((p : ℤ_[p]) ^ (2 * 1 + 1))
      = (p : ℤ_[p]) * b + (p : ℤ_[p]) * ρ * α + ρ ^ 3 - (p : ℤ_[p]) * σ ^ 2 :=
    div_pow_eq_of_eq_mul (by simpa using ha₆W6)
  have hcubicd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁) 1 1).d
      = mod (p : ℤ_[p]) (ρ ^ 3) := by
    rw [cubic]
    dsimp only
    rw [hdiv₆]
    exact mod_eq_mod_of_dvd_sub ⟨b + ρ * α - σ ^ 2, by ring⟩
  obtain ⟨m, hm⟩ : (p : ℤ_[p]) ∣ ρ - r₈ := by
    rw [← mod_eq_zero, map_sub, hr₈, mod_r_three hp3 (Step6.translate (p : ℤ_[p]) V₁), hcubicd,
      map_pow, residue_cube_self hp3, sub_self]
  have hV8 : Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁)
      = (VariableChange.mk 1 ((p : ℤ_[p]) ^ 2 * m) s
        (-(p : ℤ_[p]) * r₈ * s + ((p : ℤ_[p]) * t₆ + t))) • ofShortNF a₄ a₆ := by
    rw [show Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V₁)
        = (VariableChange.mk 1 (-(p : ℤ_[p]) * r₈) 0 0)
          • Step6.translate (p : ℤ_[p]) V₁ from rfl, hW6]
    refine smul_smul_eq _ ?_ (by ring) (by ring)
    rw [show ((p : ℤ_[p]) ^ 2 * m) = (p : ℤ_[p]) * ((p : ℤ_[p]) * m) from by ring, ← hm, hρ]
    ring
  obtain ⟨hb₂, hb₄, hb₆⟩ := smul_ofShortNF_b (p := p) a₄ a₆ ((p : ℤ_[p]) ^ 2 * m) s
    (-(p : ℤ_[p]) * r₈ * s + ((p : ℤ_[p]) * t₆ + t))
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, V₁.a₂ = (p : ℤ_[p]) ^ 2 * A₂ :=
    (step2_translate_data_three hp3 h₄3 h₆3 hΔd).2.1
  obtain ⟨A₄, hA₄⟩ : ∃ A₄, V₁.a₄ = (p : ℤ_[p]) ^ 3 * A₄ :=
    (step2_translate_data_three hp3 h₄3 h₆3 hΔd).2.2.1
  obtain ⟨σ₆, hσ₆⟩ := dvd_step6_s hp3 (step2_translate_data_three hp3 h₄3 h₆3 hΔd).1
  obtain ⟨A₃', hA₃'⟩ := hval6.a₃
  have hW6a₂ : (Step6.translate (p : ℤ_[p]) V₁).a₂ = (p : ℤ_[p]) ^ 2 * (A₂ - σ₆ ^ 2) := by
    rw [step6_translate_a₂ _ (step2_translate_data_three hp3 h₄3 h₆3 hΔd).1, hA₂, hσ₆]; ring
  have hW6a₄ : (Step6.translate (p : ℤ_[p]) V₁).a₄
      = (p : ℤ_[p]) ^ 3 * (A₄ - σ₆ * A₃') := by
    rw [step6_translate_a₄ _ (step2_translate_data_three hp3 h₄3 h₆3 hΔd).1, hA₄, hσ₆,
      hA₃']
    ring
  refine ⟨Step6.translate (p : ℤ_[p]) V₁, m, h7,
    Step8.hasValuation_translate hϖ hval6 (hasDoubleRoot_of_three hp3 hW6a₂ hW6a₄)
      (hasTripleRoot_of_three hp3 hW6a₂), ?_, ?_, ?_⟩
  · rw [hV8, hb₂]; subst hp3; push_cast; ring
  · rw [hV8, hb₄, h₄]; subst hp3; push_cast; ring
  · rw [hV8, hb₆, h₄, h₆]; ring

/-! ### Tate's algorithm on the three families

Step 8's test is `3 ∣ b₆/3⁴`, i.e. `3 ∣ 4(b + 3mα + 9m³)`, i.e. `3 ∣ b`; Step 9's is `3 ∣ b₄/3³`,
i.e. `3 ∣ 2(α + 9m²)`, i.e. `3 ∣ α`; Step 10's is `9 ∣ b₆/3⁴`. -/

open scoped Classical in
/-- **Tate's algorithm at `IV*` at `p = 3`.** A short model over `ℤ_3` with `27 ∣ a₄` and
`a₆ = 81b`, `3 ∤ b`, has reduction datum `(IV*, 3)` or `(IV*, 1)` according as the residue of `4b`
is a square in `𝔽₃`. Since `4 = 1` there and the squares are `0, 1`, that is `b ≡ 1 (mod 3)`. -/
theorem run_eq_IVstar_three (hp3 : p = 3) {a₄ a₆ α b : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 4 * b) (hb : ¬ (p : ℤ_[p]) ∣ b) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.IV! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber
        = if IsSquare (PadicInt.toZMod (4 * b)) then 3 else 1 := by
  obtain ⟨W', m, h7, hval8, -, -, hb₆⟩ := step8_bInvariants_three hp3 hΔ0 h₄ h₆
  obtain ⟨A₃, hA₃⟩ := hval8.a₃
  obtain ⟨A₆, hA₆⟩ := hval8.a₆
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  have hnd : ¬ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff_dvd hA₃ hA₆ hb₆]
    refine fun h => hb ?_
    obtain ⟨c, hc⟩ := h4u.dvd_mul_left.mp h
    exact ⟨c - m * α - (p : ℤ_[p]) * m ^ 3, by linear_combination hc⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step8 hΔ0 (step8_run_eq_error_of_not_hasDoubleRoot hΔ0 h7 hnd))]
  refine ⟨rfl, ?_⟩
  rw [show (TateAlgorithm.Output.mk (Step8.translate (p : ℤ_[p]) W') KodairaSymbol.IV!
      (if (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).toPoly.Splits then 3
        else 1)).tamagawaNumber
      = if (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).toPoly.Splits then 3
        else 1 from rfl,
    splits_quadratic_two_iff hp3 hA₃ hA₆ hb₆]
  congr 1
  refine propext (Iff.of_eq (congrArg _ ?_))
  rw [show (4 : ℤ_[p]) * (b + (p : ℤ_[p]) * m * α + (p : ℤ_[p]) ^ 2 * m ^ 3)
      = 4 * b + (p : ℤ_[p]) * (4 * m * α + (p : ℤ_[p]) * 4 * m ^ 3) from by ring, map_add,
    show PadicInt.toZMod ((p : ℤ_[p]) * (4 * m * α + (p : ℤ_[p]) * 4 * m ^ 3)) = 0 from by
      rw [← PadicInt.dvd_iff_toZMod_eq_zero]; exact Dvd.intro _ rfl,
    add_zero]

/-! ### Steps 9 and 10, read off `b₄` and `b₆`

Step 9 inspects `a₄` of its own translate and Step 10 inspects `a₆` of Step 9's output. Both are a
`y`-shift away from the Step-8 translate, so both are recoverable from the `b`-invariants: `2a₄` is
`b₄ - a₁a₃` and `4a₆` is `b₆ - a₃²`, and at these stages `3 ∣ a₁` and `3³ ∣ a₃`. -/

/-- **Step 9's branch condition, in terms of `b₄`.** On the Step-9 translate `3 ∣ a₁` and
`3³ ∣ a₃`, so `3⁴ ∣ a₁a₃`, and `2a₄ = b₄ - a₁a₃` with `2` a unit. -/
theorem pow_four_dvd_a₄_iff_dvd_B₄ (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]} {B₄ : ℤ_[p]}
    (hb₄ : V.b₄ = (p : ℤ_[p]) ^ 3 * B₄) (ha₁ : (p : ℤ_[p]) ∣ V.a₁)
    (ha₃ : (p : ℤ_[p]) ^ 3 ∣ V.a₃) : (p : ℤ_[p]) ^ 4 ∣ V.a₄ ↔ (p : ℤ_[p]) ∣ B₄ := by
  have h2u : IsUnit (2 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 2) (by rw [hp3]; norm_num)
  obtain ⟨A₁, hA₁⟩ := ha₁
  obtain ⟨A₃, hA₃⟩ := ha₃
  obtain ⟨c, hc⟩ : (p : ℤ_[p]) ^ 4 ∣ V.a₁ * V.a₃ := ⟨A₁ * A₃, by rw [hA₁, hA₃]; ring⟩
  constructor
  · rintro ⟨A₄, hA₄⟩
    refine ⟨2 * A₄ + c, mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := p))) ?_⟩
    rw [← hb₄, WeierstrassCurve.b₄, hA₄, hc]
    ring
  · rintro ⟨C₄, hC₄⟩
    refine h2u.dvd_mul_left.mp ⟨C₄ - c, ?_⟩
    rw [show (2 : ℤ_[p]) * V.a₄ = V.b₄ - V.a₁ * V.a₃ by rw [WeierstrassCurve.b₄]; ring,
      hb₄, hC₄, hc]
    ring

/-- **Step 10's branch condition, in terms of `b₆`.** On the curve Step 9 hands on, `3³ ∣ a₃`, so
`3⁶ ∣ a₃²`, and `4a₆ = b₆ - a₃²` with `4` a unit. -/
theorem pow_six_dvd_a₆_iff_sq_dvd_B₆ (hp3 : p = 3) {V : WeierstrassCurve ℤ_[p]} {B₆ : ℤ_[p]}
    (hb₆ : V.b₆ = (p : ℤ_[p]) ^ 4 * B₆) (ha₃ : (p : ℤ_[p]) ^ 3 ∣ V.a₃) :
    (p : ℤ_[p]) ^ 6 ∣ V.a₆ ↔ (p : ℤ_[p]) ^ 2 ∣ B₆ := by
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  obtain ⟨A₃, hA₃⟩ := ha₃
  constructor
  · rintro ⟨A₆, hA₆⟩
    refine ⟨4 * A₆ + A₃ ^ 2,
      mul_left_cancel₀ (pow_ne_zero 4 (PadicInt.uniformizer_ne_zero (p := p))) ?_⟩
    rw [← hb₆, WeierstrassCurve.b₆, hA₆, hA₃]
    ring
  · rintro ⟨C₆, hC₆⟩
    refine h4u.dvd_mul_left.mp ⟨C₆ - A₃ ^ 2, ?_⟩
    rw [show (4 : ℤ_[p]) * V.a₆ = V.b₆ - V.a₃ ^ 2 by rw [WeierstrassCurve.b₆]; ring,
      hb₆, hC₆, hA₃]
    ring

open scoped Classical in
/-- **Tate's algorithm at `III*` at `p = 3`.** A short model over `ℤ_3` with `a₄ = 27α`, `3 ∤ α`
and `243 ∣ a₆` has reduction datum `(III*, 2)`: Step 8 hands on because
`3 ∣ b₆/3⁴ = 4(a₆/3⁴ + 3mα)`, and Step 9 answers because `3 ∤ b₄/3³ = 2(α + 9m²)`. -/
theorem run_eq_IIIstar_three (hp3 : p = 3) {a₄ a₆ α c : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 5 * c) (hα : ¬ (p : ℤ_[p]) ∣ α) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.III! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 2 := by
  obtain ⟨W', m, h7, hval8, -, hb₄, hb₆⟩ :=
    step8_bInvariants_three hp3 hΔ0 h₄ (show a₆ = (p : ℤ_[p]) ^ 4 * ((p : ℤ_[p]) * c) from by
      rw [h₆]; ring)
  obtain ⟨A₃, hA₃⟩ := hval8.a₃
  obtain ⟨A₆, hA₆⟩ := hval8.a₆
  have h2u : IsUnit (2 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 2) (by rw [hp3]; norm_num)
  have hd : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff_dvd hA₃ hA₆ hb₆]
    exact ⟨4 * (c + m * α + (p : ℤ_[p]) * m ^ 3), by ring⟩
  have h8 := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7 hd
  have hval9 := Step9.hasValuation_translate PadicInt.uniformizer_ne_zero hval8 hd
  have hb₄9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).b₄
      = (p : ℤ_[p]) ^ 3 * (2 * (α + (p : ℤ_[p]) ^ 2 * m ^ 2)) := by
    rw [Step9.translate, Step7.translateY_b₄, hb₄]
  have ha₄ : ¬ (p : ℤ_[p]) ^ 4
      ∣ (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).a₄ := by
    rw [pow_four_dvd_a₄_iff_dvd_B₄ hp3 hb₄9 (by simpa using hval9.a₁)
      (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 3)) hval9.a₃)]
    refine fun h => hα ?_
    obtain ⟨d, hd'⟩ := h2u.dvd_mul_left.mp h
    exact ⟨d - (p : ℤ_[p]) * m ^ 2, by linear_combination hd'⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step9 hΔ0 (step9_run_eq_error_of_not_dvd hΔ0 h8 ha₄))]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Tate's algorithm at `II*` at `p = 3`.** A short model over `ℤ_3` with `81 ∣ a₄` and
`a₆ = 243c`, `3 ∤ c`, has reduction datum `(II*, 1)`: Step 8 hands on because `3 ∣ b₆/3⁴`, Step 9
hands on because `3 ∣ b₄/3³ = 2(α + 9m²)` once `3 ∣ α`, and Step 10 answers because
`9 ∤ b₆/3⁴ = 4·3(c + 3mα + 3m³)` once `3 ∤ c`. -/
theorem run_eq_IIstar_three (hp3 : p = 3) {a₄ a₆ α c : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (h₄ : a₄ = (p : ℤ_[p]) ^ 4 * α)
    (h₆ : a₆ = (p : ℤ_[p]) ^ 5 * c) (hc : ¬ (p : ℤ_[p]) ∣ c) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.II! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1 := by
  obtain ⟨W', m, h7, hval8, -, hb₄, hb₆⟩ :=
    step8_bInvariants_three hp3 hΔ0
      (show a₄ = (p : ℤ_[p]) ^ 3 * ((p : ℤ_[p]) * α) from by rw [h₄]; ring)
      (show a₆ = (p : ℤ_[p]) ^ 4 * ((p : ℤ_[p]) * c) from by rw [h₆]; ring)
  obtain ⟨A₃, hA₃⟩ := hval8.a₃
  obtain ⟨A₆, hA₆⟩ := hval8.a₆
  have hd : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff_dvd hA₃ hA₆ hb₆]
    exact ⟨4 * (c + m * ((p : ℤ_[p]) * α) + (p : ℤ_[p]) * m ^ 3), by ring⟩
  have h8 := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7 hd
  have hval9 := Step9.hasValuation_translate PadicInt.uniformizer_ne_zero hval8 hd
  have hb₄9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).b₄
      = (p : ℤ_[p]) ^ 3 * (2 * ((p : ℤ_[p]) * α + (p : ℤ_[p]) ^ 2 * m ^ 2)) := by
    rw [Step9.translate, Step7.translateY_b₄, hb₄]
  have ha₄ : (p : ℤ_[p]) ^ 4
      ∣ (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).a₄ := by
    rw [pow_four_dvd_a₄_iff_dvd_B₄ hp3 hb₄9 (by simpa using hval9.a₁)
      (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 3)) hval9.a₃)]
    exact ⟨2 * (α + (p : ℤ_[p]) * m ^ 2), by ring⟩
  have h9 := step9_run_eq_ok_of_dvd hΔ0 h8 ha₄
  have hb₆9 : (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).b₆
      = (p : ℤ_[p]) ^ 4 * ((p : ℤ_[p])
        * (4 * (c + (p : ℤ_[p]) * m * α + (p : ℤ_[p]) * m ^ 3))) := by
    rw [Step9.translate, Step7.translateY_b₆, hb₆]; ring
  have ha₆ : ¬ (p : ℤ_[p]) ^ 6
      ∣ (Step9.translate (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W')).a₆ := by
    rw [pow_six_dvd_a₆_iff_sq_dvd_B₆ hp3 hb₆9
      (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 3)) hval9.a₃)]
    intro ⟨d, hd'⟩
    have h4u : IsUnit (4 : ℤ_[p]) := by
      simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
    refine hc ?_
    obtain ⟨e, he⟩ := h4u.dvd_mul_left.mp
      (show (p : ℤ_[p]) ∣ 4 * (c + (p : ℤ_[p]) * m * α + (p : ℤ_[p]) * m ^ 3) from ⟨d, by
        refine mul_left_cancel₀ (PadicInt.uniformizer_ne_zero (p := p)) ?_
        linear_combination hd'⟩)
    exact ⟨e - m * α - m ^ 3, by linear_combination he⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step10 hΔ0 (step10_run_eq_error_of_not_dvd hΔ0 h9 ha₆))]
  exact ⟨rfl, rfl⟩

/-! ### The four families are nonsingular

`Δ = -16(4a₄³ + 27a₆²)`. On each family `v₃(a₄)` and `v₃(a₆)` are finite, so the bracket cannot
vanish: with `a₄ = 3ᵏα` and `a₆ = 3ˡc` and one of `α`, `c` a unit, one of the two terms has
strictly smaller valuation than the other. -/

/-- **`Δ ≠ 0` when `3 ∤ a₆/3⁴`**, which covers both `IV*` families: there `4a₄³ + 27a₆² = 0` would
give `3⁸ ∣ 4·3⁸(c·…)` against `3⁹ ∣ 27a₆²` with `v₃(a₆) = 4`, so `3 ∣ 16b²` — impossible. -/
theorem ofShortNF_Δ_ne_zero_snd_three (hp3 : p = 3) {a₄ a₆ α b : ℤ_[p]}
    (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α) (h₆ : a₆ = (p : ℤ_[p]) ^ 4 * b)
    (hb : ¬ (p : ℤ_[p]) ∣ b) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h16 : IsUnit (-16 : ℤ_[p]) := PadicInt.isUnit_neg_sixteen (hp3 ▸ (by decide : Odd 3))
  intro hzero
  rw [ofShortNF_Δ, h₄, h₆] at hzero
  have hbr : (4 : ℤ_[p]) * ((p : ℤ_[p]) ^ 3 * α) ^ 3
      + 27 * ((p : ℤ_[p]) ^ 4 * b) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left h16.ne_zero
  have h9 : (p : ℤ_[p]) ^ 9 * (4 * α ^ 3 + (p : ℤ_[p]) ^ 2 * b ^ 2) = 0 := by
    subst hp3; push_cast at hbr ⊢; linear_combination hbr
  have hsum : (4 : ℤ_[p]) * α ^ 3 + (p : ℤ_[p]) ^ 2 * b ^ 2 = 0 :=
    (mul_eq_zero.mp h9).resolve_left (pow_ne_zero 9 hϖ)
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  obtain ⟨A, hA⟩ : (p : ℤ_[p]) ∣ α :=
    PadicInt.prime_p.dvd_of_dvd_pow (n := 3) (h4u.dvd_mul_left.mp
      ⟨-((p : ℤ_[p]) * b ^ 2), by linear_combination hsum⟩)
  rw [hA] at hsum
  refine hb (PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ⟨-(4 * A ^ 3), ?_⟩)
  refine mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_
  linear_combination hsum

/-- **`Δ ≠ 0` when `3 ∤ a₄/3³`**, which covers the `III*` family: `4a₄³ + 27a₆² = 0` with
`v₃(a₄) = 3` and `v₃(a₆) ≥ 5` gives `3¹⁰ ∣ 4·3⁹α³`, hence `3 ∣ α`. -/
theorem ofShortNF_Δ_ne_zero_fst_three (hp3 : p = 3) {a₄ a₆ α c : ℤ_[p]}
    (h₄ : a₄ = (p : ℤ_[p]) ^ 3 * α) (h₆ : a₆ = (p : ℤ_[p]) ^ 5 * c)
    (hα : ¬ (p : ℤ_[p]) ∣ α) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h16 : IsUnit (-16 : ℤ_[p]) := PadicInt.isUnit_neg_sixteen (hp3 ▸ (by decide : Odd 3))
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  intro hzero
  rw [ofShortNF_Δ, h₄, h₆] at hzero
  have hbr : (4 : ℤ_[p]) * ((p : ℤ_[p]) ^ 3 * α) ^ 3
      + 27 * ((p : ℤ_[p]) ^ 5 * c) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left h16.ne_zero
  have h9 : (p : ℤ_[p]) ^ 9 * (4 * α ^ 3 + (p : ℤ_[p]) ^ 4 * c ^ 2) = 0 := by
    subst hp3; push_cast at hbr ⊢; linear_combination hbr
  have hsum : (4 : ℤ_[p]) * α ^ 3 + (p : ℤ_[p]) ^ 4 * c ^ 2 = 0 :=
    (mul_eq_zero.mp h9).resolve_left (pow_ne_zero 9 hϖ)
  exact hα (PadicInt.prime_p.dvd_of_dvd_pow (n := 3) (h4u.dvd_mul_left.mp
    ⟨-((p : ℤ_[p]) ^ 3 * c ^ 2), by linear_combination hsum⟩))

/-- **`Δ ≠ 0` on the `II*` family**, `a₄ = 81α` and `a₆ = 243c` with `3 ∤ c`: there
`4a₄³ + 27a₆² = 3¹²(4α³ + 3c²)`, and `4α³ + 3c² = 0` would give `3 ∣ α`, whence `36A³ + c² = 0` and
`3 ∣ c`. -/
theorem ofShortNF_Δ_ne_zero_IIstar_three (hp3 : p = 3) {a₄ a₆ α c : ℤ_[p]}
    (h₄ : a₄ = (p : ℤ_[p]) ^ 4 * α) (h₆ : a₆ = (p : ℤ_[p]) ^ 5 * c)
    (hc : ¬ (p : ℤ_[p]) ∣ c) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h16 : IsUnit (-16 : ℤ_[p]) := PadicInt.isUnit_neg_sixteen (hp3 ▸ (by decide : Odd 3))
  have h4u : IsUnit (4 : ℤ_[p]) := by
    simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 4) (by rw [hp3]; norm_num)
  intro hzero
  rw [ofShortNF_Δ, h₄, h₆] at hzero
  have hbr : (4 : ℤ_[p]) * ((p : ℤ_[p]) ^ 4 * α) ^ 3
      + 27 * ((p : ℤ_[p]) ^ 5 * c) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left h16.ne_zero
  have h12 : (p : ℤ_[p]) ^ 12 * (4 * α ^ 3 + (p : ℤ_[p]) * c ^ 2) = 0 := by
    subst hp3; push_cast at hbr ⊢; linear_combination hbr
  have hsum : (4 : ℤ_[p]) * α ^ 3 + (p : ℤ_[p]) * c ^ 2 = 0 :=
    (mul_eq_zero.mp h12).resolve_left (pow_ne_zero 12 hϖ)
  obtain ⟨A, hA⟩ : (p : ℤ_[p]) ∣ α :=
    PadicInt.prime_p.dvd_of_dvd_pow (n := 3) (h4u.dvd_mul_left.mp ⟨-(c ^ 2), by
      linear_combination hsum⟩)
  rw [hA] at hsum
  refine hc (PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ⟨-(4 * (p : ℤ_[p]) * A ^ 3), ?_⟩)
  refine mul_left_cancel₀ hϖ ?_
  linear_combination hsum

end StarredThree

/-! ### The four loci and their masses

Each locus is a union of residue classes of the coefficient plane modulo `3⁵` for the three
`mod 243` loci and modulo `3⁶` for `II*`; its mass is the class count times `3⁻²ᵏ`. -/

open StarredThree BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-- The nine classes of the **`(IV*, 3)` locus** at `3`: `27 ∣ a₄` and `a₆ ≡ 81 (mod 243)`. -/
def headResIVstarThreeThree : Finset (ZMod (3 ^ 5) × ZMod (3 ^ 5)) :=
  {(0, 81), (27, 81), (54, 81), (81, 81), (108, 81), (135, 81), (162, 81), (189, 81), (216, 81)}

/-- The nine classes of the **`(IV*, 1)` locus** at `3`: `27 ∣ a₄` and `a₆ ≡ 162 (mod 243)`. -/
def headResIVstarOneThree : Finset (ZMod (3 ^ 5) × ZMod (3 ^ 5)) :=
  {(0, 162), (27, 162), (54, 162), (81, 162), (108, 162), (135, 162), (162, 162), (189, 162),
    (216, 162)}

/-- The six classes of the **`(III*, 2)` locus** at `3`: `a₄ ≡ 27` or `54` modulo `81`, `243 ∣ a₆`.
Six rather than nine because the two thirds with `81 ∣ a₄` belong to `II*` instead. -/
def headResIIIstarThree : Finset (ZMod (3 ^ 5) × ZMod (3 ^ 5)) :=
  {(27, 0), (54, 0), (108, 0), (135, 0), (189, 0), (216, 0)}

/-- The eighteen classes of the **`(II*, 1)` locus** at `3`: `81 ∣ a₄`, `a₆ ≡ 243` or `486` modulo
`729`. -/
def headResIIstarThree : Finset (ZMod (3 ^ 6) × ZMod (3 ^ 6)) :=
  {(0, 243), (81, 243), (162, 243), (243, 243), (324, 243), (405, 243), (486, 243), (567, 243),
    (648, 243), (0, 486), (81, 486), (162, 486), (243, 486), (324, 486), (405, 486), (486, 486),
    (567, 486), (648, 486)}

set_option maxRecDepth 20000 in
/-- The `(IV*, 3)` locus at `3` consists of nine residue classes modulo `3⁵`. -/
theorem card_headResIVstarThreeThree : headResIVstarThreeThree.card = 9 := by decide

set_option maxRecDepth 20000 in
/-- The `(IV*, 1)` locus at `3` consists of nine residue classes modulo `3⁵`. -/
theorem card_headResIVstarOneThree : headResIVstarOneThree.card = 9 := by decide

set_option maxRecDepth 20000 in
/-- The `(III*, 2)` locus at `3` consists of six residue classes modulo `3⁵`. -/
theorem card_headResIIIstarThree : headResIIIstarThree.card = 6 := by decide

set_option maxRecDepth 40000 in
/-- The `(II*, 1)` locus at `3` consists of eighteen residue classes modulo `3⁶`. -/
theorem card_headResIIstarThree : headResIIstarThree.card = 18 := by decide

/-- The **`(IV*, 3)` locus** of the coefficient plane at `3`. -/
noncomputable def ivStarThree3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 5 ⁻¹' (headResIVstarThreeThree : Set (ZMod (3 ^ 5) × ZMod (3 ^ 5)))

/-- The **`(IV*, 1)` locus** of the coefficient plane at `3`. -/
noncomputable def ivStarOne3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 5 ⁻¹' (headResIVstarOneThree : Set (ZMod (3 ^ 5) × ZMod (3 ^ 5)))

/-- The **`(III*, 2)` locus** of the coefficient plane at `3`. -/
noncomputable def iiiStar3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 5 ⁻¹' (headResIIIstarThree : Set (ZMod (3 ^ 5) × ZMod (3 ^ 5)))

/-- The **`(II*, 1)` locus** of the coefficient plane at `3`. -/
noncomputable def iiStar3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 6 ⁻¹' (headResIIstarThree : Set (ZMod (3 ^ 6) × ZMod (3 ^ 6)))

/-- The `(IV*, 3)` locus at `3` is measurable. -/
theorem measurableSet_ivStarThree3Locus : MeasurableSet ivStarThree3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResIVstarThreeThree

/-- The `(IV*, 1)` locus at `3` is measurable. -/
theorem measurableSet_ivStarOne3Locus : MeasurableSet ivStarOne3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResIVstarOneThree

/-- The `(III*, 2)` locus at `3` is measurable. -/
theorem measurableSet_iiiStar3Locus : MeasurableSet iiiStar3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 5 headResIIIstarThree

/-- The `(II*, 1)` locus at `3` is measurable. -/
theorem measurableSet_iiStar3Locus : MeasurableSet iiStar3Locus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResIIstarThree

/-- `9 · 3⁻¹⁰ = 9/59049 = 1/6561`. -/
theorem nine_mul_inv_pow_ten_three_eq :
    ((9 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 5) = 1 / 6561 := by
  rw [show ((9 : ℕ) : ℝ≥0∞) = 9 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 5) = 59049 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `6 · 3⁻¹⁰ = 6/59049 = 2/19683`. -/
theorem six_mul_inv_pow_ten_three_eq :
    ((6 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 5) = 2 / 19683 := by
  rw [show ((6 : ℕ) : ℝ≥0∞) = 6 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 5) = 59049 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `18 · 3⁻¹² = 18/531441 = 2/59049`. -/
theorem eighteen_mul_inv_pow_twelve_three_eq :
    ((18 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 6) = 2 / 59049 := by
  rw [show ((18 : ℕ) : ℝ≥0∞) = 18 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 6) = 531441 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the `(IV*, 3)` locus at `3` is `9/59049 = 1/6561`.** -/
theorem volume_ivStarThree3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) ivStarThree3Locus = 1 / 6561 := by
  rw [ivStarThree3Locus, PadicInt.volume_preimage_redPairPow, card_headResIVstarThreeThree,
    nine_mul_inv_pow_ten_three_eq]

/-- **The mass of the `(IV*, 1)` locus at `3` is `9/59049 = 1/6561`.** -/
theorem volume_ivStarOne3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) ivStarOne3Locus = 1 / 6561 := by
  rw [ivStarOne3Locus, PadicInt.volume_preimage_redPairPow, card_headResIVstarOneThree,
    nine_mul_inv_pow_ten_three_eq]

/-- **The mass of the `(III*, 2)` locus at `3` is `6/59049 = 2/19683`.** -/
theorem volume_iiiStar3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iiiStar3Locus = 2 / 19683 := by
  rw [iiiStar3Locus, PadicInt.volume_preimage_redPairPow, card_headResIIIstarThree,
    six_mul_inv_pow_ten_three_eq]

/-- **The mass of the `(II*, 1)` locus at `3` is `18/531441 = 2/59049`.** -/
theorem volume_iiStar3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iiStar3Locus = 2 / 59049 := by
  rw [iiStar3Locus, PadicInt.volume_preimage_redPairPow, card_headResIIstarThree,
    eighteen_mul_inv_pow_twelve_three_eq]

/-! ### The shape of a point of each locus -/

set_option maxRecDepth 20000 in
/-- **A point of the `(IV*, 3)` locus has `a₄ = 27α` and `a₆ = 81b` with `b ≡ 1 (mod 3)`**, so
`3 ∤ b` and the residue of `4b` is the square `1`. -/
theorem exists_form_of_mem_ivStarThree3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ ivStarThree3Locus) :
    ∃ α b k : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 4 * b ∧
      b = 1 + ((3 : ℕ) : ℤ_[3]) * k := by
  rw [ivStarThree3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarThreeThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  have h6 : PadicInt.toZModPow 5 x.2 = 81 := by
    rcases hx with ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩ <;> exact h
  obtain ⟨α, hα⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 5) (by norm_num) ?_
    rcases hx with ⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩ <;>
      rw [h] <;> decide
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.2 - 81 := by
    rw [← PadicInt.toZModPow_eq_iff_pow_dvd_sub, h6, map_ofNat]
  refine ⟨α, 1 + ((3 : ℕ) : ℤ_[3]) * c, c, hα, ?_, rfl⟩
  rw [show x.2 = 81 + ((3 : ℕ) : ℤ_[3]) ^ 5 * c from by linear_combination hc,
    show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]
  ring

set_option maxRecDepth 20000 in
/-- **A point of the `(IV*, 1)` locus has `a₄ = 27α` and `a₆ = 81b` with `b ≡ 2 (mod 3)`**, so
`3 ∤ b` and the residue of `4b` is the non-square `2`. -/
theorem exists_form_of_mem_ivStarOne3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ ivStarOne3Locus) :
    ∃ α b k : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 4 * b ∧
      b = 2 + ((3 : ℕ) : ℤ_[3]) * k := by
  rw [ivStarOne3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIVstarOneThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  have h6 : PadicInt.toZModPow 5 x.2 = 162 := by
    rcases hx with ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩ <;> exact h
  obtain ⟨α, hα⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 5) (by norm_num) ?_
    rcases hx with ⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩ <;>
      rw [h] <;> decide
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.2 - 162 := by
    rw [← PadicInt.toZModPow_eq_iff_pow_dvd_sub, h6, map_ofNat]
  refine ⟨α, 2 + ((3 : ℕ) : ℤ_[3]) * c, c, hα, ?_, rfl⟩
  rw [show x.2 = 162 + ((3 : ℕ) : ℤ_[3]) ^ 5 * c from by linear_combination hc,
    show ((3 : ℕ) : ℤ_[3]) = 3 from by norm_num]
  ring

set_option maxRecDepth 20000 in
/-- **A point of the `(III*, 2)` locus has `a₄ = 27α` with `3 ∤ α`, and `a₆ = 243c`.** -/
theorem exists_form_of_mem_iiiStar3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ iiiStar3Locus) :
    ∃ α c : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 5 * c ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ α := by
  rw [iiiStar3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIIstarThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  have h6 : PadicInt.toZModPow 5 x.2 = 0 := by
    rcases hx with ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩ <;> exact h
  obtain ⟨α, hα⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ x.1 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 3) (n := 5) (by norm_num) ?_
    rcases hx with ⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩ <;> rw [h] <;> decide
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.2 :=
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.mpr h6
  refine ⟨α, c, hα, hc, fun ⟨d, hd⟩ => ?_⟩
  have h4 : ¬ (ZMod.cast (PadicInt.toZModPow 5 x.1) : ZMod (3 ^ 4)) = 0 := by
    rcases hx with ⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩ <;> rw [h] <;> decide
  refine h4 ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num) x.1,
    ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact ⟨d, by rw [hα, hd]; ring⟩

set_option maxRecDepth 40000 in
/-- **A point of the `(II*, 1)` locus has `a₄ = 81α` and `a₆ = 243c` with `3 ∤ c`.** -/
theorem exists_form_of_mem_iiStar3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ iiStar3Locus) :
    ∃ α c : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 4 * α ∧ x.2 = ((3 : ℕ) : ℤ_[3]) ^ 5 * c ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ c := by
  rw [iiStar3Locus, mem_preimage, Finset.mem_coe] at hx
  simp only [headResIIstarThree, Finset.mem_insert, Finset.mem_singleton,
    PadicInt.redPairPow, Prod.mk.injEq] at hx
  obtain ⟨α, hα⟩ : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.1 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 4) (n := 6) (by norm_num) ?_
    rcases hx with ⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|
      ⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩|⟨h, -⟩ <;> rw [h] <;> decide
  obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 5 ∣ x.2 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (m := 5) (n := 6) (by norm_num) ?_
    rcases hx with ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|
      ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩ <;> rw [h] <;> decide
  refine ⟨α, c, hα, hc, fun ⟨d, hd⟩ => ?_⟩
  have h6 : ¬ PadicInt.toZModPow 6 x.2 = 0 := by
    rcases hx with ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|
      ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩ <;> rw [h] <;> decide
  exact h6 (PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp ⟨d, by rw [hc, hd]; ring⟩)

/-! ### The two unit residues, and the two `𝔽₃` square tests

On the two `IV*` loci `b ≡ 1` or `b ≡ 2` modulo `3`. Since `4 = 1` in `𝔽₃` and the squares are `0`
and `1`, the residue of `4b` is a square on the first and not on the second. -/

/-- **`3 ∤ 1 + 3k`.** -/
theorem not_dvd_one_add_three_mul (k : ℤ_[3]) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ 1 + ((3 : ℕ) : ℤ_[3]) * k := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_add, map_one, map_mul,
    show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by rw [← PadicInt.dvd_iff_toZMod_eq_zero],
    zero_mul, add_zero]
  decide

/-- **`3 ∤ 2 + 3k`.** -/
theorem not_dvd_two_add_three_mul (k : ℤ_[3]) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ 2 + ((3 : ℕ) : ℤ_[3]) * k := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_add, map_ofNat, map_mul,
    show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by rw [← PadicInt.dvd_iff_toZMod_eq_zero],
    zero_mul, add_zero]
  decide

/-- `4(1 + 3k)` is a square in `𝔽₃` for every `k`: it is `1`. -/
theorem isSquare_four_mul_one_add_three_mul (k : ZMod 3) : IsSquare (4 * (1 + 3 * k)) := by
  revert k
  decide

/-- `4(2 + 3k)` is not a square in `𝔽₃` for any `k`: it is `2`. -/
theorem not_isSquare_four_mul_two_add_three_mul (k : ZMod 3) : ¬ IsSquare (4 * (2 + 3 * k)) := by
  revert k
  decide

/-! ### The loci lie in their strata -/

open scoped Classical in
/-- **The `(IV*, 3)` locus at `3` lies in the `(IV*, 3)` stratum.** -/
theorem ivStarThree3Locus_subset_stratFibre :
    ivStarThree3Locus ⊆ stratFibre 3 (KodairaSymbol.IV!, 3) := by
  intro x hx
  obtain ⟨α, b, k, hα, hb, hk⟩ := exists_form_of_mem_ivStarThree3Locus hx
  have hbu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ b := by rw [hk]; exact not_dvd_one_add_three_mul k
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hα, hb]
    exact ofShortNF_Δ_ne_zero_snd_three (p := 3) rfl rfl rfl hbu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IVstar_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 3 * α) (((3 : ℕ) : ℤ_[3]) ^ 4 * b)).Δ ≠ 0 from by
      rw [← hα, ← hb]; exact hΔ) rfl rfl hbu
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  refine Prod.ext (by simp only [hα, hb]; exact hks) ?_
  simp only [hα, hb]
  rw [hts, ite_eq_left]
  rw [hk, map_mul, map_add, map_mul, map_one, map_ofNat,
    show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by rw [← PadicInt.dvd_iff_toZMod_eq_zero],
    zero_mul, add_zero, show (4 : ZMod 3) * 1 = 4 * (1 + 3 * 0) from by decide]
  exact isSquare_four_mul_one_add_three_mul 0

open scoped Classical in
/-- **The `(IV*, 1)` locus at `3` lies in the `(IV*, 1)` stratum.** -/
theorem ivStarOne3Locus_subset_stratFibre :
    ivStarOne3Locus ⊆ stratFibre 3 (KodairaSymbol.IV!, 1) := by
  intro x hx
  obtain ⟨α, b, k, hα, hb, hk⟩ := exists_form_of_mem_ivStarOne3Locus hx
  have hbu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ b := by rw [hk]; exact not_dvd_two_add_three_mul k
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hα, hb]
    exact ofShortNF_Δ_ne_zero_snd_three (p := 3) rfl rfl rfl hbu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IVstar_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 3 * α) (((3 : ℕ) : ℤ_[3]) ^ 4 * b)).Δ ≠ 0 from by
      rw [← hα, ← hb]; exact hΔ) rfl rfl hbu
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  refine Prod.ext (by simp only [hα, hb]; exact hks) ?_
  simp only [hα, hb]
  rw [hts, ite_eq_right]
  rw [hk, map_mul, map_add, map_mul, map_ofNat, map_ofNat,
    show PadicInt.toZMod ((3 : ℕ) : ℤ_[3]) = 0 from by rw [← PadicInt.dvd_iff_toZMod_eq_zero],
    zero_mul, add_zero, show (4 : ZMod 3) * 2 = 4 * (2 + 3 * 0) from by decide]
  exact not_isSquare_four_mul_two_add_three_mul 0

/-- **The `(III*, 2)` locus at `3` lies in the `(III*, 2)` stratum.** -/
theorem iiiStar3Locus_subset_stratFibre :
    iiiStar3Locus ⊆ stratFibre 3 (KodairaSymbol.III!, 2) := by
  intro x hx
  obtain ⟨α, c, hα, hc, hαu⟩ := exists_form_of_mem_iiiStar3Locus hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hα, hc]
    exact ofShortNF_Δ_ne_zero_fst_three (p := 3) rfl rfl rfl hαu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IIIstar_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 3 * α) (((3 : ℕ) : ℤ_[3]) ^ 5 * c)).Δ ≠ 0 from by
      rw [← hα, ← hc]; exact hΔ) rfl rfl hαu
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  exact Prod.ext (by simp only [hα, hc]; exact hks) (by simp only [hα, hc]; exact hts)

/-- **The `(II*, 1)` locus at `3` lies in the `(II*, 1)` stratum.** -/
theorem iiStar3Locus_subset_stratFibre :
    iiStar3Locus ⊆ stratFibre 3 (KodairaSymbol.II!, 1) := by
  intro x hx
  obtain ⟨α, c, hα, hc, hcu⟩ := exists_form_of_mem_iiStar3Locus hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [hα, hc]
    exact ofShortNF_Δ_ne_zero_IIstar_three (p := 3) rfl rfl rfl hcu
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hks, hts⟩ := run_eq_IIstar_three (p := 3) rfl
    (show (ofShortNF (((3 : ℕ) : ℤ_[3]) ^ 4 * α) (((3 : ℕ) : ℤ_[3]) ^ 5 * c)).Δ ≠ 0 from by
      rw [← hα, ← hc]; exact hΔ) rfl rfl hcu
  refine (mem_stratFibre_iff hUp).2 ?_
  rw [strat]
  exact Prod.ext (by simp only [hα, hc]; exact hks) (by simp only [hα, hc]; exact hts)

/-! ### Minimality

A dilate has `3⁴ ∣ a₄` and `3⁶ ∣ a₆`. On the three `a₆`-cut loci `v₃(a₆)` is `4` or `5`, and on the
`III*` locus `v₃(a₄)` is `3`, so no point of any of the four is a dilate. Each locus therefore
lies in the part of its row outside the dilates. -/

/-- **No point of the `(IV*, 3)` locus at `3` is a dilate**: there `v₃(a₆) = 4`. -/
theorem notMem_range_of_mem_ivStarThree3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ ivStarThree3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  obtain ⟨-, b, k, -, hb, hk⟩ := exists_form_of_mem_ivStarThree3Locus hx
  rw [hk] at hb
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun ⟨d, hd⟩ => ?_
  refine not_dvd_one_add_three_mul k ⟨((3 : ℕ) : ℤ_[3]) * d, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 4 (PadicInt.uniformizer_ne_zero (p := 3))) ?_
  rw [← hb, hd]
  ring

/-- **No point of the `(IV*, 1)` locus at `3` is a dilate**, for the same reason. -/
theorem notMem_range_of_mem_ivStarOne3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ ivStarOne3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  obtain ⟨-, b, k, -, hb, hk⟩ := exists_form_of_mem_ivStarOne3Locus hx
  rw [hk] at hb
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun ⟨d, hd⟩ => ?_
  refine not_dvd_two_add_three_mul k ⟨((3 : ℕ) : ℤ_[3]) * d, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 4 (PadicInt.uniformizer_ne_zero (p := 3))) ?_
  rw [← hb, hd]
  ring

/-- **No point of the `(III*, 2)` locus at `3` is a dilate**: there `v₃(a₄) = 3`, so `3⁴ ∤ a₄`. -/
theorem notMem_range_of_mem_iiiStar3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ iiiStar3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  obtain ⟨α, -, hα, -, hαu⟩ := exists_form_of_mem_iiiStar3Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun ⟨d, hd⟩ => hαu ⟨d, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 3 (PadicInt.uniformizer_ne_zero (p := 3))) ?_
  rw [← hα, hd]
  ring

/-- **No point of the `(II*, 1)` locus at `3` is a dilate**: there `v₃(a₆) = 5`. -/
theorem notMem_range_of_mem_iiStar3Locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ iiStar3Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  obtain ⟨-, c, -, hc, hcu⟩ := exists_form_of_mem_iiStar3Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun ⟨d, hd⟩ => hcu ⟨d, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 5 (PadicInt.uniformizer_ne_zero (p := 3))) ?_
  rw [← hc, hd]
  ring

/-- Every point of the `(IV*, 3)` locus at `3` lies in a stratum with Tamagawa number `3` and is
not a dilate. -/
theorem ivStarThree3Locus_subset_headMinimal :
    ivStarThree3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 3)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three ivStarThree3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_ivStarThree3Locus hx

/-- Every point of the `(IV*, 1)` locus at `3` lies in a stratum with Tamagawa number `1` and is
not a dilate. -/
theorem ivStarOne3Locus_subset_headMinimal :
    ivStarOne3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three ivStarOne3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_ivStarOne3Locus hx

/-- Every point of the `(III*, 2)` locus at `3` lies in a stratum with Tamagawa number `2` and is
not a dilate. -/
theorem iiiStar3Locus_subset_headMinimal :
    iiiStar3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three iiiStar3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_iiiStar3Locus hx

/-- Every point of the `(II*, 1)` locus at `3` lies in a stratum with Tamagawa number `1` and is
not a dilate. -/
theorem iiStar3Locus_subset_headMinimal :
    iiStar3Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  subset_headMinimal_at_three iiStar3Locus_subset_stratFibre
    fun _ hx => notMem_range_of_mem_iiStar3Locus hx

end WeierstrassCurve

end
