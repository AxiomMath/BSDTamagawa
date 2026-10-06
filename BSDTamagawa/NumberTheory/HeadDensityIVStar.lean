/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityLargePrime
public import BSDTamagawa.TamagawaLaw.GOTClosedForm

/-!
# The `IV*` strata and the exact value of `δ_p(3)` for `p ≥ 5`

For a prime `p ≥ 5`, write `N = |goodRes p|`, so that `2N = p - 1`, and `T = (1 - p⁻¹⁰)⁻¹`. Running
Steps 6, 7 and 8 of Tate's algorithm forwards on short models with `p³ ∣ a₄` and `a₆ = p⁴u`,
`p ∤ u`, this file shows that the minimal parts of the strata `τ_p⁻¹((IV*, 3))` and
`τ_p⁻¹((IV*, 1))` are these congruence loci, split by whether the residue of `u` is a square. Each
has mass `N p⁻⁸`, so both strata have density `N p⁻⁸ T = (p-1)p²/(2(p¹⁰-1))`. Since only `I₃`, `IV`
and `IV*` carry the Tamagawa number `3`, this gives

    `δ_p(3) = (2N² + N + N p⁻³) p⁻⁵ T = p²(p⁴+1)/(2(p+1)(p⁸+p⁶+p⁴+p²+1))`.

## Main definitions

* `WeierstrassCurve.ivStarSplitLocus`: `p³ ∣ a₄` and `a₆ = p⁴u` with `u` a unit of square residue.
* `WeierstrassCurve.ivStarNonSplitLocus`: `p³ ∣ a₄` and `a₆ = p⁴u` with `u` a unit of non-square
  residue.

## Main results

* `WeierstrassCurve.run_eq_IVstar_of_eq_sq_mul`: a short model with `p³ ∣ a₄`, `a₆ = p⁴u`, `p ∤ u`
  has reduction datum `(IV*, 3)` or `(IV*, 1)` according as the residue of `u` is a square or not.
* `WeierstrassCurve.stratFibre_diff_range_eq_ivStarSplitLocus`,
  `WeierstrassCurve.stratFibre_diff_range_eq_ivStarNonSplitLocus`: the minimal parts of the two
  `IV*` strata.
* `WeierstrassCurve.deltaP_IVstar_three_eq`, `WeierstrassCurve.deltaP_IVstar_one_eq`:
  `δ_p((IV*, 3)) = δ_p((IV*, 1)) = N p⁻⁸ T`.
* `WeierstrassCurve.Cubic.card_roots_ne_two`: a monic cubic over a field with no double root does
  not have exactly two distinct roots.
* `WeierstrassCurve.TateAlgorithm.run_kodairaSymbol_of_tamagawaNumber_eq_three`: only `I₃`, `IV`
  and `IV*` carry the Tamagawa number `3`.
* `WeierstrassCurve.iUnion_stratFibre_three_eq`: `{c = 3}` is the union of the strata `(I₃, 3)`,
  `(IV, 3)` and `(IV*, 3)`.
* `WeierstrassCurve.δ_three_eq`, `WeierstrassCurve.δ_three_eq_ofReal_gotδ`: the value of `δ_p(3)`
  above.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*, Quart. J. Math.
  72 (2021), Lemma 3.1 and Table 5.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Exact quotients -/

/-- If `x = ϖⁿy` then `y` is the quotient `CommRing.div` returns. -/
theorem div_eq_of_eq_pow_mul {R : Type*} [CommRing R] [NoZeroDivisors R] {ϖ x y : R} {n : ℕ}
    (hϖ : ϖ ≠ 0) (h : x = ϖ ^ n * y) : CommRing.div x (ϖ ^ n) = y :=
  mul_left_cancel₀ (pow_ne_zero n hϖ)
    ((CommRing.mul_div (pow_ne_zero n hϖ) ⟨y, h⟩).trans h)

/-- Step 6's cubic, read off explicit quotients of the coefficients. -/
theorem cubic_one_one_eq_of_eq_mul {R : Type*} [CommRing R] [NoZeroDivisors R] {ϖ : R}
    {W : WeierstrassCurve R} {A₂ A₄ A₆ : R} (hϖ : ϖ ≠ 0) (h2 : W.a₂ = ϖ * A₂)
    (h4 : W.a₄ = ϖ ^ 2 * A₄) (h6 : W.a₆ = ϖ ^ 3 * A₆) :
    cubic ϖ W 1 1 = ⟨1, CommRing.mod ϖ A₂, CommRing.mod ϖ A₄, CommRing.mod ϖ A₆⟩ := by
  have e2 : CommRing.div W.a₂ ϖ = A₂ := by
    simpa using div_eq_of_eq_pow_mul (n := 1) hϖ (by simpa using h2)
  have e4 : CommRing.div W.a₄ (ϖ ^ (1 + 1)) = A₄ := div_eq_of_eq_pow_mul hϖ (by simpa using h4)
  have e6 : CommRing.div W.a₆ (ϖ ^ (2 * 1 + 1)) = A₆ := div_eq_of_eq_pow_mul hϖ (by simpa using h6)
  rw [cubic, e2, e4, e6, map_one]

/-- Step 8's quadratic, read off explicit quotients of the coefficients. -/
theorem quadratic_two_eq_of_eq_mul {R : Type*} [CommRing R] [NoZeroDivisors R] {ϖ : R}
    {W : WeierstrassCurve R} {A₃ A₆ : R} (hϖ : ϖ ≠ 0) (h3 : W.a₃ = ϖ ^ 2 * A₃)
    (h6 : W.a₆ = ϖ ^ 4 * A₆) :
    quadratic ϖ W 2 = ⟨0, 1, CommRing.mod ϖ A₃, -CommRing.mod ϖ A₆⟩ := by
  have e3 : CommRing.div W.a₃ (ϖ ^ 2) = A₃ := div_eq_of_eq_pow_mul hϖ h3
  have e6 : CommRing.div W.a₆ (ϖ ^ (2 * 2)) = A₆ := div_eq_of_eq_pow_mul hϖ (by simpa using h6)
  rw [quadratic, e3, e6]

/-! ### Unit numerals in the residue field -/

/-- `16` is a unit of the residue field at `p ≥ 5`. -/
theorem isUnit_mod_sixteen (hp : 5 ≤ p) :
    IsUnit (16 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  simpa only [map_ofNat] using (isUnit_sixteen hp).map (CommRing.mod (p : ℤ_[p]))

/-- `32` is a unit of the residue field at `p ≥ 5`. -/
theorem isUnit_mod_thirtyTwo (hp : 5 ≤ p) :
    IsUnit (32 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h : IsUnit ((2 : ℤ_[p]) ^ 5) := (PadicInt.isUnit_two hodd).pow 5
  rw [show (2 : ℤ_[p]) ^ 5 = 32 by norm_num] at h
  simpa only [map_ofNat] using h.map (CommRing.mod (p : ℤ_[p]))

/-- `27` is a unit of the residue field at `p ≥ 5`. -/
theorem isUnit_mod_twentySeven (hp : 5 ≤ p) :
    IsUnit (27 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  simpa only [map_ofNat] using (isUnit_twentySeven hp).map (CommRing.mod (p : ℤ_[p]))

/-- `216` is a unit of the residue field at `p ≥ 5`. -/
theorem isUnit_mod_twoHundredSixteen (hp : 5 ≤ p) :
    IsUnit (216 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  simpa only [map_ofNat] using (isUnit_twoHundredSixteen hp).map (CommRing.mod (p : ℤ_[p]))

/-- **The discriminant of a monic cubic with a triple root at its inflection.** Over a field in
which `27` is a unit, if `b² = 3c` then the discriminant of `X³ + bX² + cX + d` vanishes exactly
when `b³ = 27d`. -/
theorem hasDoubleRoot_algebra {K : Type*} [Field K] (h27 : IsUnit (27 : K)) {B C D : K}
    (htr : B ^ 2 = 3 * C) :
    B ^ 2 * C ^ 2 = 4 * C ^ 3 + 4 * B ^ 3 * D + 27 * D ^ 2 - 18 * B * C * D
      ↔ B ^ 3 = 27 * D := by
  have key : (27 : K)
      * (B ^ 2 * C ^ 2 - (4 * C ^ 3 + 4 * B ^ 3 * D + 27 * D ^ 2 - 18 * B * C * D))
      = -(B ^ 3 - 27 * D) ^ 2 := by
    linear_combination (54 * C ^ 2 + 9 * C * (B ^ 2 - 3 * C) + (B ^ 2 - 3 * C) ^ 2
      - 162 * B * D) * htr
  rw [← sub_eq_zero (a := B ^ 2 * C ^ 2), ← h27.mul_right_eq_zero, key, neg_eq_zero,
    pow_eq_zero_iff two_ne_zero, sub_eq_zero]

/-! ### Steps 6, 7 and 8 read off `c₄` and `c₆` -/

/-- **Step 7's triple-root test is `p³ ∣ c₄`.** On a curve with `p ∣ a₁`, `p ∣ a₂`, `p² ∣ a₃`,
`p² ∣ a₄` and `p³ ∣ a₆`, the cubic `X³ + (a₂/p)X² + (a₄/p²)X + a₆/p³` satisfies `b² = 3c` modulo
`p` exactly when `p³ ∣ c₄`. -/
theorem hasTripleRoot_cubic_iff (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ A₆ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 2 * A₄)
    (h6 : W.a₆ = (p : ℤ_[p]) ^ 3 * A₆) :
    (cubic (p : ℤ_[p]) W 1 1).HasTripleRoot ↔ (p : ℤ_[p]) ^ 3 ∣ W.c₄ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hz : CommRing.mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 := CommRing.mod_self _
  have hc₄ : W.c₄ = (p : ℤ_[p]) ^ 2
      * (((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)) := by
    rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h1, h2, h3, h4]; ring
  have hdvd : ((p : ℤ_[p]) ^ 3 ∣ W.c₄) ↔ (p : ℤ_[p]) ∣
      (((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)) := by
    rw [hc₄]; exact pow_succ_dvd_pow_mul hϖ 2
  have hmod : CommRing.mod (p : ℤ_[p])
        (((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃))
      = 16 * (CommRing.mod (p : ℤ_[p]) A₂ ^ 2 - 3 * CommRing.mod (p : ℤ_[p]) A₄) := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hz]; ring
  rw [hdvd, ← CommRing.mod_eq_zero, hmod, (isUnit_mod_sixteen hp).mul_right_eq_zero,
    sub_eq_zero, Cubic.HasTripleRoot, cubic_one_one_eq_of_eq_mul hϖ h2 h4 h6]

/-- **Given the triple-root condition, Step 6's double-root test is `p⁴ ∣ c₆`.** -/
theorem hasDoubleRoot_cubic_iff (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ A₆ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 2 * A₄)
    (h6 : W.a₆ = (p : ℤ_[p]) ^ 3 * A₆) (ht : (cubic (p : ℤ_[p]) W 1 1).HasTripleRoot) :
    (cubic (p : ℤ_[p]) W 1 1).HasDoubleRoot ↔ (p : ℤ_[p]) ^ 4 ∣ W.c₆ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hz : CommRing.mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 := CommRing.mod_self _
  have htr : CommRing.mod (p : ℤ_[p]) A₂ ^ 2 = 3 * CommRing.mod (p : ℤ_[p]) A₄ := by
    rw [Cubic.HasTripleRoot, cubic_one_one_eq_of_eq_mul hϖ h2 h4 h6] at ht; exact ht
  have hc₆ : W.c₆ = (p : ℤ_[p]) ^ 3 * (-(((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 3)
      + 36 * ((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)
      - 216 * ((p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆)) := by
    rw [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      h1, h2, h3, h4, h6]
    ring
  have hdvd : ((p : ℤ_[p]) ^ 4 ∣ W.c₆) ↔ (p : ℤ_[p]) ∣ (-(((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 3)
      + 36 * ((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)
      - 216 * ((p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆)) := by
    rw [hc₆]; exact pow_succ_dvd_pow_mul hϖ 3
  have hmod : CommRing.mod (p : ℤ_[p]) (-(((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 3)
        + 36 * ((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)
        - 216 * ((p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆))
      = 32 * (CommRing.mod (p : ℤ_[p]) A₂ ^ 3 - 27 * CommRing.mod (p : ℤ_[p]) A₆) := by
    simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, hz]
    linear_combination (-96 * CommRing.mod (p : ℤ_[p]) A₂) * htr
  have hright : ((p : ℤ_[p]) ^ 4 ∣ W.c₆) ↔ CommRing.mod (p : ℤ_[p]) A₂ ^ 3
      = 27 * CommRing.mod (p : ℤ_[p]) A₆ := by
    rw [hdvd, ← CommRing.mod_eq_zero, hmod, (isUnit_mod_thirtyTwo hp).mul_right_eq_zero,
      sub_eq_zero]
  have hleft : (cubic (p : ℤ_[p]) W 1 1).HasDoubleRoot ↔ CommRing.mod (p : ℤ_[p]) A₂ ^ 3
      = 27 * CommRing.mod (p : ℤ_[p]) A₆ := by
    rw [cubic_one_one_eq_of_eq_mul hϖ h2 h4 h6, Cubic.hasDoubleRoot_of_a_eq_one rfl]
    exact hasDoubleRoot_algebra (isUnit_mod_twentySeven hp) htr
  rw [hleft, hright]

/-- **The `c₆`-quotient at Step 8.** On a curve with `p ∣ a₁`, `p² ∣ a₂`, `p² ∣ a₃`, `p³ ∣ a₄` and
`p⁴ ∣ a₆`, one has `p⁴ ∣ c₆` and `c₆/p⁴ ≡ -216((a₃/p²)² + 4a₆/p⁴) (mod p)`. -/
theorem exists_step8_c₆_quotient {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ A₆ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) ^ 2 * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 3 * A₄)
    (h6 : W.a₆ = (p : ℤ_[p]) ^ 4 * A₆) :
    ∃ Y : ℤ_[p], W.c₆ = (p : ℤ_[p]) ^ 4 * Y ∧ CommRing.mod (p : ℤ_[p]) Y
      = -216 * (CommRing.mod (p : ℤ_[p]) A₃ ^ 2 + 4 * CommRing.mod (p : ℤ_[p]) A₆) := by
  have hz : CommRing.mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 := CommRing.mod_self _
  refine ⟨-((p : ℤ_[p]) ^ 2 * (A₁ ^ 2 + 4 * A₂) ^ 3)
    + 36 * (p : ℤ_[p]) * (A₁ ^ 2 + 4 * A₂) * (2 * A₄ + A₁ * A₃)
    - 216 * (A₃ ^ 2 + 4 * A₆), ?_, ?_⟩
  · rw [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      h1, h2, h3, h4, h6]
    ring
  · simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, hz]
    ring

/-- **Step 8's double-root test is `p⁵ ∣ c₆`.** -/
theorem hasDoubleRoot_quadratic_two_iff (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ A₆ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) ^ 2 * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 3 * A₄)
    (h6 : W.a₆ = (p : ℤ_[p]) ^ 4 * A₆) :
    (quadratic (p : ℤ_[p]) W 2).HasDoubleRoot ↔ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨Y, hY, hYmod⟩ := exists_step8_c₆_quotient h1 h2 h3 h4 h6
  have hdvd : ((p : ℤ_[p]) ^ 5 ∣ W.c₆) ↔ (p : ℤ_[p]) ∣ Y := by
    rw [hY]; exact pow_succ_dvd_pow_mul hϖ 4
  have hu : IsUnit (-216 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) :=
    (isUnit_mod_twoHundredSixteen hp).neg
  rw [hdvd, ← CommRing.mod_eq_zero, hYmod, hu.mul_right_eq_zero,
    Cubic.hasDoubleRoot_of_b_eq_one (P := quadratic (p : ℤ_[p]) W 2) rfl rfl,
    quadratic_two_eq_of_eq_mul hϖ h3 h6]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Step 8's split test.** On a curve carrying Step 8's valuation whose `c₆` is `-864 p⁴ u`, Step
8's quadratic splits exactly when the residue of `u` is a square. -/
theorem splits_step8_quadratic_iff (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ A₆ u : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) ^ 2 * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 3 * A₄)
    (h6 : W.a₆ = (p : ℤ_[p]) ^ 4 * A₆) (hc₆ : W.c₆ = -864 * ((p : ℤ_[p]) ^ 4 * u)) :
    (quadratic (p : ℤ_[p]) W 2).toPoly.Splits ↔ IsSquare (PadicInt.toZMod u) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2' : (2 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≠ 0 := by
    rw [show (2 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = CommRing.mod (p : ℤ_[p]) 2 from by
      simp only [map_ofNat], Ne, CommRing.mod_eq_zero]
    exact not_dvd_two_of_odd hodd
  obtain ⟨Y, hY, hYmod⟩ := exists_step8_c₆_quotient h1 h2 h3 h4 h6
  have hYeq : Y = -864 * u :=
    mul_left_cancel₀ (pow_ne_zero 4 hϖ) (by rw [← hY, hc₆]; ring)
  have hdisc : CommRing.mod (p : ℤ_[p]) A₃ ^ 2 + 4 * CommRing.mod (p : ℤ_[p]) A₆
      = 4 * CommRing.mod (p : ℤ_[p]) u := by
    have hu : IsUnit (-216 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) :=
      (isUnit_mod_twoHundredSixteen hp).neg
    refine mul_left_cancel₀ hu.ne_zero ?_
    rw [← hYmod, hYeq]
    simp only [map_mul, map_neg, map_ofNat]
    ring
  rw [quadratic_two_eq_of_eq_mul hϖ h3 h6, Cubic.of_a_eq_zero rfl]
  dsimp only
  rw [splits_quadratic_iff_isSquare h2' (CommRing.mod (p : ℤ_[p]) A₃)
      (CommRing.mod (p : ℤ_[p]) A₆), hdisc, isSquare_four_mul_iff h2',
    isSquare_mod_iff_isSquare_toZMod]

/-! ### Steps 5–8 run forwards -/

/-- Steps 1–5 succeed on a short model with `p² ∣ a₄` and `p³ ∣ a₆`, returning the Step-2
translate. -/
theorem step5_run_eq_ok_of_dvd (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]} (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄)
    (h6 : (p : ℤ_[p]) ^ 3 ∣ a₆) :
    Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
  have h4' : (p : ℤ_[p]) ∣ a₄ := dvd_trans (dvd_pow_self _ two_ne_zero) h4
  have h6' : (p : ℤ_[p]) ^ 2 ∣ a₆ :=
    dvd_trans (pow_dvd_pow _ (by norm_num : 2 ≤ 3)) h6
  have hs3 := step3_run_eq_ok_of_dvd hp h4' h6'
  have hv3 := Step3.run_hasValuation hs3
  have hc₄ : (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₄ := by
    rw [Step2.translate_c₄, ofShortNF_c₄]; exact h4.mul_left _
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv3.b₂) hv3.b₆).2 hc₄)
  have hv4 := Step4.run_hasValuation PadicInt.uniformizer_ne_zero hs4
  have hc₆ : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₆ := by
    rw [Step2.translate_c₆, ofShortNF_c₆]; exact h6.mul_left _
  rw [Step5.run.eq_def, hs4]
  simp only [except_ok_bind]
  exact ite_eq_left ((cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv4.b₂) hv4.b₄).2 hc₆)

/-- Step 6 succeeds when its cubic has a double root, returning the Step-6 translate. -/
theorem step6_run_eq_ok_of_hasDoubleRoot {W W' : WeierstrassCurve ℤ_[p]}
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok W')
    (hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot) :
    Step6.run (p : ℤ_[p]) W = Except.ok (Step6.translate (p : ℤ_[p]) W') := by
  rw [Step6.run.eq_def, h5]
  simp only [except_ok_bind]
  exact ite_eq_left hd

/-- Step 7 succeeds without answering when the Step-6 cubic has a triple root. -/
theorem step7_run_eq_ok_of_hasTripleRoot {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h6 : Step6.run (p : ℤ_[p]) W = Except.ok W')
    (ht : (cubic (p : ℤ_[p]) W' 1 1).HasTripleRoot) :
    Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W' := by
  rw [Step7.run.eq_def]
  split
  next out' heq => exact absurd (h6.symm.trans heq) (by simp)
  next W'' heq =>
    obtain rfl : W'' = W' := Except.ok.inj (heq.symm.trans h6)
    exact dite_eq_left ht

open scoped Classical in
/-- Step 8 answers `IV*` when its quadratic has **no** double root. -/
theorem step8_run_eq_error_of_not_hasDoubleRoot {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W')
    (hq : ¬ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot) :
    Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error
      ⟨Step8.translate (p : ℤ_[p]) W', KodairaSymbol.IV!,
        if (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).toPoly.Splits then 3
          else 1⟩ := by
  rw [Step8.run.eq_def, h7]
  simp only [except_ok_bind]
  exact ite_eq_right hq

/-- An answer of Step 8 is the answer of Step 11. -/
theorem step11_error_of_step8 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) {out : Output ℤ_[p]}
    (h8 : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  have h9 : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step9.run.eq_def, h8]; rfl
  have h10 : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step10.run.eq_def, h9]; rfl
  rw [Step11.run.eq_def, h10]; rfl

open scoped Classical in
/-- **The forward run at `IV*`, from the invariants.** For every prime `p ≥ 5`, a curve over `ℤ_p`
on which Steps 1–5 succeed and whose invariants satisfy `p³ ∣ c₄` and `c₆ = -864 p⁴ u` with `p ∤ u`
has reduction datum

  `(IV*, 3)` if the residue of `u` is a square, and `(IV*, 1)` if it is not.
-/
theorem run_eq_IVstar_of_invariants (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok W') (hc₄ : (p : ℤ_[p]) ^ 3 ∣ W.c₄)
    {u : ℤ_[p]} (hu : ¬ (p : ℤ_[p]) ∣ u) (hc₆ : W.c₆ = -864 * ((p : ℤ_[p]) ^ 4 * u)) :
    (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV! ∧
      (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if IsSquare (PadicInt.toZMod u) then 3 else 1 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h864 : IsUnit (-864 : ℤ_[p]) := isUnit_neg_eightSixFour hp
  have hv5 := Step5.run_hasValuation hϖ h5
  have hv6 := Step6.hasValuation_translate hϖ hv5
  have e₄ : (Step6.translate (p : ℤ_[p]) W').c₄ = W.c₄ := by
    rw [Step6.translate_c₄, Step5.run_c₄ h5]
  have e₆ : (Step6.translate (p : ℤ_[p]) W').c₆ = W.c₆ := by
    rw [Step6.translate_c₆, Step5.run_c₆ h5]
  have hc₆4 : (p : ℤ_[p]) ^ 4 ∣ W.c₆ := ⟨-864 * u, by rw [hc₆]; ring⟩
  have hc₆5 : ¬ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
    rw [hc₆, show -864 * ((p : ℤ_[p]) ^ 4 * u) = (p : ℤ_[p]) ^ 4 * (-864 * u) from by ring,
      show (5 : ℕ) = 4 + 1 from rfl, pow_succ_dvd_pow_mul hϖ, h864.dvd_mul_left]
    exact hu
  obtain ⟨A₁, hA₁⟩ := hv6.a₁
  obtain ⟨A₂, hA₂⟩ := hv6.a₂
  obtain ⟨A₃, hA₃⟩ := hv6.a₃
  obtain ⟨A₄, hA₄⟩ := hv6.a₄
  obtain ⟨A₆, hA₆⟩ := hv6.a₆
  rw [pow_one] at hA₁ hA₂
  have ht : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasTripleRoot :=
    (hasTripleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆).2 (by rw [e₄]; exact hc₄)
  have hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot :=
    (hasDoubleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆ ht).2 (by rw [e₆]; exact hc₆4)
  have hs6 := step6_run_eq_ok_of_hasDoubleRoot h5 hd
  have hs7 := step7_run_eq_ok_of_hasTripleRoot hΔ hs6 ht
  have hv8 := Step8.hasValuation_translate hϖ hv6 hd ht
  obtain ⟨B₁, hB₁⟩ := hv8.a₁
  obtain ⟨B₂, hB₂⟩ := hv8.a₂
  obtain ⟨B₃, hB₃⟩ := hv8.a₃
  obtain ⟨B₄, hB₄⟩ := hv8.a₄
  obtain ⟨B₆, hB₆⟩ := hv8.a₆
  rw [pow_one] at hB₁
  have f₆ : (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')).c₆ = W.c₆ := by
    rw [Step8.translate_c₆, e₆]
  have hq : ¬ (quadratic (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')) 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff hp hB₁ hB₂ hB₃ hB₄ hB₆, f₆]
    exact hc₆5
  have hs8 := step8_run_eq_error_of_not_hasDoubleRoot hΔ hs7 hq
  have hsplit := splits_step8_quadratic_iff hp hB₁ hB₂ hB₃ hB₄ hB₆ (u := u) (by rw [f₆, hc₆])
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step8 hΔ hs8)]
  exact ⟨rfl, if_congr hsplit rfl rfl⟩

/-- A short model with `p³ ∣ a₄` and `a₆ = p⁴u`, `p ∤ u`, satisfies `p⁹ ∤ Δ`. -/
theorem not_pow_nine_dvd_ofShortNF_Δ_of_IVstar (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (h4 : (p : ℤ_[p]) ^ 3 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 4 ∣ a₆) (h6' : ¬ (p : ℤ_[p]) ^ 5 ∣ a₆) :
    ¬ (p : ℤ_[p]) ^ 9 ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨b, rfl⟩ := h6
  intro hd
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left] at hd
  have h1 : (p : ℤ_[p]) ^ 9 ∣ 4 * ((p : ℤ_[p]) ^ 3 * c) ^ 3 := ⟨4 * c ^ 3, by ring⟩
  have h2 : (p : ℤ_[p]) ^ 9 ∣ (p : ℤ_[p]) ^ 8 * (27 * b ^ 2) := by
    have hs := dvd_sub hd h1
    rwa [show 4 * ((p : ℤ_[p]) ^ 3 * c) ^ 3 + 27 * ((p : ℤ_[p]) ^ 4 * b) ^ 2
      - 4 * ((p : ℤ_[p]) ^ 3 * c) ^ 3 = (p : ℤ_[p]) ^ 8 * (27 * b ^ 2) from by ring] at hs
  obtain ⟨z, hz⟩ := h2
  have h3 : (p : ℤ_[p]) ∣ 27 * b ^ 2 :=
    ⟨z, mul_left_cancel₀ (pow_ne_zero 8 PadicInt.uniformizer_ne_zero) (by rw [hz]; ring)⟩
  rw [(isUnit_twentySeven hp).dvd_mul_left] at h3
  exact h6' (by rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ]
                exact mul_dvd_mul_left _ (PadicInt.prime_p.dvd_of_dvd_pow h3))

open scoped Classical in
/-- **The forward run at `IV*` on the short plane.** For every prime `p ≥ 5`, a short model over
`ℤ_p` with `p³ ∣ a₄` and `a₆ = p⁴u`, `p ∤ u`, has reduction datum

  `(IV*, 3)` if the residue of `u` is a square, and `(IV*, 1)` if it is not.
-/
theorem run_eq_IVstar_of_eq_sq_mul (hp : 5 ≤ p) {a₄ a₆ u : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ^ 3 ∣ a₄) (hu : ¬ (p : ℤ_[p]) ∣ u)
    (ha₆ : a₆ = (p : ℤ_[p]) ^ 4 * u) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if IsSquare (PadicInt.toZMod u) then 3 else 1 := by
  have h6 : (p : ℤ_[p]) ^ 4 ∣ a₆ := ⟨u, ha₆⟩
  have hs5 := step5_run_eq_ok_of_dvd hp (dvd_trans (pow_dvd_pow _ (by norm_num : 2 ≤ 3)) h4)
    (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 4)) h6)
  refine run_eq_IVstar_of_invariants hp hΔ hs5 ?_ hu ?_
  · rw [ofShortNF_c₄]; exact h4.mul_left _
  · rw [ofShortNF_c₆, ha₆]

/-! ### Only Step 8 answers `IV*`

An answer of `IV*` at Steps 1–11 forces `p³ ∣ c₄`, `p⁴ ∣ c₆` and `p⁵ ∤ c₆`, i.e. `v_p(a₄) ≥ 3` and
`v_p(a₆) = 4` on the short plane. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Steps 1–2 answer `Iₙ`, not `IV*`. -/
theorem Step2.kodairaSymbol_ne_IVstar (h : Step2.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.IV! := by
  obtain ⟨n, hn⟩ := Step2.exists_kodairaSymbol_eq_I h
  rw [hn]; simp

/-- Step 3 answers `II`, not `IV*`. -/
theorem Step3.kodairaSymbol_ne_IVstar (h : Step3.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.IV! := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_ne_IVstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 4 answers `III`, not `IV*`. -/
theorem Step4.kodairaSymbol_ne_IVstar (h : Step4.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.IV! := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_ne_IVstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 5 answers `IV`, not `IV*`. -/
theorem Step5.kodairaSymbol_ne_IVstar (h : Step5.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.IV! := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_ne_IVstar h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 6 answers `I₀*`, not `IV*`. -/
theorem Step6.kodairaSymbol_ne_IVstar (h : Step6.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.IV! := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_ne_IVstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- No answer of the `Iₙ*` subprocedure of Step 7 is `IV*`. -/
theorem Step7.subprocedure_kodairaSymbol_ne_IVstar (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.IV! := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 answers `Iₙ*`, not `IV*`. -/
theorem Step7.kodairaSymbol_ne_IVstar (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.IV! := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_ne_IVstar (heq.trans h)
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    apply Step7.subprocedure_kodairaSymbol_ne_IVstar

/-- **Step 8's answer `IV*` forces `p³ ∣ c₄`, `p⁴ ∣ c₆` and `p⁵ ∤ c₆`.** -/
theorem Step8.pow_dvd_c₄_c₆_of_eq_IVstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 4 ∣ W.c₆ ∧ ¬ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact absurd hκ (Step7.kodairaSymbol_ne_IVstar hΔ h)
  · have hv8 := Step8.hasValuation_translate hϖ (Step7.run_hasValuation hϖ hΔ h')
      (Step7.run_hasDoubleRoot hϖ hΔ h') (Step7.run_hasTripleRoot hϖ hΔ h')
    have e₄ : (Step8.translate (p : ℤ_[p]) W').c₄ = W.c₄ := by
      rw [Step8.translate_c₄, Step7.run_c₄ hϖ hΔ h']
    have e₆ : (Step8.translate (p : ℤ_[p]) W').c₆ = W.c₆ := by
      rw [Step8.translate_c₆, Step7.run_c₆ hϖ hΔ h']
    obtain ⟨B₁, hB₁⟩ := hv8.a₁
    obtain ⟨B₂, hB₂⟩ := hv8.a₂
    obtain ⟨B₃, hB₃⟩ := hv8.a₃
    obtain ⟨B₄, hB₄⟩ := hv8.a₄
    obtain ⟨B₆, hB₆⟩ := hv8.a₆
    dsimp only at hB₁ hB₂ hB₃ hB₄ hB₆
    rw [pow_one] at hB₁
    have hcon : ¬ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot := by
      intro hdr
      rw [ite_eq_left hdr] at h
      simp at h
    refine ⟨e₄ ▸ hv8.c₄, e₆ ▸ hv8.c₆, ?_⟩
    rw [← e₆, ← hasDoubleRoot_quadratic_two_iff hp hB₁ hB₂ hB₃ hB₄ hB₆]
    exact hcon

/-- Step 9 answers `III*`, not `IV*`. -/
theorem Step9.pow_dvd_c₄_c₆_of_eq_IVstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 4 ∣ W.c₆ ∧ ¬ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.pow_dvd_c₄_c₆_of_eq_IVstar hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 10 answers `II*`, not `IV*`. -/
theorem Step10.pow_dvd_c₄_c₆_of_eq_IVstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 4 ∣ W.c₆ ∧ ¬ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.pow_dvd_c₄_c₆_of_eq_IVstar hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `IV*` at Steps 1–11 forces `p³ ∣ c₄`, `p⁴ ∣ c₆` and `p⁵ ∤ c₆`.** -/
theorem Step11.pow_dvd_c₄_c₆_of_eq_IVstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.IV!) :
    (p : ℤ_[p]) ^ 3 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 4 ∣ W.c₆ ∧ ¬ (p : ℤ_[p]) ^ 5 ∣ W.c₆ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.pow_dvd_c₄_c₆_of_eq_IVstar hp hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The two `IV*` loci -/

variable (p) in
/-- The elements `a₆ = p⁴u` with `u` a unit whose residue **is** a square. -/
noncomputable def ivStarGoodSnd : Set ℤ_[p] :=
  PadicInt.scaleByPPow 4 '' (PadicInt.toZMod ⁻¹' (sqUnits p : Set (ZMod p)))

variable (p) in
/-- The elements `a₆ = p⁴u` with `u` a unit whose residue is **not** a square. -/
noncomputable def ivStarBadSnd : Set ℤ_[p] :=
  PadicInt.scaleByPPow 4 '' (PadicInt.toZMod ⁻¹' (nonSqUnits p : Set (ZMod p)))

variable (p) in
/-- The **split `IV*` locus**: `p³ ∣ a₄` and `a₆ = p⁴u` with `u` a unit of square residue. -/
noncomputable def ivStarSplitLocus : Set (ℤ_[p] × ℤ_[p]) :=
  ((Ideal.span {(p : ℤ_[p]) ^ 3} : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ ivStarGoodSnd p

variable (p) in
/-- The **non-split `IV*` locus**: `p³ ∣ a₄` and `a₆ = p⁴u` with `u` a unit of non-square
residue. -/
noncomputable def ivStarNonSplitLocus : Set (ℤ_[p] × ℤ_[p]) :=
  ((Ideal.span {(p : ℤ_[p]) ^ 3} : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ ivStarBadSnd p

/-- A pair lies in the split `IV*` locus iff `p³ ∣ a₄` and `a₆ = p⁴u` for a unit `u` whose
residue is a square. -/
theorem mem_ivStarSplitLocus_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ ivStarSplitLocus p ↔ (p : ℤ_[p]) ^ 3 ∣ x.1 ∧ ∃ u : ℤ_[p], ¬ (p : ℤ_[p]) ∣ u ∧
      IsSquare (PadicInt.toZMod u) ∧ x.2 = (p : ℤ_[p]) ^ 4 * u := by
  rw [ivStarSplitLocus, Set.mem_prod]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton, ivStarGoodSnd, Set.mem_image,
    Set.mem_preimage, mem_sqUnits_iff, PadicInt.scaleByPPow,
    ← PadicInt.dvd_iff_toZMod_eq_zero, ne_eq]
  constructor
  · rintro ⟨h1, u, ⟨hu0, husq⟩, hu2⟩
    exact ⟨h1, u, hu0, husq, hu2.symm⟩
  · rintro ⟨h1, u, hu, husq, hu2⟩
    exact ⟨h1, u, ⟨hu, husq⟩, hu2.symm⟩

/-- A pair lies in the non-split `IV*` locus iff `p³ ∣ a₄` and `a₆ = p⁴u` for a unit `u` whose
residue is not a square. -/
theorem mem_ivStarNonSplitLocus_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ ivStarNonSplitLocus p ↔ (p : ℤ_[p]) ^ 3 ∣ x.1 ∧ ∃ u : ℤ_[p], ¬ (p : ℤ_[p]) ∣ u ∧
      ¬ IsSquare (PadicInt.toZMod u) ∧ x.2 = (p : ℤ_[p]) ^ 4 * u := by
  rw [ivStarNonSplitLocus, Set.mem_prod]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton, ivStarBadSnd, Set.mem_image,
    Set.mem_preimage, mem_nonSqUnits_iff, PadicInt.scaleByPPow,
    ← PadicInt.dvd_iff_toZMod_eq_zero, ne_eq]
  constructor
  · rintro ⟨h1, u, ⟨hu0, husq⟩, hu2⟩
    exact ⟨h1, u, hu0, husq, hu2.symm⟩
  · rintro ⟨h1, u, hu, husq, hu2⟩
    exact ⟨h1, u, ⟨hu, husq⟩, hu2.symm⟩

/-- **The mass of the split `IV*` locus is `N p⁻⁸`**, i.e. `(p-1)/(2p⁸)`. -/
theorem volume_ivStarSplitLocus (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (ivStarSplitLocus p)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 8 := by
  have hz : (p : ℝ≥0∞) ^ (-((4 : ℕ) : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 4 :=
    (PadicInt.measure_span_pPow (p := p) 4).symm.trans (PadicInt.measure_span_pPow' 4)
  rw [ivStarSplitLocus, ivStarGoodSnd, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.measure_span_pPow' 3, PadicInt.measure_image_scaleByPPow,
    PadicInt.volume_preimage_toZMod_coe, card_sqUnits_eq_card_goodRes hp, hz]
  ring

/-- **The mass of the non-split `IV*` locus is `N p⁻⁸`**, i.e. `(p-1)/(2p⁸)`. -/
theorem volume_ivStarNonSplitLocus (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (ivStarNonSplitLocus p)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 8 := by
  have hz : (p : ℝ≥0∞) ^ (-((4 : ℕ) : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 4 :=
    (PadicInt.measure_span_pPow (p := p) 4).symm.trans (PadicInt.measure_span_pPow' 4)
  rw [ivStarNonSplitLocus, ivStarBadSnd, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.measure_span_pPow' 3, PadicInt.measure_image_scaleByPPow,
    PadicInt.volume_preimage_toZMod_coe, ← card_sqUnits_eq_card_nonSqUnits hp,
    card_sqUnits_eq_card_goodRes hp, hz]
  ring

/-- **The split `IV*` locus lies in the stratum `τ_p⁻¹((IV*, 3))`.** -/
theorem ivStarSplitLocus_subset_stratFibre (hp : 5 ≤ p) :
    ivStarSplitLocus p ⊆ stratFibre p (KodairaSymbol.IV!, 3) := by
  intro x hx
  obtain ⟨h4, u, hu, husq, h4eq⟩ := mem_ivStarSplitLocus_iff.1 hx
  have h6 : (p : ℤ_[p]) ^ 4 ∣ x.2 := ⟨u, h4eq⟩
  have h6' : ¬ (p : ℤ_[p]) ^ 5 ∣ x.2 := by
    rintro ⟨z, hz⟩
    exact hu ⟨z, mul_left_cancel₀ (pow_ne_zero 4 PadicInt.uniformizer_ne_zero)
      (by rw [← h4eq, hz]; ring)⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_nine_dvd_ofShortNF_Δ_of_IVstar hp h4 h6 h6' (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, hc⟩ := run_eq_IVstar_of_eq_sq_mul hp hΔ h4 hu h4eq
  rw [ite_eq_left husq] at hc
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-- **The non-split `IV*` locus lies in the stratum `τ_p⁻¹((IV*, 1))`.** -/
theorem ivStarNonSplitLocus_subset_stratFibre (hp : 5 ≤ p) :
    ivStarNonSplitLocus p ⊆ stratFibre p (KodairaSymbol.IV!, 1) := by
  intro x hx
  obtain ⟨h4, u, hu, husq, h4eq⟩ := mem_ivStarNonSplitLocus_iff.1 hx
  have h6 : (p : ℤ_[p]) ^ 4 ∣ x.2 := ⟨u, h4eq⟩
  have h6' : ¬ (p : ℤ_[p]) ^ 5 ∣ x.2 := by
    rintro ⟨z, hz⟩
    exact hu ⟨z, mul_left_cancel₀ (pow_ne_zero 4 PadicInt.uniformizer_ne_zero)
      (by rw [← h4eq, hz]; ring)⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_nine_dvd_ofShortNF_Δ_of_IVstar hp h4 h6 h6' (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, hc⟩ := run_eq_IVstar_of_eq_sq_mul hp hΔ h4 hu h4eq
  rw [ite_eq_right husq] at hc
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-! ### The minimal part of the two `IV*` strata -/

open scoped Classical in
/-- **The minimal part of an `IV*` stratum is a congruence locus.** For every prime `p ≥ 5`, a
point of `τ_p⁻¹((IV*, c))` which is not a `σ_p`-dilate has `p³ ∣ a₄` and `a₆ = p⁴u` with `p ∤ u`,
and `c` is `3` or `1` according as the residue of `u` is a square or not. -/
theorem exists_eq_sq_mul_of_mem_stratFibre_IVstar (hp : 5 ≤ p) {c : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hxF : x ∈ stratFibre p (KodairaSymbol.IV!, c))
    (hxR : x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :
    (p : ℤ_[p]) ^ 3 ∣ x.1 ∧ ∃ u : ℤ_[p], ¬ (p : ℤ_[p]) ∣ u ∧ x.2 = (p : ℤ_[p]) ^ 4 * u ∧
      c = if IsSquare (PadicInt.toZMod u) then 3 else 1 := by
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  have hs := (mem_stratFibre_iff hxUp).1 hxF
  rw [strat] at hs
  have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.IV! := congrArg Prod.fst hs
  have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = c := congrArg Prod.snd hs
  rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp with out' | W'
  · obtain ⟨h4, h6, h6'⟩ := TateAlgorithm.Step11.pow_dvd_c₄_c₆_of_eq_IVstar hp hxUp e
      (by rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
          exact hκ)
    rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4
    rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6
    rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6'
    obtain ⟨u, hu4⟩ := h6
    have hu : ¬ (p : ℤ_[p]) ∣ u := fun ⟨z, hz⟩ => h6' ⟨z, by rw [hu4, hz]; ring⟩
    obtain ⟨-, hcv⟩ := run_eq_IVstar_of_eq_sq_mul hp hxUp h4 hu hu4
    exact ⟨h4, u, hu, hu4, by rw [← hc, hcv]⟩
  · refine absurd (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩) hxR
    · have hd : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
        ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hd
    · have hd : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
        ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hd

open scoped Classical in
/-- **The minimal part of the stratum `τ_p⁻¹((IV*, 3))` is the split `IV*` locus**, for every prime
`p ≥ 5`:

  `τ_p⁻¹((IV*, 3)) ∖ σ_p(ℤ_p²) = {p³ ∣ a₄, a₆ = p⁴u, p ∤ u, u` a square mod `p}`.
-/
theorem stratFibre_diff_range_eq_ivStarSplitLocus (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.IV!, 3) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = ivStarSplitLocus p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    obtain ⟨h4, u, hu, hu4, hcv⟩ := exists_eq_sq_mul_of_mem_stratFibre_IVstar hp hxF hxR
    refine mem_ivStarSplitLocus_iff.2 ⟨h4, u, hu, ?_, hu4⟩
    by_contra hns
    rw [ite_eq_right hns] at hcv
    omega
  · intro x hx
    obtain ⟨h4, u, hu, husq, hu4⟩ := mem_ivStarSplitLocus_iff.1 hx
    refine ⟨ivStarSplitLocus_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨-, h6⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    obtain ⟨z, hz⟩ := h6
    exact hu ⟨(p : ℤ_[p]) * z, mul_left_cancel₀ (pow_ne_zero 4 PadicInt.uniformizer_ne_zero)
      (by rw [← hu4, hz]; ring)⟩

open scoped Classical in
/-- **The minimal part of the stratum `τ_p⁻¹((IV*, 1))` is the non-split `IV*` locus**, for every
prime `p ≥ 5`. -/
theorem stratFibre_diff_range_eq_ivStarNonSplitLocus (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.IV!, 1) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = ivStarNonSplitLocus p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    obtain ⟨h4, u, hu, hu4, hcv⟩ := exists_eq_sq_mul_of_mem_stratFibre_IVstar hp hxF hxR
    refine mem_ivStarNonSplitLocus_iff.2 ⟨h4, u, hu, ?_, hu4⟩
    intro hsq
    rw [ite_eq_left hsq] at hcv
    omega
  · intro x hx
    obtain ⟨h4, u, hu, husq, hu4⟩ := mem_ivStarNonSplitLocus_iff.1 hx
    refine ⟨ivStarNonSplitLocus_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨-, h6⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    obtain ⟨z, hz⟩ := h6
    exact hu ⟨(p : ℤ_[p]) * z, mul_left_cancel₀ (pow_ne_zero 4 PadicInt.uniformizer_ne_zero)
      (by rw [← hu4, hz]; ring)⟩

/-! ### The densities of the two `IV*` strata -/

/-- **The density of the split `IV*` stratum**, for every prime `p ≥ 5`:

  `δ_p((IV*, 3)) = N p⁻⁸ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)p²/(2(p¹⁰-1))`. -/
theorem deltaP_IVstar_three_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.IV!, 3)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 8 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_ivStarSplitLocus hp,
    volume_ivStarSplitLocus hp]

/-- **The density of the non-split `IV*` stratum**, for every prime `p ≥ 5`:

  `δ_p((IV*, 1)) = N p⁻⁸ (1 - p⁻¹⁰)⁻¹`.
-/
theorem deltaP_IVstar_one_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.IV!, 1)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 8 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_ivStarNonSplitLocus hp,
    volume_ivStarNonSplitLocus hp]

/-! ### A monic cubic never has exactly two roots without a repeated one

Two distinct roots `r ≠ s` of a monic cubic determine the third, `t = -b - r - s`, and the
discriminant is `((r-s)(r-t)(s-t))²`, which vanishes if `t` is one of `r`, `s`. -/

/-- **The discriminant of a monic cubic in terms of its three roots.** If `b = -(r+s+t)`,
`c = rs + rt + st` and `d = -rst` then `discr = ((r-s)(r-t)(s-t))²`. -/
theorem Cubic.discr_eq_of_root_data {K : Type*} [CommRing K] {P : Cubic K} {r s t : K}
    (ha : P.a = 1) (hb : P.b = -(r + s + t)) (hc : P.c = r * s + r * t + s * t)
    (hd : P.d = -(r * s * t)) : P.discr = ((r - s) * (r - t) * (s - t)) ^ 2 := by
  simp only [Cubic.discr, ha, hb, hc, hd]
  ring

/-- **A monic cubic over a field with exactly two distinct roots has vanishing discriminant.** -/
theorem Cubic.discr_eq_zero_of_card_roots_eq_two {K : Type*} [Field K] [DecidableEq K]
    {P : Cubic K} (ha : P.a = 1) (h : P.toPoly.roots.toFinset.card = 2) : P.discr = 0 := by
  have ha' : P.a ≠ 0 := ha ▸ one_ne_zero
  have h0 : P.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha'
  have heval : ∀ x : K, P.toPoly.eval x = P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d := by
    intro x
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
  obtain ⟨r, hrm, s, hsm, hrs⟩ :=
    Finset.one_lt_card.1 (by omega : 1 < P.toPoly.roots.toFinset.card)
  rw [Multiset.mem_toFinset] at hrm hsm
  have er : r ^ 3 + P.b * r ^ 2 + P.c * r + P.d = 0 := by
    have := heval r
    rw [(Polynomial.isRoot_of_mem_roots hrm : P.toPoly.eval r = 0), ha] at this
    linear_combination -this
  have es : s ^ 3 + P.b * s ^ 2 + P.c * s + P.d = 0 := by
    have := heval s
    rw [(Polynomial.isRoot_of_mem_roots hsm : P.toPoly.eval s = 0), ha] at this
    linear_combination -this
  obtain ⟨t, ht⟩ : ∃ t : K, t = -P.b - r - s := ⟨_, rfl⟩
  have hb : P.b = -(r + s + t) := by rw [ht]; ring
  have hc : P.c = r * s + r * t + s * t := by
    have key : (r - s) * (P.c - (r * s + r * t + s * t)) = 0 := by
      rw [ht]; linear_combination er - es
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd (sub_eq_zero.1 h') hrs
    · exact sub_eq_zero.1 h'
  have hd : P.d = -(r * s * t) := by linear_combination er - r ^ 2 * hb - r * hc
  have htm : t ∈ P.toPoly.roots := by
    refine Polynomial.mem_roots'.2 ⟨h0, ?_⟩
    rw [Polynomial.IsRoot, heval, ha, hb, hc, hd]
    ring
  have hsub : ({r, s} : Finset K) ⊆ P.toPoly.roots.toFinset := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact Multiset.mem_toFinset.2 hrm
    · rw [Finset.mem_singleton] at hx'
      exact hx' ▸ Multiset.mem_toFinset.2 hsm
  have heq : ({r, s} : Finset K) = P.toPoly.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [h, Finset.card_pair hrs])
  have htrs : t = r ∨ t = s := by
    have := (heq ▸ Multiset.mem_toFinset.2 htm : t ∈ ({r, s} : Finset K))
    simpa using this
  rw [Cubic.discr_eq_of_root_data ha hb hc hd]
  rcases htrs with h' | h'
  · rw [h']; ring
  · rw [h']; ring

open scoped Classical in
/-- **A monic cubic with no double root does not have exactly two distinct roots.** -/
theorem Cubic.card_roots_ne_two {K : Type*} [Field K] [DecidableEq K] {P : Cubic K}
    (ha : P.a = 1) (hd : ¬ P.HasDoubleRoot) : P.toPoly.roots.toFinset.card ≠ 2 :=
  fun h => hd (Cubic.discr_eq_zero_of_card_roots_eq_two ha h)

/-! ### Which Kodaira symbols can carry the Tamagawa number `3`

Only Step 2's split `I₃`, Step 5's `IV` and Step 8's `IV*` can report the Tamagawa number `3`. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Step 1 answers `(I₀, 1)`. -/
theorem Step1.kodairaSymbol_of_tamagawaNumber_eq_three
    (h : Step1.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  simp at hc

/-- Step 2 answers `Iₙ`, and `3` can only be its **split** value `n`, forcing `n = 3`. -/
theorem Step2.kodairaSymbol_of_tamagawaNumber_eq_three
    (h : Step2.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step1.kodairaSymbol_of_tamagawaNumber_eq_three h hc
  · have hb : ¬ (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W').b₂ := by
      intro hb'
      rw [ite_eq_left hb'] at h
      simp at h
    rw [ite_eq_right hb] at h
    obtain rfl := Except.error.inj h
    dsimp only at hc ⊢
    split_ifs at hc
    · exact Or.inl (congrArg KodairaSymbol.I hc)
    · simp at hc
    · simp at hc

/-- Step 3 answers `(II, 1)`. -/
theorem Step3.kodairaSymbol_of_tamagawaNumber_eq_three
    (h : Step3.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_of_tamagawaNumber_eq_three h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- Step 4 answers `(III, 2)`. -/
theorem Step4.kodairaSymbol_of_tamagawaNumber_eq_three
    (h : Step4.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_of_tamagawaNumber_eq_three h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- Step 5 answers `IV`. -/
theorem Step5.kodairaSymbol_of_tamagawaNumber_eq_three
    (h : Step5.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_of_tamagawaNumber_eq_three h hc
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Or.inr (Or.inl rfl)

open scoped Classical in
/-- **Step 6 answers `I₀*` with Tamagawa number `1 + #roots`, which is never `3`.** -/
theorem Step6.kodairaSymbol_of_tamagawaNumber_eq_three
    (h : Step6.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_of_tamagawaNumber_eq_three h hc
  · have hcon : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot := by
      intro hdr
      rw [ite_eq_left hdr] at h
      simp at h
    rw [ite_eq_right hcon] at h
    obtain rfl := Except.error.inj h
    have hne := Cubic.card_roots_ne_two
      (P := cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1) rfl hcon
    dsimp only at hc
    exact absurd hc (by omega)

/-- Every answer of the `Iₙ*` subprocedure of Step 7 reports `4` or `2`, never `3`. -/
theorem Step7.subprocedure_tamagawaNumber_ne_three (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber ≠ 3 := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => dsimp only; split_ifs <;> simp
  | case3 => dsimp only; split_ifs <;> simp

/-- Step 7 answers inside its `Iₙ*` subprocedure, whose Tamagawa numbers are `4` and `2`. -/
theorem Step7.kodairaSymbol_of_tamagawaNumber_eq_three (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq =>
    exact Step6.kodairaSymbol_of_tamagawaNumber_eq_three (heq.trans h) hc
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hc ?_
    apply Step7.subprocedure_tamagawaNumber_ne_three

/-- Step 8 answers `IV*`. -/
theorem Step8.kodairaSymbol_of_tamagawaNumber_eq_three (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_of_tamagawaNumber_eq_three hΔ h hc
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Or.inr (Or.inr rfl)

/-- Step 9 answers `(III*, 2)`. -/
theorem Step9.kodairaSymbol_of_tamagawaNumber_eq_three (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.kodairaSymbol_of_tamagawaNumber_eq_three hΔ h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- Step 10 answers `(II*, 1)`. -/
theorem Step10.kodairaSymbol_of_tamagawaNumber_eq_three (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.kodairaSymbol_of_tamagawaNumber_eq_three hΔ h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- **An answer of Tamagawa number `3` at Steps 1–11 has Kodaira symbol `I₃`, `IV` or `IV*`.** -/
theorem Step11.kodairaSymbol_of_tamagawaNumber_eq_three (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 3) :
    out.kodairaSymbol = KodairaSymbol.I 3 ∨ out.kodairaSymbol = KodairaSymbol.IV
      ∨ out.kodairaSymbol = KodairaSymbol.IV! := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.kodairaSymbol_of_tamagawaNumber_eq_three hΔ h hc
  · simp at h

/-- **Only `I₃`, `IV` and `IV*` carry the Tamagawa number `3`**, for every Weierstrass curve over
`ℤ_p` with `Δ ≠ 0`. -/
theorem run_kodairaSymbol_of_tamagawaNumber_eq_three {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) :
    (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 3 →
      (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 3 ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV! := by
  induction W, hΔ using run.induct PadicInt.uniformizer_ne_zero with
  | case1 W hΔ out h =>
    intro hc
    rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ h] at hc ⊢
    exact Step11.kodairaSymbol_of_tamagawaNumber_eq_three hΔ h hc
  | case2 W hΔ W' h ih =>
    intro hc
    have hΔ' : W'.Δ ≠ 0 := fun h0 =>
      hΔ (by rw [← Step11.run_Δ PadicInt.uniformizer_ne_zero hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ h hΔ'] at hc ⊢
    exact ih hc

end TateAlgorithm

/-! ### `δ_p(3)` exactly -/

/-- **The fibre `{c = 3}` is exactly the union of the three strata `(I₃, 3)`, `(IV, 3)`,
`(IV*, 3)`**, at every prime. -/
theorem iUnion_stratFibre_three_eq :
    (⋃ κ : KodairaSymbol, stratFibre p (κ, 3))
      = stratFibre p (KodairaSymbol.I 3, 3) ∪ stratFibre p (KodairaSymbol.IV, 3)
        ∪ stratFibre p (KodairaSymbol.IV!, 3) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨κ, hxκ⟩ := Set.mem_iUnion.1 hx
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxκ
    have hs := (mem_stratFibre_iff hUp).1 hxκ
    rw [strat] at hs
    have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 3 := congrArg Prod.snd hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = κ := congrArg Prod.fst hs
    rcases TateAlgorithm.run_kodairaSymbol_of_tamagawaNumber_eq_three hUp hc with h | h | h
    · exact Or.inl (Or.inl (by rw [hκ.symm.trans h] at hxκ; exact hxκ))
    · exact Or.inl (Or.inr (by rw [hκ.symm.trans h] at hxκ; exact hxκ))
    · exact Or.inr (by rw [hκ.symm.trans h] at hxκ; exact hxκ)
  · exact Set.union_subset (Set.union_subset
      (Set.subset_iUnion (fun κ => stratFibre p (κ, 3)) _)
      (Set.subset_iUnion (fun κ => stratFibre p (κ, 3)) _))
      (Set.subset_iUnion (fun κ => stratFibre p (κ, 3)) _)

/-- **`δ_p(3)` exactly, at every prime `p ≥ 5`:**

  `δ_p(3) = (2N² + N + N p⁻³) p⁻⁵ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

the sum of the densities of the strata `(I₃, 3)`, `(IV, 3)` and `(IV*, 3)`. In closed form this is
`(p-1)(p⁶ + p²)/(2(p¹⁰-1))`. -/
theorem δ_three_eq (hp : 5 ≤ p) :
    δ p 3 = tailConstant p * ((p : ℝ≥0∞)⁻¹) ^ 3
      + ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      + ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 8 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have hd1 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 3) (κ' := KodairaSymbol.IV) (by simp) 3 3
  have hd2 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 3) (κ' := KodairaSymbol.IV!) (by simp) 3 3
  have hd3 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.IV) (κ' := KodairaSymbol.IV!) (by simp) 3 3
  rw [← volume_iUnion_stratFibre_kodaira (p := p) 3, iUnion_stratFibre_three_eq,
    measure_union (hd2.union_left hd3)
      (isOpen_stratFibre (p := p) (KodairaSymbol.IV!, 3)).measurableSet,
    measure_union hd1 (isOpen_stratFibre (p := p) (KodairaSymbol.IV, 3)).measurableSet,
    volume_stratFibre, volume_stratFibre, volume_stratFibre, deltaP_IV_three_eq hp,
    deltaP_IVstar_three_eq hp,
    deltaP_I_eq_tailConstant_mul hp (stratScaleInvariant_of_five_le hp) le_rfl]

/-- **The closed form of `δ_p(3)` at `p ≥ 5`:**

  `δ_p(3) = p²(p⁴+1)/(2(p+1)(p⁸+p⁶+p⁴+p²+1))`,

i.e. `δ_p(3) = ENNReal.ofReal (gotδ p 3)`. -/
theorem δ_three_eq_ofReal_gotδ (hp : 5 ≤ p) : δ p 3 = ENNReal.ofReal (gotδ p 3) := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
  have hpos : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 := by
    rw [inv_pow, sub_pos]
    exact inv_lt_one_of_one_lt₀ h10
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  have hten : (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10
      = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinvE,
      ← ENNReal.ofReal_pow (by positivity)]
  have key : ∀ (c : ℝ) (k : ℕ), 0 ≤ c →
      ENNReal.ofReal c * ((p : ℝ≥0∞)⁻¹) ^ k * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
        = ENNReal.ofReal (c * ((p : ℝ)⁻¹) ^ k * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
    intro c k hc
    rw [hten, ← ENNReal.ofReal_inv_of_pos hpos, hinvE, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]
  have hNc : (2 : ℝ≥0∞) * (((goodRes p).card : ℕ) : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have hNc' := (ENNReal.ofReal_natCast (goodRes p).card).symm
  have hA : tailConstant p * ((p : ℝ≥0∞)⁻¹) ^ 3
      = ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 5
        * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
    rw [tailConstant, ← key _ 5 (by positivity), ← hNc]
    ring
  have hB : (((goodRes p).card : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      = ENNReal.ofReal ((((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 5
        * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
    rw [hNc']
    exact key _ 5 (by positivity)
  have hC : (((goodRes p).card : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 8
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      = ENNReal.ofReal ((((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 8
        * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
    rw [hNc']
    exact key _ 8 (by positivity)
  rw [δ_three_eq hp, hA, hB, hC, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  have hN : (((goodRes p).card : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
    have : (p : ℝ) = 2 * (((goodRes p).card : ℕ) : ℝ) + 1 := by
      exact_mod_cast eq_two_mul_card_goodRes_add_one (p := p) hp
    rw [this]
    ring
  have hfac : (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ = (p : ℝ) ^ 10 / ((p : ℝ) ^ 10 - 1) := by
    have h1 : (1 : ℝ) - ((p : ℝ)⁻¹) ^ 10 = ((p : ℝ) ^ 10 - 1) / (p : ℝ) ^ 10 := by
      rw [inv_pow]; field_simp
    rw [h1, inv_div]
  have hne10 : (p : ℝ) ^ 10 - 1 ≠ 0 := by linarith
  have hneQ : (p : ℝ) ^ 8 + (p : ℝ) ^ 6 + (p : ℝ) ^ 4 + (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  have hnep1 : (p : ℝ) + 1 ≠ 0 := by positivity
  rw [gotδ_three_of_five_le hp, hN, hfac]
  simp only [gotQ]
  field_simp
  ring

end WeierstrassCurve
