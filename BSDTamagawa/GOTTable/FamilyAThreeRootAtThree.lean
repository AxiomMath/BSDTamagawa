/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeHalvingAtThree

/-!
# The Hensel root and the two balls of a Family A fibre at `p = 3`

Let `a₄ = 3α` with `3 ∤ α`. When `3 ∣ 4α³ + a₆²` for some `a₆`, Hensel's lemma gives a square root
`ν` of `−4α³` in `ℤ₃`, and

  `4α³ + a₆² = (a₆ − ν)(a₆ + ν)`.

Since the difference `2ν` of the two factors is a unit, at most one factor is divisible by `3`: the
set of `a₆` with `3ⁿ ∣ 4α³ + a₆²` is the union of two disjoint balls of radius `3⁻ⁿ` around `±ν`.
The reflection `a₆ ↦ 2ν − a₆` maps the ball around `ν` onto itself at every depth.

## Main results

* `WeierstrassCurve.FamilyAThree.isSquare_neg_four_mul_cube`: `−4α³` is a square in `ℤ₃` whenever
  `3 ∤ α` and `3 ∣ 4α³ + a₆²`.
* `WeierstrassCurve.FamilyAThree.exists_sqrt_neg_four_mul_cube`: the same with the root named.
* `WeierstrassCurve.FamilyAThree.isUnit_two_mul_of_isUnit`: `2ν` is a unit at `3`.
* `WeierstrassCurve.FamilyAThree.factor_form`: `(a₆ − ν)(a₆ + ν) = 4α³ + a₆²`.
* `WeierstrassCurve.FamilyAThree.pow_dvd_sub_or_pow_dvd_add`: `3ⁿ ∣ 4α³ + a₆²` implies that `3ⁿ`
  divides one of `a₆ ∓ ν`.
* `WeierstrassCurve.FamilyAThree.reflect_pow_dvd_sub`: the reflection `a₆ ↦ 2ν − a₆` preserves the
  ball around `ν` at every depth.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.HeadDensityTwoBound

namespace FamilyAThree

/-! ### The Hensel square root of `−4α³` -/

/-- `−4α³` is a **unit** of `ℤ₃` when `3 ∤ α`: `−4` is a unit at every odd prime and `α` is one by
hypothesis. -/
theorem isUnit_neg_four_mul_cube {α : ℤ_[3]} (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α) :
    IsUnit (-(4 * α ^ 3) : ℤ_[3]) := by
  have hodd : Odd 3 := by decide
  have h4 : IsUnit (4 : ℤ_[3]) := by simpa using (PadicInt.isUnit_neg_four hodd).neg
  simpa using (h4.mul ((isUnit_of_not_dvd hα).pow 3)).neg

/-- **`−4α³` is a square in `ℤ₃`** whenever `3 ∤ α` and `3 ∣ 4α³ + a₆²`. -/
theorem isSquare_neg_four_mul_cube {α e : ℤ_[3]} (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α)
    (h : ((3 : ℕ) : ℤ_[3]) ∣ 4 * α ^ 3 + e ^ 2) : IsSquare (-(4 * α ^ 3) : ℤ_[3]) := by
  have hodd : Odd 3 := by decide
  rw [PadicInt.isSquare_iff_isSquare_toZMod hodd (isUnit_neg_four_mul_cube hα)]
  have he : PadicInt.toZMod (-(4 * α ^ 3) : ℤ_[3]) = (PadicInt.toZMod e) ^ 2 := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_add, map_mul, map_pow, map_pow, map_ofNat] at h
    rw [map_neg, map_mul, map_pow, map_ofNat]
    linear_combination -h
  rw [he]
  exact ⟨PadicInt.toZMod e, by ring⟩

/-- If `3 ∤ α` and `3 ∣ 4α³ + a₆²`, there is a unit `ν` of `ℤ₃` with `ν² = −4α³`. -/
theorem exists_sqrt_neg_four_mul_cube {α e : ℤ_[3]} (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α)
    (h : ((3 : ℕ) : ℤ_[3]) ∣ 4 * α ^ 3 + e ^ 2) :
    ∃ ν : ℤ_[3], ν * ν = -(4 * α ^ 3) ∧ IsUnit ν := by
  obtain ⟨ν, hν⟩ := isSquare_neg_four_mul_cube hα h
  refine ⟨ν, hν.symm, ?_⟩
  exact (isUnit_of_mul_isUnit_left (by rw [← hν]; exact isUnit_neg_four_mul_cube hα))

/-! ### The factorisation, and the two balls -/

/-- `2ν` is a unit of `ℤ₃` whenever `ν` is. -/
theorem isUnit_two_mul_of_isUnit {ν : ℤ_[3]} (hν : IsUnit ν) : IsUnit (2 * ν : ℤ_[3]) :=
  (PadicInt.isUnit_two (by decide)).mul hν

/-- **The factorisation** `(a₆ − ν)(a₆ + ν) = 4α³ + a₆²`, given `ν² = −4α³`. An exact identity in
`ℤ₃`. -/
theorem factor_form {α ν e : ℤ_[3]} (hν : ν * ν = -(4 * α ^ 3)) :
    (e - ν) * (e + ν) = 4 * α ^ 3 + e ^ 2 := by linear_combination -hν

/-- **The two balls.** If `3ⁿ` divides `4α³ + a₆²` then it divides one of `a₆ − ν`, `a₆ + ν` — the
whole power lands on a single factor, because the other factor is then a unit. -/
theorem pow_dvd_sub_or_pow_dvd_add {n : ℕ} {α ν e : ℤ_[3]} (hν : ν * ν = -(4 * α ^ 3))
    (hνu : IsUnit ν) (h : ((3 : ℕ) : ℤ_[3]) ^ n ∣ 4 * α ^ 3 + e ^ 2) :
    ((3 : ℕ) : ℤ_[3]) ^ n ∣ e - ν ∨ ((3 : ℕ) : ℤ_[3]) ^ n ∣ e + ν := by
  have hdiff : (e + ν) - (e - ν) = 2 * ν := by ring
  rw [← factor_form hν] at h
  by_cases hL : ((3 : ℕ) : ℤ_[3]) ∣ e - ν
  · refine Or.inl ((IsUnit.dvd_mul_right (isUnit_of_not_dvd fun hR => ?_)).mp h)
    exact PadicInt.dvd_iff_not_isUnit.mp (hdiff ▸ dvd_sub hR hL) (isUnit_two_mul_of_isUnit hνu)
  · exact Or.inr ((IsUnit.dvd_mul_left (isUnit_of_not_dvd hL)).mp h)

/-- **The reflection is an involution of each ball.** `a₆ ↦ 2ν − a₆` negates `a₆ − ν`, so it
preserves divisibility of `a₆ − ν` by any power of `3`, hence maps the ball around `ν` onto itself
at every depth. -/
theorem reflect_pow_dvd_sub {n : ℕ} {ν e : ℤ_[3]} :
    ((3 : ℕ) : ℤ_[3]) ^ n ∣ (2 * ν - e) - ν ↔ ((3 : ℕ) : ℤ_[3]) ^ n ∣ e - ν := by
  rw [show (2 * ν - e) - ν = -(e - ν) by ring, dvd_neg]

end FamilyAThree

end WeierstrassCurve

end
