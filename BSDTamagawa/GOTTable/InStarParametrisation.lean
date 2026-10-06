/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarSymmetryReduction

/-!
# Good coordinates for the positively-indexed `Iₙ*` family

The good coordinates are

  `goodPair p t C := ((-3) * p ^ 2 * t ^ 2, p ^ 3 * (2 * t ^ 3 + C))`,

with `t` a unit of `ℤ_p` and `p ∣ C`. Writing `A = a₄/p²` and `B = a₆/p³`, this is `A = -3t²` and
`B = 2t³ + C`: `t` is the double root of the cubic `T³ + AT + B`, and `C = B - 2t³` measures the
distance of the model from the cusp. The discriminant factorises as `Δ = -432 p⁶ · C · (4t³ + C)`
with `4t³ + C` a unit, so `v(Δ) - 6 = v(C)`.

## Main definitions

* `goodPair`: the good coordinates `(-3p²t², p³(2t³ + C))`.

## Main results

* `four_mul_cube_add_sq_goodPair`, `ofShortNF_goodPair_Δ`: the factorisation of `4a₄³ + 27a₆²` and
  of the discriminant.
* `isUnit_add_of_dvd`, `isUnit_four_mul_cube_add`: `4t³ + C` is a unit.
* `ofShortNF_goodPair_Δ_ne_zero_iff`, `goodPair_mem_nonsingularLocus_iff`: a good pair is
  nonsingular exactly when `C ≠ 0`.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable (p) in
/-- **The good coordinates** `(a₄, a₆) = (p²A, p³B)` with `A = -3t²` and `B = 2t³ + C`. -/
noncomputable def goodPair (t C : ℤ_[p]) : ℤ_[p] × ℤ_[p] :=
  ((-3) * (p : ℤ_[p]) ^ 2 * t ^ 2, (p : ℤ_[p]) ^ 3 * (2 * t ^ 3 + C))

/-- **The cuspidal defect factorises the discriminant.** For `(a₄, a₆) = goodPair p t C`,

  `4a₄³ + 27a₆² = 27 p⁶ · C · (4t³ + C)`,

from `4(-3t²)³ + 27(2t³ + C)² = 27C(4t³ + C)`. -/
theorem four_mul_cube_add_sq_goodPair (t C : ℤ_[p]) :
    4 * (goodPair p t C).1 ^ 3 + 27 * (goodPair p t C).2 ^ 2
      = 27 * (p : ℤ_[p]) ^ 6 * (C * (4 * t ^ 3 + C)) := by
  simp only [goodPair]
  ring

/-- **The discriminant in good coordinates**: `Δ = -16 · 27 p⁶ · C · (4t³ + C)`. -/
theorem ofShortNF_goodPair_Δ (t C : ℤ_[p]) :
    (ofShortNF (goodPair p t C).1 (goodPair p t C).2).Δ
      = -16 * (27 * (p : ℤ_[p]) ^ 6 * (C * (4 * t ^ 3 + C))) := by
  rw [ofShortNF_Δ, four_mul_cube_add_sq_goodPair]

/-- **A unit stays a unit after adding a multiple of `p`.** -/
theorem isUnit_add_of_dvd {u C : ℤ_[p]} (hu : IsUnit u) (hC : (p : ℤ_[p]) ∣ C) :
    IsUnit (u + C) :=
  PadicInt.isUnit_of_dvd_sub hu (by rwa [add_sub_cancel_left])

/-- **`4t³ + C` is a unit** whenever `t` is a unit and `p ∣ C`, at every prime `p ≥ 5`. -/
theorem isUnit_four_mul_cube_add (hp : 5 ≤ p) {t C : ℤ_[p]} (ht : IsUnit t)
    (hC : (p : ℤ_[p]) ∣ C) : IsUnit (4 * t ^ 3 + C) :=
  isUnit_add_of_dvd ((isUnit_four hp).mul (ht.pow 3)) hC

/-- **A good pair is nonsingular exactly when `C ≠ 0`**, at every prime `p ≥ 5` with `t` a unit and
`p ∣ C`: the other factors `-16`, `27 p⁶` and `4t³ + C` of the discriminant are nonzero. -/
theorem ofShortNF_goodPair_Δ_ne_zero_iff (hp : 5 ≤ p) {t C : ℤ_[p]} (ht : IsUnit t)
    (hC : (p : ℤ_[p]) ∣ C) :
    (ofShortNF (goodPair p t C).1 (goodPair p t C).2).Δ ≠ 0 ↔ C ≠ 0 := by
  have hu := isUnit_four_mul_cube_add hp ht hC
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  rw [ofShortNF_goodPair_Δ]
  exact ⟨fun hne hC0 ↦ hne (by simp [hC0]), fun hC0 ↦ mul_ne_zero (by norm_num)
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 6 hϖ)) (mul_ne_zero hC0 hu.ne_zero))⟩

/-- At every prime `p ≥ 5`, with `t` a unit and `p ∣ C`, the good pair `goodPair p t C` lies in
`nonsingularLocus p` exactly when `C ≠ 0`. -/
theorem goodPair_mem_nonsingularLocus_iff (hp : 5 ≤ p) {t C : ℤ_[p]} (ht : IsUnit t)
    (hC : (p : ℤ_[p]) ∣ C) : goodPair p t C ∈ nonsingularLocus p ↔ C ≠ 0 :=
  ofShortNF_goodPair_Δ_ne_zero_iff hp ht hC

end WeierstrassCurve
