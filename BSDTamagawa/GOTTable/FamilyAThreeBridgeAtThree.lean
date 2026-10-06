/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.TwistThreeAtThree

/-!
# The Tamagawa number of an `Iₘ*` curve at `p = 3` is a function of `Δ` and `c₆`

Step 7 of Tate's algorithm runs a loop whose two exits report the Tamagawa number as a square test
on a discriminant built from the coefficients of the current model. At `p = 3` the answer is
nonetheless a function of three invariants of the input model,

  `k := v₃(Δ)`,  `D := (Δ / 3^k) mod 3`,  `G := (c₆ / 27) mod 3`,

namely `c = 4 ↔ IsSquare (G^k · D)`; both `Δ` and `c₆` are invariant under the `u = 1` changes of
variables the loop performs.

## Main results

* `WeierstrassCurve.FamilyAThree.residue_two_ne_zero_three`,
  `WeierstrassCurve.FamilyAThree.residue_three_eq_zero`,
  `WeierstrassCurve.FamilyAThree.residue_sq_eq_one_three`,
  `WeierstrassCurve.FamilyAThree.residue_cube_eq_self_three`: the arithmetic of `𝔽₃` in the residue
  field of `ℤ_3`.
* `WeierstrassCurve.FamilyAThree.eq_of_pow_mul_eq_pow_mul_three`: the valuation and the unit part
  of a nonzero element of `ℤ_3` are unique.
* `WeierstrassCurve.FamilyAThree.exists_Δ_digit_Y`,
  `WeierstrassCurve.FamilyAThree.exists_c₆_digit`,
  `WeierstrassCurve.FamilyAThree.exists_Δ_digit_X`: the leading digits of `Δ` and `c₆` at a model
  of the loop.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_tamagawaNumber_eq_four_iff_three`: at `p = 3`
  the loop's Tamagawa number is `4` exactly when `G^k D` is a square.

## Implementation notes

At a level-`n` model of the loop, with `a₁ = 3A₁`, `a₂ = 3A₂`, `a₃ = 3ⁿA₃`, `a₄ = 3ⁿ⁺¹A₄`,
`a₆ = 3²ⁿA₆`,

  `Δ = 3^(2n+3) · (−A₂³ (A₃² + 4A₆) + 3 · w)`,   `c₆ = 27 · (−A₂³ + 3 · v)`;

and after the `Y`-translation, with `a₃ = 3ⁿ⁺¹A₃`, `a₄ = 3ⁿ⁺¹A₄`, `a₆ = 3²ⁿ⁺¹A₆`,

  `Δ = 3^(2n+4) · (A₂² (A₄² − 4A₂A₆) + 3 · w')`.

The bracketed leading terms are, up to the unit `A₂`, the discriminants the two exits test; since
`a³ = a` and `a² = 1` for `a ≠ 0` in `𝔽₃`, the exit test is `IsSquare (G^k D)` at both exits.
-/

@[expose] public section

open CommRing Ideal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

namespace FamilyAThree

/-! ### The arithmetic of `𝔽₃`, in the residue field of `ℤ_3` -/

/-- `2 ≠ 0` in the residue field of `ℤ_3`. -/
theorem residue_two_ne_zero_three :
    (2 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) ≠ 0 := by
  intro h
  have h' := congrArg (residueRingEquiv 3) h
  rw [map_ofNat, map_zero] at h'
  exact absurd h' (by decide)

/-- `3 = 0` in the residue field of `ℤ_3`. -/
theorem residue_three_eq_zero : (3 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 0 := by
  rw [← map_ofNat (mod ((3 : ℕ) : ℤ_[3])) 3, mod_eq_zero]
  exact ⟨1, by norm_num⟩

/-- A nonzero element of `𝔽₃` squares to `1`. -/
theorem residue_sq_eq_one_three {x : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}} (hx : x ≠ 0) :
    x ^ 2 = 1 := by
  apply (residueRingEquiv 3).injective
  rw [map_pow, map_one]
  have hx' : residueRingEquiv 3 x ≠ 0 :=
    fun h => hx ((residueRingEquiv 3).injective (h.trans (map_zero _).symm))
  revert hx'
  generalize residueRingEquiv 3 x = z
  revert z
  decide

/-- Frobenius is the identity on `𝔽₃`: `x³ = x`. -/
theorem residue_cube_eq_self_three (x : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) : x ^ 3 = x :=
  residue_pow_self (p := 3) x

/-! ### The valuation and the unit part are unique -/

/-- `ϖ ^ a ∣ ϖ ^ b * v` with `ϖ ∤ v` forces `a ≤ b`. -/
theorem le_of_pow_dvd_pow_mul_three {a b : ℕ} {v : ℤ_[3]} (hv : ¬ ((3 : ℕ) : ℤ_[3]) ∣ v)
    (h : ((3 : ℕ) : ℤ_[3]) ^ a ∣ ((3 : ℕ) : ℤ_[3]) ^ b * v) : a ≤ b := by
  by_contra hlt
  refine hv ((pow_succ_dvd_pow_mul PadicInt.uniformizer_ne_zero b).mp ?_)
  exact (pow_dvd_pow _ (by omega : b + 1 ≤ a)).trans h

/-- **The valuation and the unit part of a nonzero element of `ℤ_3` are unique.** -/
theorem eq_of_pow_mul_eq_pow_mul_three {a b : ℕ} {u v : ℤ_[3]} (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (hv : ¬ ((3 : ℕ) : ℤ_[3]) ∣ v)
    (h : ((3 : ℕ) : ℤ_[3]) ^ a * u = ((3 : ℕ) : ℤ_[3]) ^ b * v) : a = b ∧ u = v := by
  have hab : a = b := le_antisymm
    (le_of_pow_dvd_pow_mul_three hv (h ▸ dvd_mul_right _ _))
    (le_of_pow_dvd_pow_mul_three hu (h.symm ▸ dvd_mul_right _ _))
  subst hab
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero a PadicInt.uniformizer_ne_zero) h⟩

/-! ### The three identities -/

/-- **The `Δ`-digit at a level-`n` model of the loop**, with `Y = 3^(n−2)`. -/
theorem exists_Δ_digit_Y {V : WeierstrassCurve ℤ_[3]} {A₁ A₂ A₃ A₄ A₆ Y : ℤ_[3]}
    (h₁ : V.a₁ = 3 * A₁) (h₂ : V.a₂ = 3 * A₂) (h₃ : V.a₃ = 9 * Y * A₃)
    (h₄ : V.a₄ = 27 * Y * A₄) (h₆ : V.a₆ = 81 * Y ^ 2 * A₆) :
    ∃ w : ℤ_[3], V.Δ = 2187 * Y ^ 2 * (-(A₂ ^ 3 * (A₃ ^ 2 + 4 * A₆)) + 3 * w) := by
  refine ⟨-432 * A₆ ^ 2 * Y ^ 2 - 192 * A₄ ^ 3 * Y + 288 * A₂ * A₄ * A₆ * Y
    + 16 * A₂ ^ 2 * A₄ ^ 2 - 20 * A₂ ^ 3 * A₆ - 216 * A₃ ^ 2 * A₆ * Y ^ 2
    + 72 * A₂ * A₃ ^ 2 * A₄ * Y - 5 * A₂ ^ 3 * A₃ ^ 2 - 288 * A₁ * A₃ * A₄ ^ 2 * Y
    + 144 * A₁ * A₂ * A₃ * A₆ * Y + 16 * A₁ * A₂ ^ 2 * A₃ * A₄ + 216 * A₁ ^ 2 * A₄ * A₆ * Y
    + 24 * A₁ ^ 2 * A₂ * A₄ ^ 2 - 48 * A₁ ^ 2 * A₂ ^ 2 * A₆ - 27 * A₃ ^ 4 * Y ^ 2
    + 36 * A₁ * A₂ * A₃ ^ 3 * Y - 90 * A₁ ^ 2 * A₃ ^ 2 * A₄ * Y - 8 * A₁ ^ 2 * A₂ ^ 2 * A₃ ^ 2
    + 108 * A₁ ^ 3 * A₃ * A₆ * Y + 24 * A₁ ^ 3 * A₂ * A₃ * A₄ + 9 * A₁ ^ 4 * A₄ ^ 2
    - 36 * A₁ ^ 4 * A₂ * A₆ + 3 * A₁ ^ 3 * A₃ ^ 3 * Y - 3 * A₁ ^ 4 * A₂ * A₃ ^ 2
    + 9 * A₁ ^ 5 * A₃ * A₄ - 9 * A₁ ^ 6 * A₆, ?_⟩
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
  ring

/-- **The `c₆`-digit at a level-`n` model of the loop.** Only `a₁` and `a₂` enter to first
order. -/
theorem exists_c₆_digit {V : WeierstrassCurve ℤ_[3]} {A₁ A₂ A₃ A₄ A₆ Y : ℤ_[3]}
    (h₁ : V.a₁ = 3 * A₁) (h₂ : V.a₂ = 3 * A₂) (h₃ : V.a₃ = 9 * Y * A₃)
    (h₄ : V.a₄ = 27 * Y * A₄) (h₆ : V.a₆ = 81 * Y ^ 2 * A₆) :
    ∃ v : ℤ_[3], V.c₆ = 27 * (-(A₂ ^ 3) + 3 * v) := by
  refine ⟨-864 * A₆ * Y ^ 2 + 288 * A₂ * A₄ * Y - 21 * A₂ ^ 3 - 216 * A₃ ^ 2 * Y ^ 2
    + 144 * A₁ * A₂ * A₃ * Y + 216 * A₁ ^ 2 * A₄ * Y - 48 * A₁ ^ 2 * A₂ ^ 2
    + 108 * A₁ ^ 3 * A₃ * Y - 36 * A₁ ^ 4 * A₂ - 9 * A₁ ^ 6, ?_⟩
  simp only [WeierstrassCurve.c₆, b₂, b₄, b₆, h₁, h₂, h₃, h₄, h₆]
  ring

/-- **The `Δ`-digit after the `Y`-translation at level `n`**, with `Y = 3^(n−2)`. -/
theorem exists_Δ_digit_X {V : WeierstrassCurve ℤ_[3]} {A₁ A₂ A₃ A₄ A₆ Y : ℤ_[3]}
    (h₁ : V.a₁ = 3 * A₁) (h₂ : V.a₂ = 3 * A₂) (h₃ : V.a₃ = 27 * Y * A₃)
    (h₄ : V.a₄ = 27 * Y * A₄) (h₆ : V.a₆ = 243 * Y ^ 2 * A₆) :
    ∃ w : ℤ_[3], V.Δ = 6561 * Y ^ 2 * (A₂ ^ 2 * (A₄ ^ 2 - 4 * A₂ * A₆) + 3 * w) := by
  refine ⟨-1296 * A₆ ^ 2 * Y ^ 2 - 64 * A₄ ^ 3 * Y + 288 * A₂ * A₄ * A₆ * Y
    + 5 * A₂ ^ 2 * A₄ ^ 2 - 20 * A₂ ^ 3 * A₆ - 1944 * A₃ ^ 2 * A₆ * Y ^ 2
    + 216 * A₂ * A₃ ^ 2 * A₄ * Y - 16 * A₂ ^ 3 * A₃ ^ 2 - 288 * A₁ * A₃ * A₄ ^ 2 * Y
    + 432 * A₁ * A₂ * A₃ * A₆ * Y + 16 * A₁ * A₂ ^ 2 * A₃ * A₄ + 216 * A₁ ^ 2 * A₄ * A₆ * Y
    + 8 * A₁ ^ 2 * A₂ * A₄ ^ 2 - 48 * A₁ ^ 2 * A₂ ^ 2 * A₆ - 729 * A₃ ^ 4 * Y ^ 2
    + 324 * A₁ * A₂ * A₃ ^ 3 * Y - 270 * A₁ ^ 2 * A₃ ^ 2 * A₄ * Y
    - 24 * A₁ ^ 2 * A₂ ^ 2 * A₃ ^ 2 + 324 * A₁ ^ 3 * A₃ * A₆ * Y + 24 * A₁ ^ 3 * A₂ * A₃ * A₄
    + 3 * A₁ ^ 4 * A₄ ^ 2 - 36 * A₁ ^ 4 * A₂ * A₆ + 27 * A₁ ^ 3 * A₃ ^ 3 * Y
    - 9 * A₁ ^ 4 * A₂ * A₃ ^ 2 + 9 * A₁ ^ 5 * A₃ * A₄ - 9 * A₁ ^ 6 * A₆, ?_⟩
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
  ring

/-! ### Reading a digit off a `3 ∤ ·` unit part -/

/-- Division by the exact power that divides is exact. -/
theorem div_pow_mul_three (k : ℕ) (a : ℤ_[3]) :
    div ((((3 : ℕ) : ℤ_[3])) ^ k * a) ((((3 : ℕ) : ℤ_[3])) ^ k) = a :=
  mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-- Division by the uniformizer itself is exact. -/
theorem div_mul_three (a : ℤ_[3]) : div (((3 : ℕ) : ℤ_[3]) * a) ((3 : ℕ) : ℤ_[3]) = a :=
  mul_left_cancel₀ PadicInt.uniformizer_ne_zero
    (CommRing.mul_div PadicInt.uniformizer_ne_zero (Dvd.intro a rfl))

/-- The residue of `x + 3 * w` is the residue of `x`. -/
theorem mod_add_three_mul (x w : ℤ_[3]) :
    mod ((3 : ℕ) : ℤ_[3]) (x + 3 * w) = mod ((3 : ℕ) : ℤ_[3]) x := by
  rw [map_add, map_mul, map_ofNat, residue_three_eq_zero, zero_mul, add_zero]

/-- A residue is nonzero exactly when `3` does not divide. -/
theorem not_dvd_iff_mod_ne_zero (x : ℤ_[3]) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ x ↔ mod ((3 : ℕ) : ℤ_[3]) x ≠ 0 := by
  rw [ne_eq, mod_eq_zero]

/-! ### The invariant at the two exits -/

/-- **The invariant at the `Y`-exit**: at a level-`(m + 2)` model with `ḡ = −ā`, the square test
`G^k D` is the `Y`-exit's test `A₃² + 4A₆`. -/
theorem isSquare_pow_mul_iff_of_Δ_digit_Y {V : WeierstrassCurve ℤ_[3]} {A₁ A₂ A₃ A₄ A₆ g u : ℤ_[3]}
    {m k : ℕ} (h₁ : V.a₁ = 3 * A₁) (h₂ : V.a₂ = 3 * A₂) (h₃ : V.a₃ = 9 * 3 ^ m * A₃)
    (h₄ : V.a₄ = 27 * 3 ^ m * A₄) (h₆ : V.a₆ = 81 * (3 ^ m) ^ 2 * A₆)
    (hb : mod ((3 : ℕ) : ℤ_[3]) A₂ ≠ 0)
    (hdisc : mod ((3 : ℕ) : ℤ_[3]) A₃ ^ 2 + 4 * mod ((3 : ℕ) : ℤ_[3]) A₆ ≠ 0)
    (hΔk : V.Δ = ((3 : ℕ) : ℤ_[3]) ^ k * u) (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (hmodg : mod ((3 : ℕ) : ℤ_[3]) g = -mod ((3 : ℕ) : ℤ_[3]) A₂) :
    IsSquare (mod ((3 : ℕ) : ℤ_[3]) g ^ k * mod ((3 : ℕ) : ℤ_[3]) u) ↔
      IsSquare (mod ((3 : ℕ) : ℤ_[3]) A₃ ^ 2 + 4 * mod ((3 : ℕ) : ℤ_[3]) A₆) := by
  obtain ⟨w, hw⟩ := exists_Δ_digit_Y h₁ h₂ h₃ h₄ h₆
  have hEu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (-(A₂ ^ 3 * (A₃ ^ 2 + 4 * A₆)) + 3 * w) := by
    rw [not_dvd_iff_mod_ne_zero, mod_add_three_mul]
    simp only [map_neg, map_mul, map_pow, map_add, map_ofNat]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hb) hdisc)
  have hE : V.Δ = ((3 : ℕ) : ℤ_[3]) ^ (2 * m + 7) * (-(A₂ ^ 3 * (A₃ ^ 2 + 4 * A₆)) + 3 * w) := by
    rw [hw, show ((3 : ℕ) : ℤ_[3]) = 3 by norm_num]
    ring
  obtain ⟨rfl, rfl⟩ := eq_of_pow_mul_eq_pow_mul_three hu hEu (hΔk.symm.trans hE)
  rw [hmodg, mod_add_three_mul]
  simp only [map_neg, map_mul, map_pow, map_add, map_ofNat]
  refine iff_of_eq (congrArg _ ?_)
  have ha2 := residue_sq_eq_one_three hb
  rw [show 2 * m + 7 = 2 * (m + 3) + 1 by ring, pow_succ, pow_mul, neg_sq, ha2, one_pow, one_mul,
    residue_cube_eq_self_three]
  linear_combination (mod ((3 : ℕ) : ℤ_[3]) A₃ ^ 2 + 4 * mod ((3 : ℕ) : ℤ_[3]) A₆) * ha2

/-- **The invariant at the `X`-exit**: after the `Y`-translation of a level-`(m + 2)` model with
`ḡ = −ā`, the square test `G^k D` is the `X`-exit's test `A₄² − 4A₂A₆`. -/
theorem isSquare_pow_mul_iff_of_Δ_digit_X {V : WeierstrassCurve ℤ_[3]} {A₁ A₂ A₃ A₄ A₆ g u : ℤ_[3]}
    {m k : ℕ} (h₁ : V.a₁ = 3 * A₁) (h₂ : V.a₂ = 3 * A₂) (h₃ : V.a₃ = 27 * 3 ^ m * A₃)
    (h₄ : V.a₄ = 27 * 3 ^ m * A₄) (h₆ : V.a₆ = 243 * (3 ^ m) ^ 2 * A₆)
    (hb : mod ((3 : ℕ) : ℤ_[3]) A₂ ≠ 0)
    (hdisc : mod ((3 : ℕ) : ℤ_[3]) A₄ ^ 2
      - 4 * mod ((3 : ℕ) : ℤ_[3]) A₂ * mod ((3 : ℕ) : ℤ_[3]) A₆ ≠ 0)
    (hΔk : V.Δ = ((3 : ℕ) : ℤ_[3]) ^ k * u) (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (hmodg : mod ((3 : ℕ) : ℤ_[3]) g = -mod ((3 : ℕ) : ℤ_[3]) A₂) :
    IsSquare (mod ((3 : ℕ) : ℤ_[3]) g ^ k * mod ((3 : ℕ) : ℤ_[3]) u) ↔
      IsSquare (mod ((3 : ℕ) : ℤ_[3]) A₄ ^ 2
        - 4 * mod ((3 : ℕ) : ℤ_[3]) A₂ * mod ((3 : ℕ) : ℤ_[3]) A₆) := by
  obtain ⟨w, hw⟩ := exists_Δ_digit_X h₁ h₂ h₃ h₄ h₆
  have hEu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (A₂ ^ 2 * (A₄ ^ 2 - 4 * A₂ * A₆) + 3 * w) := by
    rw [not_dvd_iff_mod_ne_zero, mod_add_three_mul]
    simp only [map_mul, map_pow, map_sub, map_ofNat]
    exact mul_ne_zero (pow_ne_zero 2 hb) hdisc
  have hE : V.Δ = ((3 : ℕ) : ℤ_[3]) ^ (2 * (m + 4))
      * (A₂ ^ 2 * (A₄ ^ 2 - 4 * A₂ * A₆) + 3 * w) := by
    rw [hw, show ((3 : ℕ) : ℤ_[3]) = 3 by norm_num]
    ring
  obtain ⟨rfl, rfl⟩ := eq_of_pow_mul_eq_pow_mul_three hu hEu (hΔk.symm.trans hE)
  rw [hmodg, mod_add_three_mul]
  simp only [map_mul, map_pow, map_sub, map_ofNat]
  rw [pow_mul, neg_sq, residue_sq_eq_one_three hb, one_pow, one_mul, one_mul]

end FamilyAThree

/-! ### The two exits, read as square tests -/

/-- Completing the square: `bx² + cx + d` has a root exactly when `c² − 4bd` is a square. -/
private theorem exists_quadratic_root_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {b : K}
    (hb : b ≠ 0) (c d : K) :
    (∃ x : K, b * x ^ 2 + c * x + d = 0) ↔ IsSquare (c ^ 2 - 4 * b * d) := by
  refine ⟨fun ⟨x, hx⟩ => ⟨2 * b * x + c, by linear_combination (-4 * b) * hx⟩,
    fun ⟨s, hs⟩ => ⟨(s - c) / (2 * b), ?_⟩⟩
  field_simp
  linear_combination -hs

open scoped Classical in
/-- A nonzero `Cubic` record has a nonempty root `Finset` exactly when it has a root. -/
private theorem card_roots_toFinset_pos_iff_exists_root' {K : Type*} [Field K] {P : Cubic K}
    (hP : P.toPoly ≠ 0) :
    0 < P.roots.toFinset.card ↔ ∃ x : K, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [Finset.card_pos]
  refine ⟨fun ⟨x, hx⟩ => ⟨x, (Cubic.mem_roots_iff hP x).1 (Multiset.mem_toFinset.1 hx)⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact ⟨x, Multiset.mem_toFinset.2 ((Cubic.mem_roots_iff hP x).2 hx)⟩

open scoped Classical in
/-- A degenerate `Cubic` with `a = 0`, `b ≠ 0` has a root exactly when `c² − 4bd` is a square. -/
private theorem card_roots_toFinset_pos_iff_isSquare' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {P : Cubic K} (ha : P.a = 0) (hb : P.b ≠ 0) :
    0 < P.roots.toFinset.card ↔ IsSquare (P.c ^ 2 - 4 * P.b * P.d) := by
  rw [card_roots_toFinset_pos_iff_exists_root' (Cubic.ne_zero_of_b_ne_zero hb),
    ← exists_quadratic_root_iff' h2 hb P.c P.d]
  refine exists_congr fun x => ?_
  simp [ha]

namespace TateAlgorithm

open FamilyAThree

section Exits

variable (hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0) {W : WeierstrassCurve ℤ_[3]} (hΔ : W.Δ ≠ 0) {n : ℕ}
  (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
  (hW : HasValuation ((3 : ℕ) : ℤ_[3]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
  (ha₂ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ W.a₂)

open scoped Classical in
/-- The `Y`-exit at `p = 3`, with its root count resolved to a square test. -/
private theorem subprocedure_tamagawaNumber_of_not_hasDoubleRoot_three
    {c d : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}}
    (hquad : quadratic ((3 : ℕ) : ℤ_[3]) W n = ⟨0, 1, c, -d⟩)
    (hY : ¬ (quadratic ((3 : ℕ) : ℤ_[3]) W n).HasDoubleRoot) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
      = if IsSquare (c ^ 2 + 4 * d) then 4 else 2 := by
  have hiff : 0 < (quadratic ((3 : ℕ) : ℤ_[3]) W n).roots.toFinset.card
      ↔ IsSquare (c ^ 2 + 4 * d) := by
    rw [card_roots_toFinset_pos_iff_isSquare' residue_two_ne_zero_three
      (P := quadratic ((3 : ℕ) : ℤ_[3]) W n) (by rw [hquad]) (by rw [hquad]; exact one_ne_zero),
      hquad]
    dsimp only
    rw [show c ^ 2 - 4 * 1 * -d = c ^ 2 + 4 * d by ring]
  rw [Step7.subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY]
  exact if_congr hiff rfl rfl

open scoped Classical in
/-- The `X`-exit at `p = 3`, with its root count resolved to a square test. -/
private theorem subprocedure_tamagawaNumber_of_not_hasDoubleRoot_cubic_three
    {b c d : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}} (hb : b ≠ 0)
    (hcub : cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W n) 0 n = ⟨0, b, c, d⟩)
    (hY : (quadratic ((3 : ℕ) : ℤ_[3]) W n).HasDoubleRoot)
    (hX : ¬ (cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W n) 0 n).HasDoubleRoot) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
      = if IsSquare (c ^ 2 - 4 * b * d) then 4 else 2 := by
  have hiff : 0 < (cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W n) 0
      n).roots.toFinset.card ↔ IsSquare (c ^ 2 - 4 * b * d) := by
    rw [card_roots_toFinset_pos_iff_isSquare' residue_two_ne_zero_three
      (P := cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W n) 0 n)
      (by rw [hcub]) (by rw [hcub]; exact hb), hcub]
  rw [Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX]
  exact if_congr hiff rfl rfl

end Exits

/-- **The invariant at the `Y`-exit** of a level-`(m + 2)` model with `ḡ = −ā`. -/
theorem subprocedure_tamagawaNumber_eq_four_iff_three_of_Y_exit (hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0)
    {W : WeierstrassCurve ℤ_[3]} (hΔ : W.Δ ≠ 0) {m : ℕ} (hn : 2 ≤ m + 2)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation ((3 : ℕ) : ℤ_[3]) W
      ⟨1, 1, m + 2, m + 2 + 1, 2 * (m + 2), b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ W.a₂) {k : ℕ} {u g A₁ A₂ A₃ A₄ A₆ : ℤ_[3]}
    (hΔk : W.Δ = ((3 : ℕ) : ℤ_[3]) ^ k * u) (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (h₁ : W.a₁ = 3 * A₁) (h₂ : W.a₂ = 3 * A₂) (h₃ : W.a₃ = 9 * 3 ^ m * A₃)
    (h₄ : W.a₄ = 27 * 3 ^ m * A₄) (h₆ : W.a₆ = 81 * (3 ^ m) ^ 2 * A₆)
    (hA₃ : W.a₃ = ((3 : ℕ) : ℤ_[3]) ^ (m + 2) * A₃)
    (hA₆ : W.a₆ = ((3 : ℕ) : ℤ_[3]) ^ (2 * (m + 2)) * A₆)
    (hb : mod ((3 : ℕ) : ℤ_[3]) A₂ ≠ 0)
    (hmodg : mod ((3 : ℕ) : ℤ_[3]) g = -mod ((3 : ℕ) : ℤ_[3]) A₂)
    (hY : ¬ (quadratic ((3 : ℕ) : ℤ_[3]) W (m + 2)).HasDoubleRoot) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 4 ↔
      IsSquare (mod ((3 : ℕ) : ℤ_[3]) g ^ k * mod ((3 : ℕ) : ℤ_[3]) u) := by
  have hquad : quadratic ((3 : ℕ) : ℤ_[3]) W (m + 2)
      = ⟨0, 1, mod ((3 : ℕ) : ℤ_[3]) A₃, -mod ((3 : ℕ) : ℤ_[3]) A₆⟩ := by
    rw [quadratic, hA₃, hA₆, div_pow_mul_three, div_pow_mul_three]
  have hdisc : mod ((3 : ℕ) : ℤ_[3]) A₃ ^ 2 + 4 * mod ((3 : ℕ) : ℤ_[3]) A₆ ≠ 0 := by
    intro h
    apply hY
    rw [Cubic.hasDoubleRoot_of_b_eq_one (by rw [hquad]) (by rw [hquad]), hquad]
    dsimp only
    linear_combination h
  rw [subprocedure_tamagawaNumber_of_not_hasDoubleRoot_three hϖ hΔ hn hW ha₂ hquad hY,
    isSquare_pow_mul_iff_of_Δ_digit_Y h₁ h₂ h₃ h₄ h₆ hb hdisc hΔk hu hmodg]
  split_ifs with h <;> simpa using h

/-- **The invariant at the `X`-exit** of a level-`(m + 2)` model with `ḡ = −ā`. -/
theorem subprocedure_tamagawaNumber_eq_four_iff_three_of_X_exit (hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0)
    {W : WeierstrassCurve ℤ_[3]} (hΔ : W.Δ ≠ 0) {m : ℕ} (hn : 2 ≤ m + 2)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation ((3 : ℕ) : ℤ_[3]) W
      ⟨1, 1, m + 2, m + 2 + 1, 2 * (m + 2), b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ W.a₂) {k : ℕ} {u g A₁ A₂ : ℤ_[3]}
    (hΔk : W.Δ = ((3 : ℕ) : ℤ_[3]) ^ k * u) (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (h₁ : W.a₁ = 3 * A₁) (hA₂ : W.a₂ = ((3 : ℕ) : ℤ_[3]) * A₂)
    (hb : mod ((3 : ℕ) : ℤ_[3]) A₂ ≠ 0)
    (hmodg : mod ((3 : ℕ) : ℤ_[3]) g = -mod ((3 : ℕ) : ℤ_[3]) A₂)
    (hY : (quadratic ((3 : ℕ) : ℤ_[3]) W (m + 2)).HasDoubleRoot)
    (hX : ¬ (cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)) 0
      (m + 2)).HasDoubleRoot) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 4 ↔
      IsSquare (mod ((3 : ℕ) : ℤ_[3]) g ^ k * mod ((3 : ℕ) : ℤ_[3]) u) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hvY := Step7.hasValuation_translateY hn hϖ hW hY
  obtain ⟨A₃, hA₃⟩ := hvY.a₃
  obtain ⟨A₄, hA₄⟩ := hvY.a₄
  obtain ⟨A₆, hA₆⟩ := hvY.a₆
  have hVa₂ : (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)).a₂ = ((3 : ℕ) : ℤ_[3]) * A₂ := by
    rw [Step7.translateY_a₂, hA₂]
  have hcub : cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)) 0 (m + 2)
      = ⟨0, mod ((3 : ℕ) : ℤ_[3]) A₂, mod ((3 : ℕ) : ℤ_[3]) A₄, mod ((3 : ℕ) : ℤ_[3]) A₆⟩ := by
    rw [cubic, hVa₂, hA₄, hA₆, div_mul_three, div_pow_mul_three, div_pow_mul_three, map_zero]
  have hdisc : mod ((3 : ℕ) : ℤ_[3]) A₄ ^ 2
      - 4 * mod ((3 : ℕ) : ℤ_[3]) A₂ * mod ((3 : ℕ) : ℤ_[3]) A₆ ≠ 0 := by
    intro h
    apply hX
    rw [Cubic.hasDoubleRoot_of_a_eq_zero (by rw [hcub]), hcub]
    dsimp only
    linear_combination mod ((3 : ℕ) : ℤ_[3]) A₂ ^ 2 * h
  rw [subprocedure_tamagawaNumber_of_not_hasDoubleRoot_cubic_three hϖ hΔ hn hW ha₂ hb hcub hY hX,
    isSquare_pow_mul_iff_of_Δ_digit_X (V := Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2))
      (by rw [Step7.translateY_a₁, h₁]) (by rw [hVa₂, hcast]) (by rw [hA₃, hcast]; ring)
      (by rw [hA₄, hcast]; ring) (by rw [hA₆, hcast]; ring) hb hdisc
      (by rw [Step7.translateY_Δ, hΔk]) hu hmodg]
  split_ifs with h <;> simpa using h

/-! ### The invariant -/

/-- **At `p = 3` the Tamagawa number reported by Step 7's subprocedure is a function of `Δ` and
`c₆` alone**: writing `Δ = 3^k u` with `3 ∤ u` and `c₆ = 27 g`, the answer is `4` exactly when
`ḡ^k ū` is a square in `𝔽₃`. -/
theorem Step7.subprocedure_tamagawaNumber_eq_four_iff_three (hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0)
    {W : WeierstrassCurve ℤ_[3]} (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation ((3 : ℕ) : ℤ_[3]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ W.a₂) {k : ℕ} {u g : ℤ_[3]}
    (hΔk : W.Δ = ((3 : ℕ) : ℤ_[3]) ^ k * u) (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (hc₆ : W.c₆ = 27 * g) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 4 ↔
      IsSquare (mod ((3 : ℕ) : ℤ_[3]) g ^ k * mod ((3 : ℕ) : ℤ_[3]) u) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨A₁, hA₁⟩ := hW.a₁
  obtain ⟨A₂, hA₂⟩ := hW.a₂
  obtain ⟨A₃, hA₃⟩ := hW.a₃
  obtain ⟨A₄, hA₄⟩ := hW.a₄
  obtain ⟨A₆, hA₆⟩ := hW.a₆
  rw [pow_one] at hA₁ hA₂
  have hb : mod ((3 : ℕ) : ℤ_[3]) A₂ ≠ 0 := by
    rw [ne_eq, mod_eq_zero]
    intro h
    exact ha₂ (by rw [hA₂, pow_two]; exact mul_dvd_mul_left _ h)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h₁' : W.a₁ = 3 * A₁ := by rw [hA₁, hcast]
  have h₂' : W.a₂ = 3 * A₂ := by rw [hA₂, hcast]
  have h₃' : W.a₃ = 9 * 3 ^ m * A₃ := by rw [hA₃, hcast]; ring
  have h₄' : W.a₄ = 27 * 3 ^ m * A₄ := by rw [hA₄, hcast]; ring
  have h₆' : W.a₆ = 81 * (3 ^ m) ^ 2 * A₆ := by rw [hA₆, hcast]; ring
  obtain ⟨v, hv⟩ := exists_c₆_digit h₁' h₂' h₃' h₄' h₆'
  have hg : g = -(A₂ ^ 3) + 3 * v :=
    mul_left_cancel₀ (by norm_num : (27 : ℤ_[3]) ≠ 0) (hc₆.symm.trans hv)
  have hmodg : mod ((3 : ℕ) : ℤ_[3]) g = -mod ((3 : ℕ) : ℤ_[3]) A₂ := by
    rw [hg, mod_add_three_mul, map_neg, map_pow, residue_cube_eq_self_three]
  by_cases hY : (quadratic ((3 : ℕ) : ℤ_[3]) W (m + 2)).HasDoubleRoot
  · have hvY := Step7.hasValuation_translateY hn hϖ hW hY
    have ha₂Y : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)).a₂ :=
      Step7.not_dvd_translateY_a₂ _ ha₂
    by_cases hX : (cubic ((3 : ℕ) : ℤ_[3]) (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)) 0
        (m + 2)).HasDoubleRoot
    · have hvX := Step7.hasValuation_translateX hn hϖ hvY ha₂Y hX
      have ha₂X := Step7.not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y
      have hΔX : (Step7.translateX ((3 : ℕ) : ℤ_[3])
          (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)) (m + 2)).Δ ≠ 0 := by
        rwa [Step7.translateX_Δ, Step7.translateY_Δ]
      have hΔkX : (Step7.translateX ((3 : ℕ) : ℤ_[3])
          (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)) (m + 2)).Δ
            = ((3 : ℕ) : ℤ_[3]) ^ k * u := by
        rwa [Step7.translateX_Δ, Step7.translateY_Δ]
      have hc₆X : (Step7.translateX ((3 : ℕ) : ℤ_[3])
          (Step7.translateY ((3 : ℕ) : ℤ_[3]) W (m + 2)) (m + 2)).c₆ = 27 * g := by
        rwa [Step7.translateX_c₆, Step7.translateY_c₆]
      have hk : 2 * (m + 2) + 5 ≤ k := le_of_pow_dvd_pow_mul_three hu (hΔkX ▸ hvX.Δ)
      rw [Step7.subprocedure_eq_subprocedure hϖ hΔ hn hW ha₂ hY hX hΔX (Nat.le_succ_of_le hn)
        hvX ha₂X]
      exact Step7.subprocedure_tamagawaNumber_eq_four_iff_three hϖ hΔX (Nat.le_succ_of_le hn)
        hvX ha₂X hΔkX hu hc₆X
    · exact subprocedure_tamagawaNumber_eq_four_iff_three_of_X_exit hϖ hΔ hn hW ha₂ hΔk hu h₁' hA₂
        hb hmodg hY hX
  · exact subprocedure_tamagawaNumber_eq_four_iff_three_of_Y_exit hϖ hΔ hn hW ha₂ hΔk hu h₁' h₂'
      h₃' h₄' h₆' hA₃ hA₆ hb hmodg hY
termination_by k - n
decreasing_by omega

end TateAlgorithm

end WeierstrassCurve

end
