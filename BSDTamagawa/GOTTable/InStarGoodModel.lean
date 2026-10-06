/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityInStarForward
public import BSDTamagawa.NumberTheory.TateRunInvariance

/-!
# Step 7's subprocedure on the good `Iₘ*` model, and the `2`/`4` rule it produces

This file computes the run of `WeierstrassCurve.TateAlgorithm.Step7.subprocedure` in the *good
coordinates* of the positively-indexed `Iₘ*` family.

For `p ≥ 5`, that family is `v(a₄) = 2`, `v(a₆) = 3`, `4A³ + 27B² ≡ 0 (mod p)` with `A = a₄/p²` a
unit; the substitution `x ↦ x + pt` at the Hensel root `t` of `3t² + A = 0` carries the short model
to

  `goodModel t C = ⟨0, 3pt, 0, 0, p³C⟩`,      `C = B - 2t³`,

in which **`a₁`, `a₃` and `a₄` vanish exactly**, and `Δ = -432 p⁶ C (4t³ + C)` (`goodModel_Δ`) has
`v(Δ) = 6 + v(C)` because `4t³ + C` is a unit. With `m = v(C)` and `c₀ = C/p^m` a unit,
`Step7.subprocedure_goodModel` proves that the subprocedure entered at any level `n ≥ 2` with
`2n ≤ m + 3` returns

  Kodaira symbol `I!m`,   Tamagawa number `4` if `goodModelTest t c₀ m` is a square, else `2`,

where `goodModelTest t c₀ m` is the residue `4c₀` for odd `m` and `-12tc₀` for even `m` in the
residue field `ℤ_[p] ⧸ (p)`.

## Main definitions

* `goodModel`: the Weierstrass curve `⟨0, 3pt, 0, 0, p³C⟩` over `ℤ_[p]`.
* `goodModelTest`: the residue `4c₀` for odd `m` and `-12tc₀` for even `m`.

## Main results

* `goodModel_Δ`: the discriminant of `goodModel t C` is `-432 p⁶ C (4t³ + C)`.
* `TateAlgorithm.Step7.subprocedure_goodModel`: the subprocedure on the good model returns `I!m`,
  with Tamagawa number `4` or `2` according as `goodModelTest t c₀ m` is a square.
* `TateAlgorithm.Step7.subprocedure_goodModel_entry`: the case of the entry level `n = 2`.

## Implementation notes

At level `n` the `Y`-quadratic is `⟨0, 1, 0, -p^k c₀⟩` with `m + 3 = 2n + k`
(`Step7.quadratic_goodModel`), its middle coefficient `a₃/pⁿ` being `0` because `a₃ = 0` exactly;
it has no double root precisely when `k = 0`, i.e. `m = 2n - 3`. Otherwise `translateY` runs,
leaving `a₄` at `0` (`Step7.translateY_goodModel_a₄`: the term it would add is `-pⁿ tY · a₁` and
`a₁ = 0`) and moving `a₆` by `-(pⁿ tY)²`, of valuation `≥ 2n + 2`; so the `X`-cubic is
`⟨0, 3t, 0, p^k c₀⟩` with `m + 3 = 2n + 1 + k` (`Step7.cubic_translateY_goodModel`), with no double
root precisely when `k = 0`, i.e. `m = 2n - 2`.

Depth relations are stated in the additive form `m + 3 = 2n + k`, avoiding truncated subtraction.
-/

@[expose] public section

universe u

open CommRing Ideal

namespace WeierstrassCurve

/-! ### The residue of Step 7's `tY` -/

namespace TateAlgorithm.Step7

variable {R : Type u} [CommRing R] {ϖ : R} [(span {ϖ}).IsMaximal]

/-- In residue characteristic `≠ 2`, the residue of `Step7.tY` is the double root `-c/2` of the
`Y`-quadratic. -/
theorem mod_tY (V : WeierstrassCurve R) (n : ℕ) (h2 : (2 : R ⧸ span {ϖ}) ≠ 0) :
    mod ϖ (tY ϖ V n) = -(quadratic ϖ V n).c / 2 := by
  rw [tY, dite_eq_right h2]
  exact mod_out _

end TateAlgorithm.Step7

/-! ### The good model -/

variable {p : ℕ} [Fact p.Prime]

/-- **The good `Iₘ*` model** `V(t, C) = ⟨0, 3pt, 0, 0, p³C⟩` over `ℤ_[p]`. It is the image of the
short model `y² = x³ + p²A x + p³B` under `x ↦ x + pt` for the root `t` of `3t² + A = 0`. -/
noncomputable def goodModel (t C : ℤ_[p]) : WeierstrassCurve ℤ_[p] :=
  ⟨0, 3 * (p : ℤ_[p]) * t, 0, 0, (p : ℤ_[p]) ^ 3 * C⟩

/-- The coefficient `a₁` of the good model is `0`. -/
@[simp] theorem goodModel_a₁ (t C : ℤ_[p]) : (goodModel t C).a₁ = 0 := rfl
/-- The coefficient `a₂` of the good model is `3pt`. -/
@[simp] theorem goodModel_a₂ (t C : ℤ_[p]) : (goodModel t C).a₂ = 3 * (p : ℤ_[p]) * t := rfl
/-- The coefficient `a₃` of the good model is `0`. -/
@[simp] theorem goodModel_a₃ (t C : ℤ_[p]) : (goodModel t C).a₃ = 0 := rfl
/-- The coefficient `a₄` of the good model is `0`. -/
@[simp] theorem goodModel_a₄ (t C : ℤ_[p]) : (goodModel t C).a₄ = 0 := rfl
/-- The coefficient `a₆` of the good model is `p³C`. -/
@[simp] theorem goodModel_a₆ (t C : ℤ_[p]) : (goodModel t C).a₆ = (p : ℤ_[p]) ^ 3 * C := rfl

/-- **The discriminant of the good model** is `-432 p⁶ C (4t³ + C)`. -/
theorem goodModel_Δ (t C : ℤ_[p]) :
    (goodModel t C).Δ = -432 * (p : ℤ_[p]) ^ 6 * C * (4 * t ^ 3 + C) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, goodModel_a₁, goodModel_a₂, goodModel_a₃, goodModel_a₄, goodModel_a₆]
  ring

/-- The residue of `ℤ_[p]` whose square class decides the Tamagawa number of the good model: `4c₀`
at odd depth `m`, `-12tc₀` at even depth. -/
noncomputable def goodModelTest (t c0 : ℤ_[p]) (m : ℕ) : ℤ_[p] ⧸ span {(p : ℤ_[p])} :=
  if Odd m then mod (p : ℤ_[p]) (4 * c0) else mod (p : ℤ_[p]) (-12 * t * c0)

/-! ### Units and residues at `p ≥ 5` -/

/-- Exact division recognises a factorisation. -/
private theorem div_eq_of_eq {q x y : ℤ_[p]} (hq : q ≠ 0) (h : x = q * y) : div x q = y :=
  mul_left_cancel₀ hq (by rw [mul_div hq ⟨y, h⟩, h])

/-- A `p`-adic integer not divisible by `p` is a unit. -/
private theorem isUnit_of_not_dvd {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) : IsUnit a :=
  not_not.1 fun h => ha (PadicInt.dvd_iff_not_isUnit.2 h)

/-- `2` is invertible in the residue field of `ℤ_[p]` for `p ≥ 5`. -/
private theorem residue_two_ne_zero (hp : 5 ≤ p) : (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ 0 := by
  have h := ((PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))).map
    (mod (p : ℤ_[p]))).ne_zero
  rwa [map_ofNat] at h

/-- `4` is invertible in the residue field of `ℤ_[p]` for `p ≥ 5`. -/
private theorem residue_four_ne_zero (hp : 5 ≤ p) : (4 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ≠ 0 := by
  have h := ((isUnit_four hp).map (mod (p : ℤ_[p]))).ne_zero
  rwa [map_ofNat] at h

/-- For `p ≥ 5` and `t` a unit, the residue of `3t` is nonzero. -/
private theorem residue_three_mul_ne_zero (hp : 5 ≤ p) {t : ℤ_[p]} (ht : ¬ (p : ℤ_[p]) ∣ t) :
    mod (p : ℤ_[p]) (3 * t) ≠ 0 := by
  rw [Ne, mod_eq_zero]
  exact fun h => (PadicInt.dvd_iff_not_isUnit.1 h) ((PadicInt.isUnit_three hp).mul
    (isUnit_of_not_dvd ht))

/-! ### The state the good model presents to Step 7 -/

/-- **The good model carries the subprocedure's level-`n` valuations** as soon as `2n ≤ m + 3`,
where `a₆ = p^{m+3}c₀`, with the valuations of `b₂, …, Δ` recorded as `0`. -/
theorem hasValuation_goodModel (t c0 : ℤ_[p]) {m n k : ℕ} (hk : m + 3 = 2 * n + k) :
    TateAlgorithm.HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0))
      ⟨1, 1, n, n + 1, 2 * n, 0, 0, 0, 0, 0, 0, 0⟩ where
  a₁ := by simp
  a₂ := ⟨3 * t, by rw [goodModel_a₂, pow_one]; ring⟩
  a₃ := by simp
  a₄ := by simp
  a₆ := ⟨(p : ℤ_[p]) ^ k * c0, by
    rw [goodModel_a₆, ← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add,
      show 3 + m = 2 * n + k from by omega]⟩
  b₂ := by simp
  b₄ := by simp
  b₆ := by simp
  b₈ := by simp
  c₄ := by simp
  c₆ := by simp
  Δ := by simp

/-- For `p ≥ 5` and `t` a unit, `p²` does not divide the coefficient `a₂ = 3pt` of the good
model. -/
theorem not_sq_dvd_goodModel_a₂ (hp : 5 ≤ p) {t C : ℤ_[p]} (ht : ¬ (p : ℤ_[p]) ∣ t) :
    ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t C).a₂ := by
  rw [goodModel_a₂]
  rintro ⟨x, hx⟩
  refine (PadicInt.dvd_iff_not_isUnit.1 ⟨x, ?_⟩)
    ((PadicInt.isUnit_three hp).mul (isUnit_of_not_dvd ht))
  rw [pow_two] at hx
  exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero (by linear_combination hx)

/-- For `p ≥ 5`, `t` and `c₀` units and `m ≥ 1`, the discriminant of `goodModel t (p^m c₀)` is
nonzero. -/
theorem goodModel_Δ_ne_zero (hp : 5 ≤ p) {t c0 : ℤ_[p]} (ht : ¬ (p : ℤ_[p]) ∣ t)
    (hc0 : ¬ (p : ℤ_[p]) ∣ c0) {m : ℕ} (hm : 1 ≤ m) :
    (goodModel t ((p : ℤ_[p]) ^ m * c0)).Δ ≠ 0 := by
  have h432 : IsUnit (-432 : ℤ_[p]) := by
    refine IsUnit.neg ?_
    rw [show (432 : ℤ_[p]) = 16 * 27 from by norm_num]
    exact (isUnit_sixteen hp).mul (isUnit_twentySeven hp)
  have hC : ((p : ℤ_[p]) ^ m * c0) ≠ 0 :=
    mul_ne_zero (pow_ne_zero m PadicInt.uniformizer_ne_zero)
      (isUnit_of_not_dvd hc0).ne_zero
  have hlast : (4 * t ^ 3 + (p : ℤ_[p]) ^ m * c0) ≠ 0 := by
    refine (isUnit_of_not_dvd fun h => ?_).ne_zero
    refine (PadicInt.dvd_iff_not_isUnit.1 ?_) ((isUnit_four hp).mul ((isUnit_of_not_dvd ht).pow 3))
    obtain ⟨y, hy⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact ⟨y - (p : ℤ_[p]) ^ j * c0, by rw [pow_succ] at hy; linear_combination hy⟩
  rw [goodModel_Δ]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h432.ne_zero
    (pow_ne_zero 6 PadicInt.uniformizer_ne_zero)) hC) hlast

/-! ### Step 7's two tests on the good model -/

namespace TateAlgorithm.Step7

/-- **The level-`n` `Y`-quadratic of the good model is `⟨0, 1, 0, -p^k c₀⟩`**, where
`m + 3 = 2n + k`. -/
theorem quadratic_goodModel (t c0 : ℤ_[p]) {m n k : ℕ} (hk : m + 3 = 2 * n + k) :
    quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n
      = ⟨0, 1, 0, -mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ k * c0)⟩ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h3 : div (goodModel t ((p : ℤ_[p]) ^ m * c0)).a₃ ((p : ℤ_[p]) ^ n) = 0 :=
    div_eq_of_eq (pow_ne_zero n hϖ) (by simp)
  have h6 : div (goodModel t ((p : ℤ_[p]) ^ m * c0)).a₆ ((p : ℤ_[p]) ^ (2 * n))
      = (p : ℤ_[p]) ^ k * c0 :=
    div_eq_of_eq (pow_ne_zero _ hϖ) (by
      rw [goodModel_a₆, ← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add,
        show 3 + m = 2 * n + k from by omega])
  rw [quadratic, h3, h6]
  simp

/-- For `p ≥ 5`, `p` divides `Step7.tY` of the good model at any level `n` with `2n ≤ m + 3`. -/
theorem dvd_tY_goodModel (hp : 5 ≤ p) (t c0 : ℤ_[p]) {m n k : ℕ} (hk : m + 3 = 2 * n + k) :
    (p : ℤ_[p]) ∣ tY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n := by
  rw [← mod_eq_zero, mod_tY _ _ (residue_two_ne_zero hp), quadratic_goodModel t c0 hk]
  simp

/-- The coefficient `a₂` of `translateY` of the good model is `3pt`. -/
theorem translateY_goodModel_a₂ (t C : ℤ_[p]) (n : ℕ) :
    (translateY (p : ℤ_[p]) (goodModel t C) n).a₂ = 3 * (p : ℤ_[p]) * t := by
  simp only [translateY, smulOne_a₂, goodModel_a₁, goodModel_a₂]
  ring

/-- The coefficient `a₄` of `translateY` of the good model is `0`. -/
theorem translateY_goodModel_a₄ (t C : ℤ_[p]) (n : ℕ) :
    (translateY (p : ℤ_[p]) (goodModel t C) n).a₄ = 0 := by
  simp only [translateY, smulOne_a₄, goodModel_a₁, goodModel_a₂, goodModel_a₃, goodModel_a₄]
  ring

/-- The coefficient `a₆` of `translateY` of the good model is `p³C - (pⁿ tY)²`. -/
theorem translateY_goodModel_a₆ (t C : ℤ_[p]) (n : ℕ) :
    (translateY (p : ℤ_[p]) (goodModel t C) n).a₆
      = (p : ℤ_[p]) ^ 3 * C - ((p : ℤ_[p]) ^ n * tY (p : ℤ_[p]) (goodModel t C) n) ^ 2 := by
  simp only [translateY, smulOne_a₆, goodModel_a₁, goodModel_a₂, goodModel_a₃, goodModel_a₄,
    goodModel_a₆]
  ring

/-- **The level-`n` `X`-cubic of the translated good model is `⟨0, 3t, 0, p^k c₀⟩`**, where
`m + 3 = 2n + 1 + k` and `p ≥ 5`. -/
theorem cubic_translateY_goodModel (hp : 5 ≤ p) (t c0 : ℤ_[p]) {m n k : ℕ}
    (hk : m + 3 = 2 * n + 1 + k) :
    cubic (p : ℤ_[p]) (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n) 0 n
      = ⟨0, mod (p : ℤ_[p]) (3 * t), 0, mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ k * c0)⟩ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨τ, hτ⟩ := dvd_tY_goodModel hp t c0 (m := m) (n := n) (k := k + 1) (by omega)
  have h2 : div (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n).a₂
      (p : ℤ_[p]) = 3 * t :=
    div_eq_of_eq hϖ (by rw [translateY_goodModel_a₂]; ring)
  have h4 : div (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n).a₄
      ((p : ℤ_[p]) ^ (n + 1)) = 0 :=
    div_eq_of_eq (pow_ne_zero _ hϖ) (by rw [translateY_goodModel_a₄]; ring)
  have h6 : div (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n).a₆
      ((p : ℤ_[p]) ^ (2 * n + 1)) = (p : ℤ_[p]) ^ k * c0 - (p : ℤ_[p]) * τ ^ 2 := by
    refine div_eq_of_eq (pow_ne_zero _ hϖ) ?_
    rw [translateY_goodModel_a₆, hτ]
    have e1 : ((p : ℤ_[p]) ^ n * ((p : ℤ_[p]) * τ)) ^ 2
        = (p : ℤ_[p]) ^ (2 * n + 1) * ((p : ℤ_[p]) * τ ^ 2) := by
      rw [mul_pow, mul_pow, ← pow_mul, show n * 2 = 2 * n from Nat.mul_comm n 2, pow_add]
      ring
    have e2 : (p : ℤ_[p]) ^ 3 * ((p : ℤ_[p]) ^ m * c0)
        = (p : ℤ_[p]) ^ (2 * n + 1) * ((p : ℤ_[p]) ^ k * c0) := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add, show 3 + m = 2 * n + 1 + k from by omega]
    rw [e1, e2]
    ring
  have hmod : mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ k * c0 - (p : ℤ_[p]) * τ ^ 2)
      = mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ k * c0) := by
    rw [map_sub, show mod (p : ℤ_[p]) ((p : ℤ_[p]) * τ ^ 2) = 0 from
      (mod_eq_zero _ _).2 (dvd_mul_right _ _), sub_zero]
  rw [cubic, h2, h4, h6, hmod]
  simp

/-- For `p ≥ 5`, `p` divides `Step7.rX` of the translated good model at any level `n` with
`2n + 1 ≤ m + 3`. -/
theorem dvd_rX_translateY_goodModel (hp : 5 ≤ p) (t c0 : ℤ_[p]) {m n k : ℕ}
    (hk : m + 3 = 2 * n + 1 + k) :
    (p : ℤ_[p]) ∣ rX (p : ℤ_[p]) (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n)
      n := by
  rw [← mod_eq_zero, mod_rX _ _ (residue_two_ne_zero hp), cubic_translateY_goodModel hp t c0 hk]
  simp

/-- Applying `translateY` and then `translateX` at level `n` to the good model `V(t, C)` gives
the change of variables `⟨1, pⁿ rX, 0, pⁿ tY⟩` applied to `V(t, C)`. -/
theorem translateX_translateY_goodModel (t C : ℤ_[p]) (n : ℕ) :
    translateX (p : ℤ_[p]) (translateY (p : ℤ_[p]) (goodModel t C) n) n
      = (VariableChange.mk 1
          ((p : ℤ_[p]) ^ n * rX (p : ℤ_[p]) (translateY (p : ℤ_[p]) (goodModel t C) n) n) 0
          ((p : ℤ_[p]) ^ n * tY (p : ℤ_[p]) (goodModel t C) n)) • goodModel t C := by
  simp only [translateX, translateY, smulOne_trans]
  congr 1
  ext <;> first | rfl | ring

/-! ### The two exits -/

variable {t c0 : ℤ_[p]} {m n : ℕ}

open scoped Classical in
/-- **The odd exit of Step 7's subprocedure on the good model.** At the level `n` with
`m + 3 = 2n` the `Y`-quadratic `⟨0, 1, 0, -c₀⟩` has no double root, because `c₀` is a unit, so the
loop stops with Kodaira symbol `I!(2n − 3) = I!m` — an odd `m` — and Tamagawa number `4` or `2`
according as the discriminant `0² + 4c₀` is a square in the residue field. -/
theorem subprocedure_goodModel_odd (hp : 5 ≤ p)
    (hc0 : ¬ (p : ℤ_[p]) ∣ c0) (hmn : m + 3 = 2 * n) (hϖ : (p : ℤ_[p]) ≠ 0)
    (hΔ : (goodModel t ((p : ℤ_[p]) ^ m * c0)).Δ ≠ 0) (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0))
      ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t ((p : ℤ_[p]) ^ m * c0)).a₂) :
    (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = .I! m ∧
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
        = if IsSquare (goodModelTest t c0 m) then 4 else 2 := by
  have hc0' : mod (p : ℤ_[p]) c0 ≠ 0 := fun h => hc0 ((mod_eq_zero _ _).1 h)
  have hquad : quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n
      = ⟨0, 1, 0, -mod (p : ℤ_[p]) c0⟩ := by
    have h := quadratic_goodModel t c0 (m := m) (n := n) (k := 0) (by omega)
    rwa [pow_zero, one_mul] at h
  have hY : ¬ (quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n).HasDoubleRoot := by
    rw [hquad, Cubic.hasDoubleRoot_of_b_eq_one rfl rfl]
    exact fun h => (mul_ne_zero (residue_four_ne_zero hp) hc0') (by linear_combination h)
  refine ⟨?_, ?_⟩
  · rw [subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY]
    exact congrArg KodairaSymbol.I! (by omega)
  · have hodd : Odd m := Nat.odd_iff.2 (by omega)
    have hXY : (0 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ^ 2 + 4 * mod (p : ℤ_[p]) c0
        = mod (p : ℤ_[p]) (4 * c0) := by
      rw [map_mul, map_ofNat]; ring
    rw [subprocedure_tamagawaNumber_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂
      (residue_two_ne_zero hp) hquad hY, hXY, goodModelTest,
      ite_eq_left hodd]

open scoped Classical in
/-- **The even exit of Step 7's subprocedure on the good model.** At the level `n` with
`m + 3 = 2n + 1` the `Y`-quadratic is `⟨0, 1, 0, 0⟩` and does have a double root, while the
`X`-cubic `⟨0, 3t, 0, c₀⟩` does not, because `3t` and `c₀` are units. So the loop stops with
Kodaira symbol `I!(2n − 2) = I!m` — an even `m` — and Tamagawa number `4` or `2` according as the
discriminant `0² − 4·(3t)·c₀ = −12tc₀` is a square in the residue field. -/
theorem subprocedure_goodModel_even (hp : 5 ≤ p) (ht : ¬ (p : ℤ_[p]) ∣ t)
    (hc0 : ¬ (p : ℤ_[p]) ∣ c0) (hmn : m + 3 = 2 * n + 1) (hϖ : (p : ℤ_[p]) ≠ 0)
    (hΔ : (goodModel t ((p : ℤ_[p]) ^ m * c0)).Δ ≠ 0) (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0))
      ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t ((p : ℤ_[p]) ^ m * c0)).a₂) :
    (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = .I! m ∧
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
        = if IsSquare (goodModelTest t c0 m) then 4 else 2 := by
  have hc0' : mod (p : ℤ_[p]) c0 ≠ 0 := fun h => hc0 ((mod_eq_zero _ _).1 h)
  have hb : mod (p : ℤ_[p]) (3 * t) ≠ 0 := residue_three_mul_ne_zero hp ht
  have hquad : quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n = ⟨0, 1, 0, 0⟩ := by
    have hz : mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ 1 * c0) = 0 :=
      (mod_eq_zero _ _).2 ⟨c0, by rw [pow_one]⟩
    rw [quadratic_goodModel t c0 (m := m) (n := n) (k := 1) (by omega), hz, neg_zero]
  have hY : (quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n).HasDoubleRoot := by
    rw [hquad, Cubic.hasDoubleRoot_of_b_eq_one rfl rfl]
    ring
  have hcub : cubic (p : ℤ_[p])
      (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n) 0 n
      = ⟨0, mod (p : ℤ_[p]) (3 * t), 0, mod (p : ℤ_[p]) c0⟩ := by
    have h := cubic_translateY_goodModel hp t c0 (m := m) (n := n) (k := 0) (by omega)
    rwa [pow_zero, one_mul] at h
  have hX : ¬ (cubic (p : ℤ_[p])
      (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0)) n) 0 n).HasDoubleRoot := by
    rw [hcub, Cubic.hasDoubleRoot_of_a_eq_zero rfl]
    refine fun h => (mul_ne_zero (mul_ne_zero (residue_four_ne_zero hp)
      (pow_ne_zero 3 hb)) hc0') ?_
    linear_combination -h
  refine ⟨?_, ?_⟩
  · rw [subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX]
    exact congrArg KodairaSymbol.I! (by omega)
  · have hev : ¬ Odd m := by rw [Nat.odd_iff]; omega
    have hXY : (0 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) ^ 2
        - 4 * mod (p : ℤ_[p]) (3 * t) * mod (p : ℤ_[p]) c0
        = mod (p : ℤ_[p]) (-12 * t * c0) := by
      simp only [map_mul, map_neg, map_ofNat]; ring
    rw [subprocedure_tamagawaNumber_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂
      (residue_two_ne_zero hp) hb hcub hY hX, hXY, goodModelTest, ite_eq_right hev]

/-! ### The induction -/

open scoped Classical in
/-- The statement of `subprocedure_goodModel` for every level `N ≥ 2` with
`2N ≤ M + 3 ≤ 2N + K`. -/
private theorem subprocedure_goodModel_aux (hp : 5 ≤ p) (ht : ¬ (p : ℤ_[p]) ∣ t)
    (hc0 : ¬ (p : ℤ_[p]) ∣ c0) (M : ℕ) :
    ∀ (K N : ℕ), M + 3 ≤ 2 * N + K → 2 * N ≤ M + 3 → ∀ (hϖ : (p : ℤ_[p]) ≠ 0)
      (hΔ : (goodModel t ((p : ℤ_[p]) ^ M * c0)).Δ ≠ 0) (hn : 2 ≤ N) {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
      (hW : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0))
        ⟨1, 1, N, N + 1, 2 * N, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
      (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t ((p : ℤ_[p]) ^ M * c0)).a₂),
      (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = .I! M ∧
        (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
          = if IsSquare (goodModelTest t c0 M) then 4 else 2 := by
  intro K
  induction K with
  | zero =>
    intro N hK hnm hϖ hΔ hn b₂ b₄ b₆ b₈ c₄ c₆ Δv hW ha₂
    exact subprocedure_goodModel_odd hp hc0 (by omega) hϖ hΔ hn hW ha₂
  | succ K ih =>
    intro N hK hnm hϖ hΔ hn b₂ b₄ b₆ b₈ c₄ c₆ Δv hW ha₂
    by_cases h1 : M + 3 = 2 * N
    · exact subprocedure_goodModel_odd hp hc0 h1 hϖ hΔ hn hW ha₂
    by_cases h2 : M + 3 = 2 * N + 1
    · exact subprocedure_goodModel_even hp ht hc0 h2 hϖ hΔ hn hW ha₂
    obtain ⟨j, hj⟩ : ∃ j, M + 3 = 2 * N + (j + 2) := ⟨M + 3 - 2 * N - 2, by omega⟩
    have hn' : 2 ≤ N + 1 := by omega
    have hqz : mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ (j + 2) * c0) = 0 :=
      (mod_eq_zero _ _).2 ⟨(p : ℤ_[p]) ^ (j + 1) * c0, by ring⟩
    have hcz : mod (p : ℤ_[p]) ((p : ℤ_[p]) ^ (j + 1) * c0) = 0 :=
      (mod_eq_zero _ _).2 ⟨(p : ℤ_[p]) ^ j * c0, by ring⟩
    have hquad : quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N = ⟨0, 1, 0, 0⟩ := by
      rw [quadratic_goodModel t c0 (m := M) (n := N) (k := j + 2) (by omega), hqz, neg_zero]
    have hY : (quadratic (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N).HasDoubleRoot := by
      rw [hquad, Cubic.hasDoubleRoot_of_b_eq_one rfl rfl]
      ring
    have hcub : cubic (p : ℤ_[p])
        (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N) 0 N
        = ⟨0, mod (p : ℤ_[p]) (3 * t), 0, 0⟩ := by
      rw [cubic_translateY_goodModel hp t c0 (m := M) (n := N) (k := j + 1) (by omega), hcz]
    have hX : (cubic (p : ℤ_[p])
        (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N) 0 N).HasDoubleRoot := by
      rw [hcub, Cubic.hasDoubleRoot_of_a_eq_zero rfl]
      ring
    have hvY := hasValuation_translateY hn hϖ hW hY
    have ha₂Y : ¬ (p : ℤ_[p]) ^ 2 ∣
        (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N).a₂ :=
      not_dvd_translateY_a₂ N ha₂
    have hvX := hasValuation_translateX hn hϖ hvY ha₂Y hX
    have ha₂X := not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y
    have hΔX : (translateX (p : ℤ_[p])
        (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N) N).Δ ≠ 0 := by
      rw [translateX_Δ, translateY_Δ]
      exact hΔ
    have hWnext : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0))
        ⟨1, 1, N + 1, N + 1 + 1, 2 * (N + 1), 0, 0, 0, 0, 0, 0, 0⟩ :=
      hasValuation_goodModel t c0 (m := M) (n := N + 1) (k := j) (by omega)
    have hr : (p : ℤ_[p]) ^ (N + 1) ∣ (p : ℤ_[p]) ^ N *
        rX (p : ℤ_[p]) (translateY (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)) N) N := by
      obtain ⟨ρ, hρ⟩ :=
        dvd_rX_translateY_goodModel hp t c0 (m := M) (n := N) (k := j + 1) (by omega)
      exact ⟨ρ, by rw [hρ, pow_succ]; ring⟩
    rw [subprocedure_eq_subprocedure hϖ hΔ hn hW ha₂ hY hX hΔX hn' hvX ha₂X]
    obtain ⟨hkod, hcnt⟩ := subprocedure_smul
      (d := max (2 * (N + 1) + 2)
        (multiplicity (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ M * c0)).Δ))
      (PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))) hϖ hΔ hΔX hn'
      hWnext hvX ha₂ ha₂X (translateX_translateY_goodModel t ((p : ℤ_[p]) ^ M * c0) N)
      (dvd_zero _) hr (le_max_left _ _) (le_max_right _ _)
    rw [← hkod, ← hcnt]
    exact ih (N + 1) (by omega) (by omega) hϖ hΔ hn' hWnext ha₂

/-! ### The answer -/

open scoped Classical in
/-- **Step 7's subprocedure on the good model `V(t, C) = ⟨0, 3pt, 0, 0, p³C⟩`, with `C = p^m c₀`,
`t` and `c₀` units and `p ≥ 5`, entered at any level `n ≥ 2` with `2n ≤ m + 3`, returns Kodaira
symbol `I!m` and Tamagawa number `4` or `2` according as `goodModelTest t c₀ m` — that is, `4c₀`
for odd `m` and `-12tc₀` for even `m` — is a square in the residue field `ℤ_[p] ⧸ (p)`.** -/
theorem subprocedure_goodModel (hp : 5 ≤ p) (ht : ¬ (p : ℤ_[p]) ∣ t) (hc0 : ¬ (p : ℤ_[p]) ∣ c0)
    (hmn : 2 * n ≤ m + 3) (hϖ : (p : ℤ_[p]) ≠ 0)
    (hΔ : (goodModel t ((p : ℤ_[p]) ^ m * c0)).Δ ≠ 0) (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0))
      ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t ((p : ℤ_[p]) ^ m * c0)).a₂) :
    (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = .I! m ∧
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
        = if IsSquare (goodModelTest t c0 m) then 4 else 2 :=
  subprocedure_goodModel_aux hp ht hc0 m (m + 3) n (by omega) hmn hϖ hΔ hn hW ha₂

open scoped Classical in
/-- **`subprocedure_goodModel` at the entry level `n = 2`**: for `m ≥ 1` the subprocedure returns
`I!m`, with Tamagawa number `4` or `2` according as `goodModelTest t c₀ m` is a square. -/
theorem subprocedure_goodModel_entry (hp : 5 ≤ p) (ht : ¬ (p : ℤ_[p]) ∣ t)
    (hc0 : ¬ (p : ℤ_[p]) ∣ c0) (hm : 1 ≤ m) (hϖ : (p : ℤ_[p]) ≠ 0)
    (hΔ : (goodModel t ((p : ℤ_[p]) ^ m * c0)).Δ ≠ 0) {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) (goodModel t ((p : ℤ_[p]) ^ m * c0))
      ⟨1, 1, 2, 2 + 1, 2 * 2, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ (goodModel t ((p : ℤ_[p]) ^ m * c0)).a₂) :
    (subprocedure hϖ hΔ le_rfl hW ha₂).kodairaSymbol = .I! m ∧
      (subprocedure hϖ hΔ le_rfl hW ha₂).tamagawaNumber
        = if IsSquare (goodModelTest t c0 m) then 4 else 2 :=
  subprocedure_goodModel hp ht hc0 (by omega) hϖ hΔ le_rfl hW ha₂

end TateAlgorithm.Step7

end WeierstrassCurve
