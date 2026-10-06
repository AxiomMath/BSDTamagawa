/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateEvenTransport

/-!
# Step 7's subprocedure of Tate's algorithm at the even prime

We show that the loop `WeierstrassCurve.TateAlgorithm.Step7.subprocedure` of Step 7 of Tate's
algorithm returns the same Kodaira symbol and the same local Tamagawa number on two curves that
differ by an integral change of variables with `u = 1`, at a prime `ϖ ∣ 2`, without dividing by
`2`.

At such a prime, `t` cannot be bounded through `a₃ ↦ a₃ + ra₁ + 2t`; instead, `t` enters the change
of `a₆` quadratically, which bounds its valuation by that of `a₆`. The shift relating the two
`Y`-quadratics of the loop is computed explicitly to be `t/ϖⁿ`, rather than recovered from
discriminants. Finally, in residue characteristic `2` the double root of the `X`-cubic `bX² + d` is
the square root of `d/b`, which is used to compare the double roots of the two `X`-cubics.

## Main results

* `WeierstrassCurve.dvd_pow_t_of_dvd_a₆`: a bound `ϖ ^ (m + 1) ∣ t` from `ϖ ^ (2m + 1) ∣ a₆` on
  both curves.
* `WeierstrassCurve.TateAlgorithm.Step7.dvd_pow_t_of_state`,
  `WeierstrassCurve.TateAlgorithm.Step7.dvd_pow_succ_t_of_state`: the bounds `ϖ ^ n ∣ t` and
  `ϖ ^ (n + 1) ∣ t` at the two states of the loop at level `n`.
* `WeierstrassCurve.TateAlgorithm.Step7.quadratic_smul_of_dvd_t`: the `Y`-quadratic of the
  translated curve is the shift of the original one by `t/ϖⁿ`.
* `WeierstrassCurve.TateAlgorithm.Step7.sq_mod_rX_of_two_eq_zero`: in residue characteristic `2`,
  the residue of `Step7.rX` squares to `d/b`.
* `WeierstrassCurve.TateAlgorithm.Step7.mod_rX_smul_of_two_eq_zero`,
  `WeierstrassCurve.TateAlgorithm.Step7.dvd_r_translateX_smul_of_two_eq_zero`: the double roots of
  the two `X`-cubics differ by `r/ϖⁿ`, so the loop invariant `ϖ ^ n ∣ r` passes to level `n + 1`.
* `WeierstrassCurve.TateAlgorithm.Step7.dvd_sq_r_of_state_of_dvd_two`: the loop invariant `ϖ ∣ s`,
  `ϖ ^ 2 ∣ r` holds on entry.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_smul_of_dvd_two`: the loop returns the same
  Kodaira symbol and the same local Tamagawa number on both curves.
-/

@[expose] public section

universe u

open CharP CommRing Ideal Polynomial

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R} {r s t : R}

/-- If `q ≠ 0` and `x = q * y`, then the exact quotient of `x` by `q` is `y`. -/
private theorem div_eq_of_eq [NoZeroDivisors R] {q x y : R} (hq : q ≠ 0) (h : x = q * y) :
    div x q = y :=
  mul_left_cancel₀ hq ((mul_div hq ⟨y, h⟩).trans h)

/-! ### Bounding `t` by the `a₆`-valuation -/

/-- **`ϖ ^ (m + 1) ∣ t` from `ϖ ^ (2m + 1) ∣ a₆` on both curves.** Let `ϖ` be prime, and suppose
that `ϖ ^ (m + 1) ∣ a₃ + ra₁` and `ϖ ^ (2m + 1) ∣ ra₄ + r²a₂ + r³`. If `ϖ ^ (2m + 1)` divides the
`a₆` of both `V` and its image under the change of variables `(1, r, s, t)`, then
`ϖ ^ (m + 1) ∣ t`. -/
theorem dvd_pow_t_of_dvd_a₆ [IsDomain R] (hprime : Prime ϖ) (m : ℕ)
    (hu : ϖ ^ (m + 1) ∣ V.a₃ + r * V.a₁)
    (hX : ϖ ^ (2 * m + 1) ∣ r * V.a₄ + r ^ 2 * V.a₂ + r ^ 3)
    (ha₆ : ϖ ^ (2 * m + 1) ∣ V.a₆)
    (ha₆' : ϖ ^ (2 * m + 1) ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ^ (m + 1) ∣ t := by
  induction m with
  | zero => exact dvd_succ_t_of_dvd_a₆ hprime (by simp) hu hX ha₆ ha₆'
  | succ k ih =>
    refine dvd_succ_t_of_dvd_a₆ hprime (ih ?_ ?_ ?_ ?_) hu hX ha₆ ha₆'
    · exact (pow_dvd_pow ϖ (by omega)).trans hu
    · exact (pow_dvd_pow ϖ (by omega)).trans hX
    · exact (pow_dvd_pow ϖ (by omega)).trans ha₆
    · exact (pow_dvd_pow ϖ (by omega)).trans ha₆'

end WeierstrassCurve

namespace WeierstrassCurve.TateAlgorithm.Step7

variable {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R} {r s t : R}

/-- **`ϖ ^ n ∣ t` at the level-`n` state of Step 7's subprocedure.** Let `ϖ` be prime and `n ≠ 0`.
If `ϖ ∣ a₂`, `ϖ ^ n ∣ a₃`, `ϖ ^ (n + 1) ∣ a₄`, `ϖ ^ (2n) ∣ a₆` and `ϖ ^ n ∣ r`, and the `a₆` of the
image of `V` under `(1, r, s, t)` is divisible by `ϖ ^ (2n)`, then `ϖ ^ n ∣ t`. -/
theorem dvd_pow_t_of_state [IsDomain R] (hprime : Prime ϖ) {n : ℕ} (hn : n ≠ 0) (hr : ϖ ^ n ∣ r)
    (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ n ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄)
    (ha₆ : ϖ ^ (2 * n) ∣ V.a₆) (ha₆' : ϖ ^ (2 * n) ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ϖ ^ n ∣ t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hu : ϖ ^ (m + 1) ∣ V.a₃ + r * V.a₁ := dvd_add ha₃ (dvd_mul_of_dvd_left hr V.a₁)
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₄, e₄⟩ := ha₄
  refine WeierstrassCurve.dvd_pow_t_of_dvd_a₆ hprime m hu ?_
    ((pow_dvd_pow ϖ (by omega)).trans ha₆) ((pow_dvd_pow ϖ (by omega)).trans ha₆')
  exact ⟨ϖ ^ 2 * ρ * α₄ + ϖ ^ 2 * ρ ^ 2 * α₂ + ϖ ^ (m + 2) * ρ ^ 3, by rw [hρ, e₂, e₄]; ring⟩

/-- **`ϖ ^ (n + 1) ∣ t` at the state left by `Step7.translateY`.** If the valuations of `V` are at
least `⟨1, 1, n + 1, n + 1, 2n + 1⟩`, `ϖ ^ n ∣ r`, and the `a₆` of the image of `V` under
`(1, r, s, t)` is divisible by `ϖ ^ (2n + 1)`, then `ϖ ^ (n + 1) ∣ t`. -/
theorem dvd_pow_succ_t_of_state [IsDomain R] (hprime : Prime ϖ) {n : ℕ} (hn : n ≠ 0)
    (hr : ϖ ^ n ∣ r) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ (n + 1) ∣ V.a₃)
    (ha₄ : ϖ ^ (n + 1) ∣ V.a₄) (ha₆ : ϖ ^ (2 * n + 1) ∣ V.a₆)
    (ha₆' : ϖ ^ (2 * n + 1) ∣ ((VariableChange.mk 1 r s t) • V).a₆) : ϖ ^ (n + 1) ∣ t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hu : ϖ ^ (m + 1 + 1) ∣ V.a₃ + r * V.a₁ :=
    dvd_add ha₃ (by rw [pow_succ]; exact mul_dvd_mul hr ha₁)
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₄, e₄⟩ := ha₄
  refine WeierstrassCurve.dvd_pow_t_of_dvd_a₆ hprime (m + 1) hu ?_ ha₆ ha₆'
  exact ⟨ρ * α₄ + ρ ^ 2 * α₂ + ϖ ^ m * ρ ^ 3, by rw [hρ, e₂, e₄]; ring⟩

/-! ### The `Y`-quadratic, with its shift exhibited -/

/-- **The subprocedure's `Y`-quadratic is the shift of the other curve's by `t/ϖⁿ`.** At the
level-`n` state — `ϖ ∣ a₁, a₂`, `ϖⁿ ∣ a₃`, `ϖⁿ⁺¹ ∣ a₄`, `ϖ²ⁿ ∣ a₆` — a change of variables with
`ϖⁿ ∣ r` and `ϖⁿ ∣ t` changes `Y² + (a₃/ϖⁿ)Y - a₆/ϖ²ⁿ` exactly as substituting `Y + t/ϖⁿ` does:
`a₃` moves by `ra₁ + 2t`, and `a₆` by `ra₄ + r²a₂ + r³ - t(a₃ + t + ra₁)`. This holds in every
characteristic. -/
theorem quadratic_smul_of_dvd_t [IsDomain R] [(span {ϖ}).IsMaximal] (hϖ : ϖ ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hr : ϖ ^ n ∣ r) (ht : ϖ ^ n ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂)
    (ha₃ : ϖ ^ n ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄) (ha₆ : ϖ ^ (2 * n) ∣ V.a₆) :
    quadratic ϖ ((VariableChange.mk 1 r s t) • V) n
      = (quadratic ϖ V n).shiftBy (mod ϖ (div t (ϖ ^ n))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨τ, hτ⟩ := ht
  have dt : div t (ϖ ^ (m + 1)) = τ := div_eq_of_eq (pow_ne_zero _ hϖ) hτ
  have d₃ : div V.a₃ (ϖ ^ (m + 1)) = α₃ := div_eq_of_eq (pow_ne_zero _ hϖ) e₃
  have d₆ : div V.a₆ (ϖ ^ (2 * (m + 1))) = α₆ := div_eq_of_eq (pow_ne_zero _ hϖ) e₆
  have g₃ : div ((VariableChange.mk 1 r s t) • V).a₃ (ϖ ^ (m + 1))
      = α₃ + ϖ * ρ * α₁ + 2 * τ :=
    div_eq_of_eq (pow_ne_zero _ hϖ) (by rw [smulOne_a₃, e₁, e₃, hρ, hτ]; ring)
  have g₆ : div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ (2 * (m + 1)))
      = α₆ + ϖ * ρ * α₄ + ϖ * ρ ^ 2 * α₂ + ϖ * ϖ ^ m * ρ ^ 3 - τ * α₃ - τ ^ 2
        - ϖ * ρ * τ * α₁ :=
    div_eq_of_eq (pow_ne_zero _ hϖ) (by rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring)
  refine Cubic.ext rfl ?_ ?_ ?_
  · change (1 : R ⧸ span {ϖ}) = 1 + 3 * 0 * mod ϖ (div t (ϖ ^ (m + 1)))
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₃ (ϖ ^ (m + 1)))
      = mod ϖ (div V.a₃ (ϖ ^ (m + 1))) + 2 * 1 * mod ϖ (div t (ϖ ^ (m + 1)))
          + 3 * 0 * mod ϖ (div t (ϖ ^ (m + 1))) ^ 2
    rw [g₃, d₃, dt]
    simp only [map_add, map_mul, map_ofNat, mod_self]
    ring
  · change -mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ (2 * (m + 1))))
      = -mod ϖ (div V.a₆ (ϖ ^ (2 * (m + 1))))
          + mod ϖ (div V.a₃ (ϖ ^ (m + 1))) * mod ϖ (div t (ϖ ^ (m + 1)))
          + 1 * mod ϖ (div t (ϖ ^ (m + 1))) ^ 2
          + 0 * mod ϖ (div t (ϖ ^ (m + 1))) ^ 3
    rw [g₆, d₆, d₃, dt]
    simp only [map_add, map_sub, map_mul, map_pow, mod_self]
    ring

/-! ### The `X`-cubic's double root in residue characteristic `2` -/

variable [(span {ϖ}).IsMaximal]

/-- **The defining property of `Step7.rX` at the even prime.** If `2 = 0` in the residue field,
then the residue of `Step7.rX ϖ V n` squares to `d/b`, where `bX² + cX + d` is the cubic
`cubic ϖ V 0 n`. -/
theorem sq_mod_rX_of_two_eq_zero [PerfectField (R ⧸ span {ϖ})] (h2 : (2 : R ⧸ span {ϖ}) = 0)
    (V : WeierstrassCurve R) (n : ℕ) :
    mod ϖ (rX ϖ V n) ^ 2 = (cubic ϖ V 0 n).d / (cubic ϖ V 0 n).b := by
  have : CharP (R ⧸ span {ϖ}) 2 := (charP_iff_prime_eq_zero Nat.prime_two).mpr h2
  have : ExpChar (R ⧸ span {ϖ}) 2 := .prime Nat.prime_two
  have : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
  rw [rX, dite_eq_left h2, mod_out]
  exact pow_root _

/-- **The two double roots of the two `X`-cubics differ by exactly the shift, at the even prime.**
The `X`-cubic of the translated curve is the shift of the original one by `γ = r/ϖⁿ`; for a cubic
`bX² + cX + d` this fixes `b`, moves `c` by `2bγ = 0` and `d` by `cγ + bγ²`. A double root forces
`b²c² = 4b³d = 0`, so `c = 0` and `d'/b' = d/b + γ²`. Hence `rX'² = (rX - γ)²`, and squaring is
injective in a domain of characteristic `2`. The hypothesis `¬ϖ² ∣ a₂` makes `b = a₂/ϖ` nonzero. -/
theorem mod_rX_smul_of_two_eq_zero [IsDomain R] [PerfectField (R ⧸ span {ϖ})]
    (h2 : (2 : R ⧸ span {ϖ}) = 0) (hϖ : ϖ ≠ 0) {n : ℕ} (hn : 2 ≤ n) (hs : ϖ ∣ s)
    (hr : ϖ ^ n ∣ r) (ht : ϖ ^ (n + 1) ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂)
    (ha₃ : ϖ ^ (n + 1) ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄) (ha₆ : ϖ ^ (2 * n + 1) ∣ V.a₆)
    (ha₂' : ¬ ϖ ^ 2 ∣ V.a₂) (hX : (cubic ϖ V 0 n).HasDoubleRoot) :
    mod ϖ (rX ϖ ((VariableChange.mk 1 r s t) • V) n)
      = mod ϖ (rX ϖ V n) - mod ϖ (div r (ϖ ^ n)) := by
  set γ : R ⧸ span {ϖ} := mod ϖ (div r (ϖ ^ n)) with hγ
  set x : R ⧸ span {ϖ} := mod ϖ (rX ϖ V n) with hxdef
  set y : R ⧸ span {ϖ} := mod ϖ (rX ϖ ((VariableChange.mk 1 r s t) • V) n) with hydef
  have ha0 : (cubic ϖ V 0 n).a = 0 := rfl
  have hb : (cubic ϖ V 0 n).b ≠ 0 := by
    rw [show (cubic ϖ V 0 n).b = mod ϖ (div V.a₂ ϖ) from rfl, Ne, mod_eq_zero]
    exact fun h ↦ ha₂' (sq_dvd.mpr ⟨ha₂, h⟩)
  have hc : (cubic ϖ V 0 n).c = 0 := by
    have h4 : ((cubic ϖ V 0 n).b * (cubic ϖ V 0 n).c) ^ 2 = 0 := by
      have hdr := (Cubic.hasDoubleRoot_of_a_eq_zero ha0).mp hX
      linear_combination hdr + (2 * (cubic ϖ V 0 n).b ^ 3 * (cubic ϖ V 0 n).d) * h2
    rcases mul_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4) with h | h
    · exact absurd h hb
    · exact h
  have hshift : cubic ϖ ((VariableChange.mk 1 r s t) • V) 0 n = (cubic ϖ V 0 n).shiftBy γ :=
    cubic_smul hϖ hn hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆
  have hd' : (cubic ϖ ((VariableChange.mk 1 r s t) • V) 0 n).d
      = (cubic ϖ V 0 n).d + (cubic ϖ V 0 n).b * γ ^ 2 := by
    rw [hshift, Cubic.shiftBy_d, hc, ha0]; ring
  have hb' : (cubic ϖ ((VariableChange.mk 1 r s t) • V) 0 n).b = (cubic ϖ V 0 n).b := by
    rw [hshift, Cubic.shiftBy_b, ha0]; ring
  have hx : x ^ 2 = (cubic ϖ V 0 n).d / (cubic ϖ V 0 n).b := sq_mod_rX_of_two_eq_zero h2 V n
  have hy : y ^ 2 = (cubic ϖ V 0 n).d / (cubic ϖ V 0 n).b + γ ^ 2 := by
    rw [hydef, sq_mod_rX_of_two_eq_zero h2 _ n, hd', hb']
    field_simp
  have key : (y - (x - γ)) ^ 2 = 0 := by
    linear_combination hy - hx + (x ^ 2 + γ ^ 2 - x * y + y * γ - x * γ) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp key)

/-- **The invariant step at the even prime: the `r`-parameter at level `n + 1` is divisible by
`ϖ ^ (n + 1)`.** The level-`(n + 1)` parameter is `r + ϖⁿ(rX' - rX)`, and dividing by `ϖⁿ` this is
`Step7.mod_rX_smul_of_two_eq_zero`. -/
theorem dvd_r_translateX_smul_of_two_eq_zero [IsDomain R] [PerfectField (R ⧸ span {ϖ})]
    (h2 : (2 : R ⧸ span {ϖ}) = 0) (hϖ : ϖ ≠ 0) {n : ℕ} (hn : 2 ≤ n) (hs : ϖ ∣ s)
    (hr : ϖ ^ n ∣ r) (ht : ϖ ^ (n + 1) ∣ t) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂)
    (ha₃ : ϖ ^ (n + 1) ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄) (ha₆ : ϖ ^ (2 * n + 1) ∣ V.a₆)
    (ha₂' : ¬ ϖ ^ 2 ∣ V.a₂) (hX : (cubic ϖ V 0 n).HasDoubleRoot) :
    ϖ ^ (n + 1) ∣ r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n) := by
  have he : r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n)
      = ϖ ^ n * (div r (ϖ ^ n)
        + (rX ϖ ((VariableChange.mk 1 r s t) • V) n - rX ϖ V n)) := by
    rw [mul_add, mul_div (pow_ne_zero n hϖ) hr]
  rw [he, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero, map_add, map_sub,
    mod_rX_smul_of_two_eq_zero h2 hϖ hn hs hr ht ha₁ ha₂ ha₃ ha₄ ha₆ ha₂' hX]
  ring

/-! ### The invariant on entry -/

omit [(span {ϖ}).IsMaximal] in
/-- **The subprocedure's parameter invariant holds on entry, at the even prime.** Let `ϖ` be a
prime with `ϖ ∣ 2`, and let `3` be a unit. If both `V` and its image under `(1, r, s, t)` have
valuations at least `⟨1, 1, 2, 3, 4⟩` and `¬ϖ² ∣ a₂`, then `ϖ ∣ s` and `ϖ² ∣ r`.

Given `ϖ ∣ r`, write `r = ϖρ` and `α₂ = a₂/ϖ`: the `a₄`-bound gives `ϖ ∣ ρ(2α₂ + 3ρ)`, the
`a₆`-bound gives `ϖ ∣ ρ²(α₂ + ρ)`, and if `ϖ ∤ ρ` then `(2α₂ + 3ρ) - 3(α₂ + ρ) = -α₂` puts `a₂` in
`(ϖ²)`, which `¬ϖ² ∣ a₂` forbids. -/
theorem dvd_sq_r_of_state_of_dvd_two [IsDomain R] (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2)
    (h3 : IsUnit (3 : R)) (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 3 ∣ V.a₄) (ha₆ : ϖ ^ 4 ∣ V.a₆) (ha₂n : ¬ ϖ ^ 2 ∣ V.a₂)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₄' : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).a₄)
    (ha₆' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ϖ ∣ s ∧ ϖ ^ 2 ∣ r := by
  have hϖ : ϖ ≠ 0 := hprime.ne_zero
  obtain ⟨hs, hr1, ht2⟩ :=
    Step6.dvd_of_state_of_dvd_two hprime hϖ2 h3 ha₁ ha₂ ha₃
      ((pow_dvd_pow ϖ (by norm_num)).trans ha₄) ((pow_dvd_pow ϖ (by norm_num)).trans ha₆) ha₂' ha₃'
      ((pow_dvd_pow ϖ (by norm_num)).trans ha₄') ((pow_dvd_pow ϖ (by norm_num)).trans ha₆')
  refine ⟨hs, ?_⟩
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr1
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht2
  have k4 : ϖ ∣ ρ * (2 * α₂ + 3 * ρ) := by
    have hsub : ϖ ^ 3 ∣ ϖ ^ 2 * (ρ * (2 * α₂ + 3 * ρ)) := by
      have hx := dvd_sub ha₄' (dvd_mul_right (ϖ ^ 3)
        (α₄ - σ * α₃ - τ * α₁ - ρ * σ * α₁ - 2 * σ * τ))
      rwa [show ((VariableChange.mk 1 r s t) • V).a₄
          - ϖ ^ 3 * (α₄ - σ * α₃ - τ * α₁ - ρ * σ * α₁ - 2 * σ * τ)
          = ϖ ^ 2 * (ρ * (2 * α₂ + 3 * ρ)) from by
        rw [smulOne_a₄, e₁, e₂, e₃, e₄, hρ, hσ, hτ]; ring] at hx
    rwa [show (ϖ : R) ^ 3 = ϖ ^ 2 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ)] at hsub
  have k6 : ϖ ∣ ρ * (ρ * (α₂ + ρ)) := by
    have hsub : ϖ ^ 4 ∣ ϖ ^ 3 * (ρ * (ρ * (α₂ + ρ))) := by
      have hx := dvd_sub ha₆' (dvd_mul_right (ϖ ^ 4)
        (α₆ + ρ * α₄ - τ * α₃ - τ ^ 2 - ρ * τ * α₁))
      rwa [show ((VariableChange.mk 1 r s t) • V).a₆
          - ϖ ^ 4 * (α₆ + ρ * α₄ - τ * α₃ - τ ^ 2 - ρ * τ * α₁)
          = ϖ ^ 3 * (ρ * (ρ * (α₂ + ρ))) from by
        rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring] at hx
    rwa [show (ϖ : R) ^ 4 = ϖ ^ 3 * ϖ from by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 3 hϖ)] at hsub
  by_contra hcon
  have hρnd : ¬ ϖ ∣ ρ := by
    rintro ⟨ρ', hρ'⟩
    exact hcon ⟨ρ', by rw [hρ, hρ']; ring⟩
  have hk1 : ϖ ∣ 2 * α₂ + 3 * ρ := (hprime.dvd_mul.mp k4).resolve_left hρnd
  have hk2 : ϖ ∣ α₂ + ρ :=
    (hprime.dvd_mul.mp ((hprime.dvd_mul.mp k6).resolve_left hρnd)).resolve_left hρnd
  have hα₂ : ϖ ∣ α₂ := by
    have hx := dvd_sub hk1 (hk2.mul_left 3)
    rw [show 2 * α₂ + 3 * ρ - 3 * (α₂ + ρ) = -α₂ from by ring] at hx
    exact dvd_neg.mp hx
  obtain ⟨α₂', hα₂'⟩ := hα₂
  exact ha₂n ⟨α₂', by rw [e₂, hα₂']; ring⟩

/-! ### The subprocedure -/

variable [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]

/-- **Step 7's subprocedure returns the same answer on an integral translate, at the even prime.**
Let `ϖ ≠ 0` be a prime with `ϖ ∣ 2`, and let `V` and `V' = (1, r, s, t) • V` both satisfy the loop
invariant at level `n ≥ 2`, with `ϖ ∣ s` and `ϖ ^ n ∣ r`. If `2 * n + 2 ≤ d` and `v_ϖ(V.Δ) ≤ d`,
then `Step7.subprocedure` returns the same Kodaira symbol and the same local Tamagawa number on `V`
and `V'`. -/
theorem subprocedure_smul_of_dvd_two (hprime : Prime ϖ) (hϖ2 : ϖ ∣ 2) (hϖ : ϖ ≠ 0) {d n : ℕ}
    {V V' : WeierstrassCurve R} {r s t : R}
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv b₂' b₄' b₆' b₈' c₄' c₆' Δv' : ℕ} (hΔ : V.Δ ≠ 0) (hΔ' : V'.Δ ≠ 0)
    (hn : 2 ≤ n) (hW : HasValuation ϖ V ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (hW' : HasValuation ϖ V' ⟨1, 1, n, n + 1, 2 * n, b₂', b₄', b₆', b₈', c₄', c₆', Δv'⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ V.a₂) (ha₂' : ¬ϖ ^ 2 ∣ V'.a₂)
    (hVV' : V' = (VariableChange.mk 1 r s t) • V) (hs : ϖ ∣ s) (hr : ϖ ^ n ∣ r)
    (hd : 2 * n + 2 ≤ d) (hdm : multiplicity ϖ V.Δ ≤ d) :
    (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol
        = (subprocedure hϖ hΔ' hn hW' ha₂').kodairaSymbol ∧
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
        = (subprocedure hϖ hΔ' hn hW' ha₂').tamagawaNumber := by
  classical
  have h2 : (2 : R ⧸ span {ϖ}) = 0 := by
    rw [← map_ofNat (mod ϖ) 2, mod_eq_zero]; exact hϖ2
  have ht : ϖ ^ n ∣ t :=
    dvd_pow_t_of_state hprime (by omega) hr (by simpa using hW.a₂) hW.a₃ hW.a₄ hW.a₆
      (by rw [← hVV']; exact hW'.a₆)
  have hγY : quadratic ϖ V' n = (quadratic ϖ V n).shiftBy (mod ϖ (div t (ϖ ^ n))) := by
    rw [hVV']
    exact quadratic_smul_of_dvd_t hϖ (by omega) hr ht (by simpa using hW.a₁)
      (by simpa using hW.a₂) hW.a₃ hW.a₄ hW.a₆
  by_cases hY : (quadratic ϖ V n).HasDoubleRoot
  · have hY' : (quadratic ϖ V' n).HasDoubleRoot := by
      rw [hγY]; exact (Cubic.hasDoubleRoot_shiftBy _ _).mpr hY
    have hvY := hasValuation_translateY hn hϖ hW hY
    have hvY' := hasValuation_translateY hn hϖ hW' hY'
    have ha₂Y : ¬ϖ ^ 2 ∣ (translateY ϖ V n).a₂ := not_dvd_translateY_a₂ n ha₂
    have ha₂Y' : ¬ϖ ^ 2 ∣ (translateY ϖ V' n).a₂ := not_dvd_translateY_a₂ n ha₂'
    obtain ⟨t₂, hYY⟩ : ∃ t₂, translateY ϖ V' n
        = (VariableChange.mk 1 r s t₂) • translateY ϖ V n := by
      subst hVV'
      exact ⟨_, translateY_smul V r s t n⟩
    have ha₆Y' : ϖ ^ (2 * n + 1) ∣ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n).a₆ := by
      rw [← hYY]; exact hvY'.a₆
    have ht₂ : ϖ ^ (n + 1) ∣ t₂ :=
      dvd_pow_succ_t_of_state hprime (by omega) hr (by simpa using hvY.a₁)
        (by simpa using hvY.a₂) hvY.a₃ hvY.a₄ hvY.a₆ ha₆Y'
    have hcubY : cubic ϖ (translateY ϖ V' n) 0 n
        = (cubic ϖ (translateY ϖ V n) 0 n).shiftBy (mod ϖ (div r (ϖ ^ n))) := by
      rw [hYY]
      exact cubic_smul hϖ hn hs hr ht₂ (by simpa using hvY.a₁) (by simpa using hvY.a₂)
        hvY.a₃ hvY.a₄ hvY.a₆
    by_cases hX : (cubic ϖ (translateY ϖ V n) 0 n).HasDoubleRoot
    · have hX' : (cubic ϖ (translateY ϖ V' n) 0 n).HasDoubleRoot := by
        rw [hcubY]; exact (Cubic.hasDoubleRoot_shiftBy _ _).mpr hX
      have hvX := hasValuation_translateX hn hϖ hvY ha₂Y hX
      have hvX' := hasValuation_translateX hn hϖ hvY' ha₂Y' hX'
      have hΔX : (translateX ϖ (translateY ϖ V n) n).Δ ≠ 0 := by
        rw [translateX_Δ, translateY_Δ]; exact hΔ
      have hΔX' : (translateX ϖ (translateY ϖ V' n) n).Δ ≠ 0 := by
        rw [translateX_Δ, translateY_Δ]; exact hΔ'
      have ha₂X := not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y
      have ha₂X' := not_dvd_translateX_a₂ hn hϖ hvY'.a₂ ha₂Y'
      have hXX : translateX ϖ (translateY ϖ V' n) n
          = (VariableChange.mk 1
              (r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n) n
                - rX ϖ (translateY ϖ V n) n)) s
              (t₂ + ϖ ^ n * rX ϖ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n) n * s))
            • translateX ϖ (translateY ϖ V n) n := by
        rw [hYY]; exact translateX_smul (translateY ϖ V n) r s t₂ n
      have hr₃ : ϖ ^ (n + 1) ∣
          r + ϖ ^ n * (rX ϖ ((VariableChange.mk 1 r s t₂) • translateY ϖ V n) n
            - rX ϖ (translateY ϖ V n) n) :=
        dvd_r_translateX_smul_of_two_eq_zero h2 hϖ hn hs hr ht₂ (by simpa using hvY.a₁)
          (by simpa using hvY.a₂) hvY.a₃ hvY.a₄ hvY.a₆ ha₂Y hX
      have hΔ₅ : 2 * n + 5 ≤ multiplicity ϖ V.Δ := by
        refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
        have hdvd := hvX.Δ
        rwa [translateX_Δ, translateY_Δ] at hdvd
      have hdmX : multiplicity ϖ (translateX ϖ (translateY ϖ V n) n).Δ ≤ d := by
        rw [translateX_Δ, translateY_Δ]; exact hdm
      rw [subprocedure_eq_subprocedure hϖ hΔ hn hW ha₂ hY hX hΔX (by omega) hvX ha₂X,
        subprocedure_eq_subprocedure hϖ hΔ' hn hW' ha₂' hY' hX' hΔX' (by omega) hvX' ha₂X']
      exact subprocedure_smul_of_dvd_two hprime hϖ2 hϖ hΔX hΔX' (by omega) hvX hvX' ha₂X ha₂X'
        hXX hs hr₃ (by omega) hdmX
    · have hX' : ¬(cubic ϖ (translateY ϖ V' n) 0 n).HasDoubleRoot := by
        rw [hcubY]; exact fun hc => hX ((Cubic.hasDoubleRoot_shiftBy _ _).mp hc)
      have hcard : (cubic ϖ (translateY ϖ V' n) 0 n).roots.toFinset.card
          = (cubic ϖ (translateY ϖ V n) 0 n).roots.toFinset.card := by
        rw [Cubic.roots_eq_toPoly_roots, Cubic.roots_eq_toPoly_roots, hcubY,
          Cubic.card_toFinset_roots_shiftBy]
      rw [subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX,
        subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ' hn hW' ha₂' hY' hX']
      exact ⟨rfl, by simp only [hcard]⟩
  · have hY' : ¬(quadratic ϖ V' n).HasDoubleRoot := by
      rw [hγY]; exact fun hc => hY ((Cubic.hasDoubleRoot_shiftBy _ _).mp hc)
    have hcard : (quadratic ϖ V' n).roots.toFinset.card
        = (quadratic ϖ V n).roots.toFinset.card := by
      rw [Cubic.roots_eq_toPoly_roots, Cubic.roots_eq_toPoly_roots, hγY,
        Cubic.card_toFinset_roots_shiftBy]
    rw [subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY,
      subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ' hn hW' ha₂' hY']
    exact ⟨rfl, by simp only [hcard]⟩
termination_by d - n
decreasing_by omega

end WeierstrassCurve.TateAlgorithm.Step7
