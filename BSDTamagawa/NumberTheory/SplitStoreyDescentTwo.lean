/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.AlphaBounds

/-!
# The `p = 2` minimal-storey descent on the split locus

On a short model `y² = x³ + a₄x + a₆` over `ℤ_2` with `a₄` a unit, `a₆ = 2b`, `27b ≡ 1 mod 8` and
`2 ^ 14 ∣ Δ`, Steps 1–10 of Tate's algorithm do not answer, so Step 11 fires. This is the input
`WeierstrassCurve.HasSplitStoreyDescent 2`, and with it the bounds `α_p < 1/2` and `α_p ≥ 1/88572`
hold at every prime `p`.

## Main results

* `WeierstrassCurve.TateAlgorithm.exists_params_of_split_two`: on that locus `a₄ ≡ 5 mod 16` and
  `b ≡ 11 + 8a mod 32`, where `a₄ = 5 + 16a`.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_split_two`: Steps 1–10 of Tate's algorithm do
  not answer on that locus, so Step 11 fires.
* `WeierstrassCurve.hasSplitStoreyDescent_of_eq_two`: `HasSplitStoreyDescent 2`.
* `WeierstrassCurve.α_bounds`: `α_p < 1/2` and `α_p ≥ 1/88572` at every prime `p`.

## Implementation notes

The congruence `27b ≡ 1 mod 8` cannot be dropped: on the whole locus `{a₄` a unit`, 2 ^ 14 ∣ Δ}`
Step 11 fires on exactly half. Writing `a₄ = 5 + 16α`, `b = 3 + 8β` and `r = 1 + 2ρ` for the Step-2
lift, the three entries of the cubic of Steps 6 and 7 are all congruent to `1 + ρ` modulo `2`, so
the cubic has a triple root; with `b ≡ 1 mod 4` the middle entry would be `≡ ρ` instead, and Step 7
would answer `I_n^*`.

Every change of variables made by the algorithm here has `u = 1`, so every intermediate curve is
`⟨1, R, S, T⟩ • ofShortNF a₄ a₆` for some cumulative `(R, S, T)`.
-/

@[expose] public section

open CommRing Ideal CharP

namespace WeierstrassCurve.TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Elementary two-adic arithmetic -/

/-- Every element of `ℤ_2` is even or odd. -/
theorem exists_even_or_odd_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) (x : ℤ_[p]) :
    ∃ y : ℤ_[p], x = 2 * y ∨ x = 1 + 2 * y := by
  by_cases h : (p : ℤ_[p]) ∣ x
  · obtain ⟨y, hy⟩ := h
    exact ⟨y, Or.inl (by rw [hy, hπ])⟩
  · have hu : IsUnit x := not_not.1 fun hnu => h (PadicInt.dvd_iff_not_isUnit.2 hnu)
    obtain ⟨y, hy⟩ := PadicInt.dvd_sub_one_of_isUnit_of_eq_two hp2 hu
    rw [hπ] at hy
    exact ⟨y, Or.inr (by linear_combination hy)⟩

/-- `x ^ 2 + x` is even in `ℤ_2`, for every `x`. -/
theorem exists_sq_add_self_eq_two_mul (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) (x : ℤ_[p]) :
    ∃ m : ℤ_[p], x ^ 2 + x = 2 * m := by
  obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ x
  · exact ⟨2 * y ^ 2 + y, by rw [hy]; ring⟩
  · exact ⟨1 + 3 * y + 2 * y ^ 2, by rw [hy]; ring⟩

/-- Divisibility by `p ^ n` read off in `ZMod (p ^ n)`. -/
theorem pow_dvd_iff_toZModPow_eq_zero (n : ℕ) (x : ℤ_[p]) :
    (p : ℤ_[p]) ^ n ∣ x ↔ PadicInt.toZModPow n x = 0 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]

/-- Exact division by the exact power that divides. -/
private theorem div_eq_of_eq_pow_mul {k : ℕ} {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) ^ k * a) :
    div x ((p : ℤ_[p]) ^ k) = a := by
  subst h
  exact mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-- Exact division by the uniformiser. -/
private theorem div_eq_of_eq_mul {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) * a) :
    div x (p : ℤ_[p]) = a := by
  subst h
  exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero
    (CommRing.mul_div PadicInt.uniformizer_ne_zero (Dvd.intro a rfl))

/-! ### The residue field `𝔽_2` -/

/-- Squaring is the identity on the residue field of `ℤ_2`. -/
theorem residue_sq_eq_self_two (hp2 : p = 2) (y : ℤ_[p] ⧸ span {(p : ℤ_[p])}) : y ^ 2 = y := by
  rcases Step2.residue_eq_zero_or_one_of_eq_two hp2 y with h | h <;> rw [h] <;> ring

/-- `4 = 0` in the residue field of `ℤ_2`. -/
theorem residue_four_eq_zero_two (hp2 : p = 2) :
    (4 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
  rw [show (4 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 2 * 2 from by norm_num,
    Step2.residue_two_eq_zero_of_eq_two hp2, mul_zero]

/-- `3 = 1` in the residue field of `ℤ_2`. -/
theorem residue_three_eq_one_two (hp2 : p = 2) :
    (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 1 := by
  linear_combination Step2.residue_two_eq_zero_of_eq_two hp2 (p := p)

/-- The Frobenius root is the identity on the residue field of `ℤ_2`. -/
theorem root_two_eq_self_two (hp2 : p = 2) [ExpChar (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2]
    [PerfectRing (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2] (y : ℤ_[p] ⧸ span {(p : ℤ_[p])}) :
    root 2 y = y :=
  (residue_sq_eq_self_two hp2 (root 2 y)).symm.trans (CharP.pow_root (p := 2) y)

/-! ### The lifts the algorithm chooses, modulo `2` -/

/-- `Step6.s` is a lift of the residue of `a₂` at `p = 2`. -/
theorem Step6.mod_s_two (hp2 : p = 2) (V : WeierstrassCurve ℤ_[p]) :
    mod (p : ℤ_[p]) (Step6.s (p : ℤ_[p]) V) = mod (p : ℤ_[p]) V.a₂ := by
  rw [Step6.s, mod_out]
  split_ifs with h2
  · have hc : CharP (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 :=
      (charP_iff_prime_eq_zero (by decide)).mpr h2
    have hpr : PerfectRing (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 := PerfectField.toPerfectRing 2
    exact root_two_eq_self_two hp2 _
  · exact absurd (Step2.residue_two_eq_zero_of_eq_two hp2) h2

/-- `Step6.t` is a lift of the residue of `a₆ / ϖ ^ 2` at `p = 2`. -/
theorem Step6.mod_t_two (hp2 : p = 2) (V : WeierstrassCurve ℤ_[p]) :
    mod (p : ℤ_[p]) (Step6.t (p : ℤ_[p]) V)
      = mod (p : ℤ_[p]) (div V.a₆ ((p : ℤ_[p]) ^ 2)) := by
  rw [Step6.t, mod_out]
  split_ifs with h2
  · have hc : CharP (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 :=
      (charP_iff_prime_eq_zero (by decide)).mpr h2
    have hpr : PerfectRing (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 := PerfectField.toPerfectRing 2
    exact root_two_eq_self_two hp2 _
  · exact absurd (Step2.residue_two_eq_zero_of_eq_two hp2) h2

/-- `Step8.r` is a lift of the residue of `a₂ / ϖ` at `p = 2`. -/
theorem Step8.mod_r_two (hp2 : p = 2) (V : WeierstrassCurve ℤ_[p]) :
    mod (p : ℤ_[p]) (Step8.r (p : ℤ_[p]) V) = mod (p : ℤ_[p]) (div V.a₂ (p : ℤ_[p])) := by
  rw [Step8.r, mod_out]
  split_ifs with h3
  · rw [residue_three_eq_one_two hp2] at h3
    exact absurd h3 one_ne_zero
  · rw [residue_three_eq_one_two hp2, div_one, cubic]

/-- `Step7.tY` is a lift of the residue of `-a₆ / ϖ ^ (2n)` at `p = 2`. -/
theorem Step7.mod_tY_two (hp2 : p = 2) (V : WeierstrassCurve ℤ_[p]) (n : ℕ) :
    mod (p : ℤ_[p]) (Step7.tY (p : ℤ_[p]) V n)
      = - mod (p : ℤ_[p]) (div V.a₆ ((p : ℤ_[p]) ^ (2 * n))) := by
  rw [Step7.tY, mod_out]
  split_ifs with h2
  · have hc : CharP (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 :=
      (charP_iff_prime_eq_zero (by decide)).mpr h2
    have hpr : PerfectRing (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 := PerfectField.toPerfectRing 2
    rw [root_two_eq_self_two hp2, quadratic]
  · exact absurd (Step2.residue_two_eq_zero_of_eq_two hp2) h2

/-! ### Changes of variables with `u = 1` on a short model -/

variable (a₄ a₆ R S T : ℤ_[p])

/-- The change of variables `(1, R, S, T)` sends the short model `y² = x³ + a₄x + a₆` to a model
with `a₁ = 2S`. -/
theorem smul_ofShortNF_a₁ :
    ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).a₁ = 2 * S := by
  simp [variableChange_a₁]

/-- The change of variables `(1, R, S, T)` sends the short model `y² = x³ + a₄x + a₆` to a model
with `a₂ = 3R - S²`. -/
theorem smul_ofShortNF_a₂ :
    ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).a₂ = 3 * R - S ^ 2 := by
  simp [variableChange_a₂]

/-- The change of variables `(1, R, S, T)` sends the short model `y² = x³ + a₄x + a₆` to a model
with `a₃ = 2T`. -/
theorem smul_ofShortNF_a₃ :
    ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).a₃ = 2 * T := by
  simp [variableChange_a₃]

/-- The change of variables `(1, R, S, T)` sends the short model `y² = x³ + a₄x + a₆` to a model
with `a₄` replaced by `a₄ + 3R² - 2ST`. -/
theorem smul_ofShortNF_a₄ :
    ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).a₄ = a₄ + 3 * R ^ 2 - 2 * S * T := by
  simp [variableChange_a₄]

/-- The change of variables `(1, R, S, T)` sends the short model `y² = x³ + a₄x + a₆` to a model
with `a₆` replaced by `a₆ + Ra₄ + R³ - T²`. -/
theorem smul_ofShortNF_a₆ :
    ((VariableChange.mk 1 R S T) • ofShortNF a₄ a₆).a₆
      = a₆ + R * a₄ + R ^ 3 - T ^ 2 := by
  simp [variableChange_a₆]

variable {a₄ a₆ R S T}

/-- Composition of two `u = 1` changes of variables. -/
theorem mk_one_mul_mk_one (R₁ S₁ T₁ R₂ S₂ T₂ : ℤ_[p]) :
    (VariableChange.mk 1 R₂ S₂ T₂ : VariableChange ℤ_[p]) * VariableChange.mk 1 R₁ S₁ T₁
      = VariableChange.mk 1 (R₂ + R₁) (S₂ + S₁) (T₂ + R₂ * S₁ + T₁) := by
  ext <;> simp [VariableChange.mul_def]

/-- Applying a second `u = 1` change of variables. -/
theorem smul_smul_eq (W : WeierstrassCurve ℤ_[p]) {R₁ S₁ T₁ R₂ S₂ T₂ : ℤ_[p]}
    (hR : R = R₂ + R₁) (hS : S = S₂ + S₁) (hT : T = T₂ + R₂ * S₁ + T₁) :
    (VariableChange.mk 1 R₂ S₂ T₂) • ((VariableChange.mk 1 R₁ S₁ T₁) • W)
      = (VariableChange.mk 1 R S T) • W := by
  subst hR; subst hS; subst hT
  rw [← mk_one_mul_mk_one, mul_smul]

/-! ### The congruences forced by the split locus -/

private theorem zmod_a₄_of_cube (hp2 : p = 2) :
    ∀ A : ZMod (p ^ 4), A ^ 3 + 3 = 0 → A - 5 = 0 := by
  subst hp2; decide

private theorem zmod_beta (hp2 : p = 2) :
    ∀ A B : ZMod (p ^ 2),
      23 + 75 * A + 240 * A ^ 2 + 256 * A ^ 3 + 81 * B + 108 * B ^ 2 = 0 → B - A - 1 = 0 := by
  subst hp2; decide

/-- **The split locus, parametrised.** On a short model over `ℤ_2` with `a₆ = 2b`, `27b ≡ 1 mod 8`
and `2 ^ 14 ∣ Δ`, one has `a₄ ≡ 5 mod 16` and `b ≡ 11 + 8a mod 32`, where `a₄ = 5 + 16a`. -/
theorem exists_params_of_split_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ b : ℤ_[p]}
    (ha₆ : a₆ = 2 * b) (hsplit : b ∈ splitSetTwo p)
    (hΔ : (p : ℤ_[p]) ^ 14 ∣ (ofShortNF a₄ a₆).Δ) :
    ∃ α k : ℤ_[p], a₄ = 5 + 16 * α ∧ b = 11 + 8 * α + 32 * k := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[p], 27 * w = 1 := by
    have h27 : IsUnit ((27 : ℕ) : ℤ_[p]) :=
      PadicInt.isUnit_natCast_of_not_dvd (by rw [hp2]; norm_num)
    obtain ⟨u, hu⟩ := h27.exists_right_inv
    exact ⟨u, by rw [← hu]; norm_num⟩
  obtain ⟨u, hu⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 1 := hsplit
  rw [hπ] at hu
  obtain ⟨β, hβ⟩ : ∃ β : ℤ_[p], b = 3 + 8 * β := by
    have h : 27 * (b - 3) = 8 * (u - 10) := by linear_combination hu
    exact ⟨w * (u - 10), by linear_combination w * h - (b - 3) * hw⟩
  obtain ⟨γ, hγ⟩ : (p : ℤ_[p]) ^ 8 ∣ a₄ ^ 3 + 27 * b ^ 2 := by
    have hkey : (ofShortNF a₄ a₆).Δ = (p : ℤ_[p]) ^ 6 * (-(a₄ ^ 3 + 27 * b ^ 2)) := by
      rw [ofShortNF_Δ, ha₆, hπ]; ring
    rw [hkey, show (14 : ℕ) = 6 + 8 from rfl, pow_add,
      mul_dvd_mul_iff_left (pow_ne_zero 6 hϖ)] at hΔ
    exact dvd_neg.1 hΔ
  rw [hπ] at hγ
  obtain ⟨α, hα⟩ : (p : ℤ_[p]) ^ 4 ∣ a₄ - 5 := by
    have h16 : (p : ℤ_[p]) ^ 4 ∣ a₄ ^ 3 + 3 := by
      refine ⟨16 * γ - (15 + 81 * β + 108 * β ^ 2), ?_⟩
      rw [hπ, hβ] at *
      linear_combination hγ
    rw [pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
    exact zmod_a₄_of_cube hp2 _ (by
      have hz := (pow_dvd_iff_toZModPow_eq_zero 4 _).1 h16
      rwa [map_add, map_pow, map_ofNat] at hz)
  rw [hπ] at hα
  have ha₄ : a₄ = 5 + 16 * α := by linear_combination hα
  have h16ne : (16 : ℤ_[p]) ≠ 0 := by
    rw [show (16 : ℤ_[p]) = (p : ℤ_[p]) ^ 4 from by rw [hπ]; norm_num]
    exact pow_ne_zero 4 hϖ
  have hE : (23 : ℤ_[p]) + 75 * α + 240 * α ^ 2 + 256 * α ^ 3 + 81 * β + 108 * β ^ 2 = 16 * γ := by
    refine mul_left_cancel₀ h16ne ?_
    rw [ha₄, hβ] at hγ
    linear_combination hγ
  obtain ⟨k, hk⟩ : (p : ℤ_[p]) ^ 2 ∣ β - α - 1 := by
    rw [pow_dvd_iff_toZModPow_eq_zero, map_sub, map_sub, map_one]
    refine zmod_beta hp2 _ _ ?_
    have hd : (p : ℤ_[p]) ^ 2 ∣ 23 + 75 * α + 240 * α ^ 2 + 256 * α ^ 3 + 81 * β + 108 * β ^ 2 :=
      ⟨4 * γ, by rw [hπ]; linear_combination hE⟩
    have hz := (pow_dvd_iff_toZModPow_eq_zero 2 _).1 hd
    rwa [map_add, map_add, map_add, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul,
      map_pow, map_pow, map_pow, map_ofNat, map_ofNat, map_ofNat, map_ofNat, map_ofNat,
      map_ofNat] at hz
  rw [hπ] at hk
  exact ⟨α, k, ha₄, by rw [hβ]; linear_combination 8 * hk⟩

/-! ### The three branch conditions in residue characteristic two -/

private theorem mod_eq_mod_of_dvd_sub {x y : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x - y) :
    mod (p : ℤ_[p]) x = mod (p : ℤ_[p]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-- **Step 6's cubic test at `p = 2`.** Over the residue field of `ℤ_2`, a cubic
`X³ + bX² + cX + d` with `b = c = d` has a double root. -/
theorem hasDoubleRoot_of_eq_two (hp2 : p = 2) {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    {e : ℤ_[p] ⧸ span {(p : ℤ_[p])}} (ha : P.a = 1) (hb : P.b = e) (hc : P.c = e)
    (hd : P.d = e) : P.HasDoubleRoot := by
  have hsq := residue_sq_eq_self_two hp2 e
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha, hb, hc, hd]
  linear_combination (-3 * e ^ 2 + 11 * e - 16) * hsq - 8 * e * h2

/-- **Step 7's cubic test at `p = 2`.** Over the residue field of `ℤ_2`, a cubic
`X³ + bX² + cX + d` with `b = c` has a triple root. -/
theorem hasTripleRoot_of_eq_two (hp2 : p = 2) {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    {e : ℤ_[p] ⧸ span {(p : ℤ_[p])}} (hb : P.b = e) (hc : P.c = e) : P.HasTripleRoot := by
  have hsq := residue_sq_eq_self_two hp2 e
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  rw [Cubic.HasTripleRoot, hb, hc]
  linear_combination hsq - e * h2

/-- **Step 8's quadratic test at `p = 2`.** Over the residue field of `ℤ_2`, `Y² + cY + d` with
`c = 0` has a double root. -/
theorem quadratic_hasDoubleRoot_of_eq_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hb : P.b = 1) (hc : P.c = 0) :
    P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_b_eq_one ha hb, hc, residue_four_eq_zero_two hp2]
  ring

/-! ### Steps 1–10 traverse on the split locus -/

/-- **Steps 1–10 of Tate's algorithm do not answer on a short model over `ℤ_2` with `a₄` a unit,
`a₆ = 2b`, `27b ≡ 1 mod 8` and `2 ^ 14 ∣ Δ`, so Step 11 fires.** -/
theorem Step11.run_eq_ok_of_split_two (hp2 : p = 2) {a₄ a₆ b : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (ha₆ : a₆ = (p : ℤ_[p]) * b) (ha₄u : IsUnit a₄)
    (hsplit : b ∈ splitSetTwo p) (hΔ14 : (p : ℤ_[p]) ^ 14 ∣ (ofShortNF a₄ a₆).Δ) :
    ∃ V, Step11.run PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  have ha₆' : a₆ = 2 * b := by rw [ha₆, hπ]
  obtain ⟨α, k, ha₄, hb⟩ := exists_params_of_split_two hp2 hπ ha₆' hsplit hΔ14
  have hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    (dvd_pow_self (p : ℤ_[p]) (by norm_num : (14 : ℕ) ≠ 0)).trans hΔ14
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
    dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inl hp2) a₄ a₆
  have h2run : Step2.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔd hc₄
  obtain ⟨r, t, hV1⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔd⟩
  have hval2 := Step2.hasValuation_translate hΔd
  rw [hV1] at h2run hval2
  have hva₄ : (p : ℤ_[p]) ∣ a₄ + 3 * r ^ 2 - 2 * 0 * t := by
    have h := hval2.a₄; rwa [smul_ofShortNF_a₄, pow_one] at h
  have hva₆ : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
    have h := hval2.a₆; rwa [smul_ofShortNF_a₆, pow_one] at h
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hy, hπ] at hc
      exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit
        ⟨c - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩ ha₄u)
    · exact ⟨y, hy⟩
  obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨b + 3 + 8 * α + 8 * ρ + 16 * α * ρ + 6 * ρ ^ 2 + 4 * ρ ^ 3, by
        rw [hπ, ha₆', ha₄, hr]; ring⟩
    have h3 : (p : ℤ_[p]) ∣ t ^ 2 := by
      have h := dvd_sub h2 hva₆
      rwa [show a₆ + r * a₄ + r ^ 3 - (a₆ + r * a₄ + r ^ 3 - t ^ 2) = t ^ 2 from by ring] at h
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h3
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 1 + 2 * α + 3 * m := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 7 + 8 * α + 16 * k + 3 * ρ + 8 * α * ρ + 2 * m + 4 * ρ * m - τ ^ 2 := ⟨_, rfl⟩
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = (p : ℤ_[p]) ^ 2 * τ := by
    rw [smul_ofShortNF_a₃, hπ, ht]; ring
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 3 * Q₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hQ₄]; linear_combination 12 * hm
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ, ha₆', hb, ha₄, hr, ht, hQ₆]; linear_combination (4 + 8 * ρ) * hm
  have h3run : Step3.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, hV1a₆⟩
  have h4run : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * r * Q₆ + 6 * r * τ ^ 2 - 8 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hπ]; ring
  have h5run : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hπ]; ring
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[p],
      x = Step6.s (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[p],
      x = Step6.t (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨σ, hs2⟩ : ∃ σ : ℤ_[p], s = 1 + 2 * σ := by
    have h : (p : ℤ_[p]) ∣ s - 3 * r := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hr] at hj
    exact ⟨1 + 3 * ρ + j, by linear_combination hj⟩
  obtain ⟨mσ, hmσ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ σ
  obtain ⟨θ, hθ⟩ : ∃ θ : ℤ_[p],
      (p : ℤ_[p]) * t₆ + t = (p : ℤ_[p]) * (1 + ρ + 2 * θ) := by
    have h : (p : ℤ_[p]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hQ₆] at hj
    refine ⟨3 + 4 * α + 8 * k + ρ + 4 * α * ρ + m + 2 * ρ * m + τ - mτ + j, ?_⟩
    rw [hπ, ht]
    linear_combination 2 * hj - 2 * hmτ
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = (p : ℤ_[p]) * (1 + ρ + 2 * θ) := by rw [hT₂, hθ]
  have hV2 : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s ((p : ℤ_[p]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[p], x = 1 + 3 * ρ - 4 * mσ := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[p], x = 2 * Q₄ - (1 + 2 * σ) * (1 + ρ + 2 * θ) := ⟨_, rfl⟩
  obtain ⟨X₆, hX₆⟩ : ∃ x : ℤ_[p], x = 3 + 4 * α + 8 * k + ρ + 4 * α * ρ + 2 * ρ * m
      - 2 * θ - 2 * ρ * θ - 2 * θ ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hs2, hX₂]; linear_combination -4 * hmσ
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hT₂v, hπ, ha₄, hr, hs2, hX₄, hQ₄]; linear_combination 12 * hm
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 3 * X₆ := by
    rw [smul_ofShortNF_a₆, hT₂v, hπ, ha₆', hb, ha₄, hr, hX₆]; linear_combination 8 * ρ * hm
  have hcb : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      (p : ℤ_[p])) = _
    rw [div_eq_of_eq_mul hV2a₂]
    exact mod_eq_mod_of_dvd_sub ⟨ρ - 2 * mσ, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul hV2a₄]
    exact mod_eq_mod_of_dvd_sub
      ⟨2 * α + 3 * m - ρ - θ - σ * (1 + ρ + 2 * θ), by rw [hπ, hX₄, hQ₄]; ring⟩
  have hcd : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      ((p : ℤ_[p]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul hV2a₆]
    exact mod_eq_mod_of_dvd_sub
      ⟨1 + 2 * α + 4 * k + 2 * α * ρ + ρ * m - θ - ρ * θ - θ ^ 2, by rw [hπ, hX₆]; ring⟩
  have hdouble := hasDoubleRoot_of_eq_two hp2 (by simp [cubic]) hcb hcc hcd
  have htriple := hasTripleRoot_of_eq_two hp2 hcb hcc
  have h6run : Step6.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    rw [hV2]
    exact ite_eq_left (by rw [← hV2] at hdouble ⊢; exact hdouble)
  have h7run : Step7.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[p],
      x = Step8.r (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℤ_[p], r₈ = 1 + ρ + 2 * ψ := by
    have h : (p : ℤ_[p]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_eq_of_eq_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hX₂] at hj
    exact ⟨ρ - 2 * mσ + j, by linear_combination hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[p], x = -1 - 4 * ψ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ x : ℤ_[p], x = θ - ψ - σ * (1 + ρ) - 2 * σ * ψ := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * v := ⟨_, rfl⟩
  have hV3 : Step8.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆ := by
    have h : Step8.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 (-(p : ℤ_[p]) * r₈) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₈def]
    rw [h]
    refine smul_smul_eq _ ?_ (by ring) ?_
    · rw [hR₃, hπ, hψ, hr]; ring
    · rw [hT₃, hT₂v, hπ, hψ, hs2, hv]; ring
  obtain ⟨E, hE⟩ : ∃ x : ℤ_[p], x = 1 + 4 * k - 2 * ψ - 4 * α * ψ - 3 * ψ ^ 2 - 4 * ψ ^ 3
      - v ^ 2 := ⟨_, rfl⟩
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃ = (p : ℤ_[p]) ^ 3 * v := by
    rw [smul_ofShortNF_a₃, hT₃, hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 4 * E := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hπ, ha₆', hb, ha₄, hE]; ring
  have hqc : (quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul (show ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * ((p : ℤ_[p]) * v) from by rw [hV3a₃]; ring), map_mul, mod_self, zero_mul]
  have hq := quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic])
    (by simp [quadratic]) hqc
  have h8run : Step8.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by
    rw [Step8.run.eq_def, h7run]
    simp only [except_ok_bind]
    rw [hV3]
    exact ite_eq_left hq
  obtain ⟨mψ, hmψ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ψ
  obtain ⟨mv, hmv⟩ := exists_sq_add_self_eq_two_mul hp2 hπ v
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[p],
      x = Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ l : ℤ_[p], v + tY = 1 + ψ + 2 * l := by
    have h : (p : ℤ_[p]) ∣ tY + E := by
      rw [← mod_eq_zero, map_add, htYdef,
        (Step7.mod_tY_two hp2 ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 :
          mod (p : ℤ_[p])
              (Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2)
            = - mod (p : ℤ_[p]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
                ((p : ℤ_[p]) ^ 4))),
        div_eq_of_eq_pow_mul hV3a₆, neg_add_cancel]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hE] at hj
    refine ⟨mv + 3 * mψ - ψ - 1 - 2 * k + 2 * α * ψ + 2 * ψ ^ 3 + j, ?_⟩
    linear_combination hj + hmv + 3 * hmψ
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * (1 + ψ + 2 * lam) := ⟨_, rfl⟩
  have hV4 : Step9.translate (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆ := by
    have h : Step9.translate (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by rw [htYdef]
    rw [h]
    refine smul_smul_eq _ (by ring) (by ring) ?_
    rw [hT₄, hT₃]
    linear_combination -(p : ℤ_[p]) ^ 2 * hlam
  have hV4a₄ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ 4 * (α + ψ + 3 * ψ ^ 2 - lam - σ * (1 + ψ + 2 * lam)) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, hπ, ha₄, hs2]; ring
  have hV4a₆ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ 6 * (k - ψ - α * ψ - ψ ^ 2 - ψ ^ 3 - lam - lam * ψ - lam ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₄, hπ, ha₆', hb, ha₄]; ring
  have h9run : Step9.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step9.run.eq_def, h8run]
    simp only [except_ok_bind]
    rw [hV4]
    exact ite_eq_left ⟨_, hV4a₄⟩
  have h10run : Step10.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step10.run.eq_def, h9run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨_, hV4a₆⟩
  exact ⟨Step11.translate (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆), by
    rw [Step11.run.eq_def, h10run]; rfl⟩

end WeierstrassCurve.TateAlgorithm

/-! ### `HasSplitStoreyDescent 2`, and the bounds on `α_p` -/

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- **`HasSplitStoreyDescent 2` holds.** On a short model over `ℤ_2` with `a₄` a unit, `a₆ = 2b`
with `27b ≡ 1 mod 8`, and `2 ^ 14 ∣ Δ`, Step 11 of Tate's algorithm fires. -/
theorem hasSplitStoreyDescent_of_eq_two (hp2 : p = 2) : HasSplitStoreyDescent p :=
  fun _a₄ _b hΔ0 ha₄ hsplit h14 =>
    TateAlgorithm.Step11.run_eq_ok_of_split_two hp2 hΔ0 rfl ha₄ hsplit h14

/-- For every prime `p`, `α_p < 1/2` and `α_p ≥ 1/88572`. -/
@[bsd_tamagawa "T022"]
theorem α_bounds : α p < 1 / 2 ∧ 1 / 88572 ≤ α p :=
  α_bounds_of_splitStoreyDescent hasSplitStoreyDescent_of_eq_two

end WeierstrassCurve
