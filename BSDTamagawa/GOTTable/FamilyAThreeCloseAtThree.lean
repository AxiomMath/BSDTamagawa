/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeBridgeAtThree
public import BSDTamagawa.GOTTable.FamilyAThreeSubsetAtThree

/-!
# The reflection halves Family A at `p = 3`

On the Family A locus at `p = 3` (the `Iₘ*` strata with `m ≥ 1`), the Tamagawa number is `2` on
exactly half of the mass and `4` on the other half: `2 · μ (part t) = μ locus` for `t = 2, 4`.

The Tamagawa number of a Family A point is `4` exactly when `ḡ^k ū` is a square in `𝔽₃`, where
`k = v₃(Δ)`, `ū = (Δ/3^k) mod 3` and `ḡ = (c₆/27) mod 3`. On a point `(3α, e)` with
`e − μ = 3^j t`, `μ` a root of `−4α³` and `t` a unit, these are `k = j + 3`, `u = −16 t (e + μ)`
and `g = −32 e`. The reflection `e ↦ 2μ − e` fixes `k` and `ḡ` and negates `ū`; since `−1` is not a
square in `𝔽₃`, it exchanges Tamagawa number `2` with `4`.

## Main definitions

* `WeierstrassCurve.FamilyAThree.half`: the half of the plane where `a₆ ≡ r (mod 3)`.

## Main results

* `WeierstrassCurve.FamilyAThree.tamagawaNumber_eq_four_iff`: on the locus, `c = 4` exactly when
  `ḡ^k ū` is a square.
* `WeierstrassCurve.FamilyAThree.invariants_of_ball`: `k` and `u` of a point near the root `μ`.
* `WeierstrassCurve.FamilyAThree.tamagawaNumber_reflect_eq_four_iff`: the reflection exchanges
  Tamagawa numbers `2` and `4`.
* `WeierstrassCurve.FamilyAThree.reflect_preimage_part`: the reflection exchanges, fibre by fibre,
  the two parts of a half.
* `WeierstrassCurve.FamilyAThree.two_mul_volume_part_two`,
  `WeierstrassCurve.FamilyAThree.two_mul_volume_part_four`: `2 · μ (part t) = μ locus` for
  `t = 2, 4`.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadDensityTwoBound
  TateAlgorithm

namespace FamilyAThree

/-! ### The invariant at the level of the run -/

/-- **On the Family A locus, the Tamagawa number is `4` exactly when `ḡ^k ū` is a square**, where
`Δ = 3^k u` with `3 ∤ u` and `c₆ = 27 g` are read off the short model. Steps 1 to 7 are `u = 1`
changes of variables, so the invariants of the model entering the subprocedure are those of the
input. -/
theorem tamagawaNumber_eq_four_iff {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0)
    (hx : x ∈ locus) {k : ℕ} {u g : ℤ_[3]}
    (hΔk : (ofShortNF x.1 x.2).Δ = ((3 : ℕ) : ℤ_[3]) ^ k * u) (hu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ u)
    (hc₆ : (ofShortNF x.1 x.2).c₆ = 27 * g) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = 4 ↔ IsSquare (mod ((3 : ℕ) : ℤ_[3]) g ^ k * mod ((3 : ℕ) : ℤ_[3]) u) := by
  obtain ⟨h6, hntr⟩ := step6_ok_of_mem_locus hx
  obtain ⟨out, h7, -⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hntr
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step7 hΔ h7)]
  rw [Step7.run.eq_def] at h7
  split at h7
  · rename_i out'' heq
    rw [h6] at heq
    exact absurd heq (by simp)
  · rename_i W₀ heq
    rw [h6] at heq
    obtain rfl := Except.ok.inj heq
    rw [dite_eq_right hntr] at h7
    obtain rfl := Except.error.inj h7
    refine Step7.subprocedure_tamagawaNumber_eq_four_iff_three _ _ _ _ _ ?_ hu ?_
    · rw [Step7.translate_Δ, Step6.translate_Δ, Step2.translate_Δ]; exact hΔk
    · rw [Step7.translate_c₆, Step6.translate_c₆, Step2.translate_c₆]; exact hc₆

/-! ### The invariants of a point near a root -/

/-- `c₆` of a short model, in the shape `27 g`. -/
theorem c₆_eq_twentySeven_mul (a e : ℤ_[3]) : (ofShortNF a e).c₆ = 27 * (-32 * e) := by
  rw [ofShortNF_c₆]; ring

/-- Two elements congruent modulo `3` have the same residue. -/
theorem mod_eq_of_dvd_sub {y z : ℤ_[3]} (h : ((3 : ℕ) : ℤ_[3]) ∣ y - z) :
    mod ((3 : ℕ) : ℤ_[3]) y = mod ((3 : ℕ) : ℤ_[3]) z := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-- Near a root, `e + μ` is a unit: `3 ∣ e − μ` and `3 ∣ e + μ` would give `3 ∣ 2μ`. -/
theorem not_dvd_add_of_dvd_sub {μ e : ℤ_[3]} (hμu : IsUnit μ) (h : ((3 : ℕ) : ℤ_[3]) ∣ e - μ) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ e + μ := by
  intro h'
  refine PadicInt.dvd_iff_not_isUnit.mp ?_ (isUnit_two_mul_of_isUnit hμu)
  have hd : (e + μ) - (e - μ) = 2 * μ := by ring
  rw [← hd]; exact dvd_sub h' h

/-- **The discriminant of a point near `μ` vanishes exactly when the point is `μ`.** -/
theorem Δ_ne_zero_iff {x : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]} (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α)
    (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ) (h : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ) :
    (ofShortNF x.1 x.2).Δ ≠ 0 ↔ x.2 - μ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have key : (ofShortNF x.1 x.2).Δ = -432 * ((x.2 - μ) * (x.2 + μ)) := by
    rw [h1, ofShortNF_Δ, hcast]; linear_combination (-432) * hμ
  rw [key, ne_eq, mul_eq_zero, mul_eq_zero, not_or, not_or]
  have hunit : x.2 + μ ≠ 0 := (isUnit_of_not_dvd (not_dvd_add_of_dvd_sub hμu h)).ne_zero
  exact ⟨fun h' => h'.2.1, fun h' => ⟨by norm_num, h', hunit⟩⟩

/-- **The invariants of a Family A point near the root `μ`**: writing `e − μ = 3^j t` with `t` a
unit, `Δ = 3^(j+3) · (−16 t (e + μ))` with a unit second factor. -/
theorem invariants_of_ball {α μ e : ℤ_[3]} (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ)
    (hne : e - μ ≠ 0) (hball : ((3 : ℕ) : ℤ_[3]) ∣ e - μ) :
    ∃ (j : ℕ) (t : ℤ_[3]), e - μ = ((3 : ℕ) : ℤ_[3]) ^ j * t ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ t ∧
      (ofShortNF (((3 : ℕ) : ℤ_[3]) * α) e).Δ
        = ((3 : ℕ) : ℤ_[3]) ^ (j + 3) * (-16 * t * (e + μ)) ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ -16 * t * (e + μ) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have ht : e - μ = ((3 : ℕ) : ℤ_[3]) ^ (e - μ).valuation * (PadicInt.unitCoeff hne : ℤ_[3]) := by
    rw [mul_comm]; exact PadicInt.unitCoeff_spec hne
  have htu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (PadicInt.unitCoeff hne : ℤ_[3]) :=
    fun h => PadicInt.dvd_iff_not_isUnit.mp h (Units.isUnit _)
  refine ⟨(e - μ).valuation, (PadicInt.unitCoeff hne : ℤ_[3]), ht, htu, ?_, ?_⟩
  · rw [ofShortNF_Δ, hcast]
    rw [hcast] at ht
    linear_combination (-432 * (e + μ)) * ht - 432 * hμ
  · rw [not_dvd_iff_mod_ne_zero, map_mul, map_mul, map_neg, map_ofNat, map_add,
      mod_eq_of_dvd_sub hball, ← two_mul]
    have h16 : (-16 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) ≠ 0 := by
      rw [show (-16 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = -1 from by
        linear_combination (-5) * residue_three_eq_zero]
      exact neg_ne_zero.mpr one_ne_zero
    have hμ0 : mod ((3 : ℕ) : ℤ_[3]) μ ≠ 0 :=
      (not_dvd_iff_mod_ne_zero μ).mp fun h => PadicInt.dvd_iff_not_isUnit.mp h hμu
    exact mul_ne_zero (mul_ne_zero h16 ((not_dvd_iff_mod_ne_zero _).mp htu))
      (mul_ne_zero residue_two_ne_zero_three hμ0)

/-! ### The reflection exchanges Tamagawa numbers `2` and `4` -/

/-- **The reflection through the near root exchanges Tamagawa `2` and `4`.** On a point `(3α, e)`
with `3⁴ ∣ e − μ`, hence in the locus, the reflected point `(3α, 2μ − e)` has the same `k` and `ḡ`
and the negated `ū`, and `−1` is not a square in `𝔽₃`. -/
theorem tamagawaNumber_reflect_eq_four_iff {x x' : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]}
    (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ) (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α)
    (h1' : x'.1 = x.1) (h2' : x'.2 = 2 * μ - x.2)
    (hball : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 - μ) (hx : x ∈ locus) (hx' : x' ∈ locus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) (hΔ' : (ofShortNF x'.1 x'.2).Δ ≠ 0) :
    ((TateAlgorithm.run (W := ofShortNF x'.1 x'.2)
        PadicInt.uniformizer_ne_zero hΔ').tamagawaNumber = 4 ↔
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hball1 : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ :=
    (dvd_pow_self _ (by norm_num : (4 : ℕ) ≠ 0)).trans hball
  have hne : x.2 - μ ≠ 0 := (Δ_ne_zero_iff h1 hμ hμu hball1).mp hΔ
  obtain ⟨j, t, ht, htu, hΔe, hue⟩ := invariants_of_ball hμ hμu hne hball1
  have hΔk : (ofShortNF x.1 x.2).Δ = ((3 : ℕ) : ℤ_[3]) ^ (j + 3) * (-16 * t * (x.2 + μ)) := by
    rw [h1]; exact hΔe
  have hΔk' : (ofShortNF x'.1 x'.2).Δ
      = ((3 : ℕ) : ℤ_[3]) ^ (j + 3) * (16 * t * (3 * μ - x.2)) := by
    rw [h1', h1, h2', ofShortNF_Δ, hcast]
    rw [hcast] at ht
    linear_combination (432 * (3 * μ - x.2)) * ht - 432 * hμ
  have hμe : mod ((3 : ℕ) : ℤ_[3]) μ = mod ((3 : ℕ) : ℤ_[3]) x.2 :=
    (mod_eq_of_dvd_sub hball1).symm
  have he0 : mod ((3 : ℕ) : ℤ_[3]) x.2 ≠ 0 := by
    rw [← hμe]
    exact (not_dvd_iff_mod_ne_zero μ).mp fun h => PadicInt.dvd_iff_not_isUnit.mp h hμu
  have hue' : ¬ ((3 : ℕ) : ℤ_[3]) ∣ 16 * t * (3 * μ - x.2) := by
    rw [not_dvd_iff_mod_ne_zero]
    simp only [map_mul, map_ofNat, map_sub, residue_three_eq_zero, zero_mul, zero_sub]
    have h16 : (16 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) ≠ 0 := by
      rw [show (16 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 1 from by
        linear_combination 5 * residue_three_eq_zero]
      exact one_ne_zero
    exact mul_ne_zero (mul_ne_zero h16 ((not_dvd_iff_mod_ne_zero _).mp htu))
      (neg_ne_zero.mpr he0)
  have hA := tamagawaNumber_eq_four_iff (x := x) hΔ hx hΔk hue (c₆_eq_twentySeven_mul x.1 x.2)
  have hB := tamagawaNumber_eq_four_iff (x := x') hΔ' hx' hΔk' hue'
    (c₆_eq_twentySeven_mul x'.1 x'.2)
  have h32 : (-32 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 1 := by
    linear_combination (-11) * residue_three_eq_zero
  have hg : mod ((3 : ℕ) : ℤ_[3]) (-32 * x'.2) = mod ((3 : ℕ) : ℤ_[3]) (-32 * x.2) := by
    rw [h2']
    simp only [map_mul, map_neg, map_ofNat, map_sub, hμe]
    ring
  have hu : mod ((3 : ℕ) : ℤ_[3]) (16 * t * (3 * μ - x.2))
      = -mod ((3 : ℕ) : ℤ_[3]) (-16 * t * (x.2 + μ)) := by
    simp only [map_mul, map_neg, map_ofNat, map_sub, map_add, hμe]
    ring
  have hGD : mod ((3 : ℕ) : ℤ_[3]) (-32 * x.2) ^ (j + 3)
      * mod ((3 : ℕ) : ℤ_[3]) (-16 * t * (x.2 + μ)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) ((not_dvd_iff_mod_ne_zero _).mp hue)
    simp only [map_mul, map_neg, map_ofNat]
    refine mul_ne_zero ?_ he0
    rw [h32]; exact one_ne_zero
  rw [hB, hg, hu, mul_neg, isSquare_neg_iff_three (p := 3) rfl hGD, ← hA]
  rcases tamagawaNumber_eq_two_or_four_of_mem_locus (x := x) hΔ hx with h2 | h4
  · rw [h2]; exact ⟨fun _ => rfl, fun _ => by norm_num⟩
  · rw [h4]; exact ⟨fun h => absurd rfl h, fun h => absurd h (by norm_num)⟩

/-! ### Membership of the locus and of its parts, near a root -/

/-- **A point near a root lies on the locus.** -/
theorem mem_locus_of_ball {x : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]} (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α)
    (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α) (hμ : μ * μ = -(4 * α ^ 3))
    (hball : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 - μ) : x ∈ locus := by
  rw [mem_locus_iff]
  refine ⟨α, h1, ?_, ?_⟩
  · have hc : (ZMod.cast (PadicInt.toZModPow 4 α) : ZMod (3 ^ 1)) = PadicInt.toZModPow 1 α :=
      PadicInt.cast_toZModPow 1 4 (by norm_num) α
    have h2 : PadicInt.toZModPow 1 α ≠ 0 := by
      rw [ne_eq, ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]; exact hα
    have h3 : (ZMod.cast (PadicInt.toZModPow 4 α) : ZMod (3 ^ 1)) ≠ 0 := hc ▸ h2
    simpa using h3
  · have hdeep : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ 4 * α ^ 3 + x.2 ^ 2 := by
      rw [← factor_form hμ]; exact hball.mul_right _
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_pow,
      map_ofNat] at hdeep
    exact hdeep

/-- A point of the locus with `3 ∣ e − μ` is in fact `3⁴`-close to `μ`: the whole depth of
`4α³ + e² = (e − μ)(e + μ)` sits on the factor `e − μ`, the other being a unit. -/
theorem pow_four_dvd_sub_of_mem_locus {x : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]}
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ)
    (hx : x ∈ locus) (h : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ) : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 - μ := by
  obtain ⟨α', h1', -, -, hdeep⟩ := exists_form_of_mem_locus hx
  obtain rfl : α' = α := mul_left_cancel₀ PadicInt.uniformizer_ne_zero (h1'.symm.trans h1)
  rcases pow_dvd_sub_or_pow_dvd_add hμ hμu hdeep with h4 | h4
  · exact h4
  · exact absurd ((dvd_pow_self _ (by norm_num : (4 : ℕ) ≠ 0)).trans h4)
      (not_dvd_add_of_dvd_sub hμu h)

/-- The reflected point is nonsingular exactly when the point is. -/
theorem reflect_Δ_ne_zero {x : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]} (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α)
    (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ) (h : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (ofShortNF (x.1, 2 * μ - x.2).1 (x.1, 2 * μ - x.2).2).Δ ≠ 0 := by
  have h' : ((3 : ℕ) : ℤ_[3]) ∣ (x.1, 2 * μ - x.2).2 - μ := by
    dsimp only
    rw [show 2 * μ - x.2 - μ = -(x.2 - μ) by ring]
    exact h.neg_right
  rw [Δ_ne_zero_iff (x := (x.1, 2 * μ - x.2)) h1 hμ hμu h']
  dsimp only
  rw [show 2 * μ - x.2 - μ = -(x.2 - μ) by ring, neg_ne_zero]
  exact (Δ_ne_zero_iff h1 hμ hμu h).mp hΔ

/-- The reflected point is `3⁴`-close to the root when the point is. -/
theorem reflect_pow_four_dvd {x : ℤ_[3] × ℤ_[3]} {μ : ℤ_[3]}
    (hball : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ x.2 - μ) :
    ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ (x.1, 2 * μ - x.2).2 - μ := by
  dsimp only
  exact reflect_pow_dvd_sub.mpr hball

/-- **The reflection carries the Tamagawa-`2` part of a ball into the Tamagawa-`4` part.** -/
theorem mem_part_four_reflect {x : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]}
    (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α) (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ)
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (h : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ) (hx : x ∈ part 2) :
    (x.1, 2 * μ - x.2) ∈ part 4 := by
  obtain ⟨hΔ, hL, h2⟩ := hx
  have hball := pow_four_dvd_sub_of_mem_locus h1 hμ hμu hL h
  have hL' : (x.1, 2 * μ - x.2) ∈ locus :=
    mem_locus_of_ball (x := (x.1, 2 * μ - x.2)) h1 hα hμ (reflect_pow_four_dvd hball)
  have hΔ' := reflect_Δ_ne_zero h1 hμ hμu h hΔ
  exact ⟨hΔ', hL', (tamagawaNumber_reflect_eq_four_iff (x' := (x.1, 2 * μ - x.2)) hμ hμu h1
    rfl rfl hball hL hL' hΔ hΔ').mpr h2⟩

/-- **The reflection carries the Tamagawa-`4` part of a ball into the Tamagawa-`2` part.** -/
theorem mem_part_two_reflect {x : ℤ_[3] × ℤ_[3]} {α μ : ℤ_[3]}
    (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α) (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ)
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (h : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ) (hx : x ∈ part 4) :
    (x.1, 2 * μ - x.2) ∈ part 2 := by
  obtain ⟨hΔ, hL, h4⟩ := hx
  have hball := pow_four_dvd_sub_of_mem_locus h1 hμ hμu hL h
  have hL' : (x.1, 2 * μ - x.2) ∈ locus :=
    mem_locus_of_ball (x := (x.1, 2 * μ - x.2)) h1 hα hμ (reflect_pow_four_dvd hball)
  have hΔ' := reflect_Δ_ne_zero h1 hμ hμu h hΔ
  refine ⟨hΔ', hL', ?_⟩
  have hflip := tamagawaNumber_reflect_eq_four_iff (x' := (x.1, 2 * μ - x.2)) hμ hμu h1
    rfl rfl hball hL hL' hΔ hΔ'
  rcases tamagawaNumber_eq_two_or_four_of_mem_locus (x := (x.1, 2 * μ - x.2)) hΔ' hL'
    with h2 | h4'
  · exact h2
  · exact absurd (hflip.mp h4') (by rw [h4]; norm_num)

/-! ### The two balls of the plane, cut by the residue of `a₆`

On the locus `a₆` is a unit, so its residue modulo `3` is `1` or `2`, and each value picks one of
the two roots `±μ` of `−4α³` — the one with the same residue. -/

/-- The half of the plane where `a₆ ≡ r (mod 3)`. -/
def half (r : ZMod (3 ^ 1)) : Set (ℤ_[3] × ℤ_[3]) := {x | PadicInt.toZModPow 1 x.2 = r}

/-- `half r` is the preimage of `r` under reduction of the second coordinate modulo `3`. -/
theorem half_eq_preimage (r : ZMod (3 ^ 1)) :
    half r = Prod.snd ⁻¹' (PadicInt.toZModPow 1 ⁻¹' {r}) := rfl

/-- A point lies in `half r` exactly when its second coordinate reduces to `r` modulo `3`. -/
@[simp] theorem mem_half_iff {r : ZMod (3 ^ 1)} {x : ℤ_[3] × ℤ_[3]} :
    x ∈ half r ↔ PadicInt.toZModPow 1 x.2 = r := Iff.rfl

/-- Each half `half r` is measurable. -/
theorem measurableSet_half (r : ZMod (3 ^ 1)) : MeasurableSet (half r) := by
  rw [half_eq_preimage]
  exact measurable_snd (PadicInt.measurableSet_preimage_toZModPow 1 r)

/-- Halves with distinct residues are disjoint. -/
theorem disjoint_half {r s : ZMod (3 ^ 1)} (hrs : r ≠ s) : Disjoint (half r) (half s) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hrs (hx.symm.trans hx')

/-- **On the locus, `a₆` is `1` or `2` modulo `3`.** -/
theorem mem_half_one_or_two_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) :
    x ∈ half 1 ∨ x ∈ half 2 := by
  obtain ⟨-, -, -, he, -⟩ := exists_form_of_mem_locus hx
  have h0 : PadicInt.toZModPow 1 x.2 ≠ 0 := by
    rw [ne_eq, ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]; exact he
  have key : ∀ z : ZMod (3 ^ 1), z ≠ 0 → z = 1 ∨ z = 2 := by decide
  exact key _ h0

/-- A root of `−4α³` may be chosen with any prescribed nonzero residue. -/
theorem exists_root_of_residue {α ν : ℤ_[3]} (hν : ν * ν = -(4 * α ^ 3)) (hνu : IsUnit ν)
    {r : ZMod (3 ^ 1)} (hr : r = 1 ∨ r = 2) :
    ∃ μ : ℤ_[3], μ * μ = -(4 * α ^ 3) ∧ IsUnit μ ∧ PadicInt.toZModPow 1 μ = r := by
  have h0 : PadicInt.toZModPow 1 ν ≠ 0 := by
    rw [ne_eq, ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact fun h => PadicInt.dvd_iff_not_isUnit.mp h hνu
  by_cases hνr : PadicInt.toZModPow 1 ν = r
  · exact ⟨ν, hν, hνu, hνr⟩
  · refine ⟨-ν, by rw [neg_mul_neg]; exact hν, hνu.neg, ?_⟩
    rw [map_neg]
    have key : ∀ z s : ZMod (3 ^ 1), z ≠ 0 → (s = 1 ∨ s = 2) → z ≠ s → -z = s := by decide
    exact key _ _ h0 hr hνr

/-- The residue condition of the half, transported to the root: `x ∈ half r` with
`toZModPow 1 μ = r` says `3 ∣ x.2 − μ`. -/
theorem dvd_sub_of_mem_half {r : ZMod (3 ^ 1)} {μ : ℤ_[3]} (hμr : PadicInt.toZModPow 1 μ = r)
    {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ half r) : ((3 : ℕ) : ℤ_[3]) ∣ x.2 - μ := by
  have h : PadicInt.toZModPow 1 x.2 = PadicInt.toZModPow 1 μ := (hx : _ = r).trans hμr.symm
  rwa [PadicInt.toZModPow_eq_iff_pow_dvd_sub, pow_one] at h

/-- The reflection through `μ` preserves the half `μ` lies in. -/
theorem reflect_mem_half {r : ZMod (3 ^ 1)} {μ e : ℤ_[3]} (hμr : PadicInt.toZModPow 1 μ = r)
    (he : PadicInt.toZModPow 1 e = r) : PadicInt.toZModPow 1 (2 * μ - e) = r := by
  rw [map_sub, map_mul, map_ofNat, hμr, he]
  ring

/-! ### The fibrewise identity -/

/-- **The reflection through the root `μ` of the half `r` exchanges, fibre by fibre over `a₄ = 3α`,
the Tamagawa-`4` and Tamagawa-`2` parts of that half.** -/
theorem reflect_preimage_part {α μ : ℤ_[3]} (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α)
    (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ) {r : ZMod (3 ^ 1)}
    (hμr : PadicInt.toZModPow 1 μ = r) :
    (fun y => 2 * μ - y) ⁻¹' (Prod.mk (((3 : ℕ) : ℤ_[3]) * α) ⁻¹' (part 4 ∩ half r))
      = Prod.mk (((3 : ℕ) : ℤ_[3]) * α) ⁻¹' (part 2 ∩ half r) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨h4, hr⟩
    have h2 := mem_part_two_reflect (x := (((3 : ℕ) : ℤ_[3]) * α, 2 * μ - y)) hα hμ hμu rfl
      (dvd_sub_of_mem_half (x := (((3 : ℕ) : ℤ_[3]) * α, 2 * μ - y)) hμr hr) h4
    have hh := reflect_mem_half (e := 2 * μ - y) hμr hr
    dsimp only at h2
    rw [sub_sub_cancel] at h2 hh
    exact ⟨h2, hh⟩
  · rintro ⟨h2, hr⟩
    exact ⟨mem_part_four_reflect (x := (((3 : ℕ) : ℤ_[3]) * α, y)) hα hμ hμu rfl
      (dvd_sub_of_mem_half (x := (((3 : ℕ) : ℤ_[3]) * α, y)) hμr hr) h2,
      reflect_mem_half (e := y) hμr hr⟩

/-- The same identity with the roles of `2` and `4` exchanged, by involutivity. -/
theorem reflect_preimage_part' {α μ : ℤ_[3]} (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α)
    (hμ : μ * μ = -(4 * α ^ 3)) (hμu : IsUnit μ) {r : ZMod (3 ^ 1)}
    (hμr : PadicInt.toZModPow 1 μ = r) :
    (fun y => 2 * μ - y) ⁻¹' (Prod.mk (((3 : ℕ) : ℤ_[3]) * α) ⁻¹' (part 2 ∩ half r))
      = Prod.mk (((3 : ℕ) : ℤ_[3]) * α) ⁻¹' (part 4 ∩ half r) := by
  rw [← reflect_preimage_part hα hμ hμu hμr, ← Set.preimage_comp]
  have h : ((fun y : ℤ_[3] => 2 * μ - y) ∘ fun y => 2 * μ - y) = id :=
    funext fun y => sub_sub_cancel _ y
  rw [h, Set.preimage_id]

/-- For `r = 1` or `2` and every `a₄`, some reflection `y ↦ c − y` exchanges the `a₄`-fibres of
`part 4 ∩ half r` and `part 2 ∩ half r`. -/
theorem exists_reflect_fibre (r : ZMod (3 ^ 1)) (hr : r = 1 ∨ r = 2) (a : ℤ_[3]) :
    ∃ c : ℤ_[3],
      (fun y => c - y) ⁻¹' (Prod.mk a ⁻¹' (part 4 ∩ half r)) = Prod.mk a ⁻¹' (part 2 ∩ half r) ∧
      (fun y => c - y) ⁻¹' (Prod.mk a ⁻¹' (part 2 ∩ half r)) = Prod.mk a ⁻¹' (part 4 ∩ half r) := by
  by_cases hex : ∃ y, (a, y) ∈ locus
  · obtain ⟨y, hy⟩ := hex
    obtain ⟨α, h1, hα, -, hdeep⟩ := exists_form_of_mem_locus hy
    have ha : a = ((3 : ℕ) : ℤ_[3]) * α := h1
    subst ha
    obtain ⟨ν, hν, hνu⟩ := exists_sqrt_neg_four_mul_cube hα
      ((dvd_pow_self _ (by norm_num : (4 : ℕ) ≠ 0)).trans hdeep)
    obtain ⟨μ, hμ, hμu, hμr⟩ := exists_root_of_residue hν hνu hr
    exact ⟨2 * μ, reflect_preimage_part hα hμ hμu hμr, reflect_preimage_part' hα hμ hμu hμr⟩
  · have hempty (t : ℕ) : Prod.mk a ⁻¹' (part t ∩ half r) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun y hy => hex ⟨y, part_subset_locus t hy.1⟩
    refine ⟨0, ?_, ?_⟩ <;> rw [hempty, hempty, Set.preimage_empty]

/-! ### Measurability of the parts -/

/-- `part t` is the intersection of the locus with the union over `m` of the strata `(I*_m, t)`. -/
theorem part_eq_inter_iUnion (t : ℕ) :
    part t = locus ∩ ⋃ m : ℕ, stratFibre 3 (KodairaSymbol.I! m, t) := by
  ext x
  constructor
  · rintro ⟨hΔ, hx, ht⟩
    obtain ⟨m, -, hks⟩ := exists_kodairaSymbol_eq_Istar_of_mem_locus hΔ hx
    refine ⟨hx, Set.mem_iUnion.2 ⟨m, (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_⟩⟩
    rw [strat]
    exact Prod.ext hks ht
  · rintro ⟨hx, hm⟩
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hm
    have hUp : x ∈ nonsingularLocus 3 := stratFibre_subset _ hm
    have h := (mem_stratFibre_iff hUp).1 hm
    rw [strat] at h
    exact ⟨hUp, hx, congrArg Prod.snd h⟩

/-- Each part `part t` is measurable. -/
theorem measurableSet_part (t : ℕ) : MeasurableSet (part t) := by
  rw [part_eq_inter_iUnion]
  exact measurableSet_locus.inter
    (MeasurableSet.iUnion fun m => (isOpen_stratFibre (p := 3) _).measurableSet)

/-! ### The halving -/

/-- The two halves cover each part. -/
theorem part_eq_union_half (t : ℕ) : part t = (part t ∩ half 1) ∪ (part t ∩ half 2) := by
  rw [← Set.inter_union_distrib_left]
  refine (Set.inter_eq_left.2 fun x hx => ?_).symm
  exact mem_half_one_or_two_of_mem_locus (part_subset_locus t hx)

/-- The singular points of the cylinder are null: `μ (locus ∩ nonsingularLocus 3) = μ locus`. -/
theorem volume_locus_inter_nonsingularLocus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (locus ∩ nonsingularLocus 3) =
      (volume : Measure (ℤ_[3] × ℤ_[3])) locus :=
  measure_inter_conull volume_compl_nonsingularLocus

/-- **Half of Family A carries Tamagawa number `2`.** -/
theorem two_mul_volume_part_two :
    2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (part 2) = (volume : Measure (ℤ_[3] × ℤ_[3])) locus := by
  rw [← volume_locus_inter_nonsingularLocus, part_two_union_part_four]
  have key := two_mul_volume_eq_of_two_fibrewise_reflects (S := part 2 ∪ part 4)
    (L₁ := part 2 ∩ half 1) (L₁' := part 4 ∩ half 1) (L₂ := part 2 ∩ half 2)
    (L₂' := part 4 ∩ half 2)
    ((measurableSet_part 2).inter (measurableSet_half 1))
    ((measurableSet_part 4).inter (measurableSet_half 1))
    ((measurableSet_part 2).inter (measurableSet_half 2))
    ((measurableSet_part 4).inter (measurableSet_half 2))
    (by rw [← part_eq_union_half 2, ← part_eq_union_half 4])
    (by rw [← part_eq_union_half 2, ← part_eq_union_half 4]; exact disjoint_part (by norm_num))
    ((disjoint_half (by decide)).mono Set.inter_subset_right Set.inter_subset_right)
    ((disjoint_half (by decide)).mono Set.inter_subset_right Set.inter_subset_right)
    (fun a => (exists_reflect_fibre 1 (Or.inl rfl) a).imp fun c h => h.1)
    (fun a => (exists_reflect_fibre 2 (Or.inr rfl) a).imp fun c h => h.1)
  rwa [← part_eq_union_half 2] at key

/-- **Half of Family A carries Tamagawa number `4`.** -/
theorem two_mul_volume_part_four :
    2 * (volume : Measure (ℤ_[3] × ℤ_[3])) (part 4) = (volume : Measure (ℤ_[3] × ℤ_[3])) locus := by
  rw [← volume_locus_inter_nonsingularLocus, part_two_union_part_four, Set.union_comm]
  have key := two_mul_volume_eq_of_two_fibrewise_reflects (S := part 4 ∪ part 2)
    (L₁ := part 4 ∩ half 1) (L₁' := part 2 ∩ half 1) (L₂ := part 4 ∩ half 2)
    (L₂' := part 2 ∩ half 2)
    ((measurableSet_part 4).inter (measurableSet_half 1))
    ((measurableSet_part 2).inter (measurableSet_half 1))
    ((measurableSet_part 4).inter (measurableSet_half 2))
    ((measurableSet_part 2).inter (measurableSet_half 2))
    (by rw [← part_eq_union_half 4, ← part_eq_union_half 2])
    (by rw [← part_eq_union_half 4, ← part_eq_union_half 2]; exact disjoint_part (by norm_num))
    ((disjoint_half (by decide)).mono Set.inter_subset_right Set.inter_subset_right)
    ((disjoint_half (by decide)).mono Set.inter_subset_right Set.inter_subset_right)
    (fun a => (exists_reflect_fibre 1 (Or.inl rfl) a).imp fun c h => h.2)
    (fun a => (exists_reflect_fibre 2 (Or.inr rfl) a).imp fun c h => h.2)
  rwa [← part_eq_union_half 4] at key

end FamilyAThree

end WeierstrassCurve

end
