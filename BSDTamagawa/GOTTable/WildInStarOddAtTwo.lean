/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildInStarAtTwo

/-!
# The odd `I₂*` loci at `p = 2`

On the class `a₄ ≡ 5 (mod 8)`, `a₆ ≡ −a₄ − 1 (mod 16)` the condition `v₂(4a₄³ + 27a₆²) = 6` is
decided modulo `32`: it is the four classes `(5, 26)`, `(13, 2)`, `(21, 10)`, `(29, 18)`, of mass
`4 · 2⁻¹⁰ = 2⁻⁸`, and on them Tate's algorithm answers `I₂*`. Modulo `64` those sixteen classes
split by Tamagawa number into two loci of eight classes each, of mass `8 · 2⁻¹² = 2⁻⁹`, lying in
the minimal parts of the rows `t = 2` and `t = 4` respectively.

With `a₄ = 5 + 8A`, `a₆ = 8A + 32F − 6`, the Tamagawa number is `4` exactly when `A + m + F` is
even, where `A² + A = 2m`. Split by `a₄ (mod 16)` that parity becomes a single linear congruence
modulo `64`: `64 ∣ a₄ + a₆ + 1` on `a₄ ≡ 5 (mod 16)` and `64 ∣ a₄ + a₆ − 15` on `a₄ ≡ 13 (mod 16)`.

In the run, Step 6's cubic has a double but not a triple root, and Step 7 enters its subprocedure
at level `2`. There the `Y`-quadratic has vanishing linear coefficient, hence a double root, and
after `Step7.translateY` the `X`-cubic `(a₂/2)X² + (a₄/8)X + a₆/32` has `a₂/2` and `a₄/8` both odd,
hence no double root: the loop exits with `I!(2·2 − 2) = I₂*`.

## Main definitions

* `WeierstrassCurve.aStarTwoTwoLocus`, `WeierstrassCurve.aStarTwoFourLocus`: the two loci.

## Main results

* `WeierstrassCurve.hasDoubleRoot_quadratic_zero_two`,
  `WeierstrassCurve.not_hasDoubleRoot_cubic_one_two`: the two branch tests of Step 7's subprocedure
  in residue characteristic `2`.
* `WeierstrassCurve.run_eq_AStar_two_of_step5`: if Steps 1–5 succeed, Step 6's cubic has a double
  but not a triple root, the level-`2` quadratic has a double root and the level-`2` cubic has
  none, Tate's algorithm returns `I₂*` with Tamagawa number `4` or `2`, at every prime.
* `WeierstrassCurve.Δ_ne_zero_AStarTwo`: nonsingularity on `a₄ = 5 + 8A`, `a₆ = 8A + 32F − 6`.
* `WeierstrassCurve.run_eq_AStar_two_at_two`: on `a₄ = 5 + 8A`, `a₆ = 8A + 32F − 6` Tate's
  algorithm returns `I₂*`, with Tamagawa number `4` exactly when `2 ∣ A + m + F`.
* `WeierstrassCurve.volume_aStarTwoTwoLocus`, `WeierstrassCurve.volume_aStarTwoFourLocus`: both
  loci have mass `1/512`.
-/

open CommRing Ideal CharP MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The two branch tests of the even exit -/

/-- **The level-`n` `Y`-quadratic has a double root once its linear coefficient vanishes.**
`HasDoubleRoot` for `⟨0, 1, c, d⟩` is `c² = 4d`, and `4 = 0` on `𝔽_2`, so `c = 0` establishes
it. -/
theorem hasDoubleRoot_quadratic_zero_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hb : P.b = 1) (hc : P.c = 0) :
    P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_b_eq_one ha hb, hc, residue_four_eq_zero_two hp2, zero_mul]
  ring

/-- **The level-`n` `X`-cubic has no double root once both its leading coefficients are units.**
`HasDoubleRoot` for `⟨0, b, c, d⟩` is `b²c² = 4b³d`, and `4 = 0` on `𝔽_2`, so `b = c = 1` refutes
it. -/
theorem not_hasDoubleRoot_cubic_one_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hb : P.b = 1) (hc : P.c = 1) :
    ¬ P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_zero ha, hb, hc, residue_four_eq_zero_two hp2]
  exact fun h => one_ne_zero (α := ℤ_[p] ⧸ span {(p : ℤ_[p])}) (by linear_combination h)

/-- If `ϖ = 2` and `x = y + 2z`, then `2 ∣ x ↔ 2 ∣ y`. -/
theorem dvd_iff_of_eq_add_two_mul (hπ : (p : ℤ_[p]) = 2) {x y z : ℤ_[p]} (h : x = y + 2 * z) :
    (p : ℤ_[p]) ∣ x ↔ (p : ℤ_[p]) ∣ y := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u - z, by rw [hπ] at hu ⊢; linear_combination hu - h⟩
  · rintro ⟨u, hu⟩
    exact ⟨u + z, by rw [hπ] at hu ⊢; linear_combination hu + h⟩

/-! ### The forwarding: the even exit of Step 7's subprocedure reaches `run` -/

open scoped Classical in
/-- **Steps 1–5 succeed, Step 6's cubic has a double but not a triple root, and Step 7's
subprocedure takes its second branch and exits there: the answer is `I₂*`**, with Tamagawa number
`4` or `2` according as the level-`2` cubic of the `Y`-translate has a root or not. -/
theorem run_eq_AStar_two_of_step5 {W V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hY : (quadratic (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2).HasDoubleRoot)
    (hX : ¬ (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 0 2).HasDoubleRoot) :
    (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I! 2 ∧
      (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if 0 < (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
            (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2)
            0 2).roots.toFinset.card
          then 4 else 2 := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h6 : Step6.run (p : ℤ_[p]) W = Except.ok (Step6.translate (p : ℤ_[p]) V) := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_left hdbl
  have hval6 := Step6.run_hasValuation hϖ h6
  have hΔc : (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)).Δ ≠ 0 := by
    rw [Step7.translate_Δ, Step6.run_Δ h6]; exact hΔ
  have hvc := Step7.hasValuation_translate hϖ hval6 hdbl hntr
  have ha₂c := Step7.not_dvd_translate_a₂ hϖ hval6.a₂ hdbl hntr
  have h7 := Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h6 hntr hΔc hvc ha₂c
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7),
    Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔc le_rfl hvc ha₂c hY hX]
  exact ⟨rfl, rfl⟩

/-! ### Nonsingularity on the locus -/

/-- On the locus the model is nonsingular: with `a₄ = 5 + 8A` and `a₆ = 2b`, `b = 4A + 16F − 3`,
the quantity `a₄³ + 27b²` is `≡ 16 (mod 32)`, hence nonzero. -/
theorem zmod_nonsingular_AStarTwo : ∀ X Z : ZMod (2 ^ 5),
    (5 + 8 * X) ^ 3 + 27 * (4 * X + 16 * Z - 3) ^ 2 ≠ 0 := by decide

/-- **Nonsingularity on the `A` locus at level `2`.** -/
theorem Δ_ne_zero_AStarTwo {a₄ a₆ A F : ℤ_[2]} (ha₄ : a₄ = 5 + 8 * A)
    (ha₆ : a₆ = 8 * A + 32 * F - 6) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  refine ofShortNF_Δ_ne_zero_of_two fun h => ?_
  have hcb : a₄ ^ 3 + 27 * (4 * A + 16 * F - 3) ^ 2 = 0 := by
    have h4 : (4 : ℤ_[2]) ≠ 0 := by
      rw [show (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 from by norm_num]
      exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero
    refine mul_left_cancel₀ h4 ?_
    rw [mul_zero, ha₆] at *
    linear_combination h
  have himg : PadicInt.toZModPow 5 (a₄ ^ 3 + 27 * (4 * A + 16 * F - 3) ^ 2) = 0 := by
    rw [hcb, map_zero]
  rw [ha₄] at himg
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at himg
  exact zmod_nonsingular_AStarTwo _ _ himg

/-! ### The forward run at level `2` -/

open scoped Classical in
/-- **The forward run at `I₂*`, on `a₄ = 5 + 8A` and `a₆ = 8A + 32F − 6`.** With `A² + A = 2m`,
Tate's algorithm at `2` returns `I₂*`, with Tamagawa number `4` if `A + m + F` is even and `2`
otherwise. -/
theorem run_eq_AStar_two_at_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A F m : ℤ_[p]}
    (ha₄ : a₄ = 5 + 8 * A) (ha₆ : a₆ = 8 * A + 32 * F - 6) (hm : A ^ 2 + A = 2 * m)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 2 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if (p : ℤ_[p]) ∣ A + m + F then 4 else 2 := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hπ]; ring⟩
  obtain ⟨r, t, hV⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔd⟩
  have hval2 := Step2.hasValuation_translate hΔd
  rw [hV] at hval2
  have hva₄ : (p : ℤ_[p]) ∣ a₄ + 3 * r ^ 2 := by
    have h := hval2.a₄
    rw [smul_ofShortNF_a₄, pow_one] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linear_combination hc⟩
  have hva₆ : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
    have h := hval2.a₆
    rw [smul_ofShortNF_a₆, pow_one] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linear_combination hc⟩
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hy, hπ, ha₄] at hc
      exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one
        ⟨c - 2 - 4 * A - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩)
    · exact ⟨y, hy⟩
  obtain ⟨mρ, hmρ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨4 * mρ + 6 * ρ + 16 * F + 8 * A + 8 * ρ * mρ + 8 * A * ρ, by
        rw [hπ, ha₆, ha₄, hr]; linear_combination (4 + 8 * ρ) * hmρ⟩
    obtain ⟨c, hc⟩ := h2
    obtain ⟨d, hd⟩ := hva₆
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨c - d, by linear_combination hc - hd⟩ : (p : ℤ_[p]) ∣ t ^ 2)
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 2 + 2 * A + 6 * mρ := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 2 * mρ + 3 * ρ + 8 * F + 4 * A - τ ^ 2 + 4 * ρ * mρ + 4 * A * ρ := ⟨_, rfl⟩
  have hA4 : a₄ + 3 * r ^ 2 = 4 * Q₄ := by rw [ha₄, hr, hQ₄]; linear_combination 12 * hmρ
  have hA6 : a₆ + r * a₄ + r ^ 3 - t ^ 2 = 4 * Q₆ := by
    rw [ha₆, ha₄, hr, ht, hQ₆]; linear_combination (4 + 8 * ρ) * hmρ
  have h5run := step5_run_eq_ok_of_two hp2 hπ hΔd hV ht hA4 hA6
  have hVa₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
  have hVa₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ]; linear_combination hA6
  obtain ⟨s, hs⟩ : ∃ x : ℤ_[p],
      x = Step6.s (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆⟩ : ∃ x : ℤ_[p],
      x = Step6.t (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ_[p], s = 1 + 2 * σ := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ s - 3 * r := by
      rw [← mod_eq_zero, map_sub, hs, Step6.mod_s_two hp2, hVa₂, sub_self]
    rw [hπ, hr] at hk
    exact ⟨1 + 3 * ρ + k, by linear_combination hk⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ_[p], t₆ = Q₆ + 2 * j := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hVa₆, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * t₆ + t := ⟨_, rfl⟩
  have hW₆ : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s ((p : ℤ_[p]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hs, ht₆]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[p], x = 1 + 3 * ρ - 2 * σ - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[p], x = Q₄ - s * (t₆ + τ) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ x : ℤ_[p], x = ρ + 2 * F + A + ρ * mρ + A * ρ := ⟨_, rfl⟩
  have hQ₆G : Q₆ = ρ ^ 2 - τ ^ 2 + 4 * G := by rw [hQ₆, hG]; linear_combination -hmρ
  have hK4 : (p : ℤ_[p]) ^ 2 ∣ Q₆ * (Q₆ + 2 * τ - 1) := by
    rw [pow_dvd_iff_toZModPow_eq_zero]
    have h4G : PadicInt.toZModPow 2 ((4 : ℤ_[p]) * G) = 0 :=
      (pow_dvd_iff_toZModPow_eq_zero 2 _).1 ⟨G, by rw [hπ]; ring⟩
    have hQr : PadicInt.toZModPow 2 Q₆
        = PadicInt.toZModPow 2 ρ ^ 2 - PadicInt.toZModPow 2 τ ^ 2 := by
      rw [hQ₆G, map_add, map_sub, map_pow, map_pow, h4G, add_zero]
    simp only [map_mul, map_sub, map_add, map_one, map_ofNat, hQr]
    exact zmod_double_root_two hp2 _ _
  obtain ⟨K, hK⟩ := hK4
  rw [hπ] at hK
  obtain ⟨X₆, hX₆⟩ : ∃ x : ℤ_[p], x = -2 * (K + j * (Q₆ + τ) + j ^ 2) := ⟨_, rfl⟩
  have hA6₂ : a₆ + r * a₄ + r ^ 3 = 4 * Q₆ + 4 * τ ^ 2 := by
    rw [ht] at hA6; linear_combination hA6
  have hW₆a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hσ, hX₂]; ring
  have hW₆a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hX₄, hT₂, ht, hπ]; linear_combination hA4
  have hW₆a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 3 * X₆ := by
    rw [smul_ofShortNF_a₆, hX₆, hT₂, hj, ht, hπ]; linear_combination hA6₂ - 4 * hK
  have hX₄res : mod (p : ℤ_[p]) X₄ = mod (p : ℤ_[p]) ρ :=
    mod_eq_mod_of_dvd_sub_two ⟨1 - j + mτ - τ + 2 * mρ - 2 * ρ - 4 * F - A - 2 * σ * j
      + 2 * mτ * σ - 2 * τ * σ - 2 * mρ * σ - 3 * ρ * σ - 2 * ρ * mρ - 8 * F * σ - 4 * A * σ
      - 2 * A * ρ - 4 * ρ * mρ * σ - 4 * A * ρ * σ, by
      rw [hX₄, hQ₄, hj, hQ₆, hσ, hπ]; linear_combination (1 + 2 * σ) * hmτ⟩
  have hcubb : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂) (p : ℤ_[p])) = _
    rw [div_eq_of_eq_mul_two hW₆a₂]
    exact mod_eq_mod_of_dvd_sub_two ⟨ρ - σ - σ ^ 2, by rw [hX₂, hπ]; ring⟩
  have hcubc : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod (p : ℤ_[p]) ρ := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄) ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hW₆a₄]
    exact hX₄res
  have hcubd : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d = 0 := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆) ((p : ℤ_[p]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hW₆a₆, mod_eq_zero]
    exact ⟨-(K + j * (Q₆ + τ) + j ^ 2), by rw [hX₆, hπ]; ring⟩
  have hdbl : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasDoubleRoot := by
    refine hasDoubleRoot_of_mul_eq_two hp2 rfl ?_
    rw [hcubb, hcubc, hcubd, ← map_mul, mod_eq_zero]
    exact ⟨mρ, by rw [hπ]; linear_combination hmρ⟩
  have hntr : ¬ (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasTripleRoot := by
    refine not_hasTripleRoot_of_sub_eq_one_two hp2 ?_
    rw [hcubb, hcubc, ← map_sub, show (1 : ℤ_[p]) + ρ - ρ = 1 from by ring, map_one]
  obtain ⟨r₇, hr₇⟩ : ∃ x : ℤ_[p],
      x = Step7.r (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨k₇, hk₇⟩ : ∃ k : ℤ_[p], r₇ = ρ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ r₇ - ρ := by
      rw [← mod_eq_zero, map_sub, hr₇, Step7.mod_r_two hp2,
        div_eq_of_eq_pow_mul_two hW₆a₄, hX₄res, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨R₇, hR₇⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * r₇ + r := ⟨_, rfl⟩
  obtain ⟨T₇, hT₇⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * r₇ * s + T₂ := ⟨_, rfl⟩
  have hW₇ : Step7.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆ := by
    have h : Step7.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 ((p : ℤ_[p]) * r₇) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₇]
    rw [h]
    exact smul_smul_eq _ (by rw [hR₇]) (by ring) (by rw [hT₇]; ring)
  obtain ⟨ν, hν⟩ : ∃ x : ℤ_[p], x = ρ + k₇ := ⟨_, rfl⟩
  obtain ⟨mν, hmν⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν
  have hR₇v : R₇ = 1 + 4 * ν := by rw [hR₇, hπ, hk₇, hr, hν]; ring
  obtain ⟨τ₈, hτ₈⟩ : ∃ x : ℤ_[p], x = k₇ + j - mτ + τ + mρ + 2 * ρ + 4 * F + 2 * A
    + 2 * σ * k₇ + ρ * σ + 2 * ρ * mρ + 2 * A * ρ := ⟨_, rfl⟩
  obtain ⟨m₈, hm₈⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ₈
  have hT₇v : T₇ = 4 * τ₈ := by
    rw [hT₇, hT₂, hπ, ht, hk₇, hσ, hj, hQ₆, hτ₈]; linear_combination -2 * hmτ
  have hpow2 : ((p : ℤ_[p])) ^ 2 = 4 := by rw [hπ]; norm_num
  have hpow3 : ((p : ℤ_[p])) ^ (2 + 1) = 8 := by rw [hπ]; norm_num
  have hpow4 : ((p : ℤ_[p])) ^ (2 * 2) = 16 := by rw [hπ]; norm_num
  have hpow5 : ((p : ℤ_[p])) ^ (2 * 2 + 1) = 32 := by rw [hπ]; norm_num
  obtain ⟨G₇, hG₇⟩ : ∃ x : ℤ_[p], x = F + ν - mν + A * ν + 4 * mν * ν - m₈ := ⟨_, rfl⟩
  obtain ⟨N₇, hN₇⟩ : ∃ x : ℤ_[p], x = A + ν + τ₈ + 2 * G₇ := ⟨_, rfl⟩
  have hW₇a₃ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * (2 * τ₈) := by rw [smul_ofShortNF_a₃, hT₇v, hpow2]; ring
  have hW₇a₆ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2) * N₇ := by
    rw [smul_ofShortNF_a₆, hR₇v, hT₇v, ha₄, ha₆, hN₇, hG₇, hpow4]
    linear_combination (-16 + 64 * ν) * hmν + -16 * hm₈
  have hτ₈res : mod (p : ℤ_[p]) (2 * τ₈) = 0 := by
    rw [mod_eq_zero]; exact ⟨τ₈, by rw [hπ]⟩
  have hquad : quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
      = ⟨0, 1, 0, -(mod (p : ℤ_[p]) N₇)⟩ := by
    rw [quadratic, div_eq_of_eq_pow_mul_two hW₇a₃, div_eq_of_eq_pow_mul_two hW₇a₆, hτ₈res]
  have hY : (quadratic (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)))
      2).HasDoubleRoot := by
    rw [hW₆, hW₇, hquad]
    exact hasDoubleRoot_quadratic_zero_two hp2 rfl rfl rfl
  obtain ⟨tY, htY⟩ : ∃ x : ℤ_[p],
      x = Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ k : ℤ_[p], tY = -N₇ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ tY + N₇ := by
      rw [← mod_eq_zero, map_add, htY, Step7.mod_tY_two hp2,
        div_eq_of_eq_pow_mul_two hW₇a₆, neg_add_cancel]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨T₈, hT₈⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * tY + T₇ := ⟨_, rfl⟩
  have hW₈ : Step7.translateY (p : ℤ_[p])
      ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
      = (VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆ := by
    have h : Step7.translateY (p : ℤ_[p])
        ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) := by rw [htY]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₈]; ring)
  obtain ⟨τ₉, hτ₉⟩ : ∃ x : ℤ_[p], x = tY + τ₈ := ⟨_, rfl⟩
  have hT₈v : T₈ = 4 * τ₉ := by rw [hT₈, hτ₉, hT₇v, hpow2]; ring
  obtain ⟨X₂', hX₂'⟩ : ∃ x : ℤ_[p], x = 1 + 6 * ν - 2 * σ - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨U₇, hU₇⟩ : ∃ x : ℤ_[p], x = 1 + A - 3 * ν + 12 * mν := ⟨_, rfl⟩
  obtain ⟨X₄', hX₄'⟩ : ∃ x : ℤ_[p], x = U₇ - s * τ₉ := ⟨_, rfl⟩
  obtain ⟨V₄, hV₄⟩ : ∃ x : ℤ_[p], x = A - ν + 6 * mν + G₇ - ℓ + σ * A + σ * ν
    + 2 * σ * G₇ - 2 * σ * ℓ := ⟨_, rfl⟩
  obtain ⟨mX, hmX⟩ : ∃ x : ℤ_[p], x = m + mν + m₈ + A * ν + A * τ₈ + ν * τ₈ := ⟨_, rfl⟩
  obtain ⟨mN, hmN'⟩ : ∃ x : ℤ_[p],
      x = mX + 2 * (A + ν + τ₈) * G₇ + 2 * G₇ ^ 2 + G₇ := ⟨_, rfl⟩
  obtain ⟨N₈, hN₈⟩ : ∃ x : ℤ_[p],
      x = N₇ - mN + τ₈ * N₇ - 2 * ℓ ^ 2 - 2 * τ₈ * ℓ + 2 * N₇ * ℓ := ⟨_, rfl⟩
  have hmN : N₇ ^ 2 + N₇ = 2 * mN := by
    rw [hN₇, hmN', hmX]; linear_combination hm + hmν + hm₈
  have hsum : a₆ + R₇ * a₄ + R₇ ^ 3 = 16 * N₇ + 16 * τ₈ ^ 2 := by
    rw [hR₇v, ha₄, ha₆, hN₇, hG₇]
    linear_combination (-16 + 64 * ν) * hmν + -16 * hm₈
  have hW₈a₂ : ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂' := by
    rw [smul_ofShortNF_a₂, hR₇v, hσ, hX₂', hπ]; ring
  have hW₈a₄ : ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ (2 + 1) * X₄' := by
    rw [smul_ofShortNF_a₄, hR₇v, hT₈v, hX₄', hU₇, hτ₉, hℓ, ha₄, hpow3]
    linear_combination 48 * hmν
  have hW₈a₆ : ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2 + 1) * N₈ := by
    rw [smul_ofShortNF_a₆, hT₈v, hτ₉, hℓ, hN₈, hpow5]
    linear_combination hsum - 16 * hmN
  have hX₂'res : mod (p : ℤ_[p]) X₂' = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := X₂') (y := 1)
      ⟨3 * ν - σ - σ ^ 2, by rw [hX₂', hπ]; ring⟩, map_one]
  have hX₄'res : mod (p : ℤ_[p]) X₄' = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := X₄') (y := 1)
      ⟨V₄, by rw [hX₄', hU₇, hτ₉, hℓ, hσ, hN₇, hV₄, hπ]; ring⟩, map_one]
  have hcub : cubic (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆) 0 2
      = ⟨0, 1, 1, mod (p : ℤ_[p]) N₈⟩ := by
    rw [cubic, div_eq_of_eq_mul_two hW₈a₂, div_eq_of_eq_pow_mul_two hW₈a₄,
      div_eq_of_eq_pow_mul_two hW₈a₆, hX₂'res, hX₄'res, map_zero]
  have hX : ¬ (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆))) 2)
      0 2).HasDoubleRoot := by
    rw [hW₆, hW₇, hW₈, hcub]
    exact not_hasDoubleRoot_cubic_one_two hp2 rfl rfl rfl
  have hmain := run_eq_AStar_two_of_step5 hΔ h5run (hW₆ ▸ hdbl) (hW₆ ▸ hntr) hY hX
  refine ⟨hmain.1, ?_⟩
  rw [hmain.2, hW₆, hW₇, hW₈, hcub]
  refine if_congr ?_ rfl rfl
  have hroot := card_roots_toFinset_pos_iff_two (p := p) hp2 (-(mod (p : ℤ_[p]) N₈))
  rw [neg_neg, neg_eq_zero] at hroot
  rw [hroot, mod_eq_zero]
  refine dvd_iff_of_eq_add_two_mul hπ (z := ν - mν + 2 * mν * ν - m - G₇ * (A + ν + τ₈)
    - G₇ ^ 2 + ℓ * (A + ν + τ₈) + 2 * ℓ * G₇ - ℓ ^ 2 + τ₈ * G₇ - τ₈ * ℓ) ?_
  rw [hN₈, hmN', hmX, hN₇, hG₇]
  linear_combination hm₈

/-! ### From a residue class modulo `64` to the parameters -/

/-- **The `a₄ ≡ 5 (mod 16)` half, parametrised.** `a₄ ≡ 5 (mod 16)` and `a₆ ≡ a₄ − 11 (mod 32)`
give `a₄ = 5 + 8(2A)` and `a₆ = 8(2A) + 32F − 6`, and then `a₄ + a₆ + 1 = 32(A + F)`. -/
theorem exists_params_AStarTwoFive {a₄ a₆ : ℤ_[2]}
    (h1 : (ZMod.cast (PadicInt.toZModPow 6 a₄ - 5) : ZMod (2 ^ 4)) = 0)
    (h2 : (ZMod.cast (PadicInt.toZModPow 6 a₆ - PadicInt.toZModPow 6 a₄ + 11)
      : ZMod (2 ^ 5)) = 0) :
    ∃ A F : ℤ_[2], a₄ = 5 + 8 * (2 * A) ∧ a₆ = 8 * (2 * A) + 32 * F - 6 ∧
      a₄ + a₆ + 1 = 32 * (A + F) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ a₄ - 5 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) ?_
    rwa [map_sub, map_ofNat]
  obtain ⟨F, hF⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ a₆ - a₄ + 11 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) ?_
    rwa [map_add, map_sub, map_ofNat]
  rw [hcast] at hA hF
  exact ⟨A, F, by linear_combination hA, by linear_combination hF + hA,
    by linear_combination hF + 2 * hA⟩

/-- **The `a₄ ≡ 13 (mod 16)` half, parametrised.** `a₄ ≡ 13 (mod 16)` and `a₆ ≡ a₄ − 11 (mod 32)`
give `a₄ = 5 + 8(1 + 2A)` and `a₆ = 8(1 + 2A) + 32F − 6`, and then
`a₄ + a₆ − 15 = 32(A + F)`. -/
theorem exists_params_AStarTwoThirteen {a₄ a₆ : ℤ_[2]}
    (h1 : (ZMod.cast (PadicInt.toZModPow 6 a₄ - 13) : ZMod (2 ^ 4)) = 0)
    (h2 : (ZMod.cast (PadicInt.toZModPow 6 a₆ - PadicInt.toZModPow 6 a₄ + 11)
      : ZMod (2 ^ 5)) = 0) :
    ∃ A F : ℤ_[2], a₄ = 5 + 8 * (1 + 2 * A) ∧ a₆ = 8 * (1 + 2 * A) + 32 * F - 6 ∧
      a₄ + a₆ - 15 = 32 * (A + F) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ a₄ - 13 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) ?_
    rwa [map_sub, map_ofNat]
  obtain ⟨F, hF⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ a₆ - a₄ + 11 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) ?_
    rwa [map_add, map_sub, map_ofNat]
  rw [hcast] at hA hF
  exact ⟨A, F, by linear_combination hA, by linear_combination hF + hA,
    by linear_combination hF + 2 * hA⟩

/-- For `x = 32y` in `ℤ_2`, `2 ∣ y` exactly when `x` vanishes modulo `2⁶`. -/
private theorem dvd_iff_toZModPow_six_two {y x : ℤ_[2]} (h : x = 32 * y) :
    ((2 : ℕ) : ℤ_[2]) ∣ y ↔ PadicInt.toZModPow 6 x = 0 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have h32 : (32 : ℤ_[2]) ≠ 0 := by
    rw [show (32 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 5 from by norm_num]
    exact pow_ne_zero 5 PadicInt.uniformizer_ne_zero
  rw [← pow_dvd_iff_toZModPow_eq_zero, hcast]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [h]; ring⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, mul_left_cancel₀ h32 (by rw [← h, hw]; ring)⟩

/-! ### The two residue sets modulo `64` -/

/-- **The residue condition cutting out the `(I₂*, 2)` locus at `2`**: eight classes modulo `64`,
four on `a₄ ≡ 5 (mod 16)` and four on `a₄ ≡ 13 (mod 16)`. -/
abbrev HeadResAStarTwoTwo (a e : ZMod (2 ^ 6)) : Prop :=
  (a = 5 ∧ e = 26) ∨ (a = 21 ∧ e = 10) ∨ (a = 37 ∧ e = 58) ∨ (a = 53 ∧ e = 42) ∨
    (a = 13 ∧ e = 34) ∨ (a = 29 ∧ e = 18) ∨ (a = 45 ∧ e = 2) ∨ (a = 61 ∧ e = 50)

/-- **The residue condition cutting out the `(I₂*, 4)` locus at `2`**: the complementary eight
classes modulo `64`, obtained from `HeadResAStarTwoTwo` by adding `32` to `a₆`. -/
abbrev HeadResAStarTwoFour (a e : ZMod (2 ^ 6)) : Prop :=
  (a = 5 ∧ e = 58) ∨ (a = 21 ∧ e = 42) ∨ (a = 37 ∧ e = 26) ∨ (a = 53 ∧ e = 10) ∨
    (a = 13 ∧ e = 2) ∨ (a = 29 ∧ e = 50) ∨ (a = 45 ∧ e = 34) ∨ (a = 61 ∧ e = 18)

/-- The eight residue pairs of `HeadResAStarTwoTwo`, as a `Finset`. -/
def headResiduesAStarTwoTwo : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(5, 26), (21, 10), (37, 58), (53, 42), (13, 34), (29, 18), (45, 2), (61, 50)}

/-- The eight residue pairs of `HeadResAStarTwoFour`, as a `Finset`. -/
def headResiduesAStarTwoFour : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(5, 58), (21, 42), (37, 26), (53, 10), (13, 2), (29, 50), (45, 34), (61, 18)}

/-- The residue set `headResiduesAStarTwoTwo` has eight elements. -/
theorem card_headResiduesAStarTwoTwo : headResiduesAStarTwoTwo.card = 8 := by decide

/-- The residue set `headResiduesAStarTwoFour` has eight elements. -/
theorem card_headResiduesAStarTwoFour : headResiduesAStarTwoFour.card = 8 := by decide

/-- A pair lies in `headResiduesAStarTwoTwo` exactly when it satisfies `HeadResAStarTwoTwo`. -/
theorem mem_headResiduesAStarTwoTwo_iff {c : ZMod (2 ^ 6) × ZMod (2 ^ 6)} :
    c ∈ headResiduesAStarTwoTwo ↔ HeadResAStarTwoTwo c.1 c.2 := by
  simp [headResiduesAStarTwoTwo, Prod.ext_iff]

/-- A pair lies in `headResiduesAStarTwoFour` exactly when it satisfies `HeadResAStarTwoFour`. -/
theorem mem_headResiduesAStarTwoFour_iff {c : ZMod (2 ^ 6) × ZMod (2 ^ 6)} :
    c ∈ headResiduesAStarTwoFour ↔ HeadResAStarTwoFour c.1 c.2 := by
  simp [headResiduesAStarTwoFour, Prod.ext_iff]

/-- **The case split of the `(I₂*, 2)` residue set**, by exhaustion over `(ZMod 64)²`: each class
either has `a₄ ≡ 5 (mod 16)`, `a₆ ≡ a₄ − 11 (mod 32)` and `a₄ + a₆ + 1 ≢ 0 (mod 64)`, or has
`a₄ ≡ 13 (mod 16)`, `a₆ ≡ a₄ − 11 (mod 32)` and `a₄ + a₆ − 15 ≢ 0 (mod 64)`. -/
theorem headResAStarTwoTwo_cases : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoTwo a e →
    ((ZMod.cast (a - 5) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast (e - a + 11) : ZMod (2 ^ 5)) = 0
        ∧ a + e + 1 ≠ 0) ∨
      ((ZMod.cast (a - 13) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast (e - a + 11) : ZMod (2 ^ 5)) = 0
        ∧ a + e - 15 ≠ 0) := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-- **The case split of the `(I₂*, 4)` residue set**: the same two congruences with the opposite
Tamagawa bit. -/
theorem headResAStarTwoFour_cases : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoFour a e →
    ((ZMod.cast (a - 5) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast (e - a + 11) : ZMod (2 ^ 5)) = 0
        ∧ a + e + 1 = 0) ∨
      ((ZMod.cast (a - 13) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast (e - a + 11) : ZMod (2 ^ 5)) = 0
        ∧ a + e - 15 = 0) := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-- On the `(I₂*, 2)` residue set `a₄` is odd, so `16 ∤ a₄`. -/
theorem headResAStarTwoTwo_notDvd : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-- On the `(I₂*, 4)` residue set `a₄` is odd, so `16 ∤ a₄`. -/
theorem headResAStarTwoFour_notDvd : ∀ a e : ZMod (2 ^ 6), HeadResAStarTwoFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-! ### The two loci, their masses and their minimality -/

/-- The **`(I₂*, 2)` locus** of the coefficient plane at `2`: eight residue classes modulo `64`. -/
noncomputable def aStarTwoTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesAStarTwoTwo : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- The **`(I₂*, 4)` locus** of the coefficient plane at `2`: eight residue classes modulo `64`. -/
noncomputable def aStarTwoFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesAStarTwoFour : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- A point lies in `aStarTwoTwoLocus` exactly when its reduction modulo `64` satisfies
`HeadResAStarTwoTwo`. -/
theorem mem_aStarTwoTwoLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ aStarTwoTwoLocus ↔
      HeadResAStarTwoTwo (PadicInt.toZModPow 6 x.1) (PadicInt.toZModPow 6 x.2) := by
  rw [aStarTwoTwoLocus, mem_preimage, Finset.mem_coe, mem_headResiduesAStarTwoTwo_iff,
    PadicInt.redPairPow]

/-- A point lies in `aStarTwoFourLocus` exactly when its reduction modulo `64` satisfies
`HeadResAStarTwoFour`. -/
theorem mem_aStarTwoFourLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ aStarTwoFourLocus ↔
      HeadResAStarTwoFour (PadicInt.toZModPow 6 x.1) (PadicInt.toZModPow 6 x.2) := by
  rw [aStarTwoFourLocus, mem_preimage, Finset.mem_coe, mem_headResiduesAStarTwoFour_iff,
    PadicInt.redPairPow]

/-- **The mass of the `(I₂*, 2)` locus is `8/4096 = 1/512`.** -/
theorem volume_aStarTwoTwoLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTwoTwoLocus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 12 := by
  rw [aStarTwoTwoLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesAStarTwoTwo]
  norm_num

/-- **The mass of the `(I₂*, 4)` locus is `8/4096 = 1/512`.** -/
theorem volume_aStarTwoFourLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTwoFourLocus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 12 := by
  rw [aStarTwoFourLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesAStarTwoFour]
  norm_num

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₂*, 2)` locus lies in the strata over `t = 2`.** -/
theorem aStarTwoTwoLocus_subset_iUnion_stratFibre :
    aStarTwoTwoLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  rcases headResAStarTwoTwo_cases _ _ (mem_aStarTwoTwoLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_AStarTwoFive h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_AStarTwo ha₄ ha₆
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_add, map_one] using h3
    obtain ⟨hk, ht⟩ := run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 2 * A ^ 2 + A) (by ring) hΔ
    rw [ite_eq_right (fun hc => hnd ((dvd_iff_of_eq_add_two_mul (p := 2) (by norm_num)
      (z := A + A ^ 2) (by ring)).1 hc))] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_AStarTwoThirteen h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_AStarTwo ha₄ ha₆
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_sub, map_add, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 1 + 3 * A + 2 * A ^ 2) (by ring) hΔ
    rw [ite_eq_right (fun hc => hnd ((dvd_iff_of_eq_add_two_mul (p := 2) (by norm_num)
      (z := 1 + 2 * A + A ^ 2) (by ring)).1 hc))] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₂*, 4)` locus lies in the strata over `t = 4`.** -/
theorem aStarTwoFourLocus_subset_iUnion_stratFibre :
    aStarTwoFourLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4) := by
  intro x hx
  rcases headResAStarTwoFour_cases _ _ (mem_aStarTwoFourLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_AStarTwoFive h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_AStarTwo ha₄ ha₆
    have hnd : ((2 : ℕ) : ℤ_[2]) ∣ A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_add, map_one] using h3
    obtain ⟨hk, ht⟩ := run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 2 * A ^ 2 + A) (by ring) hΔ
    rw [ite_eq_left ((dvd_iff_of_eq_add_two_mul (p := 2) (by norm_num)
      (z := A + A ^ 2) (by ring)).2 hnd)] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_AStarTwoThirteen h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_AStarTwo ha₄ ha₆
    have hnd : ((2 : ℕ) : ℤ_[2]) ∣ A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_sub, map_add, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_AStar_two_at_two (p := 2) rfl (by norm_num) ha₄ ha₆
      (m := 1 + 3 * A + 2 * A ^ 2) (by ring) hΔ
    rw [ite_eq_left ((dvd_iff_of_eq_add_two_mul (p := 2) (by norm_num)
      (z := 1 + 2 * A + A ^ 2) (by ring)).2 hnd)] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **No point of the `(I₂*, 2)` locus is a `(2⁴, 2⁶)`-dilate**: on it `a₄` is odd. -/
theorem notMem_range_of_mem_aStarTwoTwoLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTwoTwoLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResAStarTwoTwo_notDvd _ _ (mem_aStarTwoTwoLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- **No point of the `(I₂*, 4)` locus is a `(2⁴, 2⁶)`-dilate**: on it `a₄` is odd. -/
theorem notMem_range_of_mem_aStarTwoFourLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTwoFourLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResAStarTwoFour_notDvd _ _ (mem_aStarTwoFourLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- The `(I₂*, 2)` locus lies in the minimal part of the `t = 2` row. -/
theorem aStarTwoTwoLocus_subset_headMinimal :
    aStarTwoTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨aStarTwoTwoLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_aStarTwoTwoLocus hx⟩

/-- The `(I₂*, 4)` locus lies in the minimal part of the `t = 4` row. -/
theorem aStarTwoFourLocus_subset_headMinimal :
    aStarTwoFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨aStarTwoFourLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_aStarTwoFourLocus hx⟩

/-! ### The mass `8 · 2⁻¹²` -/

/-- `8 · 2⁻¹² = 1/512`. -/
theorem eight_mul_inv_pow_twelve_eq_two : (8 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 12 = 1 / 512 := by
  rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 12 = 4096 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
