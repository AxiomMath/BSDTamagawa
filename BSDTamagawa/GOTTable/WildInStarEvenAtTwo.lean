/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildInStarOddAtTwo
public import BSDTamagawa.GOTTable.WildRowGoodAtTwo

/-!
# The `I₄*` loci at `p = 2`

On `a₄ = 4 + 16A`, `a₆ = 16 + 32F` the quantity `4a₄³ + 27a₆²` is `2⁸ · ((1 + 4A)³ + 27(1 + 2F)²)`,
and the second factor is `4` times an odd number exactly when `A` is even. So the congruence
`a₄ ≡ 4 (mod 32)`, `a₆ ≡ 16 (mod 32)`, of mass `2⁻¹⁰`, is a locus on which `v₂(4a₄³ + 27a₆²) = 10`
and Tate's algorithm answers `I₄*`. Modulo `256` its sixty-four classes split by Tamagawa number
into two loci of thirty-two classes each, of mass `32 · 2⁻¹⁶ = 2⁻¹¹`, lying in the minimal parts
of the rows `t = 2` and `t = 4`.

With `a₄ = 4 + 32A`, `a₆ = 16 + 32F`, the Tamagawa number is `4` exactly when `J + FZ` is even,
where `F² + F = 2K`, `Z = A + K` and `Z² + Z = 2J`. That parity depends only on `Z (mod 4)` and
`F (mod 2)`, hence on `a₄ (mod 128)` and `a₆ (mod 256)`; it is not cut out by a linear congruence.

In the run, Step 6's cubic has a double but not a triple root, and Step 7 enters its subprocedure
at level `2`. There both the `Y`-quadratic and the `X`-cubic have double roots, so the loop
recurses to level `3`, where the `X`-cubic has no double root and the loop exits with
`I!(2·3 − 2) = I₄*`.

## Main definitions

* `WeierstrassCurve.iStarFourTwoLocus`, `WeierstrassCurve.iStarFourFourLocus`: the two loci.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.mod_rX_div_a₆_two`: at `p = 2`, the in-loop `X`-translation
  `Step7.rX` of Step 7's subprocedure is a lift of the residue of `a₆ / ϖ ^ (2n + 1)`.
* `WeierstrassCurve.run_eq_Istar_four_of_step5`: if Steps 1–5 succeed, Step 6's cubic has a double
  but not a triple root, Step 7's subprocedure recurses once and then exits at its second branch,
  Tate's algorithm returns `I₄*` with Tamagawa number `4` or `2`, at every prime.
* `WeierstrassCurve.Δ_ne_zero_BStarFour`: nonsingularity on `a₄ = 4 + 32A`, `a₆ = 16 + 32F`.
* `WeierstrassCurve.run_eq_Istar_four_at_two`: on `a₄ = 4 + 32A`, `a₆ = 16 + 32F` Tate's algorithm
  returns `I₄*`, with Tamagawa number `4` exactly when `2 ∣ J + FZ`.
* `WeierstrassCurve.volume_iStarFourTwoLocus`, `WeierstrassCurve.volume_iStarFourFourLocus`: both
  loci have mass `1/2048`.
-/

open CommRing Ideal CharP MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The in-loop `X`-translation, modulo `2` -/

/-- `Step7.rX` is a lift of the residue of `a₆ / ϖ ^ (2n + 1)` at `p = 2`. -/
theorem TateAlgorithm.Step7.mod_rX_div_a₆_two (hp2 : p = 2) {V : WeierstrassCurve ℤ_[p]} (n : ℕ)
    (ha₂ : (p : ℤ_[p]) ∣ V.a₂) (ha₂' : ¬(p : ℤ_[p]) ^ 2 ∣ V.a₂) :
    mod (p : ℤ_[p]) (Step7.rX (p : ℤ_[p]) V n)
      = mod (p : ℤ_[p]) (div V.a₆ ((p : ℤ_[p]) ^ (2 * n + 1))) := by
  have hne : (cubic (p : ℤ_[p]) V 1 n).b ≠ 0 := by
    rw [show (cubic (p : ℤ_[p]) V 1 n).b = mod (p : ℤ_[p]) (div V.a₂ (p : ℤ_[p])) from rfl, Ne,
      mod_eq_zero]
    exact fun h => ha₂' (sq_dvd.mpr ⟨ha₂, h⟩)
  have hb : (cubic (p : ℤ_[p]) V 1 n).b = 1 :=
    (Step2.residue_eq_zero_or_one_of_eq_two hp2 _).resolve_left hne
  rw [Step7.rX, mod_out]
  split_ifs with h2
  · have hc : CharP (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 :=
      (charP_iff_prime_eq_zero (by decide)).mpr h2
    have hpr : PerfectRing (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 := PerfectField.toPerfectRing 2
    rw [root_two_eq_self_two hp2, hb, div_one, cubic]
  · exact absurd (Step2.residue_two_eq_zero_of_eq_two hp2) h2

/-! ### The branch test of the recursion step -/

/-- **The level-`n` `X`-cubic has a double root once its linear coefficient vanishes.**
`HasDoubleRoot` for `⟨0, b, c, d⟩` is `b²c² = 4b³d`, and `4 = 0` on `𝔽_2`, so `c = 0` establishes
it. -/
theorem hasDoubleRoot_cubic_zero_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hc : P.c = 0) : P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_zero ha, hc, residue_four_eq_zero_two hp2]
  ring1

/-! ### The forwarding: one recursion of Step 7's subprocedure, then the even exit -/

open scoped Classical in
/-- **Steps 1–5 succeed, Step 6's cubic has a double but not a triple root, Step 7's subprocedure
recurses once and then takes its second branch and exits: the answer is `I₄*`**, with Tamagawa
number `4` or `2` according as the level-`3` cubic of the second `Y`-translate has a root or
not. -/
theorem run_eq_Istar_four_of_step5 {W V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬(cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hY : (quadratic (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2).HasDoubleRoot)
    (hX : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 0 2).HasDoubleRoot)
    (hY' : (quadratic (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 2) 3).HasDoubleRoot)
    (hX' : ¬(cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p])
      (Step7.translateY (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
        (Step6.translate (p : ℤ_[p]) V)) 2) 2) 3) 0 3).HasDoubleRoot) :
    (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I! 4 ∧
      (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if 0 < (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p])
            (Step7.translateY (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
              (Step6.translate (p : ℤ_[p]) V)) 2) 2) 3) 0 3).roots.toFinset.card
          then 4 else 2 := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h6 : Step6.run (p : ℤ_[p]) W = Except.ok (Step6.translate (p : ℤ_[p]) V) := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_left hdbl
  have hval6 := Step6.run_hasValuation hϖ h6
  have hΔc : (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)).Δ ≠ 0 := by
    rwa [Step7.translate_Δ, Step6.run_Δ h6]
  have hvc := Step7.hasValuation_translate hϖ hval6 hdbl hntr
  have ha₂c := Step7.not_dvd_translate_a₂ hϖ hval6.a₂ hdbl hntr
  have h7 := Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h6 hntr hΔc hvc ha₂c
  have hvY := Step7.hasValuation_translateY le_rfl hϖ hvc hY
  have ha₂Y := Step7.not_dvd_translateY_a₂ 2 ha₂c
  have hvX := Step7.hasValuation_translateX le_rfl hϖ hvY ha₂Y hX
  have ha₂X := Step7.not_dvd_translateX_a₂ le_rfl hϖ hvY.a₂ ha₂Y
  have hΔX : (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 2).Δ ≠ 0 := by
    rwa [Step7.translateX_Δ, Step7.translateY_Δ]
  have hn' : 2 ≤ 2 + 1 := by norm_num
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7),
    Step7.subprocedure_eq_subprocedure hϖ hΔc le_rfl hvc ha₂c hY hX hΔX hn' hvX ha₂X,
    Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔX hn' hvX ha₂X hY' hX']
  exact ⟨rfl, rfl⟩

/-! ### Nonsingularity on the locus -/

/-- **Nonsingularity on the `B` locus at level `4`.** With `a₄ = 4 + 32A` and `a₆ = 16 + 32F` the
quantity `4a₄³ + 27a₆²` is `1024` times a unit, since `27(F + F²)` is even. -/
theorem Δ_ne_zero_BStarFour {a₄ a₆ A F K : ℤ_[2]} (ha₄ : a₄ = 4 + 32 * A)
    (ha₆ : a₆ = 16 + 32 * F) (hK : F ^ 2 + F = 2 * K) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  refine ofShortNF_Δ_ne_zero_of_two fun h => ?_
  have h1024 : (1024 : ℤ_[2]) ≠ 0 := by
    rw [show (1024 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 10 by norm_num]
    exact pow_ne_zero 10 PadicInt.uniformizer_ne_zero
  have hfac : (1024 : ℤ_[2]) * (1 + 2 * (3 + 3 * A + 24 * A ^ 2 + 64 * A ^ 3 + 27 * K)) = 0 := by
    rw [← h, ha₄, ha₆]
    linear_combination -27648 * hK
  refine PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one
    ⟨-(3 + 3 * A + 24 * A ^ 2 + 64 * A ^ 3 + 27 * K), ?_⟩)
  have := (mul_eq_zero.mp hfac).resolve_left h1024
  rw [show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]
  linear_combination this

/-! ### Two divisibility transports -/

/-- `¬ϖ² ∣ x` when `ϖ = 2` and `x = 2 · (1 + 2y)`. -/
theorem not_sq_dvd_of_eq_two_mul_odd (hπ : (p : ℤ_[p]) = 2) {x y : ℤ_[p]}
    (h : x = 2 * (1 + 2 * y)) : ¬(p : ℤ_[p]) ^ 2 ∣ x := by
  rintro ⟨u, hu⟩
  refine PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one ⟨u - y, ?_⟩)
  rw [hπ] at hu ⊢
  refine mul_left_cancel₀ (a := (2 : ℤ_[p])) (by rw [← hπ]; exact PadicInt.uniformizer_ne_zero) ?_
  linear_combination hu - h

/-- **The carry parity is invariant under a shift by `4`.** If `M = X + 4w` then `M + m_M` and
`X + m_X` have the same parity, where `2m_M = M² + M` and `2m_X = X² + X`. -/
theorem dvd_carry_congr_iff (hπ : (p : ℤ_[p]) = 2) {M X w mM mX : ℤ_[p]} (hw : M = X + 4 * w)
    (hM : M ^ 2 + M = 2 * mM) (hX : X ^ 2 + X = 2 * mX) :
    (p : ℤ_[p]) ∣ M + mM ↔ (p : ℤ_[p]) ∣ X + mX := by
  refine dvd_iff_of_eq_add_two_mul hπ (z := 3 * w + 2 * X * w + 4 * w ^ 2) ?_
  refine mul_left_cancel₀ (a := (2 : ℤ_[p])) (by rw [← hπ]; exact PadicInt.uniformizer_ne_zero) ?_
  linear_combination -hM + hX + (3 + M + X + 4 * w) * hw

/-- **The exit parity, transported to the coefficient plane.** With `2J = Z² + Z` and
`2N = X² + X` for `X = Z(3 + 2F)`, the parity of `X + N` is the parity of `J + FZ`. -/
theorem dvd_carry_tamagawa_iff (hπ : (p : ℤ_[p]) = 2) {Z F J N : ℤ_[p]} (hJ : Z ^ 2 + Z = 2 * J)
    (hN : (3 * Z + 2 * F * Z) ^ 2 + (3 * Z + 2 * F * Z) = 2 * N) :
    (p : ℤ_[p]) ∣ 3 * Z + 2 * F * Z + N ↔ (p : ℤ_[p]) ∣ J + F * Z := by
  refine dvd_iff_of_eq_add_two_mul hπ
    (z := -(2 * F * Z) - F ^ 2 * Z + J * (4 + 6 * F + 2 * F ^ 2)) ?_
  refine mul_left_cancel₀ (a := (2 : ℤ_[p])) (by rw [← hπ]; exact PadicInt.uniformizer_ne_zero) ?_
  linear_combination -hN + (9 + 12 * F + 4 * F ^ 2) * hJ

/-! ### The forward run at level `4` -/

open scoped Classical in
/-- **The forward run at `I₄*`, on `a₄ ≡ 4 (mod 32)` and `a₆ ≡ 16 (mod 32)`.** For `a₄ = 4 + 32A`
and `a₆ = 16 + 32F`, with `F² + F = 2K`, `Z = A + K` and `Z² + Z = 2J`, Tate's algorithm at `2`
returns `I₄*`, with Tamagawa number `4` if `J + FZ` is even and `2` otherwise. -/
theorem run_eq_Istar_four_at_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A F K Z J : ℤ_[p]}
    (ha₄ : a₄ = 4 + 32 * A) (ha₆ : a₆ = 16 + 32 * F) (hK : F ^ 2 + F = 2 * K) (hZ : Z = A + K)
    (hJ : Z ^ 2 + Z = 2 * J) (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 4 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if (p : ℤ_[p]) ∣ J + F * Z then 4 else 2 := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hπ]; ring1⟩
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
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 2 * ρ := by
    obtain ⟨c, hc⟩ := hva₄
    rw [hπ, ha₄] at hc
    obtain ⟨ρ, hρ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨c - 2 - 16 * A - r ^ 2, by rw [hπ]; linear_combination hc⟩ : (p : ℤ_[p]) ∣ r ^ 2)
    exact ⟨ρ, by rw [hρ, hπ]⟩
  obtain ⟨mρ, hmρ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    obtain ⟨d, hd⟩ := hva₆
    rw [hπ, ha₆, ha₄, hr] at hd
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨8 + 16 * F + 4 * ρ + 32 * A * ρ + 4 * ρ ^ 3 - d, by rw [hπ]; linear_combination -hd⟩ :
        (p : ℤ_[p]) ∣ t ^ 2)
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 1 + 8 * A + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
    x = 4 + 8 * F + 2 * ρ + 16 * A * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
  have hA4 : a₄ + 3 * r ^ 2 = 4 * Q₄ := by rw [ha₄, hr, hQ₄]; ring1
  have hA6 : a₆ + r * a₄ + r ^ 3 - t ^ 2 = 4 * Q₆ := by rw [ha₆, ha₄, hr, ht, hQ₆]; ring1
  have h5run := step5_run_eq_ok_of_two hp2 hπ hΔd hV ht hA4 hA6
  have hVa₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring1
  have hVa₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ]; linear_combination hA6
  obtain ⟨s, hs⟩ : ∃ x : ℤ_[p],
    x = Step6.s (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆⟩ : ∃ x : ℤ_[p],
    x = Step6.t (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ_[p], s = 2 * σ := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ s - 3 * r := by
      rw [← mod_eq_zero, map_sub, hs, Step6.mod_s_two hp2, hVa₂, sub_self]
    rw [hπ, hr] at hk
    exact ⟨3 * ρ + k, by linear_combination hk⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ_[p], t₆ = Q₆ + 2 * j := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆, Step6.mod_t_two hp2, div_eq_of_eq_pow_mul_two hVa₆, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * t₆ + t := ⟨_, rfl⟩
  have hW₆ : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s ((p : ℤ_[p]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hs, ht₆]
    rw [h]
    exact smul_smul_eq _ (by ring1) (by ring1) (by rw [hT₂]; ring1)
  obtain ⟨P₁, hP₁⟩ : ∃ x : ℤ_[p],
    x = 2 + 4 * F + ρ + 8 * A * ρ + ρ ^ 3 - mτ + τ + j := ⟨_, rfl⟩
  have hT₂P : T₂ = 4 * P₁ := by rw [hT₂, hπ, hj, hQ₆, ht, hP₁]; linear_combination -2 * hmτ
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[p], x = 3 * ρ - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[p], x = Q₄ - σ * T₂ := ⟨_, rfl⟩
  obtain ⟨X₆, hX₆⟩ : ∃ x : ℤ_[p],
    x = 2 + 4 * F + ρ + 8 * A * ρ + ρ ^ 3 - 2 * P₁ ^ 2 := ⟨_, rfl⟩
  have hW₆a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hσ, hX₂]; ring1
  have hW₆a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hX₄, hσ, hπ]; linear_combination hA4
  have hW₆a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 3 * X₆ := by
    rw [smul_ofShortNF_a₆, ha₄, ha₆, hr, hT₂P, hX₆, hπ]; ring1
  have hW₆a₄' : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ (1 + 1) * X₄ := hW₆a₄
  have hW₆a₆' : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 1 + 1) * X₆ := hW₆a₆
  have hX₂res : mod (p : ℤ_[p]) X₂ = mod (p : ℤ_[p]) ρ :=
    mod_eq_mod_of_dvd_sub_two ⟨ρ - σ ^ 2, by rw [hX₂, hπ]; ring1⟩
  have hX₄res : mod (p : ℤ_[p]) X₄ = mod (p : ℤ_[p]) (1 + ρ) :=
    mod_eq_mod_of_dvd_sub_two ⟨4 * A + 3 * mρ - 2 * ρ - 2 * σ * P₁, by
      rw [hX₄, hQ₄, hT₂P, hπ]; linear_combination 3 * hmρ⟩
  have hX₆res : mod (p : ℤ_[p]) X₆ = 0 := by
    rw [mod_eq_zero]
    exact ⟨1 + 2 * F + ρ + 4 * A * ρ + mρ * ρ - mρ - P₁ ^ 2, by
      rw [hX₆, hπ]; linear_combination (-1 + ρ) * hmρ⟩
  have hcub6 : cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1
      = ⟨1, mod (p : ℤ_[p]) ρ, mod (p : ℤ_[p]) (1 + ρ), 0⟩ := by
    rw [cubic, div_eq_of_eq_mul_two hW₆a₂, div_eq_of_eq_pow_mul_two hW₆a₄',
      div_eq_of_eq_pow_mul_two hW₆a₆', hX₂res, hX₄res, hX₆res, map_one]
  have hdbl : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasDoubleRoot := by
    rw [hcub6]
    refine hasDoubleRoot_of_mul_eq_two hp2 rfl ?_
    rw [← map_mul, mod_eq_zero]
    exact ⟨mρ, by rw [hπ]; linear_combination hmρ⟩
  have hntr : ¬(cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasTripleRoot := by
    rw [hcub6]
    refine not_hasTripleRoot_of_sub_eq_one_two hp2 ?_
    rw [← map_sub, mod_eq_mod_of_dvd_sub_two (y := 1) ⟨-1, by rw [hπ]; ring1⟩, map_one]
  obtain ⟨r₇, hr₇⟩ : ∃ x : ℤ_[p],
    x = Step7.r (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨k₇, hk₇⟩ : ∃ k : ℤ_[p], r₇ = 1 + ρ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ r₇ - (1 + ρ) := by
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
    exact smul_smul_eq _ (by rw [hR₇]) (by ring1) (by rw [hT₇]; ring1)
  obtain ⟨ν, hν⟩ : ∃ x : ℤ_[p], x = ρ + k₇ := ⟨_, rfl⟩
  obtain ⟨mν, hmν⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν
  have hR₇v : R₇ = 2 + 4 * ν := by rw [hR₇, hπ, hk₇, hr, hν]; ring1
  obtain ⟨τ₈, hτ₈⟩ : ∃ x : ℤ_[p], x = σ * r₇ + P₁ := ⟨_, rfl⟩
  obtain ⟨m₈, hm₈⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ₈
  have hT₇v : T₇ = 4 * τ₈ := by rw [hT₇, hT₂P, hπ, hσ, hτ₈]; ring1
  obtain ⟨N₇, hN₇⟩ : ∃ x : ℤ_[p],
    x = 2 + 2 * F + 4 * A + 12 * mν - 2 * ν + 8 * A * ν + 4 * ν ^ 3 - τ₈ ^ 2 := ⟨_, rfl⟩
  have hW₇a₃ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * (2 * τ₈) := by rw [smul_ofShortNF_a₃, hT₇v, hπ]; ring1
  have hW₇a₆ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2) * N₇ := by
    rw [smul_ofShortNF_a₆, hR₇v, hT₇v, ha₄, ha₆, hN₇, hπ]; linear_combination 96 * hmν
  have hτ₈res : mod (p : ℤ_[p]) (2 * τ₈) = 0 := by
    rw [mod_eq_zero]; exact ⟨τ₈, by rw [hπ]⟩
  have hquad2 : quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
      = ⟨0, 1, 0, -(mod (p : ℤ_[p]) N₇)⟩ := by
    rw [quadratic, div_eq_of_eq_pow_mul_two hW₇a₃, div_eq_of_eq_pow_mul_two hW₇a₆, hτ₈res]
  have hY : (quadratic (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)))
      2).HasDoubleRoot := by
    rw [hW₆, hW₇, hquad2]
    exact hasDoubleRoot_quadratic_zero_two hp2 rfl rfl rfl
  obtain ⟨tY, htY⟩ : ∃ x : ℤ_[p],
    x = Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ k : ℤ_[p], tY = -N₇ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ tY + N₇ := by
      rw [← mod_eq_zero, map_add, htY, Step7.mod_tY_two hp2,
        div_eq_of_eq_pow_mul_two hW₇a₆, neg_add_cancel]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨G, hG⟩ : ∃ x : ℤ_[p],
    x = 1 + F + 2 * A + 6 * mν - ν + 4 * A * ν + 2 * ν ^ 3 - m₈ + τ₈ := ⟨_, rfl⟩
  have hGv : N₇ + τ₈ = 2 * G := by rw [hN₇, hG]; linear_combination -hm₈
  obtain ⟨θ, hθ⟩ : ∃ x : ℤ_[p], x = τ₈ + ℓ - G := ⟨_, rfl⟩
  obtain ⟨T₈, hT₈⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * tY + T₇ := ⟨_, rfl⟩
  have hT₈v : T₈ = 8 * θ := by rw [hT₈, hπ, hℓ, hT₇v, hθ]; linear_combination -4 * hGv
  have hW₈ : Step7.translateY (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
      = (VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆ := by
    have h : Step7.translateY (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) := by rw [htY]
    rw [h]
    exact smul_smul_eq _ (by ring1) (by ring1) (by rw [hT₈]; ring1)
  have hsum7 : a₆ + R₇ * a₄ + R₇ ^ 3 = 16 * N₇ + 16 * τ₈ ^ 2 := by
    rw [hR₇v, ha₄, ha₆, hN₇]; linear_combination 96 * hmν
  obtain ⟨N₈, hN₈⟩ : ∃ x : ℤ_[p], x = G + m₈ - τ₈ - 2 * θ ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₂', hX₂'⟩ : ∃ x : ℤ_[p], x = 3 + 6 * ν - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨U₈, hU₈⟩ : ∃ x : ℤ_[p], x = 1 + 2 * A + 6 * mν - 2 * σ * θ := ⟨_, rfl⟩
  have hW₈a₂ : ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂' := by
    rw [smul_ofShortNF_a₂, hR₇v, hσ, hX₂', hπ]; ring1
  have hW₈a₄ : ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ (2 + 1) * (2 * U₈) := by
    rw [smul_ofShortNF_a₄, hR₇v, hT₈v, hσ, ha₄, hU₈, hπ]; linear_combination 48 * hmν
  have hW₈a₆ : ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2 + 1) * N₈ := by
    rw [smul_ofShortNF_a₆, hT₈v, hN₈, hπ]; linear_combination hsum7 + 16 * hGv + 16 * hm₈
  have hX₂'res : mod (p : ℤ_[p]) X₂' = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := X₂') (y := 1) ⟨1 + 3 * ν - σ ^ 2, by
      rw [hX₂', hπ]; ring1⟩, map_one]
  have hU₈res : mod (p : ℤ_[p]) (2 * U₈) = 0 := by
    rw [mod_eq_zero]; exact ⟨U₈, by rw [hπ]⟩
  have hcub2 : cubic (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆) 0 2
      = ⟨0, 1, 0, mod (p : ℤ_[p]) N₈⟩ := by
    rw [cubic, div_eq_of_eq_mul_two hW₈a₂, div_eq_of_eq_pow_mul_two hW₈a₄,
      div_eq_of_eq_pow_mul_two hW₈a₆, hX₂'res, hU₈res, map_zero]
  have hX : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆))) 2)
      0 2).HasDoubleRoot := by
    rw [hW₆, hW₇, hW₈, hcub2]
    exact hasDoubleRoot_cubic_zero_two hp2 rfl rfl
  have hW₈a₂dvd : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₂ :=
    ⟨X₂', hW₈a₂⟩
  have hW₈a₂ndvd : ¬(p : ℤ_[p]) ^ 2 ∣ ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆).a₂ :=
    not_sq_dvd_of_eq_two_mul_odd hπ (y := 1 + 3 * ν - σ ^ 2) (by rw [hW₈a₂, hX₂', hπ]; ring1)
  obtain ⟨rX, hrX⟩ : ∃ x : ℤ_[p],
    x = Step7.rX (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ k : ℤ_[p], rX = N₈ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ rX - N₈ := by
      rw [← mod_eq_zero, map_sub, hrX, Step7.mod_rX_div_a₆_two hp2 2 hW₈a₂dvd hW₈a₂ndvd,
        div_eq_of_eq_pow_mul_two hW₈a₆, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨R₉, hR₉⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * rX + R₇ := ⟨_, rfl⟩
  obtain ⟨T₉, hT₉⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * rX * s + T₈ := ⟨_, rfl⟩
  have hW₉ : Step7.translateX (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆) 2
      = (VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆ := by
    have h : Step7.translateX (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆) 2
        = (VariableChange.mk 1 ((p : ℤ_[p]) ^ 2 * rX) 0 0)
          • ((VariableChange.mk 1 R₇ s T₈) • ofShortNF a₄ a₆) := by rw [hrX]
    rw [h]
    exact smul_smul_eq _ (by rw [hR₉]) (by ring1) (by rw [hT₉]; ring1)
  obtain ⟨ν₉, hν₉⟩ : ∃ x : ℤ_[p], x = ν + rX := ⟨_, rfl⟩
  obtain ⟨m₉, hm₉⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν₉
  have hR₉v : R₉ = 2 + 4 * ν₉ := by rw [hR₉, hπ, hR₇v, hν₉]; ring1
  obtain ⟨τ₁₀, hτ₁₀⟩ : ∃ x : ℤ_[p], x = σ * rX + θ := ⟨_, rfl⟩
  obtain ⟨m₁₀, hm₁₀⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ₁₀
  have hT₉v : T₉ = 8 * τ₁₀ := by rw [hT₉, hπ, hσ, hT₈v, hτ₁₀]; ring1
  obtain ⟨g, hg⟩ : ∃ x : ℤ_[p], x = A + 3 * mν + 2 * A * ν + ν ^ 3 - θ ^ 2 + n₂ := ⟨_, rfl⟩
  obtain ⟨mg, hmg⟩ := exists_sq_add_self_eq_two_mul hp2 hπ g
  have hν₉v : ν₉ = 1 + F + 2 * g := by rw [hν₉, hn₂, hN₈, hG, hg]; ring1
  have hm₉v : m₉ = 1 + F + K + 3 * g + 2 * F * g + 2 * g ^ 2 := by
    refine mul_left_cancel₀ (a := (2 : ℤ_[p])) (by rw [← hπ]; exact hϖ) ?_
    linear_combination -hm₉ + (2 + F + 2 * g + ν₉) * hν₉v + hK
  obtain ⟨M₂, hM₂⟩ : ∃ x : ℤ_[p], x = A - g + 3 * m₉ + 2 * A * ν₉ + ν₉ ^ 3 := ⟨_, rfl⟩
  have hM : a₆ + R₉ * a₄ + R₉ ^ 3 = 64 * M₂ := by
    rw [hR₉v, ha₄, ha₆, hM₂]; linear_combination 96 * hm₉ - 32 * hν₉v
  obtain ⟨N₉, hN₉⟩ : ∃ x : ℤ_[p], x = M₂ - τ₁₀ ^ 2 := ⟨_, rfl⟩
  have hW₉a₃ : ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 3 * (2 * τ₁₀) := by rw [smul_ofShortNF_a₃, hT₉v, hπ]; ring1
  have hW₉a₆ : ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 3) * N₉ := by
    rw [smul_ofShortNF_a₆, hT₉v, hN₉, hπ]; linear_combination hM
  have hτ₁₀res : mod (p : ℤ_[p]) (2 * τ₁₀) = 0 := by
    rw [mod_eq_zero]; exact ⟨τ₁₀, by rw [hπ]⟩
  have hquad3 : quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆) 3
      = ⟨0, 1, 0, -(mod (p : ℤ_[p]) N₉)⟩ := by
    rw [quadratic, div_eq_of_eq_pow_mul_two hW₉a₃, div_eq_of_eq_pow_mul_two hW₉a₆, hτ₁₀res]
  have hY' : (quadratic (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆))) 2) 2) 3).HasDoubleRoot := by
    rw [hW₆, hW₇, hW₈, hW₉, hquad3]
    exact hasDoubleRoot_quadratic_zero_two hp2 rfl rfl rfl
  obtain ⟨tY₂, htY₂⟩ : ∃ x : ℤ_[p],
    x = Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆) 3 := ⟨_, rfl⟩
  obtain ⟨ℓ₂, hℓ₂⟩ : ∃ k : ℤ_[p], tY₂ = -N₉ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ tY₂ + N₉ := by
      rw [← mod_eq_zero, map_add, htY₂, Step7.mod_tY_two hp2,
        div_eq_of_eq_pow_mul_two hW₉a₆, neg_add_cancel]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨η, hη⟩ : ∃ x : ℤ_[p], x = m₁₀ + ℓ₂ := ⟨_, rfl⟩
  obtain ⟨τ₁₁, hτ₁₁⟩ : ∃ x : ℤ_[p], x = -M₂ + 2 * η := ⟨_, rfl⟩
  obtain ⟨T₁₀, hT₁₀⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 3 * tY₂ + T₉ := ⟨_, rfl⟩
  have hT₁₀v : T₁₀ = 8 * τ₁₁ := by
    rw [hT₁₀, hπ, hℓ₂, hN₉, hT₉v, hτ₁₁, hη]; linear_combination 8 * hm₁₀
  have hW₁₀ : Step7.translateY (p : ℤ_[p]) ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆) 3
      = (VariableChange.mk 1 R₉ s T₁₀) • ofShortNF a₄ a₆ := by
    have h : Step7.translateY (p : ℤ_[p]) ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆) 3
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 3 * tY₂))
          • ((VariableChange.mk 1 R₉ s T₉) • ofShortNF a₄ a₆) := by rw [htY₂]
    rw [h]
    exact smul_smul_eq _ (by ring1) (by ring1) (by rw [hT₁₀]; ring1)
  obtain ⟨mM, hmM⟩ := exists_sq_add_self_eq_two_mul hp2 hπ M₂
  obtain ⟨N₁₀, hN₁₀⟩ : ∃ x : ℤ_[p], x = M₂ - mM + 2 * M₂ * η - 2 * η ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₂'', hX₂''⟩ : ∃ x : ℤ_[p], x = 3 + 6 * ν₉ - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨U₁₀, hU₁₀⟩ : ∃ x : ℤ_[p], x = 1 + 2 * A + 6 * m₉ - 2 * σ * τ₁₁ := ⟨_, rfl⟩
  have hW₁₀a₂ : ((VariableChange.mk 1 R₉ s T₁₀) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂'' := by
    rw [smul_ofShortNF_a₂, hR₉v, hσ, hX₂'', hπ]; ring1
  have hW₁₀a₄ : ((VariableChange.mk 1 R₉ s T₁₀) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ (3 + 1) * U₁₀ := by
    rw [smul_ofShortNF_a₄, hR₉v, hT₁₀v, hσ, ha₄, hU₁₀, hπ]; linear_combination 48 * hm₉
  have hW₁₀a₆ : ((VariableChange.mk 1 R₉ s T₁₀) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 3 + 1) * N₁₀ := by
    rw [smul_ofShortNF_a₆, hT₁₀v, hN₁₀, hτ₁₁, hπ]; linear_combination hM - 64 * hmM
  have hX₂''res : mod (p : ℤ_[p]) X₂'' = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := X₂'') (y := 1) ⟨1 + 3 * ν₉ - σ ^ 2, by
      rw [hX₂'', hπ]; ring1⟩, map_one]
  have hU₁₀res : mod (p : ℤ_[p]) U₁₀ = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := U₁₀) (y := 1) ⟨A + 3 * m₉ - σ * τ₁₁, by
      rw [hU₁₀, hπ]; ring1⟩, map_one]
  have hcub3 : cubic (p : ℤ_[p]) ((VariableChange.mk 1 R₉ s T₁₀) • ofShortNF a₄ a₆) 0 3
      = ⟨0, 1, 1, mod (p : ℤ_[p]) N₁₀⟩ := by
    rw [cubic, div_eq_of_eq_mul_two hW₁₀a₂, div_eq_of_eq_pow_mul_two hW₁₀a₄,
      div_eq_of_eq_pow_mul_two hW₁₀a₆, hX₂''res, hU₁₀res, map_zero]
  have hX' : ¬(cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p])
      (Step7.translateY (p : ℤ_[p]) (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆))) 2) 2) 3) 0 3).HasDoubleRoot := by
    rw [hW₆, hW₇, hW₈, hW₉, hW₁₀, hcub3]
    exact not_hasDoubleRoot_cubic_one_two hp2 rfl rfl rfl
  have hmain := run_eq_Istar_four_of_step5 hΔ h5run (hW₆ ▸ hdbl) (hW₆ ▸ hntr) hY hX hY' hX'
  refine ⟨hmain.1, ?_⟩
  rw [hmain.2, hW₆, hW₇, hW₈, hW₉, hW₁₀, hcub3]
  refine if_congr ?_ rfl rfl
  have hroot := card_roots_toFinset_pos_iff_two (p := p) hp2 (-(mod (p : ℤ_[p]) N₁₀))
  rw [neg_neg, neg_eq_zero] at hroot
  rw [hroot, mod_eq_zero]
  obtain ⟨mX, hmX⟩ := exists_sq_add_self_eq_two_mul hp2 hπ (3 * Z + 2 * F * Z)
  obtain ⟨ω, hω⟩ : ∃ x : ℤ_[p], x = 1 + F + K + 2 * g + A * g + 3 * F * g + 3 * K * g + 3 * mg
    + 3 * g ^ 2 + 3 * F * g ^ 2 + 2 * g ^ 3 := ⟨_, rfl⟩
  have hwv : M₂ = 3 * Z + 2 * F * Z + 4 * ω := by
    rw [hM₂, hm₉v, hν₉v, hZ, hω]; linear_combination (2 + F + 6 * g) * hK + 6 * hmg
  have hN₁₀v : N₁₀ = M₂ + mM + 2 * (-mM + M₂ * η - η ^ 2) := by rw [hN₁₀]; ring1
  rw [dvd_iff_of_eq_add_two_mul hπ hN₁₀v, dvd_carry_congr_iff hπ hwv hmM hmX,
    dvd_carry_tamagawa_iff hπ hJ hmX]

/-! ### From a residue class modulo `2 ^ 8` to the Tamagawa bit -/

/-- **The exit parity in terms of the residue class.** `A ≡ i` and `F ≡ k` modulo `8` pin
`Z = A + K` modulo `4` and `F` modulo `2`, and that is all the parity of `J + FZ` sees. -/
theorem dvd_tamagawa_of_class (hπ : (p : ℤ_[p]) = 2) {K Z J u v i k κ ζ ι : ℤ_[p]}
    (hK : (k + 8 * v) ^ 2 + (k + 8 * v) = 2 * K) (hZ : Z = i + 8 * u + K)
    (hJ : Z ^ 2 + Z = 2 * J) (hκ : k ^ 2 + k = 2 * κ) (hζ : ζ = i + κ)
    (hι : ζ ^ 2 + ζ = 2 * ι) :
    ((p : ℤ_[p]) ∣ J + (k + 8 * v) * Z) ↔ (p : ℤ_[p]) ∣ ι + k * ζ := by
  have h2ne : (2 : ℤ_[p]) ≠ 0 := by rw [← hπ]; exact PadicInt.uniformizer_ne_zero
  obtain ⟨W, hW⟩ : ∃ x : ℤ_[p], x = 2 * u + v * (2 * k + 8 * v + 1) := ⟨_, rfl⟩
  have hKv : K = κ + 4 * (v * (2 * k + 8 * v + 1)) := by
    refine mul_left_cancel₀ h2ne ?_
    rw [← hK]
    linear_combination hκ
  have hZv : Z = ζ + 4 * W := by rw [hZ, hKv, hζ, hW]; ring1
  have hJv : J = ι + 2 * (W * (2 * ζ + 4 * W + 1)) := by
    refine mul_left_cancel₀ h2ne ?_
    rw [← hJ, hZv]
    linear_combination hι
  exact dvd_iff_of_eq_add_two_mul hπ
    (z := W * (2 * ζ + 4 * W + 1) + 2 * k * W + 4 * v * ζ + 16 * v * W)
    (by rw [hJv, hZv]; ring1)

/-- Membership of a residue class modulo `2 ^ 8`, as a divisibility. -/
theorem pow_dvd_sub_of_res {y α : ℤ_[2]} {a : ZMod (2 ^ 8)} (hy : PadicInt.toZModPow 8 y = a)
    (hα : PadicInt.toZModPow 8 α = a) : ((2 : ℕ) : ℤ_[2]) ^ 8 ∣ y - α :=
  PadicInt.toZModPow_eq_iff_pow_dvd_sub.1 (hy.trans hα.symm)

open scoped Classical in
open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The forward run on one residue class modulo `2 ^ 8` of the `B` locus at level `4`.**
`α` and `ε` are the class representatives, `i` and `k` their positions in the parametrisation
`a₄ = 4 + 32A`, `a₆ = 16 + 32F`, and `κ`, `ζ`, `ι` the carries that decide the Tamagawa
number. -/
theorem mem_iUnion_stratFibre_of_class {x : ℤ_[2] × ℤ_[2]} {α ε i k κ ζ ι : ℤ_[2]} {t : ℕ}
    (h1 : ((2 : ℕ) : ℤ_[2]) ^ 8 ∣ x.1 - α) (h2 : ((2 : ℕ) : ℤ_[2]) ^ 8 ∣ x.2 - ε)
    (hα : α = 4 + 32 * i) (hε : ε = 16 + 32 * k) (hκ : k ^ 2 + k = 2 * κ) (hζ : ζ = i + κ)
    (hι : ζ ^ 2 + ζ = 2 * ι)
    (ht : (if ((2 : ℕ) : ℤ_[2]) ∣ ι + k * ζ then 4 else 2) = t) :
    x ∈ ⋃ κ' : KodairaSymbol, stratFibre 2 (κ', t) := by
  classical
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[2], x.1 = 4 + 32 * (i + 8 * u) := by
    obtain ⟨c, hc⟩ := h1
    rw [hcast] at hc
    exact ⟨c, by linear_combination hc + hα⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤ_[2], x.2 = 16 + 32 * (k + 8 * v) := by
    obtain ⟨c, hc⟩ := h2
    rw [hcast] at hc
    exact ⟨c, by linear_combination hc + hε⟩
  obtain ⟨K, hK⟩ := exists_sq_add_self_eq_two_mul (p := 2) rfl hcast (k + 8 * v)
  obtain ⟨J, hJ⟩ := exists_sq_add_self_eq_two_mul (p := 2) rfl hcast (i + 8 * u + K)
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_BStarFour hu hv hK
  obtain ⟨hkod, htam⟩ := run_eq_Istar_four_at_two (p := 2) rfl hcast hu hv hK rfl hJ hΔ
  rw [dvd_tamagawa_of_class (p := 2) hcast hK rfl hJ hκ hζ hι, ht] at htam
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 4,
    (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hkod htam)⟩

/-! ### The two residue sets modulo `2 ^ 8` -/

/-- **The residue condition cutting out the `(I₄*, 2)` locus at `2`**: thirty-two classes
modulo `256`, four for each of the eight classes of `a₄` modulo `256`. -/
abbrev HeadResIStarFourTwo (a e : ZMod (2 ^ 8)) : Prop :=
  (a = 4 ∧ e = 112) ∨ (a = 4 ∧ e = 144) ∨ (a = 4 ∧ e = 176) ∨ (a = 4 ∧ e = 208) ∨
    (a = 36 ∧ e = 16) ∨ (a = 36 ∧ e = 48) ∨ (a = 36 ∧ e = 112) ∨ (a = 36 ∧ e = 208) ∨
    (a = 68 ∧ e = 16) ∨ (a = 68 ∧ e = 48) ∨ (a = 68 ∧ e = 80) ∨ (a = 68 ∧ e = 240) ∨
    (a = 100 ∧ e = 80) ∨ (a = 100 ∧ e = 144) ∨ (a = 100 ∧ e = 176) ∨ (a = 100 ∧ e = 240) ∨
    (a = 132 ∧ e = 112) ∨ (a = 132 ∧ e = 144) ∨ (a = 132 ∧ e = 176) ∨ (a = 132 ∧ e = 208) ∨
    (a = 164 ∧ e = 16) ∨ (a = 164 ∧ e = 48) ∨ (a = 164 ∧ e = 112) ∨ (a = 164 ∧ e = 208) ∨
    (a = 196 ∧ e = 16) ∨ (a = 196 ∧ e = 48) ∨ (a = 196 ∧ e = 80) ∨ (a = 196 ∧ e = 240) ∨
    (a = 228 ∧ e = 80) ∨ (a = 228 ∧ e = 144) ∨ (a = 228 ∧ e = 176) ∨ (a = 228 ∧ e = 240)

/-- **The residue condition cutting out the `(I₄*, 4)` locus at `2`**: the complementary
thirty-two classes modulo `256`. -/
abbrev HeadResIStarFourFour (a e : ZMod (2 ^ 8)) : Prop :=
  (a = 4 ∧ e = 16) ∨ (a = 4 ∧ e = 48) ∨ (a = 4 ∧ e = 80) ∨ (a = 4 ∧ e = 240) ∨ (a = 36 ∧ e = 80) ∨
    (a = 36 ∧ e = 144) ∨ (a = 36 ∧ e = 176) ∨ (a = 36 ∧ e = 240) ∨ (a = 68 ∧ e = 112) ∨
    (a = 68 ∧ e = 144) ∨ (a = 68 ∧ e = 176) ∨ (a = 68 ∧ e = 208) ∨ (a = 100 ∧ e = 16) ∨
    (a = 100 ∧ e = 48) ∨ (a = 100 ∧ e = 112) ∨ (a = 100 ∧ e = 208) ∨ (a = 132 ∧ e = 16) ∨
    (a = 132 ∧ e = 48) ∨ (a = 132 ∧ e = 80) ∨ (a = 132 ∧ e = 240) ∨ (a = 164 ∧ e = 80) ∨
    (a = 164 ∧ e = 144) ∨ (a = 164 ∧ e = 176) ∨ (a = 164 ∧ e = 240) ∨ (a = 196 ∧ e = 112) ∨
    (a = 196 ∧ e = 144) ∨ (a = 196 ∧ e = 176) ∨ (a = 196 ∧ e = 208) ∨ (a = 228 ∧ e = 16) ∨
    (a = 228 ∧ e = 48) ∨ (a = 228 ∧ e = 112) ∨ (a = 228 ∧ e = 208)

/-- The thirty-two residue pairs of `HeadResIStarFourTwo`, as a `Finset`. -/
def headResiduesIStarFourTwo : Finset (ZMod (2 ^ 8) × ZMod (2 ^ 8)) :=
  {(4, 112), (4, 144), (4, 176), (4, 208), (36, 16), (36, 48), (36, 112), (36, 208), (68, 16),
   (68, 48), (68, 80), (68, 240), (100, 80), (100, 144), (100, 176), (100, 240), (132, 112),
   (132, 144), (132, 176), (132, 208), (164, 16), (164, 48), (164, 112), (164, 208), (196, 16),
   (196, 48), (196, 80), (196, 240), (228, 80), (228, 144), (228, 176), (228, 240)}

/-- The thirty-two residue pairs of `HeadResIStarFourFour`, as a `Finset`. -/
def headResiduesIStarFourFour : Finset (ZMod (2 ^ 8) × ZMod (2 ^ 8)) :=
  {(4, 16), (4, 48), (4, 80), (4, 240), (36, 80), (36, 144), (36, 176), (36, 240), (68, 112),
   (68, 144), (68, 176), (68, 208), (100, 16), (100, 48), (100, 112), (100, 208), (132, 16),
   (132, 48), (132, 80), (132, 240), (164, 80), (164, 144), (164, 176), (164, 240), (196, 112),
   (196, 144), (196, 176), (196, 208), (228, 16), (228, 48), (228, 112), (228, 208)}

set_option maxRecDepth 400000 in
/-- The residue set `headResiduesIStarFourTwo` has `32` elements. -/
theorem card_headResiduesIStarFourTwo : headResiduesIStarFourTwo.card = 32 := by decide

set_option maxRecDepth 400000 in
/-- The residue set `headResiduesIStarFourFour` has `32` elements. -/
theorem card_headResiduesIStarFourFour : headResiduesIStarFourFour.card = 32 := by decide

/-- A pair lies in `headResiduesIStarFourTwo` if and only if it satisfies
`HeadResIStarFourTwo`. -/
theorem mem_headResiduesIStarFourTwo_iff {c : ZMod (2 ^ 8) × ZMod (2 ^ 8)} :
    c ∈ headResiduesIStarFourTwo ↔ HeadResIStarFourTwo c.1 c.2 := by
  simp [headResiduesIStarFourTwo, Prod.ext_iff]

/-- A pair lies in `headResiduesIStarFourFour` if and only if it satisfies
`HeadResIStarFourFour`. -/
theorem mem_headResiduesIStarFourFour_iff {c : ZMod (2 ^ 8) × ZMod (2 ^ 8)} :
    c ∈ headResiduesIStarFourFour ↔ HeadResIStarFourFour c.1 c.2 := by
  simp [headResiduesIStarFourFour, Prod.ext_iff]

/-- On the residue set `HeadResIStarFourTwo`, `a₄ ≡ 4 (mod 16)`, so `16 ∤ a₄`. -/
theorem headResIStarFourTwo_notDvd : ∀ a e : ZMod (2 ^ 8), HeadResIStarFourTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-- On the residue set `HeadResIStarFourFour`, `a₄ ≡ 4 (mod 16)`, so `16 ∤ a₄`. -/
theorem headResIStarFourFour_notDvd : ∀ a e : ZMod (2 ^ 8), HeadResIStarFourFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by
  rintro a e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-! ### The two loci, their masses and their minimality -/

/-- The **`(I₄*, 2)` locus** of the coefficient plane at `2`: thirty-two classes modulo `256`. -/
noncomputable def iStarFourTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 8 ⁻¹' (headResiduesIStarFourTwo : Set (ZMod (2 ^ 8) × ZMod (2 ^ 8)))

/-- The **`(I₄*, 4)` locus** of the coefficient plane at `2`: thirty-two classes modulo `256`. -/
noncomputable def iStarFourFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 8 ⁻¹' (headResiduesIStarFourFour : Set (ZMod (2 ^ 8) × ZMod (2 ^ 8)))

/-- A point lies in `iStarFourTwoLocus` if and only if its reduction modulo `2 ^ 8` satisfies
`HeadResIStarFourTwo`. -/
theorem mem_iStarFourTwoLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarFourTwoLocus ↔
      HeadResIStarFourTwo (PadicInt.toZModPow 8 x.1) (PadicInt.toZModPow 8 x.2) := by
  rw [iStarFourTwoLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarFourTwo_iff,
    PadicInt.redPairPow]

/-- A point lies in `iStarFourFourLocus` if and only if its reduction modulo `2 ^ 8` satisfies
`HeadResIStarFourFour`. -/
theorem mem_iStarFourFourLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarFourFourLocus ↔
      HeadResIStarFourFour (PadicInt.toZModPow 8 x.1) (PadicInt.toZModPow 8 x.2) := by
  rw [iStarFourFourLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarFourFour_iff,
    PadicInt.redPairPow]

/-- **The mass of the `(I₄*, 2)` locus is `32/65536 = 1/2048`.** -/
theorem volume_iStarFourTwoLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarFourTwoLocus = 32 * ((2 : ℝ≥0∞)⁻¹) ^ 16 := by
  rw [iStarFourTwoLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarFourTwo]
  norm_num

/-- **The mass of the `(I₄*, 4)` locus is `32/65536 = 1/2048`.** -/
theorem volume_iStarFourFourLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarFourFourLocus = 32 * ((2 : ℝ≥0∞)⁻¹) ^ 16 := by
  rw [iStarFourFourLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarFourFour]
  norm_num

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₄*, 2)` locus lies in the strata over `t = 2`.** -/
theorem iStarFourTwoLocus_subset_iUnion_stratFibre :
    iStarFourTwoLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  rcases mem_iStarFourTwoLocus_iff.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 0) (k := 3) (κ := 6)
      (ζ := 6) (ι := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 19) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 0) (k := 4) (κ := 10)
      (ζ := 10) (ι := 55) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 47) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 0) (k := 5) (κ := 15)
      (ζ := 15) (ι := 120) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 97) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 0) (k := 6) (κ := 21)
      (ζ := 21) (ι := 231) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 178) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 1) (k := 0) (κ := 0)
      (ζ := 1) (ι := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 0) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 1) (k := 1) (κ := 1)
      (ζ := 2) (ι := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 2) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 1) (k := 3) (κ := 6)
      (ζ := 7) (ι := 28) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 24) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 1) (k := 6) (κ := 21)
      (ζ := 22) (ι := 253) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 192) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 2) (k := 0) (κ := 0)
      (ζ := 2) (ι := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 1) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 2) (k := 1) (κ := 1)
      (ζ := 3) (ι := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 4) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 2) (k := 2) (κ := 3)
      (ζ := 5) (ι := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 12) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 2) (k := 7) (κ := 28)
      (ζ := 30) (ι := 465) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 337) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 3) (k := 2) (κ := 3)
      (ζ := 6) (ι := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 16) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 3) (k := 4) (κ := 10)
      (ζ := 13) (ι := 91) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 71) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 3) (k := 5) (κ := 15)
      (ζ := 18) (ι := 171) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 130) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 3) (k := 7) (κ := 28)
      (ζ := 31) (ι := 496) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 356) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 4) (k := 3) (κ := 6)
      (ζ := 10) (ι := 55) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 42) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 4) (k := 4) (κ := 10)
      (ζ := 14) (ι := 105) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 80) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 4) (k := 5) (κ := 15)
      (ζ := 19) (ι := 190) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 142) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 4) (k := 6) (κ := 21)
      (ζ := 25) (ι := 325) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 237) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 5) (k := 0) (κ := 0)
      (ζ := 5) (ι := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 7) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 5) (k := 1) (κ := 1)
      (ζ := 6) (ι := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 13) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 5) (k := 3) (κ := 6)
      (ζ := 11) (ι := 66) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 49) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 5) (k := 6) (κ := 21)
      (ζ := 26) (ι := 351) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 253) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 6) (k := 0) (κ := 0)
      (ζ := 6) (ι := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 10) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 6) (k := 1) (κ := 1)
      (ζ := 7) (ι := 28) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 17) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 6) (k := 2) (κ := 3)
      (ζ := 9) (ι := 45) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 31) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 6) (k := 7) (κ := 28)
      (ζ := 34) (ι := 595) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 416) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 7) (k := 2) (κ := 3)
      (ζ := 10) (ι := 55) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 37) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 7) (k := 4) (κ := 10)
      (ζ := 17) (ι := 153) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 110) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 7) (k := 5) (κ := 15)
      (ζ := 22) (ι := 253) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 181) (by norm_num)))
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 7) (k := 7) (κ := 28)
      (ζ := 35) (ι := 630) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_right (not_dvd_of_eq_one_add_two_mul (y := 437) (by norm_num)))

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₄*, 4)` locus lies in the strata over `t = 4`.** -/
theorem iStarFourFourLocus_subset_iUnion_stratFibre :
    iStarFourFourLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4) := by
  intro x hx
  rcases mem_iStarFourFourLocus_iff.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 0) (k := 0) (κ := 0)
      (ζ := 0) (ι := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨0, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 0) (k := 1) (κ := 1)
      (ζ := 1) (ι := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨1, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 0) (k := 2) (κ := 3)
      (ζ := 3) (ι := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨6, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 4) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 0) (k := 7) (κ := 28)
      (ζ := 28) (ι := 406) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨301, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 1) (k := 2) (κ := 3)
      (ζ := 4) (ι := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨9, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 1) (k := 4) (κ := 10)
      (ζ := 11) (ι := 66) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨55, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 1) (k := 5) (κ := 15)
      (ζ := 16) (ι := 136) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨108, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 36) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 1) (k := 7) (κ := 28)
      (ζ := 29) (ι := 435) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨319, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 2) (k := 3) (κ := 6)
      (ζ := 8) (ι := 36) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨30, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 2) (k := 4) (κ := 10)
      (ζ := 12) (ι := 78) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨63, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 2) (k := 5) (κ := 15)
      (ζ := 17) (ι := 153) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨119, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 68) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 2) (k := 6) (κ := 21)
      (ζ := 23) (ι := 276) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨207, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 3) (k := 0) (κ := 0)
      (ζ := 3) (ι := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨3, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 3) (k := 1) (κ := 1)
      (ζ := 4) (ι := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨7, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 3) (k := 3) (κ := 6)
      (ζ := 9) (ι := 45) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨36, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 100) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 3) (k := 6) (κ := 21)
      (ζ := 24) (ι := 300) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨222, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 4) (k := 0) (κ := 0)
      (ζ := 4) (ι := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨5, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 4) (k := 1) (κ := 1)
      (ζ := 5) (ι := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨10, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 4) (k := 2) (κ := 3)
      (ζ := 7) (ι := 28) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨21, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 132) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 4) (k := 7) (κ := 28)
      (ζ := 32) (ι := 528) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨376, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 80) h2 (by rw [map_ofNat])) (i := 5) (k := 2) (κ := 3)
      (ζ := 8) (ι := 36) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨26, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 5) (k := 4) (κ := 10)
      (ζ := 15) (ι := 120) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨90, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 5) (k := 5) (κ := 15)
      (ζ := 20) (ι := 210) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨155, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 164) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 240) h2 (by rw [map_ofNat])) (i := 5) (k := 7) (κ := 28)
      (ζ := 33) (ι := 561) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨396, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 6) (k := 3) (κ := 6)
      (ζ := 12) (ι := 78) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨57, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 144) h2 (by rw [map_ofNat])) (i := 6) (k := 4) (κ := 10)
      (ζ := 16) (ι := 136) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨100, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 176) h2 (by rw [map_ofNat])) (i := 6) (k := 5) (κ := 15)
      (ζ := 21) (ι := 231) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨168, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 196) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 6) (k := 6) (κ := 21)
      (ζ := 27) (ι := 378) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨270, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 16) h2 (by rw [map_ofNat])) (i := 7) (k := 0) (κ := 0)
      (ζ := 7) (ι := 28) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨14, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 48) h2 (by rw [map_ofNat])) (i := 7) (k := 1) (κ := 1)
      (ζ := 8) (ι := 36) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨22, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 112) h2 (by rw [map_ofNat])) (i := 7) (k := 3) (κ := 6)
      (ζ := 13) (ι := 91) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨65, by norm_num⟩)
  · exact mem_iUnion_stratFibre_of_class (pow_dvd_sub_of_res (α := 228) h1 (by rw [map_ofNat]))
      (pow_dvd_sub_of_res (α := 208) h2 (by rw [map_ofNat])) (i := 7) (k := 6) (κ := 21)
      (ζ := 28) (ι := 406) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ite_eq_left ⟨287, by norm_num⟩)

/-- **No point of the `(I₄*, 2)` locus is a `(2⁴, 2⁶)`-dilate**: on it `a₄ ≡ 4 (mod 16)`. -/
theorem notMem_range_of_mem_iStarFourTwoLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarFourTwoLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarFourTwo_notDvd _ _ (mem_iStarFourTwoLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 8 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- **No point of the `(I₄*, 4)` locus is a `(2⁴, 2⁶)`-dilate**: on it `a₄ ≡ 4 (mod 16)`. -/
theorem notMem_range_of_mem_iStarFourFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ iStarFourFourLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarFourFour_notDvd _ _ (mem_iStarFourFourLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 8 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- The `(I₄*, 2)` locus lies in the minimal part of the `t = 2` row. -/
theorem iStarFourTwoLocus_subset_headMinimal :
    iStarFourTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarFourTwoLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarFourTwoLocus hx⟩

/-- The `(I₄*, 4)` locus lies in the minimal part of the `t = 4` row. -/
theorem iStarFourFourLocus_subset_headMinimal :
    iStarFourFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarFourFourLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarFourFourLocus hx⟩

/-! ### The mass `32 · 2⁻¹⁶` as a numeral -/

/-- `32 · 2⁻¹⁶ = 1/2048`. -/
theorem thirtyTwo_mul_inv_pow_sixteen_eq : (32 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 16 = 1 / 2048 := by
  rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 16 = 65536 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end WeierstrassCurve

end
