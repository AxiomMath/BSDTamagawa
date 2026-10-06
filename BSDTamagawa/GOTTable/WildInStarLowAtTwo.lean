/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildInStarAtTwo

/-!
# The `I₂*` and `I₃*` congruence loci at `p = 2`

Two members of the `Iₘ*` family at `p = 2` are cut out by a congruence alone, with no valuation
condition on the discriminant.

Both lie in `a₄ ≡ 4 (mod 8)`, `a₆ ≡ 0 (mod 16)`. There Steps 1–5 succeed, Step 6's cubic has a
double but not a triple root, and Step 7 enters its subprocedure at level `2`, where the
`Y`-quadratic has vanishing linear coefficient and hence a double root. Writing `a₄ = 4 + 8A₀`, the
`X`-cubic of the `Y`-translate has linear coefficient `≡ A₀`, and its parity decides the type:

* `a₄ ≡ 12 (mod 16)` (so `A₀` odd) with `a₆ ≡ 0 (mod 16)`: the `X`-cubic has no double root, the
  loop exits at level `2`, and the whole class is `I₂*`, of mass `1/256`;
* `a₄ ≡ 4 (mod 16)` (so `A₀` even) with `a₆ ≡ 0 (mod 32)`: the `X`-cubic has a double root, the
  loop recurses once and exits at level `3`, and the whole class is `I₃*`, of mass `1/512`.

Each class splits in half between Tamagawa numbers `2` and `4`, and the split is not a function of
`a₆` alone. On `a₄ = 12 + 16A`, `a₆ = 16G + 32F` with `G² = G` the Tamagawa number is `4` exactly
when `A + F` is odd. On `a₄ = 4 + 16α + 32A`, `a₆ = 32ε + 64E` with `α² = α` and `ε² = ε` it is `4`
exactly when `A + α + E` is even. The four resulting loci are unions of `8` classes modulo `64` and
of `16` classes modulo `128`, of masses `1/512` and `1/1024`.

## Main definitions

* `WeierstrassCurve.iStarTwoTwoLocus`, `WeierstrassCurve.iStarTwoFourLocus`: the `(I₂*, 2)` and
  `(I₂*, 4)` loci.
* `WeierstrassCurve.iStarThreeTwoLocus`, `WeierstrassCurve.iStarThreeFourLocus`: the `(I₃*, 2)` and
  `(I₃*, 4)` loci.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.mod_rX_two`: at `p = 2`, `Step7.rX` is a lift of the
  residue of `a₆/ϖ^(2n+1)` once the `X`-cubic is monic.
* `WeierstrassCurve.run_eq_Istar_two_of_step5`, `WeierstrassCurve.run_eq_Istar_three_of_step5`:
  Tate's algorithm returns `I₂*` after an exit at the `X`-cubic at level `2`, and `I₃*` after one
  recursion and an exit at the `Y`-quadratic at level `3`, at every prime.
* `WeierstrassCurve.exists_step7_entry_even_two`: Steps 1–7 on `a₄ ≡ 4 (mod 8)`, `a₆ ≡ 0 (mod 16)`.
* `WeierstrassCurve.run_eq_Istar_two_at_two`, `WeierstrassCurve.run_eq_Istar_three_at_two`: the two
  forward runs, with their Tamagawa numbers as congruences on the parameters.
-/

open CommRing Ideal CharP MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Two more characteristic-two branch tests -/

/-- **A `Cubic` record with vanishing leading and linear coefficients has a double root.** For
`⟨0, b, 0, d⟩` the discriminant is `b²c² − 4b³d = −4b³d`, and `4 = 0` on `𝔽_2`. -/
theorem hasDoubleRoot_of_c_eq_zero_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hc : P.c = 0) : P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_a_eq_zero ha, hc, residue_four_eq_zero_two hp2]
  ring

open scoped Classical in
/-- Over the residue field of `ℤ_2`, the cubic record `⟨0, 1, 1, d⟩` has a root exactly when
`d = 0`. -/
theorem card_roots_toFinset_pos_iff_cubic_two (hp2 : p = 2) (d : ℤ_[p] ⧸ span {(p : ℤ_[p])}) :
    0 < (⟨0, 1, 1, d⟩ : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})).roots.toFinset.card ↔ d = 0 := by
  rw [show (⟨0, 1, 1, d⟩ : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})) = ⟨0, 1, 1, -(-d)⟩ from by
    rw [neg_neg], card_roots_toFinset_pos_iff_two hp2, neg_eq_zero]

/-! ### The in-loop `X`-translation, modulo `2` -/

/-- **`Step7.rX` is a lift of the residue of `a₆ / ϖ^(2n+1)` at `p = 2`, once the `X`-cubic is
monic.** -/
theorem TateAlgorithm.Step7.mod_rX_two (hp2 : p = 2) (V : WeierstrassCurve ℤ_[p]) (n : ℕ)
    (hb : (cubic (p : ℤ_[p]) V 0 n).b = 1) :
    mod (p : ℤ_[p]) (Step7.rX (p : ℤ_[p]) V n) = (cubic (p : ℤ_[p]) V 0 n).d := by
  have hsq := Step7.sq_mod_rX_of_two_eq_zero (Step2.residue_two_eq_zero_of_eq_two (p := p) hp2) V n
  rw [hb, div_one] at hsq
  rw [← hsq, residue_sq_eq_self_two hp2]

/-! ### Two forwardings: the even exit at level `2`, and the odd exit at level `3` -/

open scoped Classical in
/-- **Steps 1–5 succeed, Step 6's cubic has a double but not a triple root, Step 7's level-`2`
`Y`-quadratic has a double root and the level-`2` `X`-cubic has not: the answer is `I₂*`**, with
Tamagawa number `4` or `2` according as the `X`-cubic of the `Y`-translate has a root or not. -/
theorem run_eq_Istar_two_of_step5 {W V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
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
            0 2).roots.toFinset.card then 4 else 2 := by
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
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7),
    Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔc le_rfl hvc ha₂c hY hX]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **One iteration of Step 7's subprocedure, then the exit at the level-`3` `Y`-quadratic: the
answer is `I₃*`**, with Tamagawa number `4` or `2` according as that quadratic has a root or
not. -/
theorem run_eq_Istar_three_of_step5 {W V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hY : (quadratic (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2).HasDoubleRoot)
    (hX : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 0 2).HasDoubleRoot)
    (hY' : ¬ (quadratic (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 2) 3).HasDoubleRoot) :
    (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I! 3 ∧
      (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if 0 < (quadratic (p : ℤ_[p]) (Step7.translateX (p : ℤ_[p]) (Step7.translateY
            (p : ℤ_[p]) (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 2)
            3).roots.toFinset.card then 4 else 2 := by
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
  have hvY := Step7.hasValuation_translateY (n := 2) le_rfl hϖ hvc hY
  have ha₂Y := Step7.not_dvd_translateY_a₂ 2 ha₂c
  have hΔ' : (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 2).Δ ≠ 0 := by
    rwa [Step7.translateX_Δ, Step7.translateY_Δ]
  have hn' : 2 ≤ 2 + 1 := by norm_num
  have hW' := Step7.hasValuation_translateX (n := 2) le_rfl hϖ hvY ha₂Y hX
  have ha₂' := Step7.not_dvd_translateX_a₂ (n := 2) le_rfl hϖ hvY.a₂ ha₂Y
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7),
    Step7.subprocedure_eq_subprocedure hϖ hΔc le_rfl hvc ha₂c hY hX hΔ' hn' hW' ha₂',
    Step7.subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ' hn' hW' ha₂' hY']
  exact ⟨rfl, rfl⟩

/-! ### The common Step-7 entry of the `a₄ ≡ 4 (mod 8)`, `a₆ ≡ 0 (mod 16)` locus -/

/-- **Steps 1–7 on `a₄ ≡ 4 (mod 8)`, `a₆ ≡ 0 (mod 16)`.** For `a₄ = 4 + 8A₀` and `a₆ = 16B`, Steps
1–5 succeed with output `V`, Step 6's cubic has a double but not a triple root, and the Step-7
translate is `⟨1, 2(1 + 2ν), 2σ, 4μ⟩ • (a₄, a₆)` for some `ν`, `σ`, `μ`. -/
theorem exists_step7_entry_even_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A₀ B : ℤ_[p]}
    (ha₄ : a₄ = 4 + 8 * A₀) (ha₆ : a₆ = 16 * B) :
    ∃ V : WeierstrassCurve ℤ_[p], ∃ ν σ μ : ℤ_[p],
      Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok V ∧
        (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot ∧
        ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot ∧
        Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)
          = (VariableChange.mk 1 (2 * (1 + 2 * ν)) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆ := by
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
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exact ⟨y, hy⟩
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hy, hπ, ha₄] at hc
      exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one
        ⟨c - 3 - 4 * A₀ - 6 * y - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩)
  obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨8 * B + 4 * ρ + 8 * A₀ * ρ + 4 * ρ ^ 3, by rw [hπ, ha₆, ha₄, hr]; ring⟩
    obtain ⟨c, hc⟩ := h2
    obtain ⟨d, hd⟩ := hva₆
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨c - d, by linear_combination hc - hd⟩ : (p : ℤ_[p]) ∣ t ^ 2)
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 1 + 2 * A₀ + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p], x = 4 * B + 2 * ρ + 4 * A₀ * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
  have hA4 : a₄ + 3 * r ^ 2 = 4 * Q₄ := by rw [ha₄, hr, hQ₄]; ring
  have hA6 : a₆ + r * a₄ + r ^ 3 - t ^ 2 = 4 * Q₆ := by rw [ha₆, ha₄, hr, ht, hQ₆]; ring
  have h5run := step5_run_eq_ok_of_two hp2 hπ hΔd hV ht hA4 hA6
  have hVa₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
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
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[p], x = 3 * ρ - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[p], x = Q₄ - s * (t₆ + τ) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ x : ℤ_[p], x = B + A₀ * ρ + ρ + m * ρ - m := ⟨_, rfl⟩
  have hQ₆G : Q₆ = (0 : ℤ_[p]) ^ 2 - τ ^ 2 + 4 * G := by
    rw [hQ₆, hG]; linear_combination (2 * ρ - 2) * hm
  have hK4 : (p : ℤ_[p]) ^ 2 ∣ Q₆ * (Q₆ + 2 * τ - 1) := by
    rw [pow_dvd_iff_toZModPow_eq_zero]
    have h4G : PadicInt.toZModPow 2 ((4 : ℤ_[p]) * G) = 0 :=
      (pow_dvd_iff_toZModPow_eq_zero 2 _).1 ⟨G, by rw [hπ]; ring⟩
    have hQr : PadicInt.toZModPow 2 Q₆
        = PadicInt.toZModPow 2 0 ^ 2 - PadicInt.toZModPow 2 τ ^ 2 := by
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
  have hX₄res : mod (p : ℤ_[p]) X₄ = mod (p : ℤ_[p]) (1 + ρ) :=
    mod_eq_mod_of_dvd_sub_two ⟨A₀ + 3 * m - 2 * ρ - σ * (t₆ + τ), by
      rw [hX₄, hQ₄, hσ, hπ]; linear_combination 3 * hm⟩
  have hcubb : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod (p : ℤ_[p]) ρ := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂) (p : ℤ_[p])) = _
    rw [div_eq_of_eq_mul_two hW₆a₂]
    exact mod_eq_mod_of_dvd_sub_two ⟨ρ - σ ^ 2, by rw [hX₂, hπ]; ring⟩
  have hcubc : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod (p : ℤ_[p]) (1 + ρ) := by
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
    exact ⟨m, by rw [hπ]; linear_combination hm⟩
  have hntr : ¬ (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasTripleRoot := by
    refine not_hasTripleRoot_of_sub_eq_one_two hp2 ?_
    rw [hcubb, hcubc, ← map_sub, show ρ - (1 + ρ) = -(1 : ℤ_[p]) from by ring, map_neg, map_one]
    linear_combination -(Step2.residue_two_eq_zero_of_eq_two (p := p) hp2)
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
    exact smul_smul_eq _ (by rw [hR₇]) (by ring) (by rw [hT₇]; ring)
  obtain ⟨ν, hν⟩ : ∃ x : ℤ_[p], x = ρ + k₇ := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ x : ℤ_[p], x = r₇ * σ + τ - mτ + 2 * G + j := ⟨_, rfl⟩
  have hR₇v : R₇ = 2 * (1 + 2 * ν) := by rw [hR₇, hπ, hk₇, hr, hν]; ring
  have hT₇v : T₇ = 4 * μ := by
    rw [hT₇, hμ, hT₂, hπ, ht, hσ, hj, hQ₆G]; linear_combination -2 * hmτ
  refine ⟨_, ν, σ, μ, h5run, hW₆ ▸ hdbl, hW₆ ▸ hntr, ?_⟩
  rw [hW₆, hW₇, hR₇v, hσ, hT₇v]

/-! ### The forward run on the `I₂*` locus `a₄ ≡ 12 (mod 16)`, `a₆ ≡ 0 (mod 16)` -/

open scoped Classical in
/-- **The forward run at `I₂*`, on `a₄ ≡ 12 (mod 16)` and `a₆ ≡ 0 (mod 16)`.** For `a₄ = 12 + 16A`
and `a₆ = 16G + 32F` with `G² = G`, Tate's algorithm at `2` returns `I₂*`, with Tamagawa number `4`
if `A + F` is odd and `2` otherwise. -/
theorem run_eq_Istar_two_at_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A F G : ℤ_[p]}
    (hG : G ^ 2 = G) (ha₄ : a₄ = 12 + 16 * A) (ha₆ : a₆ = 16 * G + 32 * F)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 2 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if (p : ℤ_[p]) ∣ 1 + A + F then 4 else 2 := by
  classical
  obtain ⟨V, ν, σ, μ, h5, hdbl, hntr, hW₇⟩ :=
    exists_step7_entry_even_two (a₄ := a₄) (a₆ := a₆) (A₀ := 1 + 2 * A) (B := G + 2 * F) hp2 hπ
      (by rw [ha₄]; ring) (by rw [ha₆]; ring)
  obtain ⟨u, hu⟩ : ∃ x : ℤ_[p], x = 1 + 2 * ν := ⟨_, rfl⟩
  rw [← hu] at hW₇
  obtain ⟨X, hX⟩ : ∃ x : ℤ_[p], x = F + u + A * u + u * ν + u * ν ^ 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ x : ℤ_[p], x = G + 2 * X := ⟨_, rfl⟩
  have hpow2 : ((p : ℤ_[p])) ^ 2 = 4 := by rw [hπ]; norm_num
  have hpow3 : ((p : ℤ_[p])) ^ (2 + 1) = 8 := by rw [hπ]; norm_num
  have hpow4 : ((p : ℤ_[p])) ^ (2 * 2) = 16 := by rw [hπ]; norm_num
  have hpow5 : ((p : ℤ_[p])) ^ (2 * 2 + 1) = 32 := by rw [hπ]; norm_num
  have hq3 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * (2 * μ) := by rw [smul_ofShortNF_a₃, hpow2]; ring
  have hV6 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2) * (W - μ ^ 2) := by
    rw [smul_ofShortNF_a₆, ha₄, ha₆, hW, hX, hu, hpow4]; ring
  have hqc : (quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ))
      • ofShortNF a₄ a₆).a₃) ((p : ℤ_[p]) ^ 2)) = 0
    rw [div_eq_of_eq_pow_mul_two hq3, mod_eq_zero]
    exact ⟨μ, by rw [hπ]⟩
  have hY : (quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2).HasDoubleRoot :=
    hasDoubleRoot_of_c_eq_zero_two hp2 rfl hqc
  obtain ⟨tY, htY⟩ : ∃ x : ℤ_[p], x = Step7.tY (p : ℤ_[p])
    ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[p], tY = -(W - μ ^ 2) + 2 * w := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ tY + (W - μ ^ 2) := by
      rw [← mod_eq_zero, map_add, htY, Step7.mod_tY_two hp2,
        div_eq_of_eq_pow_mul_two hV6, neg_add_cancel]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨mμ, hmμ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ μ
  obtain ⟨z, hz⟩ : ∃ x : ℤ_[p], x = mμ + w := ⟨_, rfl⟩
  have hτ₈ : tY + μ = -W + 2 * z := by rw [hw, hz]; linear_combination hmμ
  have hW₈ : Step7.translateY (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2
      = (VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆ := by
    have h : Step7.translateY (p : ℤ_[p])
        ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 2 * tY))
          • ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) := by rw [htY]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hpow2]; linear_combination (-4 : ℤ_[p]) * hτ₈)
  obtain ⟨N, hN⟩ : ∃ x : ℤ_[p], x = X - 2 * G * X - 2 * X ^ 2 + 2 * W * z - 2 * z ^ 2 := ⟨_, rfl⟩
  have ha₂8 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆).a₂
      = (p : ℤ_[p]) * (3 * u - 2 * σ ^ 2) := by rw [smul_ofShortNF_a₂, hπ]; ring
  have ha₄8 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ (2 + 1)
        * (3 + 2 * A + 6 * ν + 6 * ν ^ 2 - 2 * σ * (-W + 2 * z)) := by
    rw [smul_ofShortNF_a₄, ha₄, hu, hpow3]; ring
  have ha₆8 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2 + 1) * N := by
    rw [smul_ofShortNF_a₆, ha₄, ha₆, hN, hW, hX, hu, hpow5]; linear_combination (-16 : ℤ_[p]) * hG
  have hb1 : mod (p : ℤ_[p]) (3 * u - 2 * σ ^ 2) = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := 3 * u - 2 * σ ^ 2) (y := 1)
      ⟨1 + 3 * ν - σ ^ 2, by rw [hu, hπ]; ring⟩, map_one]
  have hc1 : mod (p : ℤ_[p]) (3 + 2 * A + 6 * ν + 6 * ν ^ 2 - 2 * σ * (-W + 2 * z)) = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (y := 1)
      ⟨1 + A + 3 * ν + 3 * ν ^ 2 - σ * (-W + 2 * z), by rw [hπ]; ring⟩, map_one]
  have hcubic : cubic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆) 0 2
      = ⟨0, 1, 1, mod (p : ℤ_[p]) N⟩ := by
    rw [cubic, div_eq_of_eq_mul_two ha₂8, div_eq_of_eq_pow_mul_two ha₄8,
      div_eq_of_eq_pow_mul_two ha₆8, hb1, hc1, map_zero]
  have hXnd : ¬ (cubic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆)
      0 2).HasDoubleRoot := by
    rw [hcubic]
    exact not_hasDoubleRoot_quadratic_two hp2 rfl rfl rfl
  obtain ⟨mν, hmν⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν
  have hNres : mod (p : ℤ_[p]) N = mod (p : ℤ_[p]) (1 + A + F) :=
    mod_eq_mod_of_dvd_sub_two ⟨ν + A * ν + u * mν - G * X - X ^ 2 + W * z - z ^ 2, by
      rw [hN, hX, hu, hπ]; linear_combination (1 + 2 * ν) * hmν⟩
  have hmain := run_eq_Istar_two_of_step5 hΔ h5 hdbl hntr
    (by rw [hW₇]; exact hY) (by rw [hW₇, hW₈]; exact hXnd)
  refine ⟨hmain.1, ?_⟩
  rw [hmain.2, hW₇, hW₈, hcubic]
  refine if_congr ?_ rfl rfl
  rw [card_roots_toFinset_pos_iff_cubic_two hp2, hNres, mod_eq_zero]

/-! ### The forward run on the `I₃*` locus `a₄ ≡ 4 (mod 16)`, `a₆ ≡ 0 (mod 32)` -/

/-- **The `I₃*` Tamagawa bit, as a `ZMod 4` identity.** For `α² = α`, `ε² = ε` and `Y` as
displayed, the displayed polynomial in `ν` and `Y` equals `2(A + α + E)` in `ZMod 4`. -/
theorem zmod_istar_three_bit (hp2 : p = 2) : ∀ α ε A E ν Y : ZMod (p ^ 2),
    α ^ 2 = α → ε ^ 2 = ε →
    Y = ε + 2 * E + ν + (1 + 2 * ν) * ν + (1 + 2 * ν) * ν ^ 2 + (α + 2 * A) * (1 + 2 * ν) →
    -2 * (α + 2 * A) * ν - (1 + 2 * ν) * (ν ^ 2 + ν) + (ν - Y) ^ 2 + (ν - Y)
        + 2 * (ν - Y) ^ 2 + 2 * (ν - Y) ^ 3 - 2 * Y - 2 * Y ^ 2 + 2 * (α + 2 * A) * (ν - Y)
      = 2 * (A + α + E) := by
  subst hp2; decide

open scoped Classical in
/-- **The forward run at `I₃*`, on `a₄ ≡ 4 (mod 16)` and `a₆ ≡ 0 (mod 32)`.** For
`a₄ = 4 + 16α + 32A` and `a₆ = 32ε + 64E` with `α² = α` and `ε² = ε`, Tate's algorithm at `2`
returns `I₃*`, with Tamagawa number `4` if `A + α + E` is even and `2` otherwise. -/
theorem run_eq_Istar_three_at_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A E α ε : ℤ_[p]}
    (hα : α ^ 2 = α) (hε : ε ^ 2 = ε)
    (ha₄ : a₄ = 4 + 16 * α + 32 * A) (ha₆ : a₆ = 32 * ε + 64 * E)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 3 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if (p : ℤ_[p]) ∣ A + α + E then 4 else 2 := by
  classical
  obtain ⟨Ā, hĀ⟩ : ∃ x : ℤ_[p], x = α + 2 * A := ⟨_, rfl⟩
  obtain ⟨Ē, hĒ⟩ : ∃ x : ℤ_[p], x = ε + 2 * E := ⟨_, rfl⟩
  have ha₄' : a₄ = 4 + 16 * Ā := by rw [hĀ, ha₄]; ring
  have ha₆' : a₆ = 32 * Ē := by rw [hĒ, ha₆]; ring
  obtain ⟨V, ν, σ, μ, h5, hdbl, hntr, hW₇⟩ :=
    exists_step7_entry_even_two (a₄ := a₄) (a₆ := a₆) (A₀ := 2 * Ā) (B := 2 * Ē) hp2 hπ
      (by rw [ha₄']; ring) (by rw [ha₆']; ring)
  obtain ⟨u, hu⟩ : ∃ x : ℤ_[p], x = 1 + 2 * ν := ⟨_, rfl⟩
  rw [← hu] at hW₇
  obtain ⟨mν, hmν⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[p], x = Ē + ν + u * ν + u * ν ^ 2 + Ā * u := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ x : ℤ_[p], x = 1 + 2 * Y := ⟨_, rfl⟩
  have hpow2 : ((p : ℤ_[p])) ^ 2 = 4 := by rw [hπ]; norm_num
  have hpow3 : ((p : ℤ_[p])) ^ 3 = 8 := by rw [hπ]; norm_num
  have hpow4 : ((p : ℤ_[p])) ^ (2 * 2) = 16 := by rw [hπ]; norm_num
  have hpow5 : ((p : ℤ_[p])) ^ (2 * 2 + 1) = 32 := by rw [hπ]; norm_num
  have hpow6 : ((p : ℤ_[p])) ^ (2 * 3) = 64 := by rw [hπ]; norm_num
  have hq3 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * (2 * μ) := by rw [smul_ofShortNF_a₃, hpow2]; ring
  have hV6 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2) * (W - μ ^ 2) := by
    rw [smul_ofShortNF_a₆, ha₄', ha₆', hW, hY, hu, hpow4]; ring
  have hqc : (quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ))
      • ofShortNF a₄ a₆).a₃) ((p : ℤ_[p]) ^ 2)) = 0
    rw [div_eq_of_eq_pow_mul_two hq3, mod_eq_zero]
    exact ⟨μ, by rw [hπ]⟩
  have hY2 : (quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2).HasDoubleRoot :=
    hasDoubleRoot_of_c_eq_zero_two hp2 rfl hqc
  obtain ⟨tY, htY⟩ : ∃ x : ℤ_[p], x = Step7.tY (p : ℤ_[p])
    ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[p], tY = -(W - μ ^ 2) + 2 * w := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ tY + (W - μ ^ 2) := by
      rw [← mod_eq_zero, map_add, htY, Step7.mod_tY_two hp2,
        div_eq_of_eq_pow_mul_two hV6, neg_add_cancel]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨mμ, hmμ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ μ
  obtain ⟨z, hz⟩ : ∃ x : ℤ_[p], x = mμ + w := ⟨_, rfl⟩
  have hτ₈ : tY + μ = -W + 2 * z := by rw [hw, hz]; linear_combination hmμ
  have hW₈ : Step7.translateY (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2
      = (VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆ := by
    have h : Step7.translateY (p : ℤ_[p])
        ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) 2
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 2 * tY))
          • ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * μ)) • ofShortNF a₄ a₆) := by rw [htY]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hpow2]; linear_combination (-4 : ℤ_[p]) * hτ₈)
  obtain ⟨N₂, hN₂⟩ : ∃ x : ℤ_[p], x = -Y - 2 * Y ^ 2 + 2 * W * z - 2 * z ^ 2 := ⟨_, rfl⟩
  have ha₂8 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆).a₂
      = (p : ℤ_[p]) * (3 * u - 2 * σ ^ 2) := by rw [smul_ofShortNF_a₂, hπ]; ring
  have ha₄8 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ (2 + 1)
        * (2 * (1 + α + 2 * A + 3 * ν + 3 * ν ^ 2 - σ * (-W + 2 * z))) := by
    rw [smul_ofShortNF_a₄, ha₄, hu, hpow3]; ring
  have ha₆8 : ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2 + 1) * N₂ := by
    rw [smul_ofShortNF_a₆, ha₄', ha₆', hN₂, hW, hY, hu, hpow5]; ring
  have hb1 : mod (p : ℤ_[p]) (3 * u - 2 * σ ^ 2) = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := 3 * u - 2 * σ ^ 2) (y := 1)
      ⟨1 + 3 * ν - σ ^ 2, by rw [hu, hπ]; ring⟩, map_one]
  have hc0 : mod (p : ℤ_[p])
      (2 * (1 + α + 2 * A + 3 * ν + 3 * ν ^ 2 - σ * (-W + 2 * z))) = 0 := by
    rw [mod_eq_zero]
    exact ⟨1 + α + 2 * A + 3 * ν + 3 * ν ^ 2 - σ * (-W + 2 * z), by rw [hπ]⟩
  have hcubic8 : cubic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆) 0 2
      = ⟨0, 1, 0, mod (p : ℤ_[p]) N₂⟩ := by
    rw [cubic, div_eq_of_eq_mul_two ha₂8, div_eq_of_eq_pow_mul_two ha₄8,
      div_eq_of_eq_pow_mul_two ha₆8, hb1, hc0, map_zero]
  have hX2 : (cubic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆)
      0 2).HasDoubleRoot := by
    rw [hcubic8]
    exact hasDoubleRoot_of_c_eq_zero_two hp2 rfl rfl
  obtain ⟨rX, hrX⟩ : ∃ x : ℤ_[p], x = Step7.rX (p : ℤ_[p])
    ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  have hrXres : mod (p : ℤ_[p]) rX = mod (p : ℤ_[p]) N₂ := by
    rw [hrX, Step7.mod_rX_two hp2 _ 2 (by rw [hcubic8]), hcubic8]
  obtain ⟨ρ₉, hρ₉⟩ : ∃ x : ℤ_[p], rX = -Y + 2 * x := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ rX - (-Y) := by
      rw [← mod_eq_zero, map_sub, hrXres,
        mod_eq_mod_of_dvd_sub_two (x := N₂) (y := -Y)
          ⟨-Y ^ 2 + W * z - z ^ 2, by rw [hN₂, hπ]; ring⟩, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨ζ, hζ⟩ : ∃ x : ℤ_[p], x = z + rX * σ := ⟨_, rfl⟩
  obtain ⟨ν₉, hν₉⟩ : ∃ x : ℤ_[p], x = ν - Y + 2 * ρ₉ := ⟨_, rfl⟩
  have hW₉ : Step7.translateX (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆) 2
      = (VariableChange.mk 1 (2 * (1 + 2 * ν₉)) (2 * σ) (4 * (-W + 2 * ζ)))
        • ofShortNF a₄ a₆ := by
    have h : Step7.translateX (p : ℤ_[p])
        ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆) 2
        = (VariableChange.mk 1 ((p : ℤ_[p]) ^ 2 * rX) 0 0)
          • ((VariableChange.mk 1 (2 * u) (2 * σ) (4 * (-W + 2 * z))) • ofShortNF a₄ a₆) := by
      rw [hrX]
    rw [h]
    exact smul_smul_eq _ (by rw [hpow2, hν₉, hρ₉, hu]; ring) (by ring)
      (by rw [hpow2, hζ]; ring)
  obtain ⟨m₉, hm₉⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν₉
  obtain ⟨N₃, hN₃⟩ : ∃ x : ℤ_[p], x = (-(Ā * ν) - u * mν + ρ₉) + m₉ + ν₉ ^ 2 + ν₉ ^ 3
    - Y - Y ^ 2 + Ā * ν₉ + W * ζ - ζ ^ 2 := ⟨_, rfl⟩
  have hkey : Ē + Ā + ν₉ + 2 * Ā * ν + 2 * u * mν - 2 * ρ₉ = 0 := by
    rw [hν₉, hY, hu]; linear_combination (-(1 + 2 * ν)) * hmν
  have ha₃9 : ((VariableChange.mk 1 (2 * (1 + 2 * ν₉)) (2 * σ) (4 * (-W + 2 * ζ)))
      • ofShortNF a₄ a₆).a₃ = (p : ℤ_[p]) ^ 3 * (-W + 2 * ζ) := by
    rw [smul_ofShortNF_a₃, hpow3]; ring
  have ha₆9 : ((VariableChange.mk 1 (2 * (1 + 2 * ν₉)) (2 * σ) (4 * (-W + 2 * ζ)))
      • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ (2 * 3) * N₃ := by
    rw [smul_ofShortNF_a₆, ha₄', ha₆', hN₃, hW, hpow6]
    linear_combination 32 * hkey + 32 * hm₉
  have hcres9 : mod (p : ℤ_[p]) (-W + 2 * ζ) = 1 := by
    rw [mod_eq_mod_of_dvd_sub_two (x := -W + 2 * ζ) (y := 1)
      ⟨-1 - Y + ζ, by rw [hW, hπ]; ring⟩, map_one]
  have hquad9 : quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * (1 + 2 * ν₉)) (2 * σ) (4 * (-W + 2 * ζ))) • ofShortNF a₄ a₆) 3
      = ⟨0, 1, 1, -(mod (p : ℤ_[p]) N₃)⟩ := by
    rw [quadratic, div_eq_of_eq_pow_mul_two ha₃9, div_eq_of_eq_pow_mul_two ha₆9, hcres9]
  have hY3 : ¬ (quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 (2 * (1 + 2 * ν₉)) (2 * σ) (4 * (-W + 2 * ζ))) • ofShortNF a₄ a₆)
      3).HasDoubleRoot := by
    rw [hquad9]
    exact not_hasDoubleRoot_quadratic_two hp2 rfl rfl rfl
  obtain ⟨mζ, hmζ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ζ
  have h2N₃ : 2 * N₃ = (-2 * (α + 2 * A) * ν - (1 + 2 * ν) * (ν ^ 2 + ν) + (ν - Y) ^ 2
      + (ν - Y) + 2 * (ν - Y) ^ 2 + 2 * (ν - Y) ^ 3 - 2 * Y - 2 * Y ^ 2
      + 2 * (α + 2 * A) * (ν - Y))
      + 4 * (ρ₉ + 3 * (ν - Y) * ρ₉ + 3 * ρ₉ ^ 2 + 3 * (ν - Y) ^ 2 * ρ₉
        + 6 * (ν - Y) * ρ₉ ^ 2 + 4 * ρ₉ ^ 3 + (α + 2 * A) * ρ₉ + Y * ζ + ζ - mζ) := by
    have hm₉' : (ν - Y + 2 * ρ₉) ^ 2 + (ν - Y + 2 * ρ₉) = 2 * m₉ := by rwa [← hν₉]
    rw [hN₃, hν₉, hW, hu, hĀ]
    linear_combination (1 + 2 * ν) * hmν - hm₉' - 2 * hmζ
  have hαm : (PadicInt.toZModPow 2 α : ZMod (p ^ 2)) ^ 2 = PadicInt.toZModPow 2 α := by
    rw [← map_pow, hα]
  have hεm : (PadicInt.toZModPow 2 ε : ZMod (p ^ 2)) ^ 2 = PadicInt.toZModPow 2 ε := by
    rw [← map_pow, hε]
  have hYm : PadicInt.toZModPow 2 Y
      = PadicInt.toZModPow 2 ε + 2 * PadicInt.toZModPow 2 E + PadicInt.toZModPow 2 ν
        + (1 + 2 * PadicInt.toZModPow 2 ν) * PadicInt.toZModPow 2 ν
        + (1 + 2 * PadicInt.toZModPow 2 ν) * PadicInt.toZModPow 2 ν ^ 2
        + (PadicInt.toZModPow 2 α + 2 * PadicInt.toZModPow 2 A)
          * (1 + 2 * PadicInt.toZModPow 2 ν) := by
    rw [hY, hu, hĀ, hĒ]
    simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
  have hsmall : (p : ℤ_[p]) ^ 2 ∣ (-2 * (α + 2 * A) * ν - (1 + 2 * ν) * (ν ^ 2 + ν)
      + (ν - Y) ^ 2 + (ν - Y) + 2 * (ν - Y) ^ 2 + 2 * (ν - Y) ^ 3 - 2 * Y - 2 * Y ^ 2
      + 2 * (α + 2 * A) * (ν - Y)) - 2 * (A + α + E) := by
    rw [pow_dvd_iff_toZModPow_eq_zero, map_sub, sub_eq_zero]
    simpa only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat, map_one] using
      zmod_istar_three_bit hp2 _ _ _ _ _ _ hαm hεm hYm
  have hdvd : (p : ℤ_[p]) ∣ N₃ - (A + α + E) := by
    obtain ⟨c, hc⟩ := hsmall
    refine ⟨c + (ρ₉ + 3 * (ν - Y) * ρ₉ + 3 * ρ₉ ^ 2 + 3 * (ν - Y) ^ 2 * ρ₉
      + 6 * (ν - Y) * ρ₉ ^ 2 + 4 * ρ₉ ^ 3 + (α + 2 * A) * ρ₉ + Y * ζ + ζ - mζ),
      mul_left_cancel₀ (a := (p : ℤ_[p])) PadicInt.uniformizer_ne_zero ?_⟩
    rw [hπ] at hc ⊢
    linear_combination hc + h2N₃
  have hmain := run_eq_Istar_three_of_step5 hΔ h5 hdbl hntr
    (by rw [hW₇]; exact hY2) (by rw [hW₇, hW₈]; exact hX2)
    (by rw [hW₇, hW₈, hW₉]; exact hY3)
  refine ⟨hmain.1, ?_⟩
  rw [hmain.2, hW₇, hW₈, hW₉, hquad9]
  refine if_congr ?_ rfl rfl
  rw [card_roots_toFinset_pos_iff_two hp2, mod_eq_mod_of_dvd_sub_two hdvd, mod_eq_zero]

/-! ### Nonsingularity on the two loci -/

/-- On `a₄ ≡ 12 (mod 16)`, `a₆ ≡ 0 (mod 16)` the inner factor of the discriminant is odd or
`≡ 2 (mod 4)`, never zero. -/
theorem zmod_nonsingular_istar_two : ∀ X Y : ZMod (2 ^ 3), (3 + 4 * X) ^ 3 + 27 * Y ^ 2 ≠ 0 := by
  decide

/-- On `a₄ ≡ 4 (mod 16)`, `a₆ ≡ 0 (mod 32)` the inner factor of the discriminant is odd. -/
theorem zmod_nonsingular_istar_three :
    ∀ X Y : ZMod (2 ^ 2), (1 + 4 * X) ^ 3 + 108 * Y ^ 2 ≠ 0 := by decide

/-- **Nonsingularity on the `I₂*` locus**: `4a₄³ + 27a₆² = 256((3 + 4A)³ + 27B²)`. -/
theorem Δ_ne_zero_istar_two_at_two {a₄ a₆ A B : ℤ_[2]} (ha₄ : a₄ = 12 + 16 * A)
    (ha₆ : a₆ = 16 * B) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  refine ofShortNF_Δ_ne_zero_of_two fun h => ?_
  have h256 : (256 : ℤ_[2]) ≠ 0 := by
    rw [show (256 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 8 from by norm_num]
    exact pow_ne_zero 8 PadicInt.uniformizer_ne_zero
  have hcb : (3 + 4 * A) ^ 3 + 27 * B ^ 2 = 0 := by
    rw [ha₄, ha₆] at h
    refine mul_left_cancel₀ h256 ?_
    rw [mul_zero]
    linear_combination h
  have himg : PadicInt.toZModPow 3 ((3 + 4 * A) ^ 3 + 27 * B ^ 2) = 0 := by rw [hcb, map_zero]
  simp only [map_add, map_mul, map_pow, map_ofNat] at himg
  exact zmod_nonsingular_istar_two _ _ himg

/-- **Nonsingularity on the `I₃*` locus**: `4a₄³ + 27a₆² = 256((1 + 4A)³ + 108B²)`. -/
theorem Δ_ne_zero_istar_three_at_two {a₄ a₆ A B : ℤ_[2]} (ha₄ : a₄ = 4 + 16 * A)
    (ha₆ : a₆ = 32 * B) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  refine ofShortNF_Δ_ne_zero_of_two fun h => ?_
  have h256 : (256 : ℤ_[2]) ≠ 0 := by
    rw [show (256 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 8 from by norm_num]
    exact pow_ne_zero 8 PadicInt.uniformizer_ne_zero
  have hcb : (1 + 4 * A) ^ 3 + 108 * B ^ 2 = 0 := by
    rw [ha₄, ha₆] at h
    refine mul_left_cancel₀ h256 ?_
    rw [mul_zero]
    linear_combination h
  have himg : PadicInt.toZModPow 2 ((1 + 4 * A) ^ 3 + 108 * B ^ 2) = 0 := by rw [hcb, map_zero]
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one] at himg
  exact zmod_nonsingular_istar_three _ _ himg

/-! ### From a residue class to the parameters, and the Tamagawa bit -/

/-- **The `I₂*` locus, parametrised**, on the half where `32 ∣ a₆`. -/
theorem exists_params_istar_two_even {a₄ a₆ : ℤ_[2]} (h1 : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ a₄ - 12)
    (h2 : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ a₆) :
    ∃ A F : ℤ_[2], a₄ = 12 + 16 * A ∧ a₆ = 32 * F ∧ 2 * a₄ + a₆ + 8 = 32 * (1 + A + F) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ := h1
  obtain ⟨F, hF⟩ := h2
  rw [hcast] at hA hF
  exact ⟨A, F, by linear_combination hA, by linear_combination hF,
    by linear_combination 2 * hA + hF⟩

/-- **The `I₂*` locus, parametrised**, on the half where `a₆ ≡ 16 (mod 32)`. -/
theorem exists_params_istar_two_odd {a₄ a₆ : ℤ_[2]} (h1 : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ a₄ - 12)
    (h2 : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ a₆ - 16) :
    ∃ A F : ℤ_[2], a₄ = 12 + 16 * A ∧ a₆ = 16 + 32 * F ∧ 2 * a₄ + a₆ - 8 = 32 * (1 + A + F) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ := h1
  obtain ⟨F, hF⟩ := h2
  rw [hcast] at hA hF
  exact ⟨A, F, by linear_combination hA, by linear_combination hF,
    by linear_combination 2 * hA + hF⟩

/-- **The `I₃*` locus, parametrised.** `α` is the `16`-bit of `a₄` and `ε` the `32`-bit of `a₆`;
`2 ∣ A + α + E` is read off `2a₄ + a₆ − 8 + 32α − 32ε` modulo `2⁷`. -/
theorem exists_params_istar_three {a₄ a₆ α ε c₄ c₆ : ℤ_[2]}
    (hc₄ : c₄ = 4 + 16 * α) (hc₆ : c₆ = 32 * ε)
    (h1 : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ a₄ - c₄) (h2 : ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ a₆ - c₆) :
    ∃ A E : ℤ_[2], a₄ = 4 + 16 * α + 32 * A ∧ a₆ = 32 * ε + 64 * E ∧
      2 * a₄ + a₆ - 8 + 32 * α - 32 * ε = 64 * (A + α + E) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ := h1
  obtain ⟨E, hE⟩ := h2
  rw [hcast, hc₄] at hA
  rw [hcast, hc₆] at hE
  exact ⟨A, E, by linear_combination hA, by linear_combination hE,
    by linear_combination 2 * hA + hE⟩

/-- For `x = 2ᵏy` in `ℤ_2`, `2 ∣ y` exactly when `x` vanishes modulo `2ᵏ⁺¹`. -/
theorem dvd_iff_toZModPow_two_pow {k : ℕ} {y x : ℤ_[2]} (h : x = ((2 : ℕ) : ℤ_[2]) ^ k * y) :
    ((2 : ℕ) : ℤ_[2]) ∣ y ↔ PadicInt.toZModPow (k + 1) x = 0 := by
  rw [← pow_dvd_iff_toZModPow_eq_zero, h, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero k PadicInt.uniformizer_ne_zero)]

/-- For `x = 32y` in `ℤ_2`, `2 ∣ y` exactly when `x` vanishes modulo `2⁶`. -/
theorem dvd_iff_toZModPow_six_two {y x : ℤ_[2]} (h : x = 32 * y) :
    ((2 : ℕ) : ℤ_[2]) ∣ y ↔ PadicInt.toZModPow 6 x = 0 :=
  dvd_iff_toZModPow_two_pow (k := 5) (by rw [h]; norm_num)

/-- For `x = 64y` in `ℤ_2`, `2 ∣ y` exactly when `x` vanishes modulo `2⁷`. -/
theorem dvd_iff_toZModPow_seven_two {y x : ℤ_[2]} (h : x = 64 * y) :
    ((2 : ℕ) : ℤ_[2]) ∣ y ↔ PadicInt.toZModPow 7 x = 0 :=
  dvd_iff_toZModPow_two_pow (k := 6) (by rw [h]; norm_num)

/-! ### The `I₂*` residue sets modulo `64` -/

/-- **The residue condition cutting out the `(I₂*, 2)` locus at `2`**: eight classes modulo `64`.
The `16`-bit of `a₄` and the `32`-bit of `a₆` decide the Tamagawa number together. -/
abbrev HeadResIStarTwoTwo (a e : ZMod (2 ^ 6)) : Prop :=
  (a = 12 ∧ e = 0) ∨ (a = 12 ∧ e = 16) ∨ (a = 28 ∧ e = 32) ∨ (a = 28 ∧ e = 48) ∨
    (a = 44 ∧ e = 0) ∨ (a = 44 ∧ e = 16) ∨ (a = 60 ∧ e = 32) ∨ (a = 60 ∧ e = 48)

/-- **The residue condition cutting out the `(I₂*, 4)` locus at `2`**: the complementary eight
classes modulo `64`, obtained from `HeadResIStarTwoTwo` by flipping the `32`-bit of `a₆`. -/
abbrev HeadResIStarTwoFour (a e : ZMod (2 ^ 6)) : Prop :=
  (a = 12 ∧ e = 32) ∨ (a = 12 ∧ e = 48) ∨ (a = 28 ∧ e = 0) ∨ (a = 28 ∧ e = 16) ∨
    (a = 44 ∧ e = 32) ∨ (a = 44 ∧ e = 48) ∨ (a = 60 ∧ e = 0) ∨ (a = 60 ∧ e = 16)

/-- The eight `(I₂*, 2)` classes modulo `64`, as a `Finset`. -/
def headResiduesIStarTwoTwo : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(12, 0), (12, 16), (28, 32), (28, 48), (44, 0), (44, 16), (60, 32), (60, 48)}

/-- The eight `(I₂*, 4)` classes modulo `64`, as a `Finset`. -/
def headResiduesIStarTwoFour : Finset (ZMod (2 ^ 6) × ZMod (2 ^ 6)) :=
  {(12, 32), (12, 48), (28, 0), (28, 16), (44, 32), (44, 48), (60, 0), (60, 16)}

/-- There are eight `(I₂*, 2)` classes modulo `64`. -/
theorem card_headResiduesIStarTwoTwo : headResiduesIStarTwoTwo.card = 8 := by decide

/-- There are eight `(I₂*, 4)` classes modulo `64`. -/
theorem card_headResiduesIStarTwoFour : headResiduesIStarTwoFour.card = 8 := by decide

/-- A pair lies in `headResiduesIStarTwoTwo` exactly when it satisfies `HeadResIStarTwoTwo`. -/
theorem mem_headResiduesIStarTwoTwo_iff {c : ZMod (2 ^ 6) × ZMod (2 ^ 6)} :
    c ∈ headResiduesIStarTwoTwo ↔ HeadResIStarTwoTwo c.1 c.2 := by
  simp [headResiduesIStarTwoTwo, Prod.ext_iff]

/-- A pair lies in `headResiduesIStarTwoFour` exactly when it satisfies `HeadResIStarTwoFour`. -/
theorem mem_headResiduesIStarTwoFour_iff {c : ZMod (2 ^ 6) × ZMod (2 ^ 6)} :
    c ∈ headResiduesIStarTwoFour ↔ HeadResIStarTwoFour c.1 c.2 := by
  simp [headResiduesIStarTwoFour, Prod.ext_iff]

set_option maxRecDepth 100000 in
/-- **The `(I₂*, 2)` classes, split by the `16`-bit of `a₆` and with the Tamagawa bit refuted.** -/
theorem headResIStarTwoTwo_cases : ∀ a e : ZMod (2 ^ 6), HeadResIStarTwoTwo a e →
    ((ZMod.cast (a - 12) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast e : ZMod (2 ^ 5)) = 0
        ∧ 2 * a + e + 8 ≠ 0) ∨
      ((ZMod.cast (a - 12) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast (e - 16) : ZMod (2 ^ 5)) = 0
        ∧ 2 * a + e - 8 ≠ 0) := by
  decide

set_option maxRecDepth 100000 in
/-- **The `(I₂*, 4)` classes, split by the `16`-bit of `a₆` and with the Tamagawa bit met.** -/
theorem headResIStarTwoFour_cases : ∀ a e : ZMod (2 ^ 6), HeadResIStarTwoFour a e →
    ((ZMod.cast (a - 12) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast e : ZMod (2 ^ 5)) = 0
        ∧ 2 * a + e + 8 = 0) ∨
      ((ZMod.cast (a - 12) : ZMod (2 ^ 4)) = 0 ∧ (ZMod.cast (e - 16) : ZMod (2 ^ 5)) = 0
        ∧ 2 * a + e - 8 = 0) := by
  decide

set_option maxRecDepth 100000 in
/-- On the `(I₂*, 2)` classes, `a₄` is nonzero modulo `16`. -/
theorem headResIStarTwoTwo_notDvd : ∀ a e : ZMod (2 ^ 6), HeadResIStarTwoTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

set_option maxRecDepth 100000 in
/-- On the `(I₂*, 4)` classes, `a₄` is nonzero modulo `16`. -/
theorem headResIStarTwoFour_notDvd : ∀ a e : ZMod (2 ^ 6), HeadResIStarTwoFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

/-! ### The two `I₂*` loci and their masses -/

/-- The `(I₂*, 2)` locus at `2`: eight residue classes modulo `64`. -/
noncomputable def iStarTwoTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesIStarTwoTwo : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- The `(I₂*, 4)` locus at `2`: the complementary eight residue classes modulo `64`. -/
noncomputable def iStarTwoFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 6 ⁻¹' (headResiduesIStarTwoFour : Set (ZMod (2 ^ 6) × ZMod (2 ^ 6)))

/-- Membership of `iStarTwoTwoLocus` is the condition `HeadResIStarTwoTwo` on the residues of
`(a₄, a₆)` modulo `64`. -/
theorem mem_iStarTwoTwoLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarTwoTwoLocus ↔
      HeadResIStarTwoTwo (PadicInt.toZModPow 6 x.1) (PadicInt.toZModPow 6 x.2) := by
  rw [iStarTwoTwoLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarTwoTwo_iff,
    PadicInt.redPairPow]

/-- Membership of `iStarTwoFourLocus` is the condition `HeadResIStarTwoFour` on the residues of
`(a₄, a₆)` modulo `64`. -/
theorem mem_iStarTwoFourLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarTwoFourLocus ↔
      HeadResIStarTwoFour (PadicInt.toZModPow 6 x.1) (PadicInt.toZModPow 6 x.2) := by
  rw [iStarTwoFourLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarTwoFour_iff,
    PadicInt.redPairPow]

/-- The `(I₂*, 2)` locus is measurable. -/
theorem measurableSet_iStarTwoTwoLocus : MeasurableSet iStarTwoTwoLocus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesIStarTwoTwo

/-- The `(I₂*, 4)` locus is measurable. -/
theorem measurableSet_iStarTwoFourLocus : MeasurableSet iStarTwoFourLocus :=
  PadicInt.measurableSet_preimage_redPairPow 6 headResiduesIStarTwoFour

/-- The `(I₂*, 2)` locus has mass `1/512`. -/
theorem volume_iStarTwoTwoLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarTwoTwoLocus = 1 / 512 := by
  rw [iStarTwoTwoLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarTwoTwo,
    show ((8 : ℕ) : ℝ≥0∞) = 8 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 6) = 4096 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The `(I₂*, 4)` locus has mass `1/512`. -/
theorem volume_iStarTwoFourLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarTwoFourLocus = 1 / 512 := by
  rw [iStarTwoFourLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarTwoFour,
    show ((8 : ℕ) : ℝ≥0∞) = 8 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 6) = 4096 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### The `I₂*` loci sit inside the minimal part of the rows `t = 2` and `t = 4` -/

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- Every curve in the `(I₂*, 2)` locus has Kodaira type `I₂*` and Tamagawa number `2` at `2`. -/
theorem iStarTwoTwoLocus_subset_iUnion_stratFibre :
    iStarTwoTwoLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  rcases headResIStarTwoTwo_cases _ _ (mem_iStarTwoTwoLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_istar_two_even (a₄ := x.1) (a₆ := x.2)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) h2)
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
      Δ_ne_zero_istar_two_at_two (B := 2 * F) ha₄ (by rw [ha₆]; ring)
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ 1 + A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_two_at_two (p := 2) rfl (by norm_num) (G := 0)
      (by ring) ha₄ (by rw [ha₆]; ring) hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_istar_two_odd (a₄ := x.1) (a₆ := x.2)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
      Δ_ne_zero_istar_two_at_two (B := 1 + 2 * F) ha₄ (by rw [ha₆]; ring)
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ 1 + A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_add, map_sub, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_two_at_two (p := 2) rfl (by norm_num) (G := 1)
      (by ring) ha₄ (by rw [ha₆]; ring) hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- Every curve in the `(I₂*, 4)` locus has Kodaira type `I₂*` and Tamagawa number `4` at `2`. -/
theorem iStarTwoFourLocus_subset_iUnion_stratFibre :
    iStarTwoFourLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4) := by
  intro x hx
  rcases headResIStarTwoFour_cases _ _ (mem_iStarTwoFourLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_istar_two_even (a₄ := x.1) (a₆ := x.2)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) h2)
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
      Δ_ne_zero_istar_two_at_two (B := 2 * F) ha₄ (by rw [ha₆]; ring)
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ 1 + A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_two_at_two (p := 2) rfl (by norm_num) (G := 0)
      (by ring) ha₄ (by rw [ha₆]; ring) hΔ
    rw [ite_eq_left hd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, F, ha₄, ha₆, hsum⟩ := exists_params_istar_two_odd (a₄ := x.1) (a₆ := x.2)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 6) (by norm_num) (by rwa [map_sub, map_ofNat]))
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
      Δ_ne_zero_istar_two_at_two (B := 1 + 2 * F) ha₄ (by rw [ha₆]; ring)
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ 1 + A + F := by
      rw [dvd_iff_toZModPow_six_two hsum]
      simpa only [map_add, map_sub, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_two_at_two (p := 2) rfl (by norm_num) (G := 1)
      (by ring) ha₄ (by rw [ha₆]; ring) hΔ
    rw [ite_eq_left hd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 2,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- A point of the `(I₂*, 2)` locus is not of the form `(2⁴ a, 2⁶ b)`. -/
theorem notMem_range_of_mem_iStarTwoTwoLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarTwoTwoLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarTwoTwo_notDvd _ _ (mem_iStarTwoTwoLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- A point of the `(I₂*, 4)` locus is not of the form `(2⁴ a, 2⁶ b)`. -/
theorem notMem_range_of_mem_iStarTwoFourLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarTwoFourLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarTwoFour_notDvd _ _ (mem_iStarTwoFourLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `(I₂*, 2)` locus lies in the minimal part of the `t = 2` fibre at `2`. -/
theorem iStarTwoTwoLocus_subset_headMinimal :
    iStarTwoTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarTwoTwoLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarTwoTwoLocus hx⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `(I₂*, 4)` locus lies in the minimal part of the `t = 4` fibre at `2`. -/
theorem iStarTwoFourLocus_subset_headMinimal :
    iStarTwoFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarTwoFourLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarTwoFourLocus hx⟩

/-! ### The `I₃*` residue sets modulo `128` -/

/-- **The residue condition cutting out the `(I₃*, 2)` locus at `2`**: sixteen classes modulo
`128`. The Tamagawa number is decided by the parity of `A + α + E`, where `α` is the `16`-bit and
`A` the `32`-bit of `a₄` and `E` the `64`-bit of `a₆`. -/
abbrev HeadResIStarThreeTwo (a e : ZMod (2 ^ 7)) : Prop :=
  (a = 4 ∧ e = 64) ∨ (a = 4 ∧ e = 96) ∨ (a = 20 ∧ e = 0) ∨ (a = 20 ∧ e = 32) ∨
    (a = 36 ∧ e = 0) ∨ (a = 36 ∧ e = 32) ∨ (a = 52 ∧ e = 64) ∨ (a = 52 ∧ e = 96) ∨
    (a = 68 ∧ e = 64) ∨ (a = 68 ∧ e = 96) ∨ (a = 84 ∧ e = 0) ∨ (a = 84 ∧ e = 32) ∨
    (a = 100 ∧ e = 0) ∨ (a = 100 ∧ e = 32) ∨ (a = 116 ∧ e = 64) ∨ (a = 116 ∧ e = 96)

/-- **The residue condition cutting out the `(I₃*, 4)` locus at `2`**: the complementary sixteen
classes modulo `128`, obtained from `HeadResIStarThreeTwo` by flipping the `64`-bit of `a₆`. -/
abbrev HeadResIStarThreeFour (a e : ZMod (2 ^ 7)) : Prop :=
  (a = 4 ∧ e = 0) ∨ (a = 4 ∧ e = 32) ∨ (a = 20 ∧ e = 64) ∨ (a = 20 ∧ e = 96) ∨
    (a = 36 ∧ e = 64) ∨ (a = 36 ∧ e = 96) ∨ (a = 52 ∧ e = 0) ∨ (a = 52 ∧ e = 32) ∨
    (a = 68 ∧ e = 0) ∨ (a = 68 ∧ e = 32) ∨ (a = 84 ∧ e = 64) ∨ (a = 84 ∧ e = 96) ∨
    (a = 100 ∧ e = 64) ∨ (a = 100 ∧ e = 96) ∨ (a = 116 ∧ e = 0) ∨ (a = 116 ∧ e = 32)

/-- The sixteen `(I₃*, 2)` classes modulo `128`, as a `Finset`. -/
def headResiduesIStarThreeTwo : Finset (ZMod (2 ^ 7) × ZMod (2 ^ 7)) :=
  {(4, 64), (4, 96), (20, 0), (20, 32), (36, 0), (36, 32), (52, 64), (52, 96),
   (68, 64), (68, 96), (84, 0), (84, 32), (100, 0), (100, 32), (116, 64), (116, 96)}

/-- The sixteen `(I₃*, 4)` classes modulo `128`, as a `Finset`. -/
def headResiduesIStarThreeFour : Finset (ZMod (2 ^ 7) × ZMod (2 ^ 7)) :=
  {(4, 0), (4, 32), (20, 64), (20, 96), (36, 64), (36, 96), (52, 0), (52, 32),
   (68, 0), (68, 32), (84, 64), (84, 96), (100, 64), (100, 96), (116, 0), (116, 32)}

set_option maxRecDepth 100000 in
/-- There are sixteen `(I₃*, 2)` classes modulo `128`. -/
theorem card_headResiduesIStarThreeTwo : headResiduesIStarThreeTwo.card = 16 := by decide

set_option maxRecDepth 100000 in
/-- There are sixteen `(I₃*, 4)` classes modulo `128`. -/
theorem card_headResiduesIStarThreeFour : headResiduesIStarThreeFour.card = 16 := by decide

/-- A pair lies in `headResiduesIStarThreeTwo` exactly when it satisfies `HeadResIStarThreeTwo`. -/
theorem mem_headResiduesIStarThreeTwo_iff {c : ZMod (2 ^ 7) × ZMod (2 ^ 7)} :
    c ∈ headResiduesIStarThreeTwo ↔ HeadResIStarThreeTwo c.1 c.2 := by
  simp [headResiduesIStarThreeTwo, Prod.ext_iff]

/-- A pair lies in `headResiduesIStarThreeFour` exactly when it satisfies
`HeadResIStarThreeFour`. -/
theorem mem_headResiduesIStarThreeFour_iff {c : ZMod (2 ^ 7) × ZMod (2 ^ 7)} :
    c ∈ headResiduesIStarThreeFour ↔ HeadResIStarThreeFour c.1 c.2 := by
  simp [headResiduesIStarThreeFour, Prod.ext_iff]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- **The `(I₃*, 2)` classes, split by the `16`-bit of `a₄` and the `32`-bit of `a₆`, with the
Tamagawa bit refuted.** -/
theorem headResIStarThreeTwo_cases : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeTwo a e →
    ((ZMod.cast (a - 4) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast e : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e - 8 ≠ 0) ∨
      ((ZMod.cast (a - 20) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast e : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e + 24 ≠ 0) ∨
      ((ZMod.cast (a - 4) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast (e - 32) : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e - 40 ≠ 0) ∨
      ((ZMod.cast (a - 20) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast (e - 32) : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e - 8 ≠ 0) := by
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- **The `(I₃*, 4)` classes, split the same way, with the Tamagawa bit met.** -/
theorem headResIStarThreeFour_cases : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeFour a e →
    ((ZMod.cast (a - 4) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast e : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e - 8 = 0) ∨
      ((ZMod.cast (a - 20) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast e : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e + 24 = 0) ∨
      ((ZMod.cast (a - 4) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast (e - 32) : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e - 40 = 0) ∨
      ((ZMod.cast (a - 20) : ZMod (2 ^ 5)) = 0 ∧ (ZMod.cast (e - 32) : ZMod (2 ^ 6)) = 0
        ∧ 2 * a + e - 8 = 0) := by
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- On the `(I₃*, 2)` classes, `a₄` is nonzero modulo `16`. -/
theorem headResIStarThreeTwo_notDvd : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- On the `(I₃*, 4)` classes, `a₄` is nonzero modulo `16`. -/
theorem headResIStarThreeFour_notDvd : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

/-! ### The two `I₃*` loci and their masses -/

/-- The `(I₃*, 2)` locus at `2`: sixteen residue classes modulo `128`. -/
noncomputable def iStarThreeTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 7 ⁻¹' (headResiduesIStarThreeTwo : Set (ZMod (2 ^ 7) × ZMod (2 ^ 7)))

/-- The `(I₃*, 4)` locus at `2`: the complementary sixteen residue classes modulo `128`. -/
noncomputable def iStarThreeFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 7 ⁻¹' (headResiduesIStarThreeFour : Set (ZMod (2 ^ 7) × ZMod (2 ^ 7)))

/-- Membership of `iStarThreeTwoLocus` is the condition `HeadResIStarThreeTwo` on the residues
of `(a₄, a₆)` modulo `128`. -/
theorem mem_iStarThreeTwoLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarThreeTwoLocus ↔
      HeadResIStarThreeTwo (PadicInt.toZModPow 7 x.1) (PadicInt.toZModPow 7 x.2) := by
  rw [iStarThreeTwoLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarThreeTwo_iff,
    PadicInt.redPairPow]

/-- Membership of `iStarThreeFourLocus` is the condition `HeadResIStarThreeFour` on the residues
of `(a₄, a₆)` modulo `128`. -/
theorem mem_iStarThreeFourLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarThreeFourLocus ↔
      HeadResIStarThreeFour (PadicInt.toZModPow 7 x.1) (PadicInt.toZModPow 7 x.2) := by
  rw [iStarThreeFourLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarThreeFour_iff,
    PadicInt.redPairPow]

/-- The `(I₃*, 2)` locus is measurable. -/
theorem measurableSet_iStarThreeTwoLocus : MeasurableSet iStarThreeTwoLocus :=
  PadicInt.measurableSet_preimage_redPairPow 7 headResiduesIStarThreeTwo

/-- The `(I₃*, 4)` locus is measurable. -/
theorem measurableSet_iStarThreeFourLocus : MeasurableSet iStarThreeFourLocus :=
  PadicInt.measurableSet_preimage_redPairPow 7 headResiduesIStarThreeFour

/-- The `(I₃*, 2)` locus has mass `1/1024`. -/
theorem volume_iStarThreeTwoLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarThreeTwoLocus = 1 / 1024 := by
  rw [iStarThreeTwoLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarThreeTwo,
    show ((16 : ℕ) : ℝ≥0∞) = 16 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 7) = 16384 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The `(I₃*, 4)` locus has mass `1/1024`. -/
theorem volume_iStarThreeFourLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarThreeFourLocus = 1 / 1024 := by
  rw [iStarThreeFourLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarThreeFour,
    show ((16 : ℕ) : ℝ≥0∞) = 16 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 7) = 16384 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### The `I₃*` loci sit inside the minimal part of the rows `t = 2` and `t = 4` -/

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- Every curve in the `(I₃*, 2)` locus has Kodaira type `I₃*` and Tamagawa number `2` at `2`. -/
theorem iStarThreeTwoLocus_subset_iUnion_stratFibre :
    iStarThreeTwoLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  rcases headResIStarThreeTwo_cases _ _ (mem_iStarThreeTwoLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 0) (ε := 0) (c₄ := 4) (c₆ := 0) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [sub_zero]))
    have hsum' : 2 * x.1 + x.2 - 8 = 64 * (A + 0 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 2 * A) (B := 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + 0 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_sub, map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 1) (ε := 0) (c₄ := 20) (c₆ := 0) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [sub_zero]))
    have hsum' : 2 * x.1 + x.2 + 24 = 64 * (A + 1 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 1 + 2 * A) (B := 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + 1 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 0) (ε := 1) (c₄ := 4) (c₆ := 32) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
    have hsum' : 2 * x.1 + x.2 - 40 = 64 * (A + 0 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 2 * A) (B := 1 + 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + 0 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_sub, map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 1) (ε := 1) (c₄ := 20) (c₆ := 32) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
    have hsum' : 2 * x.1 + x.2 - 8 = 64 * (A + 1 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 1 + 2 * A) (B := 1 + 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + 1 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_sub, map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- Every curve in the `(I₃*, 4)` locus has Kodaira type `I₃*` and Tamagawa number `4` at `2`. -/
theorem iStarThreeFourLocus_subset_iUnion_stratFibre :
    iStarThreeFourLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4) := by
  intro x hx
  rcases headResIStarThreeFour_cases _ _ (mem_iStarThreeFourLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 0) (ε := 0) (c₄ := 4) (c₆ := 0) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [sub_zero]))
    have hsum' : 2 * x.1 + x.2 - 8 = 64 * (A + 0 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 2 * A) (B := 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ A + 0 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_sub, map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_left hd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 1) (ε := 0) (c₄ := 20) (c₆ := 0) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [sub_zero]))
    have hsum' : 2 * x.1 + x.2 + 24 = 64 * (A + 1 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 1 + 2 * A) (B := 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ A + 1 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_left hd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 0) (ε := 1) (c₄ := 4) (c₆ := 32) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
    have hsum' : 2 * x.1 + x.2 - 40 = 64 * (A + 0 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 2 * A) (B := 1 + 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ A + 0 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_sub, map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_left hd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_istar_three (a₄ := x.1) (a₆ := x.2)
      (α := 1) (ε := 1) (c₄ := 20) (c₆ := 32) (by norm_num) (by norm_num)
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
      (pow_dvd_of_cast_toZModPow_eq_zero (n := 7) (by norm_num) (by rwa [map_sub, map_ofNat]))
    have hsum' : 2 * x.1 + x.2 - 8 = 64 * (A + 1 + E) := by linear_combination hsum
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_istar_three_at_two
      (A := 1 + 2 * A) (B := 1 + 2 * E) (by rw [ha₄]; ring) (by rw [ha₆]; ring)
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ A + 1 + E := by
      rw [dvd_iff_toZModPow_seven_two hsum']
      simpa only [map_sub, map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_three_at_two (p := 2) rfl (by norm_num)
      (by norm_num) (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_left hd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 3,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- A point of the `(I₃*, 2)` locus is not of the form `(2⁴ a, 2⁶ b)`. -/
theorem notMem_range_of_mem_iStarThreeTwoLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ iStarThreeTwoLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarThreeTwo_notDvd _ _ (mem_iStarThreeTwoLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 7 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- A point of the `(I₃*, 4)` locus is not of the form `(2⁴ a, 2⁶ b)`. -/
theorem notMem_range_of_mem_iStarThreeFourLocus {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ iStarThreeFourLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarThreeFour_notDvd _ _ (mem_iStarThreeFourLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 7 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `(I₃*, 2)` locus lies in the minimal part of the `t = 2` fibre at `2`. -/
theorem iStarThreeTwoLocus_subset_headMinimal :
    iStarThreeTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarThreeTwoLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarThreeTwoLocus hx⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `(I₃*, 4)` locus lies in the minimal part of the `t = 4` fibre at `2`. -/
theorem iStarThreeFourLocus_subset_headMinimal :
    iStarThreeFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarThreeFourLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarThreeFourLocus hx⟩

/-! ### The `I₂*` and `I₃*` loci are disjoint -/

set_option maxRecDepth 100000 in
/-- On the `(I₂*, 2)` classes, `a₄ ≡ 12 (mod 16)`. -/
theorem headResIStarTwoTwo_fst : ∀ a e : ZMod (2 ^ 6), HeadResIStarTwoTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) = 12 := by decide

set_option maxRecDepth 100000 in
/-- On the `(I₂*, 4)` classes, `a₄ ≡ 12 (mod 16)`. -/
theorem headResIStarTwoFour_fst : ∀ a e : ZMod (2 ^ 6), HeadResIStarTwoFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) = 12 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²`, sixteen thousand pairs, exceeds the default budget
/-- On the `(I₃*, 2)` classes, `a₄ ≡ 4 (mod 16)`. -/
theorem headResIStarThreeTwo_fst : ∀ a e : ZMod (2 ^ 7), HeadResIStarThreeTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) = 4 := by decide

/-- The `I₂*` and `I₃*` loci are separated already by `a₄` modulo `16`: `12` against `4`. -/
theorem disjoint_iStarTwoTwoLocus_iStarThreeTwoLocus :
    Disjoint iStarTwoTwoLocus iStarThreeTwoLocus := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := headResIStarTwoTwo_fst _ _ (mem_iStarTwoTwoLocus_iff.1 hx)
  have h2 := headResIStarThreeTwo_fst _ _ (mem_iStarThreeTwoLocus_iff.1 hx')
  rw [PadicInt.cast_toZModPow 4 6 (by norm_num)] at h1
  rw [PadicInt.cast_toZModPow 4 7 (by norm_num)] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

end WeierstrassCurve
