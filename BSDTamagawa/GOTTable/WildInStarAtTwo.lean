/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.HeadDensityInStarSource
public import BSDTamagawa.GOTTable.WildRowLowerBound

/-!
# The `I₁*` loci at `p = 2`

Two explicit loci in the coefficient plane `(a₄, a₆)` over `ℤ_2` on which Tate's algorithm answers
`(I₁*, 2)` and `(I₁*, 4)`. Each is eight residue classes modulo `32`, of mass `8 · 2⁻¹⁰ = 1/128`,
and lies in the part of its row outside the dilates. Each splits into two halves according to the
parity of the Step-2 lift `r`:

* odd half:  `a₄ ≡ 1 (mod 8)` and `a₆ ≡ a₄ + 1 (mod 16)`, so `a₄ = 1 + 8A`, `a₆ = 2 + 8A + 16E`;
* even half: `a₄ ≡ 4 (mod 8)` and `a₆ ≡ 4 (mod 16)`, so `a₄ = 4 + 8A`, `a₆ = 4 + 16E`.

On the odd half the Tamagawa number is `4` when `A + E` is even and `2` when it is odd; on the even
half the parities are exchanged. Both conditions are congruences modulo `32`, through
`a₄ + a₆ − 3 = 16(A + E)` and `2a₄ + a₆ + 4 = 16(1 + A + E)`.

On both halves Step 6's cubic `X³ + bX² + cX + d` has `{b, c} = {ρ, 1 + ρ}` and `d = 0`. In residue
characteristic `2` its discriminant is `(bc − d)²`, so it has a double root, and `b − c = ±1` rules
out a triple root. Step 7 then enters its subprocedure at level `2`, where the `Y`-quadratic
`Y² + Y − a₆(W₇)/16` has a unit linear coefficient, hence no double root: the algorithm exits with
`I₁*`, and the Tamagawa number is `4` exactly when `a₆(W₇)/16` is even.

## Main definitions

* `WeierstrassCurve.iStarOneTwoLocus`, `WeierstrassCurve.iStarOneFourLocus`: the two loci.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.mod_r_two`: at `p = 2`, `Step7.r` is a lift of the residue
  of `a₄/ϖ²`.
* `WeierstrassCurve.card_roots_toFinset_pos_iff_two`: over the residue field of `ℤ_2`, `Y² + Y − d`
  has a root if and only if `d = 0`.
* `WeierstrassCurve.run_eq_Istar_one_of_step5`: if Steps 1–5 succeed, Step 6's cubic has a double
  but not a triple root, and the level-`2` quadratic has no double root, Tate's algorithm returns
  `I₁*` with Tamagawa number `4` or `2`, at every prime.
* `WeierstrassCurve.step5_run_eq_ok_of_two`: Steps 1–5 succeed whenever the Step-2 translate has
  `4 ∣ a₄`, `4 ∣ a₆` and `2 ∣ t`.
* `WeierstrassCurve.run_eq_Istar_one_two_odd`, `WeierstrassCurve.run_eq_Istar_one_two_even`: the
  forward runs on the two halves.
* `WeierstrassCurve.volume_iStarOneTwoLocus`, `WeierstrassCurve.volume_iStarOneFourLocus`: both
  loci have mass `1/128`.
-/

open CommRing Ideal CharP MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The fifth opaque lift: Step 7's double root, modulo `2` -/

/-- `Step7.r` is a lift of the residue of `a₄ / ϖ ^ 2` at `p = 2`. -/
theorem TateAlgorithm.Step7.mod_r_two (hp2 : p = 2) (V : WeierstrassCurve ℤ_[p]) :
    mod (p : ℤ_[p]) (Step7.r (p : ℤ_[p]) V)
      = mod (p : ℤ_[p]) (div V.a₄ ((p : ℤ_[p]) ^ 2)) := by
  rw [Step7.r, mod_out]
  split_ifs with h2
  · have hc : CharP (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 :=
      (charP_iff_prime_eq_zero (by decide)).mpr h2
    have hpr : PerfectRing (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 2 := PerfectField.toPerfectRing 2
    rw [root_two_eq_self_two hp2, cubic]
  · exact absurd (Step2.residue_two_eq_zero_of_eq_two hp2) h2

/-! ### The exit test at the even prime -/

open scoped Classical in
/-- **A nonzero cubic record has a nonempty root `Finset` exactly when it has a root.** -/
theorem card_roots_toFinset_pos_iff_root_two {K : Type*} [Field K] {P : Cubic K}
    (hP : P.toPoly ≠ 0) :
    0 < P.roots.toFinset.card ↔ ∃ x : K, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [Finset.card_pos]
  refine ⟨fun ⟨x, hx⟩ => ⟨x, (Cubic.mem_roots_iff hP x).1 (Multiset.mem_toFinset.1 hx)⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact ⟨x, Multiset.mem_toFinset.2 ((Cubic.mem_roots_iff hP x).2 hx)⟩

open scoped Classical in
/-- **A monic quadratic `Y² + Y - d` over `𝔽_2` has a root exactly when `d = 0`.** Over the residue
field of `ℤ_2` squaring is the identity, so `x² + x = 0` for every `x` and the polynomial takes the
single value `-d`. -/
theorem card_roots_toFinset_pos_iff_two (hp2 : p = 2) (d : ℤ_[p] ⧸ span {(p : ℤ_[p])}) :
    0 < (⟨0, 1, 1, -d⟩ : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})).roots.toFinset.card ↔ d = 0 := by
  rw [card_roots_toFinset_pos_iff_root_two (Cubic.ne_zero_of_b_ne_zero one_ne_zero)]
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  constructor
  · rintro ⟨x, hx⟩
    have hsq := residue_sq_eq_self_two hp2 x
    linear_combination -hx + hsq + x * h2
  · rintro rfl
    exact ⟨0, by ring⟩

/-! ### The forwarding: an immediate exit of Step 7's subprocedure reaches `run` -/

open scoped Classical in
/-- **Steps 1–5 succeed, Step 6's cubic has a double but not a triple root, and Step 7's
subprocedure exits at once: the answer is `I₁*`**, with Tamagawa number `4` or `2` according as the
level-`2` `Y`-quadratic has a root or not. -/
theorem run_eq_Istar_one_of_step5 {W V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hY : ¬ (quadratic (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2).HasDoubleRoot) :
    (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I! 1 ∧
      (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if 0 < (quadratic (p : ℤ_[p])
            (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2).roots.toFinset.card
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
    Step7.subprocedure_eq_of_not_hasDoubleRoot hϖ hΔc le_rfl hvc ha₂c hY]
  exact ⟨rfl, rfl⟩

/-! ### Steps 1–5 traverse the entry locus -/

/-- **Steps 1–5 succeed on a short model whose Step-2 translate has `4 ∣ a₄`, `4 ∣ a₆` and
`2 ∣ t`.** With `a₁(V) = 0`, `a₂(V) = 3r`, `a₃(V) = 2t`, Step 3 wants `4 ∣ a₆(V)`, Step 4 wants
`8 ∣ b₈(V) = 12r·a₆(V) + 3r·a₃(V)² − a₄(V)²` and Step 5 wants `8 ∣ b₆(V) = a₃(V)² + 4a₆(V)`; under
the three hypotheses every one of those is divisible by `16`. -/
theorem step5_run_eq_ok_of_two (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ r t τ Q₄ Q₆ : ℤ_[p]}
    (hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ)
    (hV : Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
    (ht : t = 2 * τ) (h4 : a₄ + 3 * r ^ 2 = 4 * Q₄)
    (h6 : a₆ + r * a₄ + r ^ 3 - t ^ 2 = 4 * Q₆) :
    Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
    dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inl hp2) a₄ a₆
  have h2run := Step2.run_eq_ok_of_dvd_c₄ hΔd hc₄
  rw [hV] at h2run
  have ha₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have ha₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
  have ha₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 4 * τ := by
    rw [smul_ofShortNF_a₃, ht]; ring
  have ha₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = 4 * Q₄ := by
    rw [smul_ofShortNF_a₄]; linear_combination h4
  have ha₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = 4 * Q₆ := by
    rw [smul_ofShortNF_a₆]; linear_combination h6
  have h3run : Step3.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, by rw [ha₆, hπ]; ring⟩
  have h4run : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * r * Q₆ + 6 * r * τ ^ 2 - 2 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, ha₁, ha₂, ha₃, ha₄, ha₆, hπ]; ring
  rw [Step5.run.eq_def, h4run]
  simp only [except_ok_bind]
  refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
  rw [WeierstrassCurve.b₆, ha₃, ha₆, hπ]; ring

/-! ### Characteristic-two branch tests -/

/-- Two elements of `ℤ_p` with `ϖ`-divisible difference have the same residue. -/
theorem mod_eq_mod_of_dvd_sub_two {x y : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x - y) :
    mod (p : ℤ_[p]) x = mod (p : ℤ_[p]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-- **Step 6's cubic test at `p = 2`.** In residue characteristic two the discriminant of
`X³ + bX² + cX + d` is `(bc − d)²`, so `bc = d` gives a double root. -/
theorem hasDoubleRoot_of_mul_eq_two (hp2 : p = 2) {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (h : P.b * P.c = P.d) : P.HasDoubleRoot := by
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha, ← h]
  linear_combination (-(4 * P.b ^ 2 * P.c ^ 2 + 2 * P.c ^ 3 + 2 * P.b ^ 4 * P.c)) * h2

/-- **Step 7's entry test at `p = 2`, negated.** `HasTripleRoot` is `b² = 3c`, and on `𝔽_2` both
`y² = y` and `3 = 1`, so it says `b = c`; a cubic whose first two coefficients differ by `1` has no
triple root. -/
theorem not_hasTripleRoot_of_sub_eq_one_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (h : P.b - P.c = 1) : ¬ P.HasTripleRoot := by
  intro hT
  rw [Cubic.HasTripleRoot] at hT
  have hsq := residue_sq_eq_self_two hp2 P.b
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  exact one_ne_zero (α := ℤ_[p] ⧸ span {(p : ℤ_[p])})
    (by linear_combination -h + hsq - hT + (P.b - 2 * P.c) * h2)

/-- **The level-`n` `Y`-quadratic has no double root once its linear coefficient is a unit.**
`HasDoubleRoot` for `⟨0, 1, c, d⟩` is `c² = 4d`, and `4 = 0` on `𝔽_2`, so `c = 1` refutes it. -/
theorem not_hasDoubleRoot_quadratic_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hb : P.b = 1) (hc : P.c = 1) :
    ¬ P.HasDoubleRoot := by
  rw [Cubic.hasDoubleRoot_of_b_eq_one ha hb, hc, residue_four_eq_zero_two hp2, zero_mul]
  exact fun h => one_ne_zero (α := ℤ_[p] ⧸ span {(p : ℤ_[p])}) (by linear_combination h)

/-- In `ZMod 4`, `(Y² − T²)(Y² − T² + 2T − 1) = 0` for all `Y` and `T`. -/
theorem zmod_double_root_two (hp2 : p = 2) :
    ∀ Y T : ZMod (p ^ 2), (Y ^ 2 - T ^ 2) * (Y ^ 2 - T ^ 2 + 2 * T - 1) = 0 := by
  subst hp2; decide

/-- Exact division by the uniformiser. -/
theorem div_eq_of_eq_mul_two {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) * a) : div x (p : ℤ_[p]) = a := by
  subst h
  exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero
    (CommRing.mul_div PadicInt.uniformizer_ne_zero (Dvd.intro a rfl))

/-! ### The forward run on the odd half of the `I₁*` locus -/

open scoped Classical in
/-- **The forward run at `I₁*`, on `a₄ ≡ 1 (mod 8)`, `a₆ ≡ a₄ + 1 (mod 16)`.** For `a₄ = 1 + 8A`
and `a₆ = 2 + 8A + 16E`, Tate's algorithm at `2` returns `I₁*`, with Tamagawa number `4` if `A + E`
is even and `2` otherwise. -/
theorem run_eq_Istar_one_two_odd (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A E : ℤ_[p]}
    (ha₄ : a₄ = 1 + 8 * A) (ha₆ : a₆ = 2 + 8 * A + 16 * E)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 1 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if (p : ℤ_[p]) ∣ A + E then 4 else 2 := by
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
        ⟨c - 4 * A - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩)
    · exact ⟨y, hy⟩
  obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨2 + 8 * A + 8 * E + 4 * m + 2 * ρ + 8 * A * ρ + 8 * m * ρ, by
        rw [hπ, ha₆, ha₄, hr]; linear_combination (4 + 8 * ρ) * hm⟩
    obtain ⟨c, hc⟩ := h2
    obtain ⟨d, hd⟩ := hva₆
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨c - d, by linear_combination hc - hd⟩ : (p : ℤ_[p]) ∣ t ^ 2)
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 1 + 2 * A + 6 * m := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 1 + 4 * A + 4 * E + 2 * m + ρ + 4 * A * ρ + 4 * m * ρ - τ ^ 2 := ⟨_, rfl⟩
  have hA4 : a₄ + 3 * r ^ 2 = 4 * Q₄ := by rw [ha₄, hr, hQ₄]; linear_combination 12 * hm
  have hA6 : a₆ + r * a₄ + r ^ 3 - t ^ 2 = 4 * Q₆ := by
    rw [ha₆, ha₄, hr, ht, hQ₆]; linear_combination (4 + 8 * ρ) * hm
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
  obtain ⟨G, hG⟩ : ∃ x : ℤ_[p], x = A + E + A * ρ + m * ρ := ⟨_, rfl⟩
  have hQ₆G : Q₆ = (1 + ρ) ^ 2 - τ ^ 2 + 4 * G := by rw [hQ₆, hG]; linear_combination -hm
  have hK4 : (p : ℤ_[p]) ^ 2 ∣ Q₆ * (Q₆ + 2 * τ - 1) := by
    rw [pow_dvd_iff_toZModPow_eq_zero]
    have h4G : PadicInt.toZModPow 2 ((4 : ℤ_[p]) * G) = 0 :=
      (pow_dvd_iff_toZModPow_eq_zero 2 _).1 ⟨G, by rw [hπ]; ring⟩
    have hQr : PadicInt.toZModPow 2 Q₆
        = PadicInt.toZModPow 2 (1 + ρ) ^ 2 - PadicInt.toZModPow 2 τ ^ 2 := by
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
    mod_eq_mod_of_dvd_sub_two ⟨mτ - j - σ + 2 * m - τ - ρ - 2 * E - A + 2 * σ * mτ - 2 * σ * j
      - 2 * m * σ - 2 * τ * σ - ρ * σ - 2 * ρ * m - 4 * E * σ - 4 * A * σ - 2 * A * ρ
      - 4 * ρ * m * σ - 4 * A * ρ * σ, by
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
    exact ⟨m, by rw [hπ]; linear_combination hm⟩
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
  obtain ⟨ν₇, hν₇⟩ : ∃ x : ℤ_[p], x = ρ + k₇ := ⟨_, rfl⟩
  have hR₇v : R₇ = 1 + 4 * ν₇ := by rw [hR₇, hπ, hk₇, hr, hν₇]; ring
  obtain ⟨τ₇, hτ₇⟩ : ∃ x : ℤ_[p], x = r₇ * s + t₆ + τ := ⟨_, rfl⟩
  have hT₇v : T₇ = 2 * τ₇ := by rw [hT₇, hτ₇, hT₂, hπ, ht]; ring
  obtain ⟨ν, hν⟩ : ∃ x : ℤ_[p], τ₇ = 1 + 2 * x :=
    ⟨-mτ + k₇ + j + m + τ + ρ + 2 * E + 2 * A + 2 * σ * k₇ + ρ * σ + 2 * ρ * m + 2 * A * ρ, by
      rw [hτ₇, hk₇, hσ, hj, hQ₆]; linear_combination -hmτ⟩
  obtain ⟨mν, hmν⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν
  obtain ⟨m₇, hm₇⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν₇
  obtain ⟨N, hN⟩ : ∃ x : ℤ_[p],
      x = A + E + ν₇ + 2 * A * ν₇ + 3 * ν₇ ^ 2 + 4 * ν₇ ^ 3 - ν - ν ^ 2 := ⟨_, rfl⟩
  have hpow2 : ((p : ℤ_[p])) ^ 2 = 4 := by rw [hπ]; norm_num
  have hpow4 : ((p : ℤ_[p])) ^ (2 * 2) = 16 := by rw [hπ]; norm_num
  have hW₇a₃ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * τ₇ := by rw [smul_ofShortNF_a₃, hT₇v, hpow2]; ring
  have hW₇a₆ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2) * N := by
    rw [smul_ofShortNF_a₆, hR₇v, hT₇v, hν, ha₄, ha₆, hN, hpow4]; ring
  have hτ₇res : mod (p : ℤ_[p]) τ₇ = 1 := by
    rw [hν, mod_eq_mod_of_dvd_sub_two (x := 1 + 2 * ν) (y := 1) ⟨ν, by rw [hπ]; ring⟩, map_one]
  have hNres : mod (p : ℤ_[p]) N = mod (p : ℤ_[p]) (A + E) :=
    mod_eq_mod_of_dvd_sub_two ⟨-m₇ - mν + ν₇ + 4 * ν₇ * m₇ + A * ν₇, by
      rw [hN, hπ]; linear_combination (-1 + 4 * ν₇) * hm₇ - hmν⟩
  have hquad : quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
      = ⟨0, 1, 1, -(mod (p : ℤ_[p]) N)⟩ := by
    rw [quadratic, div_eq_of_eq_pow_mul_two hW₇a₃, div_eq_of_eq_pow_mul_two hW₇a₆, hτ₇res]
  have hY : ¬ (quadratic (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)))
      2).HasDoubleRoot := by
    rw [hW₆, hW₇, hquad]
    exact not_hasDoubleRoot_quadratic_two hp2 rfl rfl rfl
  have hmain := run_eq_Istar_one_of_step5 hΔ h5run (hW₆ ▸ hdbl) (hW₆ ▸ hntr) hY
  refine ⟨hmain.1, ?_⟩
  rw [hmain.2, hW₆, hW₇, hquad]
  refine if_congr ?_ rfl rfl
  rw [card_roots_toFinset_pos_iff_two hp2, hNres, mod_eq_zero]

/-! ### The forward run on the even half of the `I₁*` locus -/

open scoped Classical in
/-- **The forward run at `I₁*`, on `a₄ ≡ 4 (mod 8)`, `a₆ ≡ 4 (mod 16)`.** For `a₄ = 4 + 8A` and
`a₆ = 4 + 16E`, Tate's algorithm at `2` returns `I₁*`, with Tamagawa number `4` if `1 + A + E` is
even and `2` otherwise. -/
theorem run_eq_Istar_one_two_even (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A E : ℤ_[p]}
    (ha₄ : a₄ = 4 + 8 * A) (ha₆ : a₆ = 4 + 16 * E)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 1 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if (p : ℤ_[p]) ∣ 1 + A + E then 4 else 2 := by
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
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exact ⟨y, hy⟩
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hy, hπ, ha₄] at hc
      exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one
        ⟨c - 3 - 4 * A - 6 * y - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩)
  obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨2 + 8 * E + 4 * ρ + 8 * A * ρ + 4 * ρ ^ 3, by rw [hπ, ha₆, ha₄, hr]; ring⟩
    obtain ⟨c, hc⟩ := h2
    obtain ⟨d, hd⟩ := hva₆
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨c - d, by linear_combination hc - hd⟩ : (p : ℤ_[p]) ∣ t ^ 2)
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 1 + 2 * A + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 1 + 4 * E + 2 * ρ + 4 * A * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
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
  obtain ⟨G, hG⟩ : ∃ x : ℤ_[p], x = E + ρ - m + ρ * m + A * ρ := ⟨_, rfl⟩
  have hQ₆G : Q₆ = 1 ^ 2 - τ ^ 2 + 4 * G := by
    rw [hQ₆, hG]; linear_combination (-2 + 2 * ρ) * hm
  have hK4 : (p : ℤ_[p]) ^ 2 ∣ Q₆ * (Q₆ + 2 * τ - 1) := by
    rw [pow_dvd_iff_toZModPow_eq_zero]
    have h4G : PadicInt.toZModPow 2 ((4 : ℤ_[p]) * G) = 0 :=
      (pow_dvd_iff_toZModPow_eq_zero 2 _).1 ⟨G, by rw [hπ]; ring⟩
    have hQr : PadicInt.toZModPow 2 Q₆
        = PadicInt.toZModPow 2 1 ^ 2 - PadicInt.toZModPow 2 τ ^ 2 := by
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
    mod_eq_mod_of_dvd_sub_two ⟨-σ + 3 * m - 2 * ρ + A + 2 * σ * mτ - 2 * σ * j + 4 * m * σ
      - 2 * τ * σ - 4 * ρ * σ - 4 * E * σ - 4 * ρ * m * σ - 4 * A * ρ * σ, by
      rw [hX₄, hQ₄, hj, hQ₆, hσ, hπ]
      linear_combination (3 + 4 * σ - 4 * ρ * σ) * hm + 2 * σ * hmτ⟩
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
  obtain ⟨ν₇, hν₇⟩ : ∃ x : ℤ_[p], x = ρ + k₇ := ⟨_, rfl⟩
  have hR₇v : R₇ = 2 + 4 * ν₇ := by rw [hR₇, hπ, hk₇, hr, hν₇]; ring
  obtain ⟨τ₇, hτ₇⟩ : ∃ x : ℤ_[p], x = 2 * r₇ * σ + t₆ + τ := ⟨_, rfl⟩
  have hT₇v : T₇ = 2 * τ₇ := by rw [hT₇, hτ₇, hT₂, hπ, ht, hσ]; ring
  obtain ⟨ν, hν⟩ : ∃ x : ℤ_[p], τ₇ = 1 + 2 * x :=
    ⟨-mτ + j + σ - 2 * m + τ + 2 * ρ + 2 * E + 2 * σ * k₇ + ρ * σ + 2 * ρ * m + 2 * A * ρ, by
      rw [hτ₇, hk₇, hj, hQ₆]; linear_combination (-2 + 2 * ρ) * hm - hmτ⟩
  obtain ⟨mν, hmν⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ν
  obtain ⟨N, hN⟩ : ∃ x : ℤ_[p],
      x = 1 + A + E + 4 * ν₇ + 2 * A * ν₇ + 6 * ν₇ ^ 2 + 4 * ν₇ ^ 3 - ν - ν ^ 2 := ⟨_, rfl⟩
  have hpow2 : ((p : ℤ_[p])) ^ 2 = 4 := by rw [hπ]; norm_num
  have hpow4 : ((p : ℤ_[p])) ^ (2 * 2) = 16 := by rw [hπ]; norm_num
  have hW₇a₃ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * τ₇ := by rw [smul_ofShortNF_a₃, hT₇v, hpow2]; ring
  have hW₇a₆ : ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ (2 * 2) * N := by
    rw [smul_ofShortNF_a₆, hR₇v, hT₇v, hν, ha₄, ha₆, hN, hpow4]; ring
  have hτ₇res : mod (p : ℤ_[p]) τ₇ = 1 := by
    rw [hν, mod_eq_mod_of_dvd_sub_two (x := 1 + 2 * ν) (y := 1) ⟨ν, by rw [hπ]; ring⟩, map_one]
  have hNres : mod (p : ℤ_[p]) N = mod (p : ℤ_[p]) (1 + A + E) :=
    mod_eq_mod_of_dvd_sub_two ⟨-mν + 2 * ν₇ + 3 * ν₇ ^ 2 + A * ν₇ + 2 * ν₇ ^ 3, by
      rw [hN, hπ]; linear_combination -hmν⟩
  have hquad : quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆) 2
      = ⟨0, 1, 1, -(mod (p : ℤ_[p]) N)⟩ := by
    rw [quadratic, div_eq_of_eq_pow_mul_two hW₇a₃, div_eq_of_eq_pow_mul_two hW₇a₆, hτ₇res]
  have hY : ¬ (quadratic (p : ℤ_[p]) (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)))
      2).HasDoubleRoot := by
    rw [hW₆, hW₇, hquad]
    exact not_hasDoubleRoot_quadratic_two hp2 rfl rfl rfl
  have hmain := run_eq_Istar_one_of_step5 hΔ h5run (hW₆ ▸ hdbl) (hW₆ ▸ hntr) hY
  refine ⟨hmain.1, ?_⟩
  rw [hmain.2, hW₆, hW₇, hquad]
  refine if_congr ?_ rfl rfl
  rw [card_roots_toFinset_pos_iff_two hp2, hNres, mod_eq_zero]

/-! ### Nonsingularity on the locus -/

/-- On the odd half of the locus the model is nonsingular: with `a₄ = 1 + 8A` and `a₆ = 2b`,
`b = 1 + 4A + 8E`, the quantity `a₄³ + 27b²` is `≡ 4 (mod 8)`, hence nonzero. -/
theorem zmod_nonsingular_odd_two : ∀ Y X Z : ZMod (2 ^ 3),
    (1 + 8 * Y) ^ 3 + 27 * (1 + 4 * X + 8 * Z) ^ 2 ≠ 0 := by decide

/-- On the even half of the locus the model is nonsingular: `4a₄³ + 27a₆² = 16(16(1+2A)³ +
27(1+4E)²)` and the inner factor is odd. -/
theorem zmod_nonsingular_even_two : ∀ X Z : ZMod (2 ^ 1),
    16 * (1 + 2 * X) ^ 3 + 27 * (1 + 4 * Z) ^ 2 ≠ 0 := by decide

/-- `Δ ≠ 0` from `4a₄³ + 27a₆² ≠ 0`. -/
theorem ofShortNF_Δ_ne_zero_of_two {a₄ a₆ : ℤ_[2]} (h : 4 * a₄ ^ 3 + 27 * a₆ ^ 2 ≠ 0) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  rw [ofShortNF_Δ]
  exact mul_ne_zero neg_sixteen_ne_zero_two h

/-- **Nonsingularity on the odd half.** -/
theorem Δ_ne_zero_odd_two {a₄ a₆ A E : ℤ_[2]} (ha₄ : a₄ = 1 + 8 * A)
    (ha₆ : a₆ = 2 + 8 * A + 16 * E) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  refine ofShortNF_Δ_ne_zero_of_two fun h => ?_
  have hcb : a₄ ^ 3 + 27 * (1 + 4 * A + 8 * E) ^ 2 = 0 := by
    have h4 : (4 : ℤ_[2]) ≠ 0 := by
      rw [show (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 from by norm_num]
      exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero
    refine mul_left_cancel₀ h4 ?_
    rw [mul_zero, ha₆] at *
    linear_combination h
  have himg : PadicInt.toZModPow 3 (a₄ ^ 3 + 27 * (1 + 4 * A + 8 * E) ^ 2) = 0 := by
    rw [hcb, map_zero]
  rw [ha₄] at himg
  simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at himg
  exact zmod_nonsingular_odd_two _ _ _ himg

/-- **Nonsingularity on the even half.** -/
theorem Δ_ne_zero_even_two {a₄ a₆ A E : ℤ_[2]} (ha₄ : a₄ = 4 + 8 * A)
    (ha₆ : a₆ = 4 + 16 * E) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  refine ofShortNF_Δ_ne_zero_of_two fun h => ?_
  have h16 : (16 : ℤ_[2]) ≠ 0 := by
    rw [show (16 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 4 from by norm_num]
    exact pow_ne_zero 4 PadicInt.uniformizer_ne_zero
  have hcb : 16 * (1 + 2 * A) ^ 3 + 27 * (1 + 4 * E) ^ 2 = 0 := by
    refine mul_left_cancel₀ h16 ?_
    rw [mul_zero, ha₄, ha₆] at *
    linear_combination h
  have himg : PadicInt.toZModPow 1 (16 * (1 + 2 * A) ^ 3 + 27 * (1 + 4 * E) ^ 2) = 0 := by
    rw [hcb, map_zero]
  simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at himg
  exact zmod_nonsingular_even_two _ _ himg

/-! ### From a residue class modulo `32` to the parameters -/

/-- **The odd half, parametrised.** `a₄ ≡ 1 (mod 8)` and `a₆ ≡ a₄ + 1 (mod 16)` give
`a₄ = 1 + 8A` and `a₆ = 2 + 8A + 16E`, and then `a₄ + a₆ − 3 = 16(A + E)`. -/
theorem exists_params_odd_two {a₄ a₆ : ℤ_[2]}
    (h1 : (ZMod.cast (PadicInt.toZModPow 5 a₄ - 1) : ZMod (2 ^ 3)) = 0)
    (h2 : (ZMod.cast (PadicInt.toZModPow 5 a₆ - PadicInt.toZModPow 5 a₄ - 1)
      : ZMod (2 ^ 4)) = 0) :
    ∃ A E : ℤ_[2], a₄ = 1 + 8 * A ∧ a₆ = 2 + 8 * A + 16 * E ∧ a₄ + a₆ - 3 = 16 * (A + E) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ a₄ - 1 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) ?_
    rwa [map_sub, map_one]
  obtain ⟨E, hE⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ a₆ - a₄ - 1 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) ?_
    rwa [map_sub, map_sub, map_one]
  rw [hcast] at hA hE
  exact ⟨A, E, by linear_combination hA, by linear_combination hE + hA,
    by linear_combination hE + 2 * hA⟩

/-- **The even half, parametrised.** `a₄ ≡ 4 (mod 8)` and `a₆ ≡ 4 (mod 16)` give `a₄ = 4 + 8A` and
`a₆ = 4 + 16E`, and then `2a₄ + a₆ + 4 = 16(1 + A + E)`. -/
theorem exists_params_even_two {a₄ a₆ : ℤ_[2]}
    (h1 : (ZMod.cast (PadicInt.toZModPow 5 a₄ - 4) : ZMod (2 ^ 3)) = 0)
    (h2 : (ZMod.cast (PadicInt.toZModPow 5 a₆ - 4) : ZMod (2 ^ 4)) = 0) :
    ∃ A E : ℤ_[2], a₄ = 4 + 8 * A ∧ a₆ = 4 + 16 * E ∧
      2 * a₄ + a₆ + 4 = 16 * (1 + A + E) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ a₄ - 4 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) ?_
    rwa [map_sub, map_ofNat]
  obtain ⟨E, hE⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ a₆ - 4 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) ?_
    rwa [map_sub, map_ofNat]
  rw [hcast] at hA hE
  exact ⟨A, E, by linear_combination hA, by linear_combination hE,
    by linear_combination hE + 2 * hA⟩

/-- For `x = 16y` in `ℤ_2`, `2 ∣ y` exactly when `x` vanishes modulo `2⁵`. -/
theorem dvd_iff_toZModPow_five_two {y x : ℤ_[2]} (h : x = 16 * y) :
    ((2 : ℕ) : ℤ_[2]) ∣ y ↔ PadicInt.toZModPow 5 x = 0 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have h16 : (16 : ℤ_[2]) ≠ 0 := by
    rw [show (16 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 4 from by norm_num]
    exact pow_ne_zero 4 PadicInt.uniformizer_ne_zero
  rw [← pow_dvd_iff_toZModPow_eq_zero, hcast]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [h]; ring⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, mul_left_cancel₀ h16 (by rw [← h, hw]; ring)⟩

/-! ### The two residue sets modulo `32` -/

/-- **The residue condition cutting out the `(I₁*, 2)` locus at `2`**: eight classes modulo `32`,
four on `a₄ ≡ 1 (mod 8)` and four on `a₄ ≡ 4 (mod 8)`. -/
abbrev HeadResIStarOneTwo (a e : ZMod (2 ^ 5)) : Prop :=
  (a = 1 ∧ e = 18) ∨ (a = 9 ∧ e = 10) ∨ (a = 17 ∧ e = 2) ∨ (a = 25 ∧ e = 26) ∨
    (a = 4 ∧ e = 4) ∨ (a = 12 ∧ e = 20) ∨ (a = 20 ∧ e = 4) ∨ (a = 28 ∧ e = 20)

/-- **The residue condition cutting out the `(I₁*, 4)` locus at `2`**: the complementary eight
classes modulo `32`, obtained from `HeadResIStarOneTwo` by flipping the `16`-bit of `a₆`. -/
abbrev HeadResIStarOneFour (a e : ZMod (2 ^ 5)) : Prop :=
  (a = 1 ∧ e = 2) ∨ (a = 9 ∧ e = 26) ∨ (a = 17 ∧ e = 18) ∨ (a = 25 ∧ e = 10) ∨
    (a = 4 ∧ e = 20) ∨ (a = 12 ∧ e = 4) ∨ (a = 20 ∧ e = 20) ∨ (a = 28 ∧ e = 4)

/-- The eight residue pairs of `HeadResIStarOneTwo`, as a `Finset`. -/
def headResiduesIStarOneTwo : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(1, 18), (9, 10), (17, 2), (25, 26), (4, 4), (12, 20), (20, 4), (28, 20)}

/-- The eight residue pairs of `HeadResIStarOneFour`, as a `Finset`. -/
def headResiduesIStarOneFour : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(1, 2), (9, 26), (17, 18), (25, 10), (4, 20), (12, 4), (20, 20), (28, 4)}

/-- The `(I₁*, 2)` residue set has eight elements. -/
theorem card_headResiduesIStarOneTwo : headResiduesIStarOneTwo.card = 8 := by decide

/-- The `(I₁*, 4)` residue set has eight elements. -/
theorem card_headResiduesIStarOneFour : headResiduesIStarOneFour.card = 8 := by decide

/-- A pair lies in `headResiduesIStarOneTwo` exactly when it satisfies `HeadResIStarOneTwo`. -/
theorem mem_headResiduesIStarOneTwo_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ headResiduesIStarOneTwo ↔ HeadResIStarOneTwo c.1 c.2 := by
  simp [headResiduesIStarOneTwo, Prod.ext_iff]

/-- A pair lies in `headResiduesIStarOneFour` exactly when it satisfies `HeadResIStarOneFour`. -/
theorem mem_headResiduesIStarOneFour_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ headResiduesIStarOneFour ↔ HeadResIStarOneFour c.1 c.2 := by
  simp [headResiduesIStarOneFour, Prod.ext_iff]

/-- **The case split of the `(I₁*, 2)` residue set**, by exhaustion over `(ZMod 32)²`: each class
either has `a₄ ≡ 1 (mod 8)`, `a₆ ≡ a₄ + 1 (mod 16)` and `a₄ + a₆ ≢ 3 (mod 32)`, or has
`a₄ ≡ 4 (mod 8)`, `a₆ ≡ 4 (mod 16)` and `2a₄ + a₆ + 4 ≢ 0 (mod 32)`. -/
theorem headResIStarOneTwo_cases : ∀ a e : ZMod (2 ^ 5), HeadResIStarOneTwo a e →
    ((ZMod.cast (a - 1) : ZMod (2 ^ 3)) = 0 ∧ (ZMod.cast (e - a - 1) : ZMod (2 ^ 4)) = 0
        ∧ a + e - 3 ≠ 0) ∨
      ((ZMod.cast (a - 4) : ZMod (2 ^ 3)) = 0 ∧ (ZMod.cast (e - 4) : ZMod (2 ^ 4)) = 0
        ∧ 2 * a + e + 4 ≠ 0) := by decide

/-- **The case split of the `(I₁*, 4)` residue set**: the same two congruences with the opposite
Tamagawa bit. -/
theorem headResIStarOneFour_cases : ∀ a e : ZMod (2 ^ 5), HeadResIStarOneFour a e →
    ((ZMod.cast (a - 1) : ZMod (2 ^ 3)) = 0 ∧ (ZMod.cast (e - a - 1) : ZMod (2 ^ 4)) = 0
        ∧ a + e - 3 = 0) ∨
      ((ZMod.cast (a - 4) : ZMod (2 ^ 3)) = 0 ∧ (ZMod.cast (e - 4) : ZMod (2 ^ 4)) = 0
        ∧ 2 * a + e + 4 = 0) := by decide

/-- On the `(I₁*, 2)` residue set `a₄` is not divisible by `16`. -/
theorem headResIStarOneTwo_notDvd : ∀ a e : ZMod (2 ^ 5), HeadResIStarOneTwo a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

/-- On the `(I₁*, 4)` residue set `a₄` is not divisible by `16`. -/
theorem headResIStarOneFour_notDvd : ∀ a e : ZMod (2 ^ 5), HeadResIStarOneFour a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

/-! ### The two loci, their masses and their minimality -/

/-- The **`(I₁*, 2)` locus** of the coefficient plane at `2`: eight residue classes modulo `32`. -/
noncomputable def iStarOneTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (headResiduesIStarOneTwo : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- The **`(I₁*, 4)` locus** of the coefficient plane at `2`: eight residue classes modulo `32`. -/
noncomputable def iStarOneFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (headResiduesIStarOneFour : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- A point lies in the `(I₁*, 2)` locus exactly when its residues modulo `32` satisfy
`HeadResIStarOneTwo`. -/
theorem mem_iStarOneTwoLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarOneTwoLocus ↔
      HeadResIStarOneTwo (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [iStarOneTwoLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarOneTwo_iff,
    PadicInt.redPairPow]

/-- A point lies in the `(I₁*, 4)` locus exactly when its residues modulo `32` satisfy
`HeadResIStarOneFour`. -/
theorem mem_iStarOneFourLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iStarOneFourLocus ↔
      HeadResIStarOneFour (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [iStarOneFourLocus, mem_preimage, Finset.mem_coe, mem_headResiduesIStarOneFour_iff,
    PadicInt.redPairPow]

/-- **The mass of the `(I₁*, 2)` locus is `8/1024 = 1/128`.** -/
theorem volume_iStarOneTwoLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarOneTwoLocus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 10 := by
  rw [iStarOneTwoLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarOneTwo]
  norm_num

/-- **The mass of the `(I₁*, 4)` locus is `8/1024 = 1/128`.** -/
theorem volume_iStarOneFourLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iStarOneFourLocus = 8 * ((2 : ℝ≥0∞)⁻¹) ^ 10 := by
  rw [iStarOneFourLocus, PadicInt.volume_preimage_redPairPow, card_headResiduesIStarOneFour]
  norm_num

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₁*, 2)` locus lies in the strata over `t = 2`.** -/
theorem iStarOneTwoLocus_subset_iUnion_stratFibre :
    iStarOneTwoLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  rcases headResIStarOneTwo_cases _ _ (mem_iStarOneTwoLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_odd_two h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_odd_two ha₄ ha₆
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ A + E := by
      rw [dvd_iff_toZModPow_five_two hsum]
      simpa only [map_sub, map_add, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_one_two_odd rfl (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 1,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_even_two h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_even_two ha₄ ha₆
    have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ 1 + A + E := by
      rw [dvd_iff_toZModPow_five_two hsum]
      simpa only [map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_one_two_even rfl (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_right hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 1,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₁*, 4)` locus lies in the strata over `t = 4`.** -/
theorem iStarOneFourLocus_subset_iUnion_stratFibre :
    iStarOneFourLocus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4) := by
  intro x hx
  rcases headResIStarOneFour_cases _ _ (mem_iStarOneFourLocus_iff.1 hx) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_odd_two h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_odd_two ha₄ ha₆
    have hnd : ((2 : ℕ) : ℤ_[2]) ∣ A + E := by
      rw [dvd_iff_toZModPow_five_two hsum]
      simpa only [map_sub, map_add, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_one_two_odd rfl (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_left hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 1,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩
  · obtain ⟨A, E, ha₄, ha₆, hsum⟩ := exists_params_even_two h1 h2
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_even_two ha₄ ha₆
    have hnd : ((2 : ℕ) : ℤ_[2]) ∣ 1 + A + E := by
      rw [dvd_iff_toZModPow_five_two hsum]
      simpa only [map_add, map_mul, map_ofNat] using h3
    obtain ⟨hk, ht⟩ := run_eq_Istar_one_two_even rfl (by norm_num) ha₄ ha₆ hΔ
    rw [ite_eq_left hnd] at ht
    exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 1,
      (mem_stratFibre_iff hΔ).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **No point of the `(I₁*, 2)` locus is a `(2⁴, 2⁶)`-dilate**: on it `16 ∤ a₄`. -/
theorem notMem_range_of_mem_iStarOneTwoLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarOneTwoLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarOneTwo_notDvd _ _ (mem_iStarOneTwoLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- **No point of the `(I₁*, 4)` locus is a `(2⁴, 2⁶)`-dilate**: on it `16 ∤ a₄`. -/
theorem notMem_range_of_mem_iStarOneFourLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ iStarOneFourLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine headResIStarOneFour_notDvd _ _ (mem_iStarOneFourLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

/-- The `(I₁*, 2)` locus lies in the minimal part of the `t = 2` row. -/
theorem iStarOneTwoLocus_subset_headMinimal :
    iStarOneTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarOneTwoLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarOneTwoLocus hx⟩

/-- The `(I₁*, 4)` locus lies in the minimal part of the `t = 4` row. -/
theorem iStarOneFourLocus_subset_headMinimal :
    iStarOneFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx =>
    ⟨iStarOneFourLocus_subset_iUnion_stratFibre hx, notMem_range_of_mem_iStarOneFourLocus hx⟩

end WeierstrassCurve

end
