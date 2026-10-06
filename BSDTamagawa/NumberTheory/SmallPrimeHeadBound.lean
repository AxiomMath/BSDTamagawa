/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateTailLaw

/-!
# Head-sum lower bounds at the small primes `2` and `3`

For every prime `p`, the head sums satisfy `A_{p,2} ≥ 1/(2p²)` and `A_{p,3} ≥ 1/(3p³)`. For `p ≥ 5`
these are `WeierstrassCurve.inv_two_mul_sq_le_headSum_two` and
`WeierstrassCurve.inv_three_mul_cube_le_headSum_three`; this file proves the cases `p ∈ {2, 3}` by
exhibiting explicit loci of the short coefficient plane on which Tate's algorithm returns a
reduction datum of Tamagawa number exactly `2` (type `III`) or exactly `3` (split type `IV`), and
computing their Haar masses: `1/8` and `2/27` for type `III` at `2` and `3`, and `1/16` and `1/81`
for split type `IV` at `2` and `3`.

## Main definitions

* `WeierstrassCurve.iii2Locus`, `WeierstrassCurve.iii3Locus`: the type-`III` loci at `2` and `3`.
* `WeierstrassCurve.iv2Locus`, `WeierstrassCurve.iv3Locus`: the split type-`IV` loci at `2` and
  `3`.

## Main results

* `WeierstrassCurve.run_eq_III_two`: a short model over `ℤ_2` with `a₄ ≡ 2` or `3 (mod 4)` and
  `a₆ ≡ 0 (mod 4)` has reduction datum exactly `(III, 2)`.
* `WeierstrassCurve.run_eq_III_three`, `WeierstrassCurve.run_eq_IV_two`,
  `WeierstrassCurve.run_eq_IV_three`: the analogous forward runs of Tate's algorithm.
* `WeierstrassCurve.volume_iii2Locus`, `WeierstrassCurve.volume_iii3Locus`,
  `WeierstrassCurve.volume_iv2Locus`, `WeierstrassCurve.volume_iv3Locus`: the masses of the loci.
* `WeierstrassCurve.inv_two_mul_sq_le_headSum_two_of_prime`: `A_{p,2} ≥ 1/(2p²)` for every prime
  `p`.
* `WeierstrassCurve.inv_three_mul_cube_le_headSum_three_of_prime`: `A_{p,3} ≥ 1/(3p³)` for every
  prime `p`.

## Implementation notes

On the short plane `y² = x³ + a₄x + a₆` the invariant `c₄ = -48a₄` is divisible by `2` and by `3`,
so the reduction is never multiplicative at these primes and no `I_n` stratum exists there. Type
`III` is reported by Step 4 of Tate's algorithm with no splitting test, which makes it usable at a
wild prime. Step 5's split test for type `IV` is settled at `2` by a vanishing constant term and at
`3` by the discriminant `4`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

/-! ### The Step-2 translate of a short model -/

namespace TateAlgorithm.Step2

variable {p : ℕ} [Fact p.Prime]

/-- **The coefficients of the Step-2 translate of a short model.** Once `ϖ ∣ Δ`, Step 2 applies the
substitution `⟨1, r, 0, t⟩` for some `r`, `t` (lifts of the coordinates of the singular point), and
on `y² = x³ + a₄x + a₆` that gives `a₁ = 0`, `a₂ = 3r`, `a₃ = 2t`, `a₄ + 3r²` and
`a₆ + r(a₄ + r²) - t²`. -/
theorem exists_translate_ofShortNF {a₄ a₆ : ℤ_[p]}
    (hΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ) :
    ∃ r t : ℤ_[p],
      (translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₁ = 0 ∧
        (translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₂ = 3 * r ∧
        (translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₃ = 2 * t ∧
        (translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₄ = a₄ + 3 * r ^ 2 ∧
        (translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).a₆
          = a₆ + r * (a₄ + r ^ 2) - t ^ 2 := by
  refine ⟨(singularPoint hΔ).x.out, (singularPoint hΔ).y.out, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [translate_eq_smul (p : ℤ_[p]) hΔ, translateVariableChange]
  · simp [WeierstrassCurve.variableChange_a₁]
  · simp [WeierstrassCurve.variableChange_a₂]
  · simp [WeierstrassCurve.variableChange_a₃]
  · simp only [WeierstrassCurve.variableChange_a₄, inv_one, Units.val_one]; ring
  · simp only [WeierstrassCurve.variableChange_a₆, inv_one, Units.val_one]; ring

end TateAlgorithm.Step2

/-! ### Parity arithmetic in `ℤ_[2]` -/

/-- In `ℤ_[2]`, the difference of two odd elements is even. -/
theorem two_dvd_sub_of_not_dvd {x y : ℤ_[2]} (hx : ¬ ((2 : ℕ) : ℤ_[2]) ∣ x)
    (hy : ¬ ((2 : ℕ) : ℤ_[2]) ∣ y) : ((2 : ℕ) : ℤ_[2]) ∣ x - y := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero] at hx hy ⊢
  rw [map_sub]
  have h : ∀ X Y : ZMod 2, X ≠ 0 → Y ≠ 0 → X - Y = 0 := by decide
  exact h _ _ hx hy

/-- In `ℤ_[2]`, `27` is odd. -/
theorem not_two_dvd_twentySeven : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (27 : ℤ_[2]) := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat]
  decide

/-- **The congruence cutting out the `III` locus.** For `a ≡ 2` or `3 (mod 4)` in `ℤ_[2]`, the
element `a + 3r²` is never divisible by `4`, whatever `r` is: modulo `4` the values of `A + 3R²` at
`A ∈ {2, 3}` are `1` and `2`. -/
theorem not_sq_dvd_add_three_mul_sq_two {a r : ℤ_[2]}
    (hA : PadicInt.toZModPow 2 a = 2 ∨ PadicInt.toZModPow 2 a = 3) :
    ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a + 3 * r ^ 2 := by
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_ofNat]
  have h : ∀ A R : ZMod (2 ^ 2), (A = 2 ∨ A = 3) → A + 3 * R ^ 2 ≠ 0 := by decide
  exact h _ _ hA

/-- **`4 ∣ r(a + r²)` from `v_2(a + 3r²) = 1`.** Writing `a + 3r² = 2n` with `n` odd gives
`a + r² = 2(n - r²)`, and `r(n - r²)` is even: if `r` is even that is immediate, and if `r` is odd
then `n` and `r²` are both odd, so their difference is even. -/
theorem sq_dvd_mul_add_sq_two {a r n : ℤ_[2]} (hn : a + 3 * r ^ 2 = 2 * n)
    (hodd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ n) :
    ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ r * (a + r ^ 2) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hsplit : a + r ^ 2 = 2 * (n - r ^ 2) := by linear_combination hn
  have hkey : ((2 : ℕ) : ℤ_[2]) ∣ r * (n - r ^ 2) := by
    by_cases hr : ((2 : ℕ) : ℤ_[2]) ∣ r
    · exact hr.mul_right _
    · exact (two_dvd_sub_of_not_dvd hodd fun hc =>
        hr (PadicInt.prime_p.dvd_of_dvd_pow (n := 2) hc)).mul_left _
  obtain ⟨w, hw⟩ := hkey
  refine ⟨w, ?_⟩
  rw [hsplit]
  rw [hcast] at hw ⊢
  calc r * (2 * (n - r ^ 2)) = 2 * (r * (n - r ^ 2)) := by ring
    _ = 2 * (2 * w) := by rw [hw]
    _ = 2 ^ 2 * w := by ring

/-! ### Nonsingularity on the locus -/

/-- **The `III` locus at `2` consists of nonsingular models.** If `a₄ ≡ 2` or `3 (mod 4)` and
`4 ∣ a₆` then `Δ = -16(4a₄³ + 27a₆²) ≠ 0`. -/
theorem ofShortNF_Δ_ne_zero_two {a₄ a₆ : ℤ_[2]}
    (hA : PadicInt.toZModPow 2 a₄ = 2 ∨ PadicInt.toZModPow 2 a₄ = 3)
    (hE : PadicInt.toZModPow 2 a₆ = 0) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have h2 : (2 : ℤ_[2]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h4 : (4 : ℤ_[2]) ≠ 0 := fun h => h2 (by
    have : (2 : ℤ_[2]) * 2 = 0 := by rw [← h]; ring
    exact (mul_eq_zero.mp this).elim id id)
  have h16 : (-16 : ℤ_[2]) ≠ 0 := fun h => h4 (by
    have : (4 : ℤ_[2]) * (-4) = 0 := by rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_right fun hc => h4 (by
      have : (4 : ℤ_[2]) = -(-4) := by ring
      rw [this, hc, neg_zero]))
  obtain ⟨c, hc⟩ : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a₆ :=
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.mpr hE
  rw [hcast] at hc
  have hfour : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a₄ := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    rcases hA with h | h <;> rw [h] <;> decide
  rw [ofShortNF_Δ]
  intro hzero
  have hD : (4 : ℤ_[2]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h h16
    · exact h
  have e1 : (4 : ℤ_[2]) * (a₄ ^ 3 + 108 * c ^ 2) = 0 := by rw [hc] at hD; linear_combination hD
  have e2 : a₄ ^ 3 + 108 * c ^ 2 = 0 := (mul_eq_zero.mp e1).resolve_left h4
  have hda₄ : ((2 : ℕ) : ℤ_[2]) ∣ a₄ := by
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 3) ?_
    exact ⟨-(54 * c ^ 2), by rw [hcast]; linear_combination e2⟩
  obtain ⟨m, hm⟩ := hda₄
  rw [hcast] at hm
  have e3 : (4 : ℤ_[2]) * (2 * m ^ 3 + 27 * c ^ 2) = 0 := by
    rw [hm] at e2; linear_combination e2
  have e4 : (2 : ℤ_[2]) * m ^ 3 + 27 * c ^ 2 = 0 := (mul_eq_zero.mp e3).resolve_left h4
  have hdc : ((2 : ℕ) : ℤ_[2]) ∣ c := by
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ?_
    refine (PadicInt.prime_p.dvd_or_dvd (a := (27 : ℤ_[2])) (b := c ^ 2)
      ⟨-m ^ 3, by rw [hcast]; linear_combination e4⟩).resolve_left not_two_dvd_twentySeven
  obtain ⟨d, hd⟩ := hdc
  rw [hcast] at hd
  have e5 : (2 : ℤ_[2]) * (m ^ 3 + 54 * d ^ 2) = 0 := by rw [hd] at e4; linear_combination e4
  have e6 : m ^ 3 + 54 * d ^ 2 = 0 := (mul_eq_zero.mp e5).resolve_left h2
  have hdm : ((2 : ℕ) : ℤ_[2]) ∣ m := by
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 3) ?_
    exact ⟨-(27 * d ^ 2), by rw [hcast]; linear_combination e6⟩
  obtain ⟨k, hk⟩ := hdm
  exact hfour ⟨k, by rw [hcast, hm, hk]; ring⟩

/-! ### The forward run at `III` -/

open TateAlgorithm in
/-- **The forward run at `III`, at the prime `2`.** A short model over `ℤ_2` with `a₄ ≡ 2` or
`3 (mod 4)` and `a₆ ≡ 0 (mod 4)` has reduction datum exactly `(III, 2)`. -/
theorem run_eq_III_two {a₄ a₆ : ℤ_[2]}
    (hA : PadicInt.toZModPow 2 a₄ = 2 ∨ PadicInt.toZModPow 2 a₄ = 3)
    (hE : PadicInt.toZModPow 2 a₆ = 0) (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.III ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hcast]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  have hd4 : ((2 : ℕ) : ℤ_[2]) ∣ a₄ + 3 * r ^ 2 := by
    have h := hval.a₄; rw [e4, pow_one] at h; exact h
  obtain ⟨n, hn⟩ := hd4
  rw [hcast] at hn
  have hnodd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ n := by
    intro hc
    obtain ⟨w, hw⟩ := hc
    exact not_sq_dvd_add_three_mul_sq_two (r := r) hA ⟨w, by rw [hn, hw, hcast]; ring⟩
  obtain ⟨c, hc⟩ : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a₆ :=
    PadicInt.pow_dvd_iff_toZModPow_eq_zero.mpr hE
  rw [hcast] at hc
  obtain ⟨s, hs⟩ := sq_dvd_mul_add_sq_two hn hnodd
  rw [hcast] at hs
  have hdt : ((2 : ℕ) : ℤ_[2]) ∣ t := by
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ?_
    have h := hval.a₆
    rw [e6, pow_one, hcast] at h
    have h2 : (2 : ℤ_[2]) ∣ a₆ + r * (a₄ + r ^ 2) := ⟨2 * c + 2 * s, by rw [hc, hs]; ring⟩
    obtain ⟨u, hu⟩ := h
    obtain ⟨v, hv⟩ := h2
    rw [hcast]
    exact ⟨v - u, by linear_combination hv - hu⟩
  obtain ⟨τ, hτ⟩ := hdt
  rw [hcast] at hτ
  have ha₆V : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
      = 4 * (c + s - τ ^ 2) := by rw [e6, hc, hs, hτ]; ring
  have hs3 : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨c + s - τ ^ 2, by rw [ha₆V, hcast]; ring⟩
  have hb₈ : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈
      = 8 * (6 * r * (c + s - τ ^ 2) + 6 * r * τ ^ 2) - 4 * n ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, ha₆V, hτ, hn]; ring
  have hs4 : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆),
          KodairaSymbol.III, 2⟩ := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    refine ite_eq_right fun hcon => hnodd ?_
    obtain ⟨w, hw⟩ := hcon
    rw [hb₈, hcast] at hw
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ⟨6 * r * (c + s - τ ^ 2) + 6 * r * τ ^ 2 - w,
      ?_⟩
    rw [hcast]
    have h4 : (4 : ℤ_[2]) ≠ 0 := by
      rw [show (4 : ℤ_[2]) = 2 ^ 2 by ring]
      exact pow_ne_zero 2 (by rw [← hcast]; exact PadicInt.uniformizer_ne_zero)
    refine mul_left_cancel₀ h4 ?_
    linear_combination -hw
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step4 hΔ hs4)]
  exact ⟨rfl, rfl⟩

/-! ### The `III` locus of the coefficient plane and its mass -/

/-- The two residue pairs modulo `4` cut out by `a₄ ≡ 2, 3` and `a₆ ≡ 0`. -/
def headResiduesTwo : Finset (ZMod (2 ^ 2) × ZMod (2 ^ 2)) := {(2, 0), (3, 0)}

/-- `headResiduesTwo` has exactly two elements. -/
theorem card_headResiduesTwo : headResiduesTwo.card = 2 := by decide

/-- The **`III` locus** of the coefficient plane at `2`: the pairs `(a₄, a₆) ∈ ℤ_2 × ℤ_2` with
`a₄ ≡ 2` or `3 (mod 4)` and `a₆ ≡ 0 (mod 4)`. -/
noncomputable def iii2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 2 ⁻¹' (headResiduesTwo : Set (ZMod (2 ^ 2) × ZMod (2 ^ 2)))

/-- A pair `(a₄, a₆)` lies in `iii2Locus` iff `a₄ ≡ 2` or `3 (mod 4)` and `a₆ ≡ 0 (mod 4)`. -/
theorem mem_iii2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iii2Locus ↔ (PadicInt.toZModPow 2 x.1 = 2 ∨ PadicInt.toZModPow 2 x.1 = 3) ∧
      PadicInt.toZModPow 2 x.2 = 0 := by
  simp only [iii2Locus, mem_preimage, PadicInt.redPairPow, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq, headResiduesTwo]
  exact or_and_right.symm

/-- **The mass of the `III` locus at `2` is `1/8`**: two of the sixteen residue classes modulo `4`
in the plane. -/
theorem volume_iii2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iii2Locus = 1 / (2 * ((2 : ℕ) : ℝ≥0∞) ^ 2) := by
  rw [iii2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesTwo]
  have h2 : ((2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
  rw [h2, ← ENNReal.inv_pow, one_div]
  rw [show (2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ 2 = 8 by ring,
    show (2 : ℝ≥0∞) ^ (2 * 2) = 2 * 8 by norm_num]
  rw [ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `III` locus lies in the strata over `t = 2`**: on it the model is nonsingular and Tate's
algorithm returns `(III, 2)`. -/
theorem iii2Locus_subset_iUnion_stratFibre :
    iii2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  obtain ⟨hA, hE⟩ := mem_iii2Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_two hA hE
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_III_two hA hE hΔ
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.III, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-! ### The bound on `δ_2(2)` and on `A_{2,2}` -/

open BSDTamagawa.LocalConstancy in
/-- **`1/(2·2²) ≤ δ_2(2)`**: the `p = 2` case of the bound `1/(2p²) ≤ δ_p(2)`. -/
theorem inv_two_mul_sq_le_δ_two_at_two :
    1 / (2 * ((2 : ℕ) : ℝ≥0∞) ^ 2) ≤ δ 2 2 :=
  calc 1 / (2 * ((2 : ℕ) : ℝ≥0∞) ^ 2)
      = (volume : Measure (ℤ_[2] × ℤ_[2])) iii2Locus := volume_iii2Locus.symm
    _ ≤ volume (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) :=
        measure_mono iii2Locus_subset_iUnion_stratFibre
    _ = δ 2 2 := volume_iUnion_stratFibre_kodaira 2

/-- **`1/(2·2²) ≤ A_{2,2}`**: the head-sum bound `A_{p,2} ≥ 1/(2p²)` at the prime `2`. -/
theorem inv_two_mul_sq_le_headSum_two_at_two :
    1 / (2 * ((2 : ℕ) : ℝ≥0∞) ^ 2) ≤ headSum 2 2 := by
  have hterm : δ 2 2 * (padicValNat 2 2 : ℝ≥0∞) ≤ headSum 2 2 := by
    rw [headSum]
    exact Finset.single_le_sum (f := fun t => δ 2 t * (padicValNat 2 t : ℝ≥0∞))
      (fun _ _ => zero_le) (by decide)
  calc 1 / (2 * ((2 : ℕ) : ℝ≥0∞) ^ 2) ≤ δ 2 2 := inv_two_mul_sq_le_δ_two_at_two
    _ = δ 2 2 * (padicValNat 2 2 : ℝ≥0∞) := by
        rw [show padicValNat 2 2 = 1 from by simp]
        simp
    _ ≤ headSum 2 2 := hterm

/-! ## The prime `3` -/

/-- `2` is a unit modulo `3`. -/
theorem not_three_dvd_two : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (2 : ℤ_[3]) := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat]
  decide

/-- **Reading `p ∣ y` off the residue modulo `p²`.** If the image of `toZModPow 2 y` under the
reduction `ℤ/p² → ℤ/p` vanishes then `p ∣ y`. -/
theorem dvd_of_cast_toZModPow_eq_zero {p : ℕ} [Fact p.Prime] {y : ℤ_[p]}
    (h : (ZMod.cast (PadicInt.toZModPow 2 y) : ZMod (p ^ 1)) = 0) : (p : ℤ_[p]) ∣ y := by
  rw [← pow_one (p : ℤ_[p]), PadicInt.pow_dvd_iff_toZModPow_eq_zero,
    ← PadicInt.cast_toZModPow 1 2 (by norm_num) y]
  exact h

/-- **The residue condition cutting out the `III` locus at `3`**, as a predicate on the pair
`(a₄, a₆) mod 9`: the six classes `(0, 1), (0, 8), (3, 0), (3, 4), (3, 5), (6, 0)`. -/
abbrev HeadResThree (A E : ZMod (3 ^ 2)) : Prop :=
  (A = 0 ∧ E = 1) ∨ (A = 0 ∧ E = 8) ∨ (A = 3 ∧ E = 0) ∨ (A = 3 ∧ E = 4) ∨
    (A = 3 ∧ E = 5) ∨ (A = 6 ∧ E = 0)

/-- The six residue pairs of `HeadResThree`, as a `Finset`. -/
def headResiduesThree : Finset (ZMod (3 ^ 2) × ZMod (3 ^ 2)) :=
  {(0, 1), (0, 8), (3, 0), (3, 4), (3, 5), (6, 0)}

/-- `headResiduesThree` has exactly six elements. -/
theorem card_headResiduesThree : headResiduesThree.card = 6 := by decide

/-- A residue pair modulo `9` lies in `headResiduesThree` iff it satisfies `HeadResThree`. -/
theorem mem_headResiduesThree_iff {c : ZMod (3 ^ 2) × ZMod (3 ^ 2)} :
    c ∈ headResiduesThree ↔ HeadResThree c.1 c.2 := by
  simp [headResiduesThree, Prod.ext_iff]

/-- On the `III` locus at `3`, `Δ = -16(4a₄³ + 27a₆²)` vanishes modulo `9`. -/
theorem headResThree_dvd_Δ : ∀ A E : ZMod (3 ^ 2), HeadResThree A E →
    (-16 : ZMod (3 ^ 2)) * (4 * A ^ 3 + 27 * E ^ 2) = 0 := by decide

/-- On the `III` locus at `3`, `a₄` vanishes modulo `3`. -/
theorem headResThree_cast : ∀ A E : ZMod (3 ^ 2), HeadResThree A E →
    (ZMod.cast A : ZMod (3 ^ 1)) = 0 := by decide

/-- Multiples of `3` in `ℤ/9`. -/
theorem three_mul_cases : ∀ Z : ZMod (3 ^ 2), 3 * Z = 0 ∨ 3 * Z = 3 ∨ 3 * Z = 6 := by decide

/-- **The residue computation behind the `III` locus at `3`.** For a pair satisfying `HeadResThree`
and any residue `R` for which `a₆ + R(a₄ + R²)` is divisible by `3`, that quantity is `0` modulo
`9` and `a₄ + 3R²` is nonzero modulo `9`. -/
theorem headResThree_key : ∀ A E R : ZMod (3 ^ 2), HeadResThree A E →
    (E + R * (A + R ^ 2) = 0 ∨ E + R * (A + R ^ 2) = 3 ∨ E + R * (A + R ^ 2) = 6) →
    E + R * (A + R ^ 2) = 0 ∧ A + 3 * R ^ 2 ≠ 0 := by decide

/-- **Nonsingularity, read modulo `9`.** No residue pair satisfying `HeadResThree` with `A = 3U`
has `E² = -4U³`. -/
theorem headResThree_ne : ∀ A E U : ZMod (3 ^ 2), HeadResThree A E → A = 3 * U →
    E ^ 2 ≠ -4 * U ^ 3 := by decide

/-- **The `III` locus at `3` consists of nonsingular models.** -/
theorem ofShortNF_Δ_ne_zero_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResThree (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h27 : (27 : ℤ_[3]) ≠ 0 := by
    rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]; exact pow_ne_zero 3 h3
  have h16u : IsUnit (16 : ℤ_[3]) := by
    refine not_not.mp fun hc => ?_
    have : ((3 : ℕ) : ℤ_[3]) ∣ (16 : ℤ_[3]) := PadicInt.dvd_iff_not_isUnit.mpr hc
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat] at this
    exact absurd this (by decide)
  have h16 : (-16 : ℤ_[3]) ≠ 0 := h16u.neg.ne_zero
  obtain ⟨u, hu⟩ : ((3 : ℕ) : ℤ_[3]) ∣ a₄ :=
    dvd_of_cast_toZModPow_eq_zero (headResThree_cast _ _ hA)
  rw [hcast] at hu
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[3]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left h16
  have hE : (27 : ℤ_[3]) * (4 * u ^ 3 + a₆ ^ 2) = 0 := by rw [hu] at hD; linear_combination hD
  have hE' : (4 : ℤ_[3]) * u ^ 3 + a₆ ^ 2 = 0 := (mul_eq_zero.mp hE).resolve_left h27
  refine headResThree_ne _ _ (PadicInt.toZModPow 2 u) hA ?_ ?_
  · rw [hu, map_mul, map_ofNat]
  · have h := congrArg (PadicInt.toZModPow 2) hE'
    rw [map_add, map_mul, map_pow, map_pow, map_ofNat, map_zero] at h
    linear_combination h

open TateAlgorithm in
/-- **The forward run at `III`, at the prime `3`.** A short model over `ℤ_3` whose coefficient pair
reduces into `headResiduesThree` modulo `9` has reduction datum exactly `(III, 2)`. -/
theorem run_eq_III_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResThree (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.III ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h9 : (9 : ℤ_[3]) ≠ 0 := by
    rw [show (9 : ℤ_[3]) = 3 ^ 2 by norm_num, ← hcast]
    exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  have hΔ9 : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ (ofShortNF a₄ a₆).Δ := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ofShortNF_Δ, map_mul, map_add, map_mul, map_mul,
      map_pow, map_pow, map_neg, map_ofNat, map_ofNat, map_ofNat]
    exact headResThree_dvd_Δ _ _ hA
  have hΔdvd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).Δ :=
    dvd_trans (dvd_pow_self _ two_ne_zero) hΔ9
  have hc₄ : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-16 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  obtain ⟨τ, hτ⟩ : ((3 : ℕ) : ℤ_[3]) ∣ t := by
    have h := hval.a₃
    rw [e3, pow_one] at h
    exact (PadicInt.prime_p.dvd_or_dvd h).resolve_left not_three_dvd_two
  rw [hcast] at hτ
  have hd4 : ((3 : ℕ) : ℤ_[3]) ∣ a₄ + 3 * r ^ 2 := by
    have h := hval.a₄; rw [e4, pow_one] at h; exact h
  obtain ⟨Z, hZ⟩ : ((3 : ℕ) : ℤ_[3]) ∣ a₆ + r * (a₄ + r ^ 2) := by
    have h := hval.a₆
    rw [e6, pow_one, hcast] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w + 3 * τ ^ 2, by rw [hcast]; linear_combination hw + (t + 3 * τ) * hτ⟩
  rw [hcast] at hZ
  have hZ9 : PadicInt.toZModPow 2 a₆ + PadicInt.toZModPow 2 r *
      (PadicInt.toZModPow 2 a₄ + PadicInt.toZModPow 2 r ^ 2)
        = 3 * PadicInt.toZModPow 2 Z := by
    have h := congrArg (PadicInt.toZModPow 2) hZ
    rw [map_add, map_mul, map_add, map_pow, map_mul, map_ofNat] at h
    exact h
  obtain ⟨hE0, hAne⟩ := headResThree_key _ _ (PadicInt.toZModPow 2 r) hA
    (by rw [hZ9]; exact three_mul_cases _)
  have h9a₆ : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ a₆ + r * (a₄ + r ^ 2) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_add, map_pow]
    exact hE0
  have h9a₄ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ a₄ + 3 * r ^ 2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_ofNat]
    exact hAne
  obtain ⟨n, hn⟩ := hd4
  rw [hcast] at hn
  have hnodd : ¬ ((3 : ℕ) : ℤ_[3]) ∣ n := by
    intro hc
    obtain ⟨w, hw⟩ := hc
    exact h9a₄ ⟨w, by rw [hn, hw, hcast]; ring⟩
  obtain ⟨S, hS⟩ := h9a₆
  rw [hcast] at hS
  have ha₆V : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆ = 9 * (S - τ ^ 2) := by
    rw [e6, hS, hτ]; ring
  have hs3 : Step3.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨S - τ ^ 2, by rw [ha₆V, hcast]; ring⟩
  have hb₈ : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₈
      = 27 * (4 * r * (S - τ ^ 2) + 4 * r * τ ^ 2) - 9 * n ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, ha₆V, hτ, hn]; ring
  have hs4 : Step4.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆),
          KodairaSymbol.III, 2⟩ := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    refine ite_eq_right fun hcon => hnodd ?_
    obtain ⟨w, hw⟩ := hcon
    rw [hb₈, hcast] at hw
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      ⟨4 * r * (S - τ ^ 2) + 4 * r * τ ^ 2 - w, ?_⟩
    rw [hcast]
    refine mul_left_cancel₀ h9 ?_
    linear_combination -hw
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step4 hΔ hs4)]
  exact ⟨rfl, rfl⟩

/-- The **`III` locus** of the coefficient plane at `3`: the six residue classes modulo `9` of
`headResiduesThree`. -/
noncomputable def iii3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 2 ⁻¹' (headResiduesThree : Set (ZMod (3 ^ 2) × ZMod (3 ^ 2)))

/-- A pair `(a₄, a₆)` lies in `iii3Locus` iff its reduction modulo `9` satisfies
`HeadResThree`. -/
theorem mem_iii3Locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ iii3Locus ↔
      HeadResThree (PadicInt.toZModPow 2 x.1) (PadicInt.toZModPow 2 x.2) := by
  rw [iii3Locus, mem_preimage, Finset.mem_coe, mem_headResiduesThree_iff, PadicInt.redPairPow]

/-- **The mass of the `III` locus at `3` is `6/81`**: six of the eighty-one residue classes modulo
`9` in the plane. -/
theorem volume_iii3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iii3Locus = 6 * ((3 : ℝ≥0∞)⁻¹) ^ 4 := by
  rw [iii3Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesThree]
  norm_num

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `III` locus at `3` lies in the strata over `t = 2`.** -/
theorem iii3Locus_subset_iUnion_stratFibre :
    iii3Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2) := by
  intro x hx
  have hA := mem_iii3Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_three hA
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_III_three hA hΔ
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.III, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- The numerical comparison `1/18 ≤ 6/81`, stated with both sides multiplied by `162`. -/
theorem inv_eighteen_le_six_mul :
    1 / (2 * ((3 : ℕ) : ℝ≥0∞) ^ 2) ≤ 6 * ((3 : ℝ≥0∞)⁻¹) ^ 4 := by
  have h3 : ((3 : ℕ) : ℝ≥0∞) = 3 := by norm_num
  rw [h3, one_div, ← ENNReal.inv_pow, show (2 : ℝ≥0∞) * (3 : ℝ≥0∞) ^ 2 = 18 by ring,
    show (3 : ℝ≥0∞) ^ 4 = 81 by ring]
  have hL : (18 : ℝ≥0∞)⁻¹ * 162 = 9 := by
    rw [show (162 : ℝ≥0∞) = 18 * 9 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hR : 6 * (81 : ℝ≥0∞)⁻¹ * 162 = 12 := by
    rw [show 6 * (81 : ℝ≥0∞)⁻¹ * 162 = (81 : ℝ≥0∞)⁻¹ * 81 * 12 by ring,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [← ENNReal.mul_le_mul_iff_left (c := (162 : ℝ≥0∞)) (by norm_num) (by norm_num), hL, hR]
  norm_num

open BSDTamagawa.LocalConstancy in
/-- **`1/(2·3²) ≤ δ_3(2)`**: the `p = 3` case of the bound `1/(2p²) ≤ δ_p(2)`. -/
theorem inv_two_mul_sq_le_δ_two_at_three :
    1 / (2 * ((3 : ℕ) : ℝ≥0∞) ^ 2) ≤ δ 3 2 :=
  calc 1 / (2 * ((3 : ℕ) : ℝ≥0∞) ^ 2) ≤ 6 * ((3 : ℝ≥0∞)⁻¹) ^ 4 := inv_eighteen_le_six_mul
    _ = (volume : Measure (ℤ_[3] × ℤ_[3])) iii3Locus := volume_iii3Locus.symm
    _ ≤ volume (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2)) :=
        measure_mono iii3Locus_subset_iUnion_stratFibre
    _ = δ 3 2 := volume_iUnion_stratFibre_kodaira 2

/-- **`1/(2·3²) ≤ A_{3,2}`**: the head-sum bound `A_{p,2} ≥ 1/(2p²)` at the prime `3`. -/
theorem inv_two_mul_sq_le_headSum_two_at_three :
    1 / (2 * ((3 : ℕ) : ℝ≥0∞) ^ 2) ≤ headSum 3 2 := by
  have hterm : δ 3 2 * (padicValNat 2 2 : ℝ≥0∞) ≤ headSum 3 2 := by
    rw [headSum]
    exact Finset.single_le_sum (f := fun t => δ 3 t * (padicValNat 2 t : ℝ≥0∞))
      (fun _ _ => zero_le) (by decide)
  calc 1 / (2 * ((3 : ℕ) : ℝ≥0∞) ^ 2) ≤ δ 3 2 := inv_two_mul_sq_le_δ_two_at_three
    _ = δ 3 2 * (padicValNat 2 2 : ℝ≥0∞) := by
        rw [show padicValNat 2 2 = 1 from by simp]
        simp
    _ ≤ headSum 3 2 := hterm

/-! ## Tamagawa number `3` at the prime `2`: the split `IV` locus -/

/-- **A monic quadratic with vanishing constant term splits**, with the root `0`. -/
theorem splits_quadratic_of_d_eq_zero {K : Type*} [Field K] (c : K) :
    (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X
      + Polynomial.C (0 : K)).Splits := by
  refine Polynomial.Splits.of_natDegree_eq_two (x := 0)
    (Polynomial.natDegree_quadratic one_ne_zero) ?_
  simp

/-- **Reading `pᵐ ∣ y` off the residue modulo `pⁿ`**, for `m ≤ n`. -/
theorem pow_dvd_of_cast_toZModPow_eq_zero {p : ℕ} [Fact p.Prime] {m n : ℕ} (h : m ≤ n) {y : ℤ_[p]}
    (hy : (ZMod.cast (PadicInt.toZModPow n y) : ZMod (p ^ m)) = 0) : (p : ℤ_[p]) ^ m ∣ y := by
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow m n h y]
  exact hy

/-- `-16` is nonzero in `ℤ_[2]`. -/
theorem neg_sixteen_ne_zero_two : (-16 : ℤ_[2]) ≠ 0 := by
  have h : (-16 : ℤ_[2]) = -(((2 : ℕ) : ℤ_[2]) ^ 4) := by norm_num
  rw [h, neg_ne_zero]
  exact pow_ne_zero 4 PadicInt.uniformizer_ne_zero

/-- **An odd `a₆` makes the short model over `ℤ_[2]` nonsingular.** -/
theorem ofShortNF_Δ_ne_zero_of_not_dvd_snd {a₄ a₆ : ℤ_[2]} (h6 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ a₆) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[2]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left neg_sixteen_ne_zero_two
  have hdvd : ((2 : ℕ) : ℤ_[2]) ∣ (27 : ℤ_[2]) * a₆ ^ 2 :=
    ⟨-(2 * a₄ ^ 3), by rw [hcast]; linear_combination hD⟩
  exact h6 (PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
    ((PadicInt.prime_p.dvd_or_dvd hdvd).resolve_left not_two_dvd_twentySeven))

/-- **The residue condition cutting out the split `IV` locus at `2`**: the four classes
`(a₄, a₆) ≡ (0, 1), (4, 1), (3, 5), (7, 1)` modulo `8`. -/
abbrev HeadResIVTwo (A E : ZMod (2 ^ 3)) : Prop :=
  (A = 0 ∧ E = 1) ∨ (A = 4 ∧ E = 1) ∨ (A = 3 ∧ E = 5) ∨ (A = 7 ∧ E = 1)

/-- The four residue pairs of `HeadResIVTwo`, as a `Finset`. -/
def headResiduesIVTwo : Finset (ZMod (2 ^ 3) × ZMod (2 ^ 3)) := {(0, 1), (4, 1), (3, 5), (7, 1)}

/-- `headResiduesIVTwo` has exactly four elements. -/
theorem card_headResiduesIVTwo : headResiduesIVTwo.card = 4 := by decide

/-- A residue pair modulo `8` lies in `headResiduesIVTwo` iff it satisfies `HeadResIVTwo`. -/
theorem mem_headResiduesIVTwo_iff {c : ZMod (2 ^ 3) × ZMod (2 ^ 3)} :
    c ∈ headResiduesIVTwo ↔ HeadResIVTwo c.1 c.2 := by
  simp [headResiduesIVTwo, Prod.ext_iff]

/-- On the split `IV` locus at `2` the coefficient `a₆` is odd. -/
theorem headResIVTwo_odd : ∀ A E : ZMod (2 ^ 3), HeadResIVTwo A E →
    (ZMod.cast E : ZMod (2 ^ 1)) ≠ 0 := by decide

/-- **The residue computation behind the split `IV` locus at `2`.** For a pair satisfying
`HeadResIVTwo` and any lifts `R`, `T` with `2 ∣ a₄ + 3R²` and `2 ∣ a₆(V)`: `8 ∣ a₆(V)`, `8 ∣ b₈(V)`
and `8 ∤ b₆(V)`. -/
theorem headResIVTwo_key : ∀ A E R T : ZMod (2 ^ 3), HeadResIVTwo A E →
    (ZMod.cast (A + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (E + R * (A + R ^ 2) - T ^ 2) : ZMod (2 ^ 1)) = 0 →
    E + R * (A + R ^ 2) - T ^ 2 = 0 ∧
      12 * R * (E + R * (A + R ^ 2) - T ^ 2) + 12 * R * T ^ 2 - (A + 3 * R ^ 2) ^ 2 = 0 ∧
      4 * T ^ 2 + 4 * (E + R * (A + R ^ 2) - T ^ 2) ≠ 0 := by decide

open TateAlgorithm in
/-- **The forward run at split `IV`, at the prime `2`.** A short model over `ℤ_2` whose coefficient
pair reduces into `HeadResIVTwo` modulo `8` has reduction datum exactly `(IV, 3)`. -/
theorem run_eq_IV_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResIVTwo (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 3 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hcast]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  have hm4 : (ZMod.cast (PadicInt.toZModPow 3 a₄ +
      3 * PadicInt.toZModPow 3 r ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 3 a₄ + 3 * PadicInt.toZModPow 3 r ^ 2
        = PadicInt.toZModPow 3 (a₄ + 3 * r ^ 2) by rw [map_add, map_mul, map_pow, map_ofNat],
      PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h := hval.a₄; rw [e4, pow_one] at h; exact h
  have hm6 : (ZMod.cast (PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
      (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2)
        - PadicInt.toZModPow 3 t ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
          (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2) - PadicInt.toZModPow 3 t ^ 2
        = PadicInt.toZModPow 3 (a₆ + r * (a₄ + r ^ 2) - t ^ 2) by
      rw [map_sub, map_add, map_mul, map_add, map_pow, map_pow],
      PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h := hval.a₆; rw [e6, pow_one] at h; exact h
  obtain ⟨k1, k2, k3⟩ := headResIVTwo_key _ _ (PadicInt.toZModPow 3 r)
    (PadicInt.toZModPow 3 t) hA hm4 hm6
  have h8a₆ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ a₆ + r * (a₄ + r ^ 2) - t ^ 2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_add, map_mul, map_add, map_pow,
      map_pow]
    exact k1
  have hb₈ : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈
      = 12 * r * (a₆ + r * (a₄ + r ^ 2) - t ^ 2) + 12 * r * t ^ 2 - (a₄ + 3 * r ^ 2) ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, e6]; ring
  have h8b₈ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hb₈, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    exact k2
  have hb₆ : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₆
      = 4 * t ^ 2 + 4 * (a₆ + r * (a₄ + r ^ 2) - t ^ 2) := by
    rw [WeierstrassCurve.b₆, e3, e6]; ring
  have hnb₆ : ¬ ((2 : ℕ) : ℤ_[2]) ^ 3 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₆ := by
    rw [hb₆, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    exact k3
  have h4a₆V : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆ := by
    rw [e6]; exact dvd_trans (pow_dvd_pow _ (by norm_num)) h8a₆
  have hs3 : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left h4a₆V
  have hs4 : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left h8b₈
  have hd0 : CommRing.mod ((2 : ℕ) : ℤ_[2])
      (CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
        (((2 : ℕ) : ℤ_[2]) ^ 2)) = 0 := by
    rw [CommRing.mod_eq_zero]
    have he : ((2 : ℕ) : ℤ_[2]) ^ 2 *
        CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
          (((2 : ℕ) : ℤ_[2]) ^ 2)
        = (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆ :=
      CommRing.mul_div (pow_ne_zero 2 hϖ) h4a₆V
    obtain ⟨w, hw⟩ := h8a₆
    refine ⟨w, mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_⟩
    rw [he, e6, hw]; ring
  have hsplit : (quadratic ((2 : ℕ) : ℤ_[2])
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).toPoly.Splits := by
    have hd : (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).d = 0 := by
      have hd' : (quadratic ((2 : ℕ) : ℤ_[2])
          (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).d
          = -CommRing.mod ((2 : ℕ) : ℤ_[2])
              (CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
                (((2 : ℕ) : ℤ_[2]) ^ 2)) := by
        norm_num [quadratic]
      rw [hd', hd0, neg_zero]
    have hb : (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).b = 1 := by
      norm_num [quadratic]
    rw [Cubic.of_a_eq_zero (by norm_num [quadratic] :
      (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).a = 0), hb, hd]
    exact splits_quadratic_of_d_eq_zero _
  have hs5 : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆),
          KodairaSymbol.IV, 3⟩ := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    rw [ite_eq_right hnb₆, ite_eq_left hsplit]
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step5 hΔ hs5)]
  exact ⟨rfl, rfl⟩

/-- The **split `IV` locus** of the coefficient plane at `2`: four residue classes modulo `8`. -/
noncomputable def iv2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 3 ⁻¹' (headResiduesIVTwo : Set (ZMod (2 ^ 3) × ZMod (2 ^ 3)))

/-- A pair `(a₄, a₆)` lies in `iv2Locus` iff its reduction modulo `8` satisfies
`HeadResIVTwo`. -/
theorem mem_iv2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iv2Locus ↔ HeadResIVTwo (PadicInt.toZModPow 3 x.1) (PadicInt.toZModPow 3 x.2) := by
  rw [iv2Locus, mem_preimage, Finset.mem_coe, mem_headResiduesIVTwo_iff, PadicInt.redPairPow]

/-- **The mass of the split `IV` locus at `2` is `4/64 = 1/16`.** -/
theorem volume_iv2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iv2Locus = 4 * ((2 : ℝ≥0∞)⁻¹) ^ 6 := by
  rw [iv2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIVTwo]
  norm_num

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The split `IV` locus at `2` lies in the strata over `t = 3`.** -/
theorem iv2Locus_subset_iUnion_stratFibre :
    iv2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3) := by
  intro x hx
  have hA := mem_iv2Locus_iff.1 hx
  have h6 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ x.2 := by
    intro hc
    refine headResIVTwo_odd _ _ hA ?_
    rw [PadicInt.cast_toZModPow 1 3 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero,
      pow_one]
    exact hc
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_of_not_dvd_snd h6
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_IV_two hA hΔ
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.IV, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- The numerical comparison `1/24 ≤ 4/64`, stated with both sides multiplied by `48`. -/
theorem inv_twentyFour_le_four_mul :
    1 / (3 * ((2 : ℕ) : ℝ≥0∞) ^ 3) ≤ 4 * ((2 : ℝ≥0∞)⁻¹) ^ 6 := by
  have h2 : ((2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
  rw [h2, one_div, ← ENNReal.inv_pow, show (3 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ 3 = 24 by ring,
    show (2 : ℝ≥0∞) ^ 6 = 64 by ring]
  have hL : (24 : ℝ≥0∞)⁻¹ * 48 = 2 := by
    rw [show (48 : ℝ≥0∞) = 24 * 2 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hR : 4 * (64 : ℝ≥0∞)⁻¹ * 48 = 3 := by
    rw [show 4 * (64 : ℝ≥0∞)⁻¹ * 48 = (64 : ℝ≥0∞)⁻¹ * 64 * 3 by ring,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [← ENNReal.mul_le_mul_iff_left (c := (48 : ℝ≥0∞)) (by norm_num) (by norm_num), hL, hR]
  norm_num

open BSDTamagawa.LocalConstancy in
/-- **`1/(3·2³) ≤ δ_2(3)`**: the `p = 2` case of the bound `1/(3p³) ≤ δ_p(3)`. -/
theorem inv_three_mul_cube_le_δ_three_at_two :
    1 / (3 * ((2 : ℕ) : ℝ≥0∞) ^ 3) ≤ δ 2 3 :=
  calc 1 / (3 * ((2 : ℕ) : ℝ≥0∞) ^ 3) ≤ 4 * ((2 : ℝ≥0∞)⁻¹) ^ 6 := inv_twentyFour_le_four_mul
    _ = (volume : Measure (ℤ_[2] × ℤ_[2])) iv2Locus := volume_iv2Locus.symm
    _ ≤ volume (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 3)) :=
        measure_mono iv2Locus_subset_iUnion_stratFibre
    _ = δ 2 3 := volume_iUnion_stratFibre_kodaira 3

/-- **`1/(3·2³) ≤ A_{2,3}`**: the head-sum bound `A_{p,3} ≥ 1/(3p³)` at the prime `2`. -/
theorem inv_three_mul_cube_le_headSum_three_at_two :
    1 / (3 * ((2 : ℕ) : ℝ≥0∞) ^ 3) ≤ headSum 2 3 := by
  have hterm : δ 2 3 * (padicValNat 3 3 : ℝ≥0∞) ≤ headSum 2 3 := by
    rw [headSum]
    exact Finset.single_le_sum (f := fun t => δ 2 t * (padicValNat 3 t : ℝ≥0∞))
      (fun _ _ => zero_le) (by decide)
  calc 1 / (3 * ((2 : ℕ) : ℝ≥0∞) ^ 3) ≤ δ 2 3 := inv_three_mul_cube_le_δ_three_at_two
    _ = δ 2 3 * (padicValNat 3 3 : ℝ≥0∞) := by
        rw [show padicValNat 3 3 = 1 from by simp]
        simp
    _ ≤ headSum 2 3 := hterm

/-! ## Tamagawa number `3` at the prime `3`: the split `IV` locus -/

/-- `4` is a unit modulo `3`. -/
theorem not_three_dvd_four : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (4 : ℤ_[3]) := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat]
  decide

/-- **No short model over `ℤ_3` with `v_3(a₆) = 2` is singular**: `4a₄³ + 27(9c)² = 0` with `3 ∤ c`
is impossible. -/
theorem no_singular_of_emultiplicity_snd_eq_two {a₄ c : ℤ_[3]}
    (hc : ¬ ((3 : ℕ) : ℤ_[3]) ∣ c) (h : (4 : ℤ_[3]) * a₄ ^ 3 + 27 * (9 * c) ^ 2 = 0) : False := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h27 : (27 : ℤ_[3]) ≠ 0 := by
    rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]; exact pow_ne_zero 3 h3
  have step : ∀ x y : ℤ_[3], (4 : ℤ_[3]) * x ^ 3 = 3 * y → ((3 : ℕ) : ℤ_[3]) ∣ x := by
    intro x y hxy
    refine PadicInt.prime_p.dvd_of_dvd_pow (n := 3) ?_
    refine (PadicInt.prime_p.dvd_or_dvd (a := (4 : ℤ_[3])) (b := x ^ 3) ?_).resolve_left
      not_three_dvd_four
    exact ⟨y, by rw [hcast]; exact hxy⟩
  obtain ⟨u, hu⟩ := step a₄ (-(729 * c ^ 2)) (by linear_combination h)
  rw [hcast] at hu
  have e1 : (27 : ℤ_[3]) * (4 * u ^ 3 + 81 * c ^ 2) = 0 := by rw [hu] at h; linear_combination h
  have e1' : (4 : ℤ_[3]) * u ^ 3 + 81 * c ^ 2 = 0 := (mul_eq_zero.mp e1).resolve_left h27
  obtain ⟨w, hw⟩ := step u (-(27 * c ^ 2)) (by linear_combination e1')
  rw [hcast] at hw
  have e2 : (27 : ℤ_[3]) * (4 * w ^ 3 + 3 * c ^ 2) = 0 := by
    rw [hw] at e1'; linear_combination e1'
  have e2' : (4 : ℤ_[3]) * w ^ 3 + 3 * c ^ 2 = 0 := (mul_eq_zero.mp e2).resolve_left h27
  obtain ⟨z, hz⟩ := step w (-(c ^ 2)) (by linear_combination e2')
  rw [hcast] at hz
  have e3 : (3 : ℤ_[3]) * (36 * z ^ 3 + c ^ 2) = 0 := by rw [hz] at e2'; linear_combination e2'
  have e3' : (36 : ℤ_[3]) * z ^ 3 + c ^ 2 = 0 := (mul_eq_zero.mp e3).resolve_left h3
  refine hc (PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ⟨-(12 * z ^ 3), ?_⟩)
  rw [hcast]; linear_combination e3'

/-- **The residue condition cutting out the split `IV` locus at `3`**: the nine classes
`(a₄, a₆) ≡ (0, 9), (6, 2), (6, 16), (9, 9), (15, 20), (15, 25), (18, 9), (24, 7), (24, 11)`
modulo `27`. Every one has `3 ∣ a₄`, and `a₆` is either a unit or of valuation exactly `2`. -/
abbrev HeadResIVThree (A E : ZMod (3 ^ 3)) : Prop :=
  (A = 0 ∧ E = 9) ∨ (A = 6 ∧ E = 2) ∨ (A = 6 ∧ E = 16) ∨ (A = 9 ∧ E = 9) ∨
    (A = 15 ∧ E = 20) ∨ (A = 15 ∧ E = 25) ∨ (A = 18 ∧ E = 9) ∨ (A = 24 ∧ E = 7) ∨
    (A = 24 ∧ E = 11)

/-- The nine residue pairs of `HeadResIVThree`, as a `Finset`. -/
def headResiduesIVThree : Finset (ZMod (3 ^ 3) × ZMod (3 ^ 3)) :=
  {(0, 9), (6, 2), (6, 16), (9, 9), (15, 20), (15, 25), (18, 9), (24, 7), (24, 11)}

/-- `headResiduesIVThree` has exactly nine elements. -/
theorem card_headResiduesIVThree : headResiduesIVThree.card = 9 := by decide

/-- A residue pair modulo `27` lies in `headResiduesIVThree` iff it satisfies
`HeadResIVThree`. -/
theorem mem_headResiduesIVThree_iff {c : ZMod (3 ^ 3) × ZMod (3 ^ 3)} :
    c ∈ headResiduesIVThree ↔ HeadResIVThree c.1 c.2 := by
  simp [headResiduesIVThree, Prod.ext_iff]

/-- **The residue computation behind the split `IV` locus at `3`.** For a pair satisfying
`HeadResIVThree` and any lift `R` for which `X = a₆ + R(a₄ + R²)` is divisible by `3`:
`X ≡ 9 (mod 27)`, and `27 ∣ 12RX - (a₄ + 3R²)²`. -/
theorem headResIVThree_key : ∀ A E R : ZMod (3 ^ 3), HeadResIVThree A E →
    (ZMod.cast (E + R * (A + R ^ 2)) : ZMod (3 ^ 1)) = 0 →
    E + R * (A + R ^ 2) = 9 ∧
      12 * R * (E + R * (A + R ^ 2)) - (A + 3 * R ^ 2) ^ 2 = 0 := by decide

/-- On the split `IV` locus at `3`, `a₆` is either a unit or `≡ 9 (mod 27)`. -/
theorem headResIVThree_snd : ∀ A E : ZMod (3 ^ 3), HeadResIVThree A E →
    (ZMod.cast E : ZMod (3 ^ 1)) ≠ 0 ∨ E = 9 := by decide

/-- **Nonsingularity for the unit-`a₆` classes, read modulo `27`.** No residue pair satisfying
`HeadResIVThree` with `E` a unit and `A = 3U` has `E² = -4U³`. -/
theorem headResIVThree_ne : ∀ A E U : ZMod (3 ^ 3), HeadResIVThree A E →
    (ZMod.cast E : ZMod (3 ^ 1)) ≠ 0 → A = 3 * U → E ^ 2 ≠ -4 * U ^ 3 := by decide

/-- On the split `IV` locus at `3`, `a₄` vanishes modulo `3`. -/
theorem headResIVThree_cast : ∀ A E : ZMod (3 ^ 3), HeadResIVThree A E →
    (ZMod.cast A : ZMod (3 ^ 1)) = 0 := by decide

/-- **The split `IV` locus at `3` consists of nonsingular models.** -/
theorem ofShortNF_Δ_ne_zero_IV_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResIVThree (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h27 : (27 : ℤ_[3]) ≠ 0 := by
    rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]; exact pow_ne_zero 3 h3
  have h16u : IsUnit (16 : ℤ_[3]) := by
    refine not_not.mp fun hcu => ?_
    have hd : ((3 : ℕ) : ℤ_[3]) ∣ (16 : ℤ_[3]) := PadicInt.dvd_iff_not_isUnit.mpr hcu
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat] at hd
    exact absurd hd (by decide)
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[3]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left h16u.neg.ne_zero
  rcases headResIVThree_snd _ _ hA with hunit | hnine
  · have hd4 : ((3 : ℕ) : ℤ_[3]) ∣ a₄ := by
      have h := pow_dvd_of_cast_toZModPow_eq_zero (p := 3) (m := 1) (n := 3) (by norm_num)
        (y := a₄) (headResIVThree_cast _ _ hA)
      rwa [pow_one] at h
    obtain ⟨u, hu⟩ := hd4
    rw [hcast] at hu
    have hE : (27 : ℤ_[3]) * (4 * u ^ 3 + a₆ ^ 2) = 0 := by rw [hu] at hD; linear_combination hD
    have hE' : (4 : ℤ_[3]) * u ^ 3 + a₆ ^ 2 = 0 := (mul_eq_zero.mp hE).resolve_left h27
    refine headResIVThree_ne _ _ (PadicInt.toZModPow 3 u) hA hunit ?_ ?_
    · rw [hu, map_mul, map_ofNat]
    · have h := congrArg (PadicInt.toZModPow 3) hE'
      rw [map_add, map_mul, map_pow, map_pow, map_ofNat, map_zero] at h
      linear_combination h
  · obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ a₆ := by
      refine pow_dvd_of_cast_toZModPow_eq_zero (m := 2) (n := 3) (by norm_num) ?_
      rw [hnine]; decide
    rw [hcast] at hc
    refine no_singular_of_emultiplicity_snd_eq_two (a₄ := a₄) (c := c) ?_ ?_
    · intro hdc
      obtain ⟨d, hd⟩ := hdc
      have h27a₆ : PadicInt.toZModPow 3 a₆ = 0 :=
        PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp ⟨d, by rw [hc, hd, hcast]; ring⟩
      rw [hnine] at h27a₆
      exact absurd h27a₆ (by decide)
    · rw [hc] at hD; linear_combination hD

open TateAlgorithm in
/-- **The forward run at split `IV`, at the prime `3`.** A short model over `ℤ_3` whose coefficient
pair reduces into `HeadResIVThree` modulo `27` has reduction datum exactly `(IV, 3)`. -/
theorem run_eq_IV_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResIVThree (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 3 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h9 : (9 : ℤ_[3]) ≠ 0 := by
    rw [show (9 : ℤ_[3]) = 3 ^ 2 by norm_num, ← hcast]
    exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  obtain ⟨u, hu⟩ : ((3 : ℕ) : ℤ_[3]) ∣ a₄ := by
    have h := pow_dvd_of_cast_toZModPow_eq_zero (p := 3) (m := 1) (n := 3) (by norm_num)
      (y := a₄) (headResIVThree_cast _ _ hA)
    rwa [pow_one] at h
  rw [hcast] at hu
  have hΔdvd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-144 * (4 * u ^ 3 + a₆ ^ 2), by rw [ofShortNF_Δ, hu, hcast]; ring⟩
  have hc₄ : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-16 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  obtain ⟨τ, hτ⟩ : ((3 : ℕ) : ℤ_[3]) ∣ t := by
    have h := hval.a₃
    rw [e3, pow_one] at h
    exact (PadicInt.prime_p.dvd_or_dvd h).resolve_left not_three_dvd_two
  rw [hcast] at hτ
  have hX3 : ((3 : ℕ) : ℤ_[3]) ∣ a₆ + r * (a₄ + r ^ 2) := by
    have h := hval.a₆
    rw [e6, pow_one, hcast] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w + 3 * τ ^ 2, by rw [hcast]; linear_combination hw + (t + 3 * τ) * hτ⟩
  have hXcast : (ZMod.cast (PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
      (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2)) : ZMod (3 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
          (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2)
        = PadicInt.toZModPow 3 (a₆ + r * (a₄ + r ^ 2)) by rw [map_add, map_mul, map_add, map_pow],
      PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact hX3
  obtain ⟨k1, k2⟩ := headResIVThree_key _ _ (PadicInt.toZModPow 3 r) hA hXcast
  obtain ⟨m, hm⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ (a₆ + r * (a₄ + r ^ 2) - 9) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [k1, sub_self]
  rw [hcast] at hm
  have hXM : a₆ + r * (a₄ + r ^ 2) = 9 * (1 + 3 * m) := by linear_combination hm
  have hM3 : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (1 + 3 * m) := by
    intro hcm
    obtain ⟨v, hv⟩ := hcm
    rw [hcast] at hv
    exact PadicInt.prime_p.not_dvd_one ⟨v - m, by rw [hcast]; linear_combination hv⟩
  have ha₆V : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
      = 9 * (1 + 3 * m - τ ^ 2) := by rw [e6, hXM, hτ]; ring
  have h9a₆V : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆ :=
    ⟨1 + 3 * m - τ ^ 2, by rw [ha₆V, hcast]; ring⟩
  have hs3 : Step3.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left h9a₆V
  have hb₈ : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₈
      = 12 * r * (a₆ + r * (a₄ + r ^ 2)) - (a₄ + 3 * r ^ 2) ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, e6]; ring
  have h27b₈ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hb₈, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    exact k2
  have hs4 : Step4.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left h27b₈
  have hb₆ : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
      = 9 * (4 * (1 + 3 * m)) := by rw [WeierstrassCurve.b₆, e3, e6, hXM]; ring
  have hnb₆ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 3 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆ := by
    rw [hb₆]
    intro hcb
    obtain ⟨w, hw⟩ := hcb
    refine hM3 ((PadicInt.prime_p.dvd_or_dvd (a := (4 : ℤ_[3])) (b := 1 + 3 * m)
      ⟨w, ?_⟩).resolve_left not_three_dvd_four)
    rw [hcast] at hw ⊢
    refine mul_left_cancel₀ h9 ?_
    linear_combination hw
  have hv3 := Step3.run_hasValuation hs3
  have ea₃ : ((3 : ℕ) : ℤ_[3]) *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃ ((3 : ℕ) : ℤ_[3])
        = (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃ :=
    CommRing.mul_div hϖ (by simpa using hv3.a₃)
  have ea₆ : ((3 : ℕ) : ℤ_[3]) ^ 2 *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
        (((3 : ℕ) : ℤ_[3]) ^ 2)
        = (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ) hv3.a₆
  have eb₆ : ((3 : ℕ) : ℤ_[3]) ^ 2 *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
        (((3 : ℕ) : ℤ_[3]) ^ 2)
        = (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ) hv3.b₆
  have hdisc : CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
        ((3 : ℕ) : ℤ_[3]) ^ 2
      + 4 * CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
        (((3 : ℕ) : ℤ_[3]) ^ 2)
      = CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
        (((3 : ℕ) : ℤ_[3]) ^ 2) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_
    rw [eb₆, WeierstrassCurve.b₆]
    linear_combination (((3 : ℕ) : ℤ_[3]) *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃ ((3 : ℕ) : ℤ_[3])
        + (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃) * ea₃ + 4 * ea₆
  have edivb₆ : CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
      (((3 : ℕ) : ℤ_[3]) ^ 2) = 4 * (1 + 3 * m) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_
    rw [eb₆, hb₆, hcast]; ring
  have hmod4M : CommRing.mod ((3 : ℕ) : ℤ_[3]) (4 * (1 + 3 * m))
      = (4 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])}) := by
    have hd : ((3 : ℕ) : ℤ_[3]) ∣ (4 * (1 + 3 * m) - 4) := ⟨4 * m, by rw [hcast]; ring⟩
    have h0 := (CommRing.mod_eq_zero ((3 : ℕ) : ℤ_[3]) (4 * (1 + 3 * m) - 4)).2 hd
    rw [map_sub, map_ofNat, sub_eq_zero] at h0
    exact h0
  have h2' : (2 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])}) ≠ 0 := by
    rw [show (2 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])})
        = CommRing.mod ((3 : ℕ) : ℤ_[3]) 2 from by simp only [map_ofNat], Ne,
      CommRing.mod_eq_zero]
    exact not_three_dvd_two
  have hsqd : IsSquare (CommRing.mod ((3 : ℕ) : ℤ_[3])
      (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
        ((3 : ℕ) : ℤ_[3])) ^ 2
      + 4 * CommRing.mod ((3 : ℕ) : ℤ_[3])
        (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
          (((3 : ℕ) : ℤ_[3]) ^ 2))) := by
    rw [show CommRing.mod ((3 : ℕ) : ℤ_[3])
          (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
            ((3 : ℕ) : ℤ_[3])) ^ 2
          + 4 * CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
              (((3 : ℕ) : ℤ_[3]) ^ 2))
        = CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
              ((3 : ℕ) : ℤ_[3]) ^ 2
              + 4 * CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
                (((3 : ℕ) : ℤ_[3]) ^ 2)) from by
      simp only [map_add, map_mul, map_pow, map_ofNat], hdisc, edivb₆, hmod4M]
    exact ⟨2, by norm_num⟩
  have hsplit : (quadratic ((3 : ℕ) : ℤ_[3])
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).toPoly.Splits := by
    have hb : (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).b = 1 := by
      norm_num [quadratic]
    have hcq : (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).c
        = CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
              ((3 : ℕ) : ℤ_[3])) := by norm_num [quadratic]
    have hdq : (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).d
        = -CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
              (((3 : ℕ) : ℤ_[3]) ^ 2)) := by norm_num [quadratic]
    rw [Cubic.of_a_eq_zero (by norm_num [quadratic] :
      (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).a = 0), hb, hcq, hdq]
    exact BSDTamagawa.HeadSumThree.splits_quadratic_of_isSquare h2' hsqd
  have hs5 : Step5.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆),
          KodairaSymbol.IV, 3⟩ := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    rw [ite_eq_right hnb₆, ite_eq_left hsplit]
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step5 hΔ hs5)]
  exact ⟨rfl, rfl⟩

/-- The **split `IV` locus** of the coefficient plane at `3`: nine residue classes modulo `27`. -/
noncomputable def iv3Locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 3 ⁻¹' (headResiduesIVThree : Set (ZMod (3 ^ 3) × ZMod (3 ^ 3)))

/-- A pair `(a₄, a₆)` lies in `iv3Locus` iff its reduction modulo `27` satisfies
`HeadResIVThree`. -/
theorem mem_iv3Locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ iv3Locus ↔ HeadResIVThree (PadicInt.toZModPow 3 x.1) (PadicInt.toZModPow 3 x.2) := by
  rw [iv3Locus, mem_preimage, Finset.mem_coe, mem_headResiduesIVThree_iff, PadicInt.redPairPow]

/-- **The mass of the split `IV` locus at `3` is `9/729 = 1/81`.** -/
theorem volume_iv3Locus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iv3Locus = 1 / (3 * ((3 : ℕ) : ℝ≥0∞) ^ 3) := by
  rw [iv3Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIVThree]
  have h3 : ((3 : ℕ) : ℝ≥0∞) = 3 := by norm_num
  have h9 : ((9 : ℕ) : ℝ≥0∞) = 9 := by norm_num
  rw [h3, h9, ← ENNReal.inv_pow, one_div, show (3 : ℝ≥0∞) * (3 : ℝ≥0∞) ^ 3 = 81 by ring,
    show (3 : ℝ≥0∞) ^ (2 * 3) = 9 * 81 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The split `IV` locus at `3` lies in the strata over `t = 3`.** -/
theorem iv3Locus_subset_iUnion_stratFibre :
    iv3Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 3) := by
  intro x hx
  have hA := mem_iv3Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_IV_three hA
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_IV_three hA hΔ
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.IV, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

open BSDTamagawa.LocalConstancy in
/-- **`1/(3·3³) ≤ δ_3(3)`**: the `p = 3` case of the bound `1/(3p³) ≤ δ_p(3)`. -/
theorem inv_three_mul_cube_le_δ_three_at_three :
    1 / (3 * ((3 : ℕ) : ℝ≥0∞) ^ 3) ≤ δ 3 3 :=
  calc 1 / (3 * ((3 : ℕ) : ℝ≥0∞) ^ 3)
      = (volume : Measure (ℤ_[3] × ℤ_[3])) iv3Locus := volume_iv3Locus.symm
    _ ≤ volume (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 3)) :=
        measure_mono iv3Locus_subset_iUnion_stratFibre
    _ = δ 3 3 := volume_iUnion_stratFibre_kodaira 3

/-- **`1/(3·3³) ≤ A_{3,3}`**: the head-sum bound `A_{p,3} ≥ 1/(3p³)` at the prime `3`. -/
theorem inv_three_mul_cube_le_headSum_three_at_three :
    1 / (3 * ((3 : ℕ) : ℝ≥0∞) ^ 3) ≤ headSum 3 3 := by
  have hterm : δ 3 3 * (padicValNat 3 3 : ℝ≥0∞) ≤ headSum 3 3 := by
    rw [headSum]
    exact Finset.single_le_sum (f := fun t => δ 3 t * (padicValNat 3 t : ℝ≥0∞))
      (fun _ _ => zero_le) (by decide)
  calc 1 / (3 * ((3 : ℕ) : ℝ≥0∞) ^ 3) ≤ δ 3 3 := inv_three_mul_cube_le_δ_three_at_three
    _ = δ 3 3 * (padicValNat 3 3 : ℝ≥0∞) := by
        rw [show padicValNat 3 3 = 1 from by simp]
        simp
    _ ≤ headSum 3 3 := hterm

/-! ## The head-sum bounds at every prime -/

/-- A prime is `2`, `3`, or at least `5`. -/
theorem eq_two_or_eq_three_or_five_le {p : ℕ} (hp : p.Prime) : p = 2 ∨ p = 3 ∨ 5 ≤ p := by
  rcases Nat.lt_or_ge p 5 with h | h
  · have h2 := hp.two_le
    interval_cases p
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by decide)
  · exact Or.inr (Or.inr h)

/-- For every prime `p`, `A_{p,2} ≥ 1/(2p²)`. -/
@[bsd_tamagawa "T049"]
theorem inv_two_mul_sq_le_headSum_two_of_prime {p : ℕ} [Fact p.Prime] :
    1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2 := by
  rcases eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with rfl | rfl | h5
  · exact inv_two_mul_sq_le_headSum_two_at_two
  · exact inv_two_mul_sq_le_headSum_two_at_three
  · exact inv_two_mul_sq_le_headSum_two h5

/-- For every prime `p`, `A_{p,3} ≥ 1/(3p³)`. -/
@[bsd_tamagawa "T049"]
theorem inv_three_mul_cube_le_headSum_three_of_prime {p : ℕ} [Fact p.Prime] :
    1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3 := by
  rcases eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with rfl | rfl | h5
  · exact inv_three_mul_cube_le_headSum_three_at_two
  · exact inv_three_mul_cube_le_headSum_three_at_three
  · exact inv_three_mul_cube_le_headSum_three h5

/-- For every prime `p`, both head-sum lower bounds `A_{p,2} ≥ 1/(2p²)` and `A_{p,3} ≥ 1/(3p³)`
hold. -/
theorem headSum_lower_bounds_of_prime {p : ℕ} [Fact p.Prime] :
    1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2 ∧ 1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3 :=
  ⟨inv_two_mul_sq_le_headSum_two_of_prime, inv_three_mul_cube_le_headSum_three_of_prime⟩

end WeierstrassCurve
