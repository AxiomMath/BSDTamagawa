/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowGoodAtTwo
public import BSDTamagawa.GOTTable.WildStarredAtTwo

/-!
# Tate's algorithm on the odd starred and good-reduction families at `p = 2`

Tate's algorithm on four parametrised families of the coefficient plane at `2`: the even and the
mirror good-reduction families run to `(I₀, 1)`, the odd `III*` family to `(III*, 2)` and the odd
`II*` family to `(II*, 1)`.

## Main results

* `WeierstrassCurve.TateAlgorithm.run_eq_I0_of_goodEven_two`,
  `WeierstrassCurve.TateAlgorithm.run_eq_IIIstarOdd_two`,
  `WeierstrassCurve.TateAlgorithm.run_eq_IIstarOdd_two`,
  `WeierstrassCurve.TateAlgorithm.run_eq_I0_of_goodOdd_two`: Tate's algorithm on the four
  families.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

namespace TateAlgorithm

/-! ### Exact division and residues at `2` -/

private theorem div_two_eq_of_eq_mul {x a : ℤ_[2]} (h : x = ((2 : ℕ) : ℤ_[2]) * a) :
    div x ((2 : ℕ) : ℤ_[2]) = a := by
  rw [← pow_one ((2 : ℕ) : ℤ_[2])] at h ⊢
  exact div_eq_of_eq_pow_mul_two h

private theorem mod_two_eq_of_dvd_sub {x y : ℤ_[2]} (h : ((2 : ℕ) : ℤ_[2]) ∣ x - y) :
    mod ((2 : ℕ) : ℤ_[2]) x = mod ((2 : ℕ) : ℤ_[2]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-- Step 2 at `2` on a short model: it hands on a translate by some `(r, t)`, and the
translated `a₄` and `a₆` are divisible by `2`. -/
private theorem exists_step2_run_two (a₄ a₆ : ℤ_[2]) :
    ∃ r t : ℤ_[2], Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
        = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) ∧
      ((2 : ℕ) : ℤ_[2]) ∣ a₄ + 3 * r ^ 2 - 2 * 0 * t ∧
      ((2 : ℕ) : ℤ_[2]) ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hπ]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hπ]; ring⟩
  obtain ⟨r, t, hV1⟩ : ∃ r t : ℤ_[2], Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔdvd⟩
  have hval2 := Step2.hasValuation_translate hΔdvd
  rw [hV1] at hval2
  refine ⟨r, t, hV1 ▸ Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄, ?_, ?_⟩
  · simpa only [smul_ofShortNF_a₄, pow_one] using hval2.a₄
  · simpa only [smul_ofShortNF_a₆, pow_one] using hval2.a₆

/-! ### The forward run on the even good-reduction family -/

open scoped Classical in
/-- **The forward run on the even good-reduction family at `2`.** A short model over `ℤ_2` with
`a₄ = 16A` and `a₆ = 16(1 + 4G)` has reduction datum exactly `(I₀, 1)`. -/
theorem run_eq_I0_of_goodEven_two {a₄ a₆ A G : ℤ_[2]} (ha₄ : a₄ = 16 * A)
    (ha₆ : a₆ = 16 * (1 + 4 * G)) (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1 := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_two a₄ a₆
  have hone : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_one]; decide
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[2], r = 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exact ⟨y, hy⟩
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      have h3 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (3 : ℤ_[2]) := by
        rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat]; decide
      rw [hπ, ha₄, hy] at hc
      refine h3 ⟨c - 8 * A - 6 * y - 6 * y ^ 2, ?_⟩
      rw [hπ]
      linear_combination hc
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨8 + 32 * G + 16 * A * ρ + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 4 * A + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2], x = 4 + 16 * G + 8 * A * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 6 * ρ := by
    rw [smul_ofShortNF_a₂, hr]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 4 * τ := by
    rw [smul_ofShortNF_a₃, ht]; ring
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hQ₄]; ring
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, ht, hQ₆]; ring
  have h3run : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, hV1a₆⟩
  have h4run : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨12 * ρ * Q₆ + 12 * ρ * τ ^ 2 - 2 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hπ]; ring
  have h5run : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hπ]; ring
  obtain ⟨nρ, hnρ⟩ : ∃ n : ℤ_[2], ρ ^ 2 - ρ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
    exact ⟨m - ρ, by linear_combination hm⟩
  obtain ⟨nτ, hnτ⟩ : ∃ n : ℤ_[2], τ ^ 2 - τ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
    exact ⟨m - τ, by linear_combination hm⟩
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[2],
      x = Step6.s ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[2],
      x = Step6.t ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℤ_[2], s = 2 * S := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ s - 6 * ρ := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨3 * ρ + j, by linear_combination hj⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℤ_[2], t₆ = Q₆ + 2 * θ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨u₀, hu₀⟩ : ∃ x : ℤ_[2], x = 2 + 8 * G + 4 * A * ρ + ρ ^ 3 - nτ := ⟨_, rfl⟩
  have hu₀v : Q₆ + τ = 2 * u₀ := by rw [hQ₆, hu₀]; linear_combination -hnτ
  obtain ⟨U, hU⟩ : ∃ x : ℤ_[2], x = Q₆ + 2 * θ + τ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = 2 * U := by rw [hT₂, hπ, hθ, ht, hU]; ring
  have hUv : U = 2 * (u₀ + θ) := by rw [hU]; linear_combination hu₀v
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[2], x = 3 * ρ - 2 * S ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[2], x = Q₄ - 2 * S * U := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[2], x = u₀ + nτ - 2 * (u₀ + θ) ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂
      = ((2 : ℕ) : ℤ_[2]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hS, hX₂]; ring
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hS, hT₂v, hX₄, hQ₄]; ring
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 3 * Y := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, hT₂v, hUv, hY, hu₀]; ring
  have hcb : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      ((2 : ℕ) : ℤ_[2])) = _
    rw [div_two_eq_of_eq_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₄]
    exact mod_two_eq_of_dvd_sub ⟨2 * A + 3 * nρ + ρ - S * U, by
      rw [hπ, hX₄, hQ₄]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₆]
    exact mod_two_eq_of_dvd_sub ⟨1 + 4 * G + 2 * A * ρ + nρ * (ρ + 1) - (u₀ + θ) ^ 2, by
      rw [hπ, hY, hu₀]; linear_combination (ρ + 1) * hnρ⟩
  have hdouble := hasDoubleRoot_of_eq_two hp2 (by simp [cubic]) hcb hcc hcd
  have htriple := hasTripleRoot_of_eq_two hp2 hcb hcc
  have h6run : Step6.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    rw [hV2]
    exact ite_eq_left (by rw [← hV2] at hdouble ⊢; exact hdouble)
  have h7run : Step7.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[2],
      x = Step8.r ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ_[2], ρ - r₈ = 2 * D := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_eq_of_eq_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hX₂] at hj
    exact ⟨S ^ 2 - ρ - j, by linear_combination -hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[2], x = 4 * D := ⟨_, rfl⟩
  obtain ⟨W', hW'⟩ : ∃ x : ℤ_[2], x = (u₀ + θ) - r₈ * S := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[2], x = 4 * W' := ⟨_, rfl⟩
  have hV3 : Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆ := by
    have h : Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 (-((2 : ℕ) : ℤ_[2]) * r₈) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₈def]
    rw [h]
    refine smul_smul_eq _ ?_ (by ring) ?_
    · rw [hR₃, hπ, hr]; linear_combination (-2 : ℤ_[2]) * hD
    · rw [hT₃, hT₂v, hπ, hUv, hW', hS]; ring
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * (((2 : ℕ) : ℤ_[2]) * W') := by
    rw [smul_ofShortNF_a₃, hT₃, hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 4 * (1 + 4 * G + 4 * A * D + 4 * D ^ 3 - W' ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hπ, ha₄, ha₆]; ring
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV3a₃, map_mul, mod_self, zero_mul]
  have hq : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).HasDoubleRoot :=
    quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic]) (by simp [quadratic]) hqc
  have h8run : Step8.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by
    rw [Step8.run.eq_def, h7run]
    simp only [except_ok_bind]
    rw [hV3]
    exact ite_eq_left hq
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[2],
      x = Step7.tY ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨mW, hmW⟩ := exists_sq_add_self_eq_two_mul hp2 hπ W'
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℤ_[2], tY + W' = 1 + 2 * ξ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ tY + (1 + 4 * G + 4 * A * D + 4 * D ^ 3 - W' ^ 2) := by
      rw [← mod_eq_zero, map_add, htYdef,
        (Step7.mod_tY_two hp2 ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 :
          mod ((2 : ℕ) : ℤ_[2])
              (Step7.tY ((2 : ℕ) : ℤ_[2])
                ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2)
            = - mod ((2 : ℕ) : ℤ_[2])
                (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
                  (((2 : ℕ) : ℤ_[2]) ^ (2 * 2)))),
        show (2 * 2 : ℕ) = 4 from rfl, div_eq_of_eq_pow_mul_two hV3a₆, neg_add_cancel]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j - 1 - 2 * G - 2 * A * D - 2 * D ^ 3 + mW, by linear_combination hj + hmW⟩
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[2], x = 4 * (tY + W') := ⟨_, rfl⟩
  have hV4 : Step9.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆ := by
    have h : Step9.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 0 (((2 : ℕ) : ℤ_[2]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by rw [htYdef]
    rw [h]
    refine smul_smul_eq _ (by ring) (by ring) ?_
    rw [hT₄, hT₃, hπ]; ring
  have hV4a₄ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 4 * (A + 3 * D ^ 2 - S * (tY + W')) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, hπ, ha₄, hS]; ring
  have hV4a₆ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 6 * (G + A * D + D ^ 3 - ξ - ξ ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₄, hπ, ha₄, ha₆]
    linear_combination (-16 * (tY + W' + 1 + 2 * ξ) : ℤ_[2]) * hξ
  have h9run : Step9.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step9.run.eq_def, h8run]
    simp only [except_ok_bind]
    rw [hV4]
    exact ite_eq_left ⟨_, hV4a₄⟩
  have h10run : Step10.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step10.run.eq_def, h9run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨_, hV4a₆⟩
  obtain ⟨V, hV⟩ : ∃ V, Step11.run PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V :=
    ⟨Step11.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆), by
      rw [Step11.run.eq_def, h10run]; rfl⟩
  have hΔV : ((2 : ℕ) : ℤ_[2]) ^ 12 * V.Δ = (ofShortNF a₄ a₆).Δ :=
    Step11.run_Δ PadicInt.uniformizer_ne_zero hΔ0 hV
  have h4096 : ((2 : ℕ) : ℤ_[2]) ^ 12 = 4096 := by rw [hπ]; norm_num
  have hne : (4096 : ℤ_[2]) ≠ 0 := by
    rw [← h4096]; exact pow_ne_zero 12 PadicInt.uniformizer_ne_zero
  have hVΔ : V.Δ = -(1 + 2 * (13 + 32 * A ^ 3 + 108 * G + 216 * G ^ 2)) := by
    refine mul_left_cancel₀ hne ?_
    rw [← h4096, hΔV, ofShortNF_Δ, ha₄, ha₆]
    ring
  have hVdvd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ V.Δ :=
    not_dvd_of_eq_one_add_two_mul (y := -1 - (13 + 32 * A ^ 3 + 108 * G + 216 * G ^ 2))
      (by rw [hVΔ]; ring)
  have hVne : V.Δ ≠ 0 := fun h0 => hVdvd (h0 ▸ dvd_zero _)
  have hs1 : Step1.run ((2 : ℕ) : ℤ_[2]) V = Except.error ⟨V, KodairaSymbol.I 0, 1⟩ := by
    rw [Step1.run.eq_def]; exact ite_eq_right hVdvd
  have hrun : TateAlgorithm.run (W := ofShortNF a₄ a₆) PadicInt.uniformizer_ne_zero hΔ0
      = ⟨V, KodairaSymbol.I 0, 1⟩ := by
    rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ0 hV hVne]
    exact run_eq_of_step11_error PadicInt.uniformizer_ne_zero hVne
      (step11_error_of_step2 hVne (step2_error_of_step1 hs1))
  exact ⟨by rw [hrun], by rw [hrun]⟩

/-! ### The forward run on the odd `III*` family -/

open scoped Classical in
/-- **The forward run at `III*` on the odd family at `2`.** A short model over `ℤ_2` with
`a₄ = 5 + 8A` and `a₆ = 6 + 24A + 32E` has reduction datum exactly `(III*, 2)`. -/
theorem run_eq_IIIstarOdd_two {a₄ a₆ A E : ℤ_[2]} (ha₄ : a₄ = 5 + 8 * A)
    (ha₆ : a₆ = 6 + 24 * A + 32 * E) (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.III! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 2 := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_two a₄ a₆
  have hone : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_one]; decide
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[2], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hπ, ha₄, hy] at hc
      refine hone ⟨c - 4 * A - 6 * y ^ 2 - 2, ?_⟩
      rw [hπ]
      linear_combination hc
    · exact ⟨y, hy⟩
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨6 + 16 * A + 16 * E + 8 * ρ + 8 * A * ρ + 6 * ρ ^ 2 + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨nρ, hnρ⟩ : ∃ n : ℤ_[2], ρ ^ 2 - ρ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
    exact ⟨m - ρ, by linear_combination hm⟩
  obtain ⟨nτ, hnτ⟩ : ∃ n : ℤ_[2], τ ^ 2 - τ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
    exact ⟨m - τ, by linear_combination hm⟩
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 2 + 2 * A + 3 * ρ + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2],
      x = 3 + 8 * A + 8 * E + 4 * ρ + 4 * A * ρ + 3 * ρ ^ 2 + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 + 6 * ρ := by
    rw [smul_ofShortNF_a₂, hr]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 4 * τ := by
    rw [smul_ofShortNF_a₃, ht]; ring
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hQ₄]; ring
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, ht, hQ₆]; ring
  have h3run : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, hV1a₆⟩
  have h4run : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * Q₆ + 12 * ρ * Q₆ + 6 * τ ^ 2 + 12 * ρ * τ ^ 2 - 2 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hπ]; ring
  have h5run : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hπ]; ring
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[2],
      x = Step6.s ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[2],
      x = Step6.t ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℤ_[2], s = 1 + 2 * S := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ s - (3 + 6 * ρ) := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨1 + 3 * ρ + j, by linear_combination hj⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℤ_[2], t₆ = Q₆ + 2 * θ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℤ_[2], v = 1 + 4 * A + 4 * E + 4 * ρ + 2 * A * ρ + 5 * nρ
      + 2 * ρ * nρ - nτ := ⟨_, rfl⟩
  have hv₀v : Q₆ + τ = 1 + ρ + 2 * v₀ := by
    rw [hQ₆, hv₀]; linear_combination (2 * ρ + 5) * hnρ - hnτ
  obtain ⟨U, hU⟩ : ∃ x : ℤ_[2], x = Q₆ + 2 * θ + τ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = 2 * U := by rw [hT₂, hπ, hθ, ht, hU]; ring
  have hUv : U = 1 + ρ + 2 * (v₀ + θ) := by rw [hU]; linear_combination hv₀v
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[2], x = 1 + 3 * ρ - 2 * S - 2 * S ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[2], x = Q₄ - U - 2 * S * U := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[2], x = v₀ + nτ - nρ - ρ - 2 * (v₀ + θ) - 2 * ρ * (v₀ + θ)
      - 2 * (v₀ + θ) ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂
      = ((2 : ℕ) : ℤ_[2]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hS, hX₂]; ring
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hS, hT₂v, hX₄, hQ₄]; ring
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 3 * Y := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, hT₂v, hUv, hY, hv₀]
    linear_combination (8 * ρ + 16) * hnρ
  have hcb : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      ((2 : ℕ) : ℤ_[2])) = _
    rw [div_two_eq_of_eq_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₄]
    exact mod_two_eq_of_dvd_sub ⟨A + 2 * ρ + 3 * nρ - (v₀ + θ) - S * (1 + ρ + 2 * (v₀ + θ)), by
      rw [hπ, hX₄, hQ₄, hUv]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₆]
    exact mod_two_eq_of_dvd_sub
      ⟨2 * A + 2 * E + ρ + A * ρ + 2 * nρ + ρ * nρ - (v₀ + θ) - ρ * (v₀ + θ) - (v₀ + θ) ^ 2, by
        rw [hπ, hY]; linear_combination hv₀⟩
  have hdouble := hasDoubleRoot_of_eq_two hp2 (by simp [cubic]) hcb hcc hcd
  have htriple := hasTripleRoot_of_eq_two hp2 hcb hcc
  have h6run : Step6.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    rw [hV2]
    exact ite_eq_left (by rw [← hV2] at hdouble ⊢; exact hdouble)
  have h7run : Step7.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W'' heq =>
        obtain rfl : W'' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[2],
      x = Step8.r ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℤ_[2], ρ - r₈ = 1 + 2 * h := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_eq_of_eq_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := hdv
    rw [hπ, hX₂] at hj
    exact ⟨-1 - ρ + S + S ^ 2 - j, by linear_combination -hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[2], x = 3 + 4 * h := ⟨_, rfl⟩
  obtain ⟨W₃, hW₃⟩ : ∃ x : ℤ_[2], x = U - r₈ - 2 * r₈ * S := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[2], x = 2 * W₃ := ⟨_, rfl⟩
  have hV3 : Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆ := by
    have hst : Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 (-((2 : ℕ) : ℤ_[2]) * r₈) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₈def]
    rw [hst]
    refine smul_smul_eq _ ?_ (by ring) ?_
    · rw [hR₃, hπ, hr]; linear_combination (-2 : ℤ_[2]) * hh
    · rw [hT₃, hT₂v, hπ, hW₃, hS]; ring
  obtain ⟨W', hW'⟩ : ∃ W' : ℤ_[2], W₃ = 2 * W' :=
    ⟨1 + (v₀ + θ) + h - r₈ * S, by rw [hW₃, hUv]; linear_combination hh⟩
  obtain ⟨mh, hmh⟩ := exists_sq_add_self_eq_two_mul hp2 hπ h
  obtain ⟨mW, hmW⟩ := exists_sq_add_self_eq_two_mul hp2 hπ W'
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * (((2 : ℕ) : ℤ_[2]) * W') := by
    rw [smul_ofShortNF_a₃, hT₃, hW', hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 4
        * (3 + 3 * A + 2 * E + 8 * h + 2 * A * h + 9 * h ^ 2 + 4 * h ^ 3 - W' ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hW', hπ, ha₄, ha₆]; ring
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV3a₃, map_mul, mod_self, zero_mul]
  have hq : (quadratic ((2 : ℕ) : ℤ_[2]) (Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)) 2).HasDoubleRoot := by
    rw [hV3]
    exact quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic]) (by simp [quadratic]) hqc
  have h8run := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7run hq
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[2],
      x = Step7.tY ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℤ_[2], tY + W' + A + h = 1 + 2 * μ := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ tY
        + (3 + 3 * A + 2 * E + 8 * h + 2 * A * h + 9 * h ^ 2 + 4 * h ^ 3 - W' ^ 2) := by
      rw [← mod_eq_zero, map_add, htYdef,
        (Step7.mod_tY_two hp2 ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 :
          mod ((2 : ℕ) : ℤ_[2])
              (Step7.tY ((2 : ℕ) : ℤ_[2])
                ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2)
            = - mod ((2 : ℕ) : ℤ_[2])
                (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
                  (((2 : ℕ) : ℤ_[2]) ^ (2 * 2)))),
        show (2 * 2 : ℕ) = 4 from rfl, div_eq_of_eq_pow_mul_two hV3a₆, neg_add_cancel]
    obtain ⟨j, hj⟩ := hdv
    rw [hπ] at hj
    exact ⟨j - 2 - A - E - A * h - 5 * mh - 4 * h * mh + mW - h, by
      linear_combination hj + hmW + (-4 * h - 5) * hmh⟩
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[2], x = 4 * (tY + W') := ⟨_, rfl⟩
  have hV4 : Step9.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆ := by
    have hst : Step9.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 0 (((2 : ℕ) : ℤ_[2]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by rw [htYdef]
    rw [hst]
    refine smul_smul_eq _ (by ring) (by ring) ?_
    rw [hT₄, hT₃, hW', hπ]; ring
  have hV4a₄ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₄
      = 8 + 16 * (1 + A + 2 * h + 6 * mh - μ - S * (tY + W')) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, ha₄, hS]
    linear_combination (-8 : ℤ_[2]) * hμ + 48 * hmh
  have ha₄' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ (Step9.translate ((2 : ℕ) : ℤ_[2])
      (Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆))).a₄ := by
    rw [hV3, hV4, hV4a₄]
    rintro ⟨m, hm⟩
    rw [hπ] at hm
    have h8ne : (8 : ℤ_[2]) ≠ 0 := by
      rw [show (8 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 3 by norm_num]
      exact pow_ne_zero 3 PadicInt.uniformizer_ne_zero
    refine hone ⟨m - (1 + A + 2 * h + 6 * mh - μ - S * (tY + W')), ?_⟩
    refine mul_left_cancel₀ h8ne ?_
    rw [hπ]
    linear_combination hm
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step9 hΔ0 (step9_run_eq_error_of_not_dvd hΔ0 h8run ha₄'))]
  exact ⟨rfl, rfl⟩

/-! ### The forward run on the odd `II*` family -/

open scoped Classical in
/-- **The forward run at `II*` on the odd family at `2`.** A short model over `ℤ_2` with
`a₄ = 5 + 8A` and `a₆ = 54 + 40A + 16A² + 64G` has reduction datum exactly `(II*, 1)`. -/
theorem run_eq_IIstarOdd_two {a₄ a₆ A G : ℤ_[2]} (ha₄ : a₄ = 5 + 8 * A)
    (ha₆ : a₆ = 54 + 40 * A + 16 * A ^ 2 + 64 * G) (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.II! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1 := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_two a₄ a₆
  have hone : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_one]; decide
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[2], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hπ, ha₄, hy] at hc
      refine hone ⟨c - 4 * A - 6 * y ^ 2 - 2, ?_⟩
      rw [hπ]
      linear_combination hc
    · exact ⟨y, hy⟩
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨30 + 24 * A + 8 * A ^ 2 + 32 * G + 8 * ρ + 8 * A * ρ + 6 * ρ ^ 2
        + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨nρ, hnρ⟩ : ∃ n : ℤ_[2], ρ ^ 2 - ρ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
    exact ⟨m - ρ, by linear_combination hm⟩
  obtain ⟨nτ, hnτ⟩ : ∃ n : ℤ_[2], τ ^ 2 - τ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
    exact ⟨m - τ, by linear_combination hm⟩
  obtain ⟨mA, hmA⟩ := exists_sq_add_self_eq_two_mul hp2 hπ A
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 2 + 2 * A + 3 * ρ + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2],
      x = 15 + 12 * A + 4 * A ^ 2 + 16 * G + 4 * ρ + 4 * A * ρ + 3 * ρ ^ 2 + 2 * ρ ^ 3
        - τ ^ 2 := ⟨_, rfl⟩
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 + 6 * ρ := by
    rw [smul_ofShortNF_a₂, hr]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 4 * τ := by
    rw [smul_ofShortNF_a₃, ht]; ring
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hQ₄]; ring
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, ht, hQ₆]; ring
  have h3run : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, hV1a₆⟩
  have h4run : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * Q₆ + 12 * ρ * Q₆ + 6 * τ ^ 2 + 12 * ρ * τ ^ 2 - 2 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hπ]; ring
  have h5run : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hπ]; ring
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[2],
      x = Step6.s ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[2],
      x = Step6.t ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℤ_[2], s = 1 + 2 * S := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ s - (3 + 6 * ρ) := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨1 + 3 * ρ + j, by linear_combination hj⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℤ_[2], t₆ = Q₆ + 2 * θ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℤ_[2], v = 7 + 4 * A + 4 * mA + 8 * G + 4 * ρ + 2 * A * ρ + 5 * nρ
      + 2 * ρ * nρ - nτ := ⟨_, rfl⟩
  have hv₀v : Q₆ + τ = 1 + ρ + 2 * v₀ := by
    rw [hQ₆, hv₀]; linear_combination 4 * hmA + (2 * ρ + 5) * hnρ - hnτ
  obtain ⟨U, hU⟩ : ∃ x : ℤ_[2], x = Q₆ + 2 * θ + τ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = 2 * U := by rw [hT₂, hπ, hθ, ht, hU]; ring
  have hUv : U = 1 + ρ + 2 * (v₀ + θ) := by rw [hU]; linear_combination hv₀v
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[2], x = 1 + 3 * ρ - 2 * S - 2 * S ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[2], x = Q₄ - U - 2 * S * U := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[2], x = v₀ + nτ - nρ - ρ - 2 * (v₀ + θ) - 2 * ρ * (v₀ + θ)
      - 2 * (v₀ + θ) ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂
      = ((2 : ℕ) : ℤ_[2]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hS, hX₂]; ring
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hS, hT₂v, hX₄, hQ₄]; ring
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 3 * Y := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, hT₂v, hUv, hY, hv₀]
    linear_combination 16 * hmA + (8 * ρ + 16) * hnρ
  have hcb : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      ((2 : ℕ) : ℤ_[2])) = _
    rw [div_two_eq_of_eq_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₄]
    exact mod_two_eq_of_dvd_sub ⟨A + 2 * ρ + 3 * nρ - (v₀ + θ) - S * (1 + ρ + 2 * (v₀ + θ)), by
      rw [hπ, hX₄, hQ₄, hUv]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₆]
    exact mod_two_eq_of_dvd_sub ⟨3 + 2 * A + 2 * mA + 4 * G + ρ + A * ρ + 2 * nρ + ρ * nρ - (v₀ + θ)
      - ρ * (v₀ + θ) - (v₀ + θ) ^ 2, by rw [hπ, hY]; linear_combination hv₀⟩
  have hdouble := hasDoubleRoot_of_eq_two hp2 (by simp [cubic]) hcb hcc hcd
  have htriple := hasTripleRoot_of_eq_two hp2 hcb hcc
  have h6run : Step6.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    rw [hV2]
    exact ite_eq_left (by rw [← hV2] at hdouble ⊢; exact hdouble)
  have h7run : Step7.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W'' heq =>
        obtain rfl : W'' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[2],
      x = Step8.r ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℤ_[2], ρ - r₈ = 1 + 2 * h := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_eq_of_eq_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := hdv
    rw [hπ, hX₂] at hj
    exact ⟨-1 - ρ + S + S ^ 2 - j, by linear_combination -hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[2], x = 3 + 4 * h := ⟨_, rfl⟩
  obtain ⟨W₃, hW₃⟩ : ∃ x : ℤ_[2], x = U - r₈ - 2 * r₈ * S := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[2], x = 2 * W₃ := ⟨_, rfl⟩
  have hV3 : Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆ := by
    have hst : Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 (-((2 : ℕ) : ℤ_[2]) * r₈) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₈def]
    rw [hst]
    refine smul_smul_eq _ ?_ (by ring) ?_
    · rw [hR₃, hπ, hr]; linear_combination (-2 : ℤ_[2]) * hh
    · rw [hT₃, hT₂v, hπ, hW₃, hS]; ring
  obtain ⟨W', hW'⟩ : ∃ W' : ℤ_[2], W₃ = 2 * W' :=
    ⟨1 + (v₀ + θ) + h - r₈ * S, by rw [hW₃, hUv]; linear_combination hh⟩
  obtain ⟨mh, hmh⟩ := exists_sq_add_self_eq_two_mul hp2 hπ h
  obtain ⟨mW, hmW⟩ := exists_sq_add_self_eq_two_mul hp2 hπ W'
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * (((2 : ℕ) : ℤ_[2]) * W') := by
    rw [smul_ofShortNF_a₃, hT₃, hW', hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 4
        * (6 + 4 * A + A ^ 2 + 4 * G + 8 * h + 2 * A * h + 9 * h ^ 2 + 4 * h ^ 3
          - W' ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hW', hπ, ha₄, ha₆]; ring
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV3a₃, map_mul, mod_self, zero_mul]
  have hq : (quadratic ((2 : ℕ) : ℤ_[2]) (Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)) 2).HasDoubleRoot := by
    rw [hV3]
    exact quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic]) (by simp [quadratic]) hqc
  have h8run := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7run hq
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[2],
      x = Step7.tY ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ_[2], tY + W' = A + h + 2 * κ := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ tY
        + (6 + 4 * A + A ^ 2 + 4 * G + 8 * h + 2 * A * h + 9 * h ^ 2 + 4 * h ^ 3
          - W' ^ 2) := by
      rw [← mod_eq_zero, map_add, htYdef,
        (Step7.mod_tY_two hp2 ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 :
          mod ((2 : ℕ) : ℤ_[2])
              (Step7.tY ((2 : ℕ) : ℤ_[2])
                ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2)
            = - mod ((2 : ℕ) : ℤ_[2])
                (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
                  (((2 : ℕ) : ℤ_[2]) ^ (2 * 2)))),
        show (2 * 2 : ℕ) = 4 from rfl, div_eq_of_eq_pow_mul_two hV3a₆, neg_add_cancel]
    obtain ⟨j, hj⟩ := hdv
    rw [hπ] at hj
    exact ⟨j - 3 - 2 * A - mA - 2 * G - A * h + mW - 5 * mh - 4 * h * mh - 2 * h, by
      linear_combination hj + hmW - hmA + (-4 * h - 5) * hmh⟩
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[2], x = 4 * (tY + W') := ⟨_, rfl⟩
  have hV4 : Step9.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆ := by
    have hst : Step9.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 0 (((2 : ℕ) : ℤ_[2]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by rw [htYdef]
    rw [hst]
    refine smul_smul_eq _ (by ring) (by ring) ?_
    rw [hT₄, hT₃, hW', hπ]; ring
  have hV4a₄ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 4 * (2 + h + 6 * mh - κ - S * (tY + W')) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, hπ, ha₄, hS]
    linear_combination (-8 : ℤ_[2]) * hκ + 48 * hmh
  have hV4a₆ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₆
      = 32 * (1 + 2 * (1 + A + G + 2 * h + 2 * h ^ 2 + h ^ 3 - κ ^ 2 - A * κ - h * κ)) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₄, ha₄, ha₆]
    linear_combination (-16 * (tY + W' + A + h + 2 * κ) : ℤ_[2]) * hκ
  have ha₄' : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ (Step9.translate ((2 : ℕ) : ℤ_[2])
      (Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆))).a₄ := by
    rw [hV3, hV4]
    exact ⟨_, hV4a₄⟩
  have h9run := step9_run_eq_ok_of_dvd hΔ0 h8run ha₄'
  have ha₆' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ (Step9.translate ((2 : ℕ) : ℤ_[2])
      (Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆))).a₆ := by
    rw [hV3, hV4, hV4a₆]
    rintro ⟨m, hm⟩
    rw [hπ] at hm
    have h32ne : (32 : ℤ_[2]) ≠ 0 := by
      rw [show (32 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 5 by norm_num]
      exact pow_ne_zero 5 PadicInt.uniformizer_ne_zero
    refine hone ⟨m - (1 + A + G + 2 * h + 2 * h ^ 2 + h ^ 3 - κ ^ 2 - A * κ - h * κ), ?_⟩
    refine mul_left_cancel₀ h32ne ?_
    rw [hπ]
    linear_combination hm
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step10 hΔ0 (step10_run_eq_error_of_not_dvd hΔ0 h9run ha₆'))]
  exact ⟨rfl, rfl⟩

/-! ### The forward run on the mirror good-reduction family -/

open scoped Classical in
/-- **The forward run on the mirror good-reduction family at `2`.** A short model over `ℤ_2` with
`a₄ = 13 + 16α` and `a₆ = 14 + 80α + 128k` has reduction datum exactly `(I₀, 1)`. -/
theorem run_eq_I0_of_goodOdd_two {a₄ a₆ α k : ℤ_[2]} (ha₄ : a₄ = 13 + 16 * α)
    (ha₆ : a₆ = 14 + 80 * α + 128 * k) (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1 := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_two a₄ a₆
  have hone : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_one]; decide
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[2], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hπ, ha₄, hy] at hc
      refine hone ⟨c - 8 * α - 6 * y ^ 2 - 6, ?_⟩
      rw [hπ]
      linear_combination hc
    · exact ⟨y, hy⟩
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨14 + 48 * α + 64 * k + 16 * ρ + 16 * α * ρ + 6 * ρ ^ 2 + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨nρ, hnρ⟩ : ∃ n : ℤ_[2], ρ ^ 2 - ρ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
    exact ⟨m - ρ, by linear_combination hm⟩
  obtain ⟨nτ, hnτ⟩ : ∃ n : ℤ_[2], τ ^ 2 - τ = 2 * n := by
    obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
    exact ⟨m - τ, by linear_combination hm⟩
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 4 + 4 * α + 3 * ρ + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2],
      x = 7 + 24 * α + 32 * k + 8 * ρ + 8 * α * ρ + 3 * ρ ^ 2 + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 + 6 * ρ := by
    rw [smul_ofShortNF_a₂, hr]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 4 * τ := by
    rw [smul_ofShortNF_a₃, ht]; ring
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hQ₄]; ring
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, ht, hQ₆]; ring
  have h3run : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, hV1a₆⟩
  have h4run : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * Q₆ + 12 * ρ * Q₆ + 6 * τ ^ 2 + 12 * ρ * τ ^ 2 - 2 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hπ]; ring
  have h5run : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hπ]; ring
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[2],
      x = Step6.s ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[2],
      x = Step6.t ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℤ_[2], s = 1 + 2 * S := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ s - (3 + 6 * ρ) := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨1 + 3 * ρ + j, by linear_combination hj⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℤ_[2], t₆ = Q₆ + 2 * θ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℤ_[2], v = 3 + 12 * α + 16 * k + 6 * ρ + 4 * α * ρ + 5 * nρ
      + 2 * ρ * nρ - nτ := ⟨_, rfl⟩
  have hv₀v : Q₆ + τ = 1 + ρ + 2 * v₀ := by
    rw [hQ₆, hv₀]; linear_combination (2 * ρ + 5) * hnρ - hnτ
  obtain ⟨U, hU⟩ : ∃ x : ℤ_[2], x = Q₆ + 2 * θ + τ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = 2 * U := by rw [hT₂, hπ, hθ, ht, hU]; ring
  have hUv : U = 1 + ρ + 2 * (v₀ + θ) := by rw [hU]; linear_combination hv₀v
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[2], x = 1 + 3 * ρ - 2 * S - 2 * S ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[2], x = Q₄ - U - 2 * S * U := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[2], x = v₀ + nτ - nρ - ρ - 2 * (v₀ + θ) - 2 * ρ * (v₀ + θ)
      - 2 * (v₀ + θ) ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂
      = ((2 : ℕ) : ℤ_[2]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hS, hX₂]; ring
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hS, hT₂v, hX₄, hQ₄]; ring
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 3 * Y := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, hT₂v, hUv, hY, hv₀]
    linear_combination (8 * ρ + 16) * hnρ
  have hcb : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      ((2 : ℕ) : ℤ_[2])) = _
    rw [div_two_eq_of_eq_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₄]
    exact mod_two_eq_of_dvd_sub
      ⟨1 + 2 * α + 2 * ρ + 3 * nρ - (v₀ + θ) - S * (1 + ρ + 2 * (v₀ + θ)), by
      rw [hπ, hX₄, hQ₄, hUv]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₆]
    exact mod_two_eq_of_dvd_sub ⟨1 + 6 * α + 8 * k + 2 * ρ + 2 * α * ρ + 2 * nρ + ρ * nρ - (v₀ + θ)
      - ρ * (v₀ + θ) - (v₀ + θ) ^ 2, by rw [hπ, hY]; linear_combination hv₀⟩
  have hdouble := hasDoubleRoot_of_eq_two hp2 (by simp [cubic]) hcb hcc hcd
  have htriple := hasTripleRoot_of_eq_two hp2 hcb hcc
  have h6run : Step6.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    rw [hV2]
    exact ite_eq_left (by rw [← hV2] at hdouble ⊢; exact hdouble)
  have h7run : Step7.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W'' heq =>
        obtain rfl : W'' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[2],
      x = Step8.r ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℤ_[2], ρ - r₈ = 1 + 2 * h := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_eq_of_eq_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := hdv
    rw [hπ, hX₂] at hj
    exact ⟨-1 - ρ + S + S ^ 2 - j, by linear_combination -hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[2], x = 3 + 4 * h := ⟨_, rfl⟩
  obtain ⟨W₃, hW₃⟩ : ∃ x : ℤ_[2], x = U - r₈ - 2 * r₈ * S := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[2], x = 2 * W₃ := ⟨_, rfl⟩
  have hV3 : Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆ := by
    have hst : Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 (-((2 : ℕ) : ℤ_[2]) * r₈) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₈def]
    rw [hst]
    refine smul_smul_eq _ ?_ (by ring) ?_
    · rw [hR₃, hπ, hr]; linear_combination (-2 : ℤ_[2]) * hh
    · rw [hT₃, hT₂v, hπ, hW₃, hS]; ring
  obtain ⟨W', hW'⟩ : ∃ W' : ℤ_[2], W₃ = 2 * W' :=
    ⟨1 + (v₀ + θ) + h - r₈ * S, by rw [hW₃, hUv]; linear_combination hh⟩
  obtain ⟨mh, hmh⟩ := exists_sq_add_self_eq_two_mul hp2 hπ h
  obtain ⟨mW, hmW⟩ := exists_sq_add_self_eq_two_mul hp2 hπ W'
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * (((2 : ℕ) : ℤ_[2]) * W') := by
    rw [smul_ofShortNF_a₃, hT₃, hW', hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 4
        * (5 + 8 * α + 8 * k + 10 * h + 4 * α * h + 9 * h ^ 2 + 4 * h ^ 3 - W' ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hW', hπ, ha₄, ha₆]; ring
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV3a₃, map_mul, mod_self, zero_mul]
  have hq : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).HasDoubleRoot :=
    quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic]) (by simp [quadratic]) hqc
  have h8run : Step8.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by
    rw [Step8.run.eq_def, h7run]
    simp only [except_ok_bind]
    rw [hV3]
    exact ite_eq_left hq
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[2],
      x = Step7.tY ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ l : ℤ_[2], tY + W' = 1 + h + 2 * l := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ tY
        + (5 + 8 * α + 8 * k + 10 * h + 4 * α * h + 9 * h ^ 2 + 4 * h ^ 3 - W' ^ 2) := by
      rw [← mod_eq_zero, map_add, htYdef,
        (Step7.mod_tY_two hp2 ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 :
          mod ((2 : ℕ) : ℤ_[2])
              (Step7.tY ((2 : ℕ) : ℤ_[2])
                ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2)
            = - mod ((2 : ℕ) : ℤ_[2])
                (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
                  (((2 : ℕ) : ℤ_[2]) ^ (2 * 2)))),
        show (2 * 2 : ℕ) = 4 from rfl, div_eq_of_eq_pow_mul_two hV3a₆, neg_add_cancel]
    obtain ⟨j, hj⟩ := hdv
    rw [hπ] at hj
    exact ⟨j - 3 - 4 * α - 4 * k - 2 * α * h - 5 * mh - 4 * h * mh - 3 * h + mW, by
      linear_combination hj + hmW + (-4 * h - 5) * hmh⟩
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[2], x = 4 * (tY + W') := ⟨_, rfl⟩
  have hV4 : Step9.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆ := by
    have hst : Step9.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 0 (((2 : ℕ) : ℤ_[2]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by rw [htYdef]
    rw [hst]
    refine smul_smul_eq _ (by ring) (by ring) ?_
    rw [hT₄, hT₃, hW', hπ]; ring
  have hV4a₄ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 4 * (2 + α + h + 6 * mh - lam - S * (tY + W')) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, hπ, ha₄, hS]
    linear_combination (-8 : ℤ_[2]) * hlam + 48 * hmh
  have hV4a₆ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 6 * (1 + 2 * α + 2 * k + 2 * h + α * h + 2 * h ^ 2 + h ^ 3
        - lam ^ 2 - lam - h * lam) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₄, hπ, ha₄, ha₆]
    linear_combination (-16 * (tY + W' + 1 + h + 2 * lam) : ℤ_[2]) * hlam
  have h9run : Step9.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step9.run.eq_def, h8run]
    simp only [except_ok_bind]
    rw [hV4]
    exact ite_eq_left ⟨_, hV4a₄⟩
  have h10run : Step10.run PadicInt.uniformizer_ne_zero hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step10.run.eq_def, h9run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨_, hV4a₆⟩
  obtain ⟨mα, hmα⟩ := exists_sq_add_self_eq_two_mul hp2 hπ α
  obtain ⟨V, hV⟩ : ∃ V, Step11.run PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V :=
    ⟨Step11.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆), by
      rw [Step11.run.eq_def, h10run]; rfl⟩
  have hΔV : ((2 : ℕ) : ℤ_[2]) ^ 12 * V.Δ = (ofShortNF a₄ a₆).Δ :=
    Step11.run_Δ PadicInt.uniformizer_ne_zero hΔ0 hV
  have h4096 : ((2 : ℕ) : ℤ_[2]) ^ 12 = 4096 := by rw [hπ]; norm_num
  have hne : (4096 : ℤ_[2]) ≠ 0 := by
    rw [← h4096]; exact pow_ne_zero 12 PadicInt.uniformizer_ne_zero
  have hVΔ : V.Δ = -(1 + 2 * (mα + 27 + 181 * α + 415 * α ^ 2 + 32 * α ^ 3 + 189 * k
      + 1080 * α * k + 864 * k ^ 2)) := by
    refine mul_left_cancel₀ hne ?_
    rw [← h4096, hΔV, ofShortNF_Δ, ha₄, ha₆]
    linear_combination (-4096 : ℤ_[2]) * hmα
  have hVdvd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ V.Δ :=
    not_dvd_of_eq_one_add_two_mul
      (y := -1 - (mα + 27 + 181 * α + 415 * α ^ 2 + 32 * α ^ 3 + 189 * k + 1080 * α * k
        + 864 * k ^ 2)) (by rw [hVΔ]; ring)
  have hVne : V.Δ ≠ 0 := fun h0 => hVdvd (h0 ▸ dvd_zero _)
  have hs1 : Step1.run ((2 : ℕ) : ℤ_[2]) V = Except.error ⟨V, KodairaSymbol.I 0, 1⟩ := by
    rw [Step1.run.eq_def]; exact ite_eq_right hVdvd
  have hrun : TateAlgorithm.run (W := ofShortNF a₄ a₆) PadicInt.uniformizer_ne_zero hΔ0
      = ⟨V, KodairaSymbol.I 0, 1⟩ := by
    rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ0 hV hVne]
    exact run_eq_of_step11_error PadicInt.uniformizer_ne_zero hVne
      (step11_error_of_step2 hVne (step2_error_of_step1 hs1))
  exact ⟨by rw [hrun], by rw [hrun]⟩

end TateAlgorithm

end WeierstrassCurve

end
