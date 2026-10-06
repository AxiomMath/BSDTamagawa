/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityWildIVNonSplit
public import BSDTamagawa.NumberTheory.HeadDensityOne
public import BSDTamagawa.NumberTheory.SplitStoreyDescentTwo
public import BSDTamagawa.NumberTheory.HeadDensityTwo

/-!
# Tate's algorithm on the starred families at `p = 2`

The four parametrised families of the coefficient plane at `2` that cover the starred strata
`IV*`, `III*` and `II*` are nonsingular, and Tate's algorithm on them runs to `IV*` (with
Tamagawa number `3` or `1` by the parity of the parameter `F`), `III*` and `II*`.

## Main results

* `WeierstrassCurve.TateAlgorithm.run_eq_IVstarEven_two`,
  `WeierstrassCurve.TateAlgorithm.run_eq_IVstarOdd_two`,
  `WeierstrassCurve.TateAlgorithm.run_eq_IIIstarEven_two`,
  `WeierstrassCurve.TateAlgorithm.run_eq_IIstarEven_two`: Tate's algorithm on the four families.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal CharP

@[expose] public section

namespace WeierstrassCurve

/-! ### The parametrised families are nonsingular

`Δ = -16(4a₄³ + 27a₆²)` and on each `IV*` family that is `-256` times an odd element of `ℤ_2`, so
`v_2(Δ) = 8`. -/

/-- **`Δ ≠ 0` on the even family**, `a₄ = 8A` and `a₆ = 4 + 16F`: there
`4a₄³ + 27a₆² = 16(128A³ + 27 + 216F + 432F²)` and the bracket is odd. -/
theorem ofShortNF_Δ_ne_zero_of_IVstarEven {a₄ a₆ A F : ℤ_[2]} (ha₄ : a₄ = 8 * A)
    (ha₆ : a₆ = 4 + 16 * F) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  intro hzero
  rw [ofShortNF_Δ, ha₄, ha₆] at hzero
  have hprod : (256 : ℤ_[2]) * (128 * A ^ 3 + 27 + 216 * F + 432 * F ^ 2) = 0 := by
    linear_combination -hzero
  have h256 : (256 : ℤ_[2]) ≠ 0 := by
    rw [show (256 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 8 by norm_num]
    exact pow_ne_zero 8 PadicInt.uniformizer_ne_zero
  have hbr : (128 * A ^ 3 + 27 + 216 * F + 432 * F ^ 2 : ℤ_[2]) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left h256
  refine not_two_dvd_twentySeven ⟨-(64 * A ^ 3 + 108 * F + 216 * F ^ 2), ?_⟩
  rw [show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]
  linear_combination hbr

/-- **`Δ ≠ 0` on the odd family**, `a₄ = 1 + 8A` and `a₆ = 6 + 8A + 16F`: there
`4a₄³ + 27a₆² = 16(61 + 168A + 324F + 156A² + 432AF + 432F² + 128A³)` and the bracket is odd. -/
theorem ofShortNF_Δ_ne_zero_of_IVstarOdd {a₄ a₆ A F : ℤ_[2]} (ha₄ : a₄ = 1 + 8 * A)
    (ha₆ : a₆ = 6 + 8 * A + 16 * F) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  intro hzero
  rw [ofShortNF_Δ, ha₄, ha₆] at hzero
  have hprod : (256 : ℤ_[2]) * (61 + 168 * A + 324 * F + 156 * A ^ 2 + 432 * A * F
      + 432 * F ^ 2 + 128 * A ^ 3) = 0 := by linear_combination -hzero
  have h256 : (256 : ℤ_[2]) ≠ 0 := by
    rw [show (256 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 8 by norm_num]
    exact pow_ne_zero 8 PadicInt.uniformizer_ne_zero
  have hbr : (61 + 168 * A + 324 * F + 156 * A ^ 2 + 432 * A * F + 432 * F ^ 2
      + 128 * A ^ 3 : ℤ_[2]) = 0 := (mul_eq_zero.mp hprod).resolve_left h256
  have h61 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (61 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat]; decide
  refine h61 ⟨-(84 * A + 162 * F + 78 * A ^ 2 + 216 * A * F + 216 * F ^ 2 + 64 * A ^ 3), ?_⟩
  rw [show ((2 : ℕ) : ℤ_[2]) = 2 by norm_num]
  linear_combination hbr

/-- **`Δ ≠ 0` on the `III*` family**, `a₄ = 8 + 16A` and `a₆ = 16E`. -/
theorem ofShortNF_Δ_ne_zero_of_IIIstarEven {a₄ a₆ A E : ℤ_[2]} (ha₄ : a₄ = 8 + 16 * A)
    (ha₆ : a₆ = 16 * E) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have h2 : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hone : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_one]; decide
  have h27 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (27 : ℤ_[2]) := not_two_dvd_twentySeven
  intro hzero
  rw [ofShortNF_Δ, ha₄, ha₆] at hzero
  have hprod : (4096 : ℤ_[2]) * (8 * (1 + 2 * A) ^ 3 + 27 * E ^ 2) = 0 := by
    linear_combination -hzero
  have h4096 : (4096 : ℤ_[2]) ≠ 0 := by
    rw [show (4096 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 12 by norm_num]
    exact pow_ne_zero 12 PadicInt.uniformizer_ne_zero
  have hbr : (8 * (1 + 2 * A) ^ 3 + 27 * E ^ 2 : ℤ_[2]) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left h4096
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : ℤ_[2], E = 2 * E₁ := by
    obtain ⟨E₁, hE₁⟩ : ((2 : ℕ) : ℤ_[2]) ∣ E :=
      PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
        ((PadicInt.prime_p.dvd_or_dvd (a := (27 : ℤ_[2]))
          ⟨-4 * (1 + 2 * A) ^ 3, by rw [h2]; linear_combination hbr⟩).resolve_left h27)
    exact ⟨E₁, by rw [hE₁, h2]⟩
  subst hE₁
  have hbr₁ : (27 * E₁ ^ 2 + 2 * (1 + 2 * A) ^ 3 : ℤ_[2]) = 0 := by
    refine mul_left_cancel₀ (a := (4 : ℤ_[2])) (by
      rw [show (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 by norm_num]
      exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero) ?_
    rw [mul_zero]
    linear_combination hbr
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : ℤ_[2], E₁ = 2 * E₂ := by
    obtain ⟨E₂, hE₂⟩ : ((2 : ℕ) : ℤ_[2]) ∣ E₁ :=
      PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
        ((PadicInt.prime_p.dvd_or_dvd (a := (27 : ℤ_[2]))
          ⟨-(1 + 2 * A) ^ 3, by rw [h2]; linear_combination hbr₁⟩).resolve_left h27)
    exact ⟨E₂, by rw [hE₂, h2]⟩
  subst hE₂
  have hbr₂ : (54 * E₂ ^ 2 + (1 + 2 * A) ^ 3 : ℤ_[2]) = 0 := by
    refine mul_left_cancel₀ (a := (2 : ℤ_[2])) (by
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num]
      exact PadicInt.uniformizer_ne_zero) ?_
    rw [mul_zero]
    linear_combination hbr₁
  refine hone ⟨-(27 * E₂ ^ 2 + 3 * A + 6 * A ^ 2 + 4 * A ^ 3), ?_⟩
  rw [h2]
  linear_combination hbr₂

/-- **`Δ ≠ 0` on the `II*` family**, `a₄ = 16A` and `a₆ = 16G` with `4 ∤ G`. -/
theorem ofShortNF_Δ_ne_zero_of_IIstarEven {a₄ a₆ A G : ℤ_[2]} (ha₄ : a₄ = 16 * A)
    (ha₆ : a₆ = 16 * G) (hG : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ G) : (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have h2 : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have h27 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (27 : ℤ_[2]) := not_two_dvd_twentySeven
  intro hzero
  rw [ofShortNF_Δ, ha₄, ha₆] at hzero
  have hprod : (4096 : ℤ_[2]) * (64 * A ^ 3 + 27 * G ^ 2) = 0 := by linear_combination -hzero
  have h4096 : (4096 : ℤ_[2]) ≠ 0 := by
    rw [show (4096 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 12 by norm_num]
    exact pow_ne_zero 12 PadicInt.uniformizer_ne_zero
  have hbr : (64 * A ^ 3 + 27 * G ^ 2 : ℤ_[2]) = 0 := (mul_eq_zero.mp hprod).resolve_left h4096
  obtain ⟨G₁, hG₁⟩ : ∃ G₁ : ℤ_[2], G = 2 * G₁ := by
    obtain ⟨G₁, hG₁⟩ : ((2 : ℕ) : ℤ_[2]) ∣ G :=
      PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
        ((PadicInt.prime_p.dvd_or_dvd (a := (27 : ℤ_[2]))
          ⟨-32 * A ^ 3, by rw [h2]; linear_combination hbr⟩).resolve_left h27)
    exact ⟨G₁, by rw [hG₁, h2]⟩
  subst hG₁
  have hbr₁ : (16 * A ^ 3 + 27 * G₁ ^ 2 : ℤ_[2]) = 0 := by
    refine mul_left_cancel₀ (a := (4 : ℤ_[2])) (by
      rw [show (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 by norm_num]
      exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero) ?_
    rw [mul_zero]
    linear_combination hbr
  obtain ⟨G₂, hG₂⟩ : ∃ G₂ : ℤ_[2], G₁ = 2 * G₂ := by
    obtain ⟨G₂, hG₂⟩ : ((2 : ℕ) : ℤ_[2]) ∣ G₁ :=
      PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
        ((PadicInt.prime_p.dvd_or_dvd (a := (27 : ℤ_[2]))
          ⟨-8 * A ^ 3, by rw [h2]; linear_combination hbr₁⟩).resolve_left h27)
    exact ⟨G₂, by rw [hG₂, h2]⟩
  exact hG ⟨G₂, by rw [hG₂, h2]; ring⟩

namespace TateAlgorithm

/-! ### Exact division and residues at `2` -/

private theorem div_two_pow_mul {k : ℕ} {x a : ℤ_[2]} (h : x = ((2 : ℕ) : ℤ_[2]) ^ k * a) :
    div x (((2 : ℕ) : ℤ_[2]) ^ k) = a := by
  subst h
  exact mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

private theorem div_two_mul {x a : ℤ_[2]} (h : x = ((2 : ℕ) : ℤ_[2]) * a) :
    div x ((2 : ℕ) : ℤ_[2]) = a := by
  subst h
  exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero
    (CommRing.mul_div PadicInt.uniformizer_ne_zero (Dvd.intro a rfl))

private theorem mod_two_eq_of_dvd_sub {x y : ℤ_[2]} (h : ((2 : ℕ) : ℤ_[2]) ∣ x - y) :
    mod ((2 : ℕ) : ℤ_[2]) x = mod ((2 : ℕ) : ℤ_[2]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

open scoped Classical in
/-- Steps 1 and 2 of Tate's algorithm at `2` pass on a short model, through a translate
`(1, r, 0, t)` whose `a₄` and `a₆` are divisible by `2`. -/
theorem exists_step2_run_ofShortNF_two (a₄ a₆ : ℤ_[2]) :
    ∃ r t : ℤ_[2], Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
        = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) ∧
      ((2 : ℕ) : ℤ_[2]) ∣ a₄ + 3 * r ^ 2 - 2 * 0 * t ∧
      ((2 : ℕ) : ℤ_[2]) ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hπ]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hπ]; ring⟩
  have h2run : Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, hV1⟩ : ∃ r t : ℤ_[2], Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔdvd⟩
  have hval2 := Step2.hasValuation_translate hΔdvd
  rw [hV1] at h2run hval2
  have hva₄ := hval2.a₄
  have hva₆ := hval2.a₆
  rw [smul_ofShortNF_a₄, pow_one] at hva₄
  rw [smul_ofShortNF_a₆, pow_one] at hva₆
  exact ⟨r, t, h2run, hva₄, hva₆⟩

/-! ### The forward run, on the even family and on the odd family -/

open scoped Classical in
/-- **The forward run at `IV*` on the even family at `2`.** A short model over `ℤ_2` with
`a₄ = 8A` and `a₆ = 4 + 16F` has Kodaira symbol `IV*`, with Tamagawa number `3` if `F` is even and
`1` if `F` is odd. -/
theorem run_eq_IVstarEven_two {a₄ a₆ A F : ℤ_[2]} (ha₄ : a₄ = 8 * A) (ha₆ : a₆ = 4 + 16 * F)
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.IV! ∧
      (((2 : ℕ) : ℤ_[2]) ∣ F → (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 3) ∧
      (¬ ((2 : ℕ) : ℤ_[2]) ∣ F → (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1) := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_ofShortNF_two a₄ a₆
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
      refine h3 ⟨c - 4 * A - 6 * y - 6 * y ^ 2, ?_⟩
      rw [hπ]
      linear_combination hc
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨2 + 8 * F + 8 * A * ρ + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 2 * A + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2], x = 1 + 4 * F + 4 * A * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
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
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2, div_two_pow_mul hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℤ_[2], Q₆ + τ = 1 + 2 * w :=
    ⟨2 * F + 2 * A * ρ + ρ ^ 3 - nτ, by rw [hQ₆]; linear_combination -hnτ⟩
  have hw₀v : w₀ + nτ = 2 * F + 2 * A * ρ + ρ ^ 3 := by
    refine mul_left_cancel₀ (a := (2 : ℤ_[2])) (by norm_num) ?_
    rw [hQ₆] at hw₀
    linear_combination -hw₀ - hnτ
  obtain ⟨U, hU⟩ : ∃ x : ℤ_[2], x = Q₆ + 2 * θ + τ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = 2 * U := by rw [hT₂, hπ, hθ, ht, hU]; ring
  have hUv : U = 1 + 2 * (w₀ + θ) := by rw [hU]; linear_combination hw₀
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[2], x = 3 * ρ - 2 * S ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[2], x = Q₄ - 2 * S * U := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[2], x = w₀ + nτ - 2 * (w₀ + θ) - 2 * (w₀ + θ) ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂
      = ((2 : ℕ) : ℤ_[2]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hS, hX₂]; ring
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hS, hT₂v, hX₄, hQ₄]; ring
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 3 * Y := by
    rw [smul_ofShortNF_a₆, hπ, ha₄, ha₆, hr, hT₂v, hUv, hY]
    linear_combination (-8 : ℤ_[2]) * hw₀v
  have hcb : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      ((2 : ℕ) : ℤ_[2])) = _
    rw [div_two_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV2a₄]
    exact mod_two_eq_of_dvd_sub
      ⟨A + 3 * nρ + ρ - S * U, by rw [hπ, hX₄, hQ₄]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_two_pow_mul hV2a₆]
    exact mod_two_eq_of_dvd_sub ⟨F + A * ρ + nρ * (ρ + 1) - (w₀ + θ) - (w₀ + θ) ^ 2, by
      rw [hπ, hY]; linear_combination hw₀v + (ρ + 1) * hnρ⟩
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
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hX₂] at hj
    exact ⟨S ^ 2 - ρ - j, by linear_combination -hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[2], x = 4 * D := ⟨_, rfl⟩
  obtain ⟨W₃, hW₃⟩ : ∃ x : ℤ_[2], x = U - 2 * r₈ * S := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[2], x = 2 * W₃ := ⟨_, rfl⟩
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
    · rw [hT₃, hT₂v, hπ, hW₃, hS]; ring
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[2], W₃ = 1 + 2 * w :=
    ⟨w₀ + θ - r₈ * S, by rw [hW₃, hUv]; ring⟩
  obtain ⟨mw, hmw⟩ := exists_sq_add_self_eq_two_mul hp2 hπ w
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * W₃ := by rw [smul_ofShortNF_a₃, hT₃, hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 4 * (F + 2 * (A * D + 2 * D ^ 3 - mw)) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hπ, ha₄, ha₆, hw]
    linear_combination (-16 : ℤ_[2]) * hmw
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c
      = mod ((2 : ℕ) : ℤ_[2]) W₃ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV3a₃]
  have hqd : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).d
      = -mod ((2 : ℕ) : ℤ_[2]) (F + 2 * (A * D + 2 * D ^ 3 - mw)) := by
    change -mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 4)) = _
    rw [div_two_pow_mul hV3a₆]
  have hqb : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).b = 1 := by simp [quadratic]
  have hqc1 : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 1 := by
    rw [hqc, mod_two_eq_of_dvd_sub (x := W₃) (y := 1) ⟨w, by rw [hπ]; linear_combination hw⟩,
      map_one]
  have hq : ¬ (quadratic ((2 : ℕ) : ℤ_[2]) (Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)) 2).HasDoubleRoot := by
    rw [hV3, Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) hqb, hqc1,
      residue_four_eq_zero_two hp2, zero_mul, one_pow]
    exact one_ne_zero
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step8 hΔ0 (step8_run_eq_error_of_not_hasDoubleRoot hΔ0 h7run hq))]
  refine ⟨rfl, fun hF => ite_eq_left ?_, fun hF => ite_eq_right ?_⟩
  · obtain ⟨G, hG⟩ := hF
    rw [hπ] at hG
    rw [hV3, Cubic.of_a_eq_zero (by simp [quadratic]), hqb, hqd,
      mod_two_eq_of_dvd_sub (x := F + 2 * (A * D + 2 * D ^ 3 - mw)) (y := 0)
        ⟨G + A * D + 2 * D ^ 3 - mw, by rw [hπ]; linear_combination hG⟩,
      map_zero, neg_zero]
    exact splits_quadratic_of_d_eq_zero _
  · have hZ : ¬ ((2 : ℕ) : ℤ_[2]) ∣ F + 2 * (A * D + 2 * D ^ 3 - mw) := by
      intro ⟨j, hj⟩
      exact hF ⟨j - (A * D + 2 * D ^ 3 - mw), by rw [hπ] at hj ⊢; linear_combination hj⟩
    have hW : ¬ ((2 : ℕ) : ℤ_[2]) ∣ W₃ := by
      intro ⟨j, hj⟩
      exact hone ⟨j - w, by rw [hπ] at hj ⊢; linear_combination hj - hw⟩
    rw [hV3, Cubic.of_a_eq_zero (by simp [quadratic]), hqb, hqc, hqd]
    exact not_splits_quadratic_of_forall_ne _ _ (no_root_quadratic_two hW hZ)

open scoped Classical in
/-- **The forward run at `IV*` on the odd family at `2`.** A short model over `ℤ_2` with
`a₄ = 1 + 8A` and `a₆ = 6 + 8A + 16F` has Kodaira symbol `IV*`, with Tamagawa number `3` if `F` is
even and `1` if `F` is odd. -/
theorem run_eq_IVstarOdd_two {a₄ a₆ A F : ℤ_[2]} (ha₄ : a₄ = 1 + 8 * A)
    (ha₆ : a₆ = 6 + 8 * A + 16 * F) (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.IV! ∧
      (((2 : ℕ) : ℤ_[2]) ∣ F → (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 3) ∧
      (¬ ((2 : ℕ) : ℤ_[2]) ∣ F → (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1) := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_ofShortNF_two a₄ a₆
  have hone : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    rw [PadicInt.dvd_iff_toZMod_eq_zero, map_one]; decide
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[2], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hπ, ha₄, hy] at hc
      refine hone ⟨c - 4 * A - 6 * y ^ 2, ?_⟩
      rw [hπ]
      linear_combination hc
    · exact ⟨y, hy⟩
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨4 + 8 * A + 8 * F + 4 * ρ + 8 * A * ρ + 6 * ρ ^ 2 + 4 * ρ ^ 3 - c, ?_⟩
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
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 1 + 2 * A + 3 * ρ + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2],
      x = 2 + 4 * A + 4 * F + 2 * ρ + 4 * A * ρ + 3 * ρ ^ 2 + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
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
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2, div_two_pow_mul hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℤ_[2], v = 1 + 2 * A + 2 * F + 2 * A * ρ + 3 * ρ + 5 * nρ
      + 2 * nρ * ρ - nτ := ⟨_, rfl⟩
  have hv₀v : Q₆ + τ = ρ + 2 * v₀ := by
    rw [hQ₆, hv₀]; linear_combination (5 + 2 * ρ) * hnρ - hnτ
  obtain ⟨U, hU⟩ : ∃ x : ℤ_[2], x = Q₆ + 2 * θ + τ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = 2 * U := by rw [hT₂, hπ, hθ, ht, hU]; ring
  have hUv : U = ρ + 2 * (v₀ + θ) := by rw [hU]; linear_combination hv₀v
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[2], x = 1 + 3 * ρ - 2 * S - 2 * S ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[2], x = Q₄ - U - 2 * S * U := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℤ_[2],
      x = v₀ + nτ - nρ - 2 * ρ * (v₀ + θ) - 2 * (v₀ + θ) ^ 2 := ⟨_, rfl⟩
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
    rw [div_two_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV2a₄]
    exact mod_two_eq_of_dvd_sub ⟨A + 3 * nρ + 2 * ρ - (v₀ + θ) - S * (ρ + 2 * (v₀ + θ)), by
      rw [hπ, hX₄, hQ₄, hUv]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod ((2 : ℕ) : ℤ_[2]) (1 + ρ) := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_two_pow_mul hV2a₆]
    exact mod_two_eq_of_dvd_sub
      ⟨A + F + A * ρ + ρ + 2 * nρ + nρ * ρ - ρ * (v₀ + θ) - (v₀ + θ) ^ 2, by
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
    · next W' heq =>
        obtain rfl : W' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[2],
      x = Step8.r ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℤ_[2], ρ - r₈ = 1 + 2 * h := by
    have hdv : ((2 : ℕ) : ℤ_[2]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_mul hV2a₂, sub_self]
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
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[2], W₃ = 1 + 2 * w :=
    ⟨(v₀ + θ) + h - r₈ * S, by rw [hW₃, hUv]; linear_combination hh⟩
  obtain ⟨mh, hmh⟩ := exists_sq_add_self_eq_two_mul hp2 hπ h
  obtain ⟨mw, hmw⟩ := exists_sq_add_self_eq_two_mul hp2 hπ w
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * W₃ := by rw [smul_ofShortNF_a₃, hT₃, hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 4
        * (F + 2 * (1 + A + 3 * h + 4 * h ^ 2 + 2 * h ^ 3 + A * h + mh - mw)) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hπ, ha₄, ha₆, hw]
    linear_combination (16 : ℤ_[2]) * hmh - 16 * hmw
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c
      = mod ((2 : ℕ) : ℤ_[2]) W₃ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV3a₃]
  have hqd : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).d
      = -mod ((2 : ℕ) : ℤ_[2])
        (F + 2 * (1 + A + 3 * h + 4 * h ^ 2 + 2 * h ^ 3 + A * h + mh - mw)) := by
    change -mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 4)) = _
    rw [div_two_pow_mul hV3a₆]
  have hqb : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).b = 1 := by simp [quadratic]
  have hqc1 : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 1 := by
    rw [hqc, mod_two_eq_of_dvd_sub (x := W₃) (y := 1) ⟨w, by rw [hπ]; linear_combination hw⟩,
      map_one]
  have hq : ¬ (quadratic ((2 : ℕ) : ℤ_[2]) (Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)) 2).HasDoubleRoot := by
    rw [hV3, Cubic.hasDoubleRoot_of_b_eq_one (by simp [quadratic]) hqb, hqc1,
      residue_four_eq_zero_two hp2, zero_mul, one_pow]
    exact one_ne_zero
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step8 hΔ0 (step8_run_eq_error_of_not_hasDoubleRoot hΔ0 h7run hq))]
  refine ⟨rfl, fun hF => ite_eq_left ?_, fun hF => ite_eq_right ?_⟩
  · obtain ⟨G, hG⟩ := hF
    rw [hπ] at hG
    rw [hV3, Cubic.of_a_eq_zero (by simp [quadratic]), hqb, hqd,
      mod_two_eq_of_dvd_sub
        (x := F + 2 * (1 + A + 3 * h + 4 * h ^ 2 + 2 * h ^ 3 + A * h + mh - mw)) (y := 0)
        ⟨G + 1 + A + 3 * h + 4 * h ^ 2 + 2 * h ^ 3 + A * h + mh - mw, by
          rw [hπ]; linear_combination hG⟩,
      map_zero, neg_zero]
    exact splits_quadratic_of_d_eq_zero _
  · have hZ : ¬ ((2 : ℕ) : ℤ_[2])
        ∣ F + 2 * (1 + A + 3 * h + 4 * h ^ 2 + 2 * h ^ 3 + A * h + mh - mw) := by
      intro ⟨j, hj⟩
      exact hF ⟨j - (1 + A + 3 * h + 4 * h ^ 2 + 2 * h ^ 3 + A * h + mh - mw), by
        rw [hπ] at hj ⊢; linear_combination hj⟩
    have hW : ¬ ((2 : ℕ) : ℤ_[2]) ∣ W₃ := by
      intro ⟨j, hj⟩
      exact hone ⟨j - w, by rw [hπ] at hj ⊢; linear_combination hj - hw⟩
    rw [hV3, Cubic.of_a_eq_zero (by simp [quadratic]), hqb, hqc, hqd]
    exact not_splits_quadratic_of_forall_ne _ _ (no_root_quadratic_two hW hZ)

open scoped Classical in
/-- **The forward run at `III*` on the even family at `2`.** A short model over `ℤ_2` with
`a₄ = 8 + 16A` and `a₆ = 16E` has reduction datum exactly `(III*, 2)`. -/
theorem run_eq_IIIstarEven_two {a₄ a₆ A E : ℤ_[2]} (ha₄ : a₄ = 8 + 16 * A) (ha₆ : a₆ = 16 * E)
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.III! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 2 := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_ofShortNF_two a₄ a₆
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
      refine h3 ⟨c - 4 - 8 * A - 6 * y - 6 * y ^ 2, ?_⟩
      rw [hπ]
      linear_combination hc
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[2], t = 2 * τ := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ t ^ 2 := by
      obtain ⟨c, hc⟩ := hva₆
      rw [hπ, ha₄, ha₆, hr] at hc
      refine ⟨8 * E + 8 * ρ + 16 * A * ρ + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 2 + 4 * A + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2],
      x = 4 * E + 4 * ρ + 8 * A * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
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
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2, div_two_pow_mul hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨u₀, hu₀⟩ : ∃ x : ℤ_[2], x = 2 * E + 2 * ρ + 4 * A * ρ + ρ ^ 3 - nτ := ⟨_, rfl⟩
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
    rw [div_two_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV2a₄]
    exact mod_two_eq_of_dvd_sub ⟨1 + 2 * A + 3 * nρ + ρ - S * U, by
      rw [hπ, hX₄, hQ₄]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_two_pow_mul hV2a₆]
    exact mod_two_eq_of_dvd_sub ⟨E + ρ + 2 * A * ρ + nρ * (ρ + 1) - (u₀ + θ) ^ 2, by
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
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_mul hV2a₂, sub_self]
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
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV3a₃, map_mul, mod_self, zero_mul]
  have hq : (quadratic ((2 : ℕ) : ℤ_[2]) (Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)) 2).HasDoubleRoot := by
    rw [hV3]
    exact quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic]) (by simp [quadratic]) hqc
  have h8run := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7run hq
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[2],
      x = Step7.tY ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
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
      = 8 + 16 * (A + 3 * D ^ 2 - S * (tY + W')) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, ha₄, hS]; ring
  have ha₄' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ (Step9.translate ((2 : ℕ) : ℤ_[2])
      (Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆))).a₄ := by
    rw [hV3, hV4, hV4a₄]
    rintro ⟨m, hm⟩
    rw [hπ] at hm
    have h8ne : (8 : ℤ_[2]) ≠ 0 := by
      rw [show (8 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 3 by norm_num]
      exact pow_ne_zero 3 PadicInt.uniformizer_ne_zero
    refine hone ⟨m - (A + 3 * D ^ 2 - S * (tY + W')), ?_⟩
    refine mul_left_cancel₀ h8ne ?_
    rw [hπ]
    linear_combination hm
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step9 hΔ0 (step9_run_eq_error_of_not_dvd hΔ0 h8run ha₄'))]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **The forward run at `II*` on the even family at `2`.** A short model over `ℤ_2` with
`a₄ = 16A` and `a₆ = 16G`, where `G` is `2` or `3` modulo `4`, has reduction datum exactly
`(II*, 1)`. -/
theorem run_eq_IIstarEven_two {a₄ a₆ A G : ℤ_[2]} (ha₄ : a₄ = 16 * A) (ha₆ : a₆ = 16 * G)
    (hG : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ G) (hG' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ (G - 1))
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.II! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = 1 := by
  have hp2 : (2 : ℕ) = 2 := rfl
  have hπ : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨r, t, h2run, hva₄, hva₆⟩ := exists_step2_run_ofShortNF_two a₄ a₆
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
      refine ⟨8 * G + 16 * A * ρ + 4 * ρ ^ 3 - c, ?_⟩
      rw [hπ]
      linear_combination -hc
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h2
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[2], x = 4 * A + 3 * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[2], x = 4 * G + 8 * A * ρ + 2 * ρ ^ 3 - τ ^ 2 := ⟨_, rfl⟩
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
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2, div_two_pow_mul hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨u₀, hu₀⟩ : ∃ x : ℤ_[2], x = 2 * G + 4 * A * ρ + ρ ^ 3 - nτ := ⟨_, rfl⟩
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
    rw [div_two_mul hV2a₂]
    exact mod_two_eq_of_dvd_sub ⟨ρ - S ^ 2, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV2a₄]
    exact mod_two_eq_of_dvd_sub ⟨2 * A + 3 * nρ + ρ - S * U, by
      rw [hπ, hX₄, hQ₄]; linear_combination 3 * hnρ⟩
  have hcd : (cubic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d = mod ((2 : ℕ) : ℤ_[2]) ρ := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_two_pow_mul hV2a₆]
    exact mod_two_eq_of_dvd_sub ⟨G + 2 * A * ρ + nρ * (ρ + 1) - (u₀ + θ) ^ 2, by
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
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_two_mul hV2a₂, sub_self]
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
  have hqc : (quadratic ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
    change mod ((2 : ℕ) : ℤ_[2]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_two_pow_mul hV3a₃, map_mul, mod_self, zero_mul]
  have hq : (quadratic ((2 : ℕ) : ℤ_[2]) (Step8.translate ((2 : ℕ) : ℤ_[2])
      ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)) 2).HasDoubleRoot := by
    rw [hV3]
    exact quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic]) (by simp [quadratic]) hqc
  have h8run := step8_run_eq_ok_of_hasDoubleRoot hΔ0 h7run hq
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[2],
      x = Step7.tY ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
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
      = 16 * (G + 4 * A * D + 4 * D ^ 3 - (tY + W') ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₄, ha₄, ha₆]; ring
  have ha₄' : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ (Step9.translate ((2 : ℕ) : ℤ_[2])
      (Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆))).a₄ := by
    rw [hV3, hV4]
    exact ⟨_, hV4a₄⟩
  have h9run := step9_run_eq_ok_of_dvd hΔ0 h8run ha₄'
  have h16ne : (16 : ℤ_[2]) ≠ 0 := by
    rw [show (16 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 4 by norm_num]
    exact pow_ne_zero 4 PadicInt.uniformizer_ne_zero
  have ha₆' : ¬ ((2 : ℕ) : ℤ_[2]) ^ 6 ∣ (Step9.translate ((2 : ℕ) : ℤ_[2])
      (Step8.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆))).a₆ := by
    rw [hV3, hV4, hV4a₆]
    rintro ⟨m, hm⟩
    rw [hπ] at hm
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ (tY + W')
    · refine hG ⟨m - (A * D + D ^ 3 - y ^ 2), ?_⟩
      refine mul_left_cancel₀ h16ne ?_
      rw [hπ]
      linear_combination hm + 16 * (tY + W' + 2 * y) * hy
    · refine hG' ⟨m - (A * D + D ^ 3 - y - y ^ 2), ?_⟩
      refine mul_left_cancel₀ h16ne ?_
      rw [hπ]
      linear_combination hm + 16 * (tY + W' + 1 + 2 * y) * hy
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0
    (step11_error_of_step10 hΔ0 (step10_run_eq_error_of_not_dvd hΔ0 h9run ha₆'))]
  exact ⟨rfl, rfl⟩

end TateAlgorithm

end WeierstrassCurve

end
