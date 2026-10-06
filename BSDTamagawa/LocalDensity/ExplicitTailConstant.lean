/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.GOTClosedForm
public import BSDTamagawa.NumberTheory.TateTailLaw

/-!
# Explicit tail constants

Let `α_p = p⁵ δ_p(5)` be the tail constant `WeierstrassCurve.α`. For every prime `p ≥ 5`, the tail
constant `a_p = 2N² p⁻² (1 - p⁻¹⁰)⁻¹`, with `N = (p-1)/2` the number of nonzero squares modulo
`p`, equals `p⁸(p-1)²/(2(p¹⁰-1))` unconditionally, and under `StratScaleInvariant p` it equals
`α_p`. At `p = 2` and `p = 3` the expression `p⁸(p-1)²/(2(p¹⁰-1))` equals `128/1023` and
`26244/118096`, which are not the values `α_2 = 1/(2 · 1023)` and `α_3 = 1/(3 · 29524)` given by
the table of Lemma 3.1 of Griffin–Ono–Tsai.

## Main results

* `WeierstrassCurve.tailConstant_eq_ofReal_gotα`: `a_p = p⁸(p-1)²/(2(p¹⁰-1))` for `p ≥ 5`.
* `WeierstrassCurve.α_eq_tailConstant_of_stratScaleInvariant`: `α_p = a_p` for `p ≥ 5` under
  `StratScaleInvariant p`.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound

variable {p : ℕ} [Fact p.Prime]

/-! ### The closed form of `tailConstant` -/

omit [Fact p.Prime] in
/-- For `p ≥ 5`, `(p⁻¹)¹⁰ < 1` in `ℝ`. -/
theorem inv_natCast_pow_ten_lt_one_of_five_le (hp : 5 ≤ p) : ((p : ℝ)⁻¹) ^ 10 < 1 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : ((p : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; linarith
  exact pow_lt_one₀ (by positivity) h1 (by norm_num)

/-- For every prime `p ≥ 5`, the tail constant `a_p = 2N² p⁻² (1 - p⁻¹⁰)⁻¹`, where
`N = |goodRes p|`, equals `gotα p = p⁸(p-1)²/(2(p¹⁰-1))`. -/
theorem tailConstant_eq_ofReal_gotα (hp : 5 ≤ p) :
    tailConstant p = ENNReal.ofReal (gotα p) := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt := inv_natCast_pow_ten_lt_one_of_five_le (p := p) hp
  have hpos : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 := by linarith
  set N := (goodRes p).card with hNdef
  have hN : (p : ℝ) = 2 * (N : ℝ) + 1 := by
    have hnat := eq_two_mul_card_goodRes_add_one (p := p) hp
    rw [hNdef]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hnat
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  have hten : (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10
      = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinvE,
      ← ENNReal.ofReal_pow (by positivity)]
  have hhead : 2 * (N : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 2
      = ENNReal.ofReal (2 * (N : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
      ← hinvE, ENNReal.ofReal_natCast]
    norm_num
  have harith : 2 * (N : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 2 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ = gotα p := by
    rw [gotα_of_five_le hp]
    have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
    have hne : (p : ℝ) ^ 10 - 1 ≠ 0 := by linarith
    rw [hN]
    field_simp
    ring
  rw [tailConstant, hhead, hten, ← ENNReal.ofReal_inv_of_pos hpos,
    ← ENNReal.ofReal_mul (by positivity), harith]

/-! ### Values under `StratScaleInvariant` -/

/-- If `p ≥ 5` and `StratScaleInvariant p` holds, then `α_p = tailConstant p`. -/
theorem α_eq_tailConstant_of_stratScaleInvariant (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    α p = tailConstant p := by
  have h5 := δ_eq_tailConstant_mul hp h (le_refl 5)
  obtain ⟨h0, htop⟩ := pow_five_ne_zero_and_ne_top (p := p)
  rw [α, h5, ← ENNReal.inv_pow, ← mul_assoc, mul_comm ((p : ℝ≥0∞) ^ 5) (tailConstant p),
    mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]

end WeierstrassCurve
