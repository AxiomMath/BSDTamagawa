/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.GOTTailRowLargePrime
public import BSDTamagawa.NumberTheory.RatioLawAtTwo

/-!
# The tail of the density table at the wild primes

For `t ≥ 5` the density `δ_p(t)` agrees with the tabulated value `gotδ p t` at `p = 2` and `p = 3`.
At `p = 2` the density is `(1/(2 · 1023)) · 2^{-t}` and the table entry is `1/(2^{t+1} · 1023)`; at
`p = 3` they are `(1/(3 · 29524)) · 3^{-t}` and `1/(3^{t+1} · 29524)`. Together with the case
`p ≥ 5`, this gives the tail of the table at every prime.

## Main results

* `WeierstrassCurve.δ_eq_ofReal_gotδ_of_eq_two`: `δ_2(t) = gotδ 2 t` for `t ≥ 5`.
* `WeierstrassCurve.δ_eq_ofReal_gotδ_of_eq_three`: `δ_3(t) = gotδ 3 t` for `t ≥ 5`.
* `WeierstrassCurve.δ_eq_ofReal_gotδ_tail`: `δ_p(t) = gotδ p t` for every prime `p` and every
  `t ≥ 5`.
* `WeierstrassCurve.hasGOTDensities_of_head`: at every prime `p`, `HasGOTDensities p` holds as soon
  as `δ_p(t) = gotδ p t` for `t = 1, 2, 3, 4`.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- At `p = 2`, `δ_2(t) = gotδ 2 t` for every `t ≥ 5`. -/
theorem δ_eq_ofReal_gotδ_of_eq_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = ENNReal.ofReal (gotδ p t) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hp2]; norm_num
  have hinv : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  have harith : (1 / (2 * 1023) : ℝ) * ((p : ℝ)⁻¹) ^ t = gotδ p t := by
    subst hp2
    rw [gotδ_tail_two ht, show ((2 : ℕ) : ℝ) = 2 by norm_num, pow_succ]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    field_simp
    rw [← mul_pow]
    norm_num
  rw [δ_eq_ofReal_two_of_eq_two hp2 ht, hinv,
    ← ENNReal.ofReal_pow (le_of_lt (inv_pos.2 hp0)),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / (2 * 1023)), harith]

/-- At `p = 3`, `δ_3(t) = gotδ 3 t` for every `t ≥ 5`. -/
theorem δ_eq_ofReal_gotδ_of_eq_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = ENNReal.ofReal (gotδ p t) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hp3]; norm_num
  have hinv : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  have harith : (1 / (3 * 29524) : ℝ) * ((p : ℝ)⁻¹) ^ t = gotδ p t := by
    subst hp3
    rw [gotδ_tail_three ht, show ((3 : ℕ) : ℝ) = 3 by norm_num, pow_succ]
    have hpow : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
    field_simp
    rw [← mul_pow]
    norm_num
  rw [δ_eq_ofReal_three_of_eq_three hp3 ht, hinv,
    ← ENNReal.ofReal_pow (le_of_lt (inv_pos.2 hp0)),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / (3 * 29524)), harith]

/-- For every prime `p` and every `t ≥ 5`, `δ_p(t) = gotδ p t`. -/
theorem δ_eq_ofReal_gotδ_tail {t : ℕ} (ht : 5 ≤ t) : δ p t = ENNReal.ofReal (gotδ p t) := by
  rcases eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with h | h | h
  · exact δ_eq_ofReal_gotδ_of_eq_two h ht
  · exact δ_eq_ofReal_gotδ_of_eq_three h ht
  · exact δ_eq_ofReal_gotδ_of_five_le h ht

/-- For every prime `p`, if `δ_p(t) = gotδ p t` for `t = 1, 2, 3, 4`, then `HasGOTDensities p`,
that is, `δ_p(t) = gotδ p t` for every `t`. -/
theorem hasGOTDensities_of_head
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ 4 → δ p t = ENNReal.ofReal (gotδ p t)) :
    HasGOTDensities p := by
  intro t
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · rw [ht0, δ_zero, gotδ_zero, ENNReal.ofReal_zero]
  · by_cases ht5 : 5 ≤ t
    · exact δ_eq_ofReal_gotδ_tail ht5
    · exact h t ht1 (by omega)

end WeierstrassCurve
