/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.LocalDensity.DegreeBound
public import BSDTamagawa.LocalDensity.PrimeSquareTail
public import BSDTamagawa.PrimeCount.EulerProduct

/-!
# Summability of the local tail masses `1 - δ_p(1)`

The family `(1 - δ_p(1))_{p prime}` of local tail masses is summable, `∑_p (1 - δ_p(1)) < ∞`, where
`δ_p(1)` is the proportion of short Weierstrass models over `ℤ_p` with trivial local Tamagawa
number. For `p ≥ 5` one has `1 - δ_p(1) ≤ 3/p²`, and `∑_p p⁻²` converges.

## Main definitions

* `WeierstrassCurve.tamagawaLocalTailMass`: the real-valued family equal to `1 - (δ_p(1)).toReal`
  at a prime `p` and `0` elsewhere.

## Main results

* `WeierstrassCurve.summable_tamagawaLocalTailMass`: `tamagawaLocalTailMass` is summable.
* `WeierstrassCurve.tsum_one_sub_δ_one_lt_top`: `∑_p (1 - δ_p(1)) < ⊤` in `ℝ≥0∞`.
* `WeierstrassCurve.tamagawaOmegaEulerFactor_sub_one`: `F_p(u) - 1 = (1 - δ_p(1))(u - 1)` for the
  local Euler factor `F_p`.

## Implementation notes

In `ℝ≥0∞` every family is summable, so there convergence is expressed as finiteness of the `tsum`.
Since `δ_p(1) ≤ 1`, the truncated subtraction `1 - δ_p(1)` in `ℝ≥0∞` agrees with the real
difference.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.PrimeSqTail

open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ### The real-valued local tail mass -/

/-- `(δ_p(1)).toReal ≤ 1`. -/
theorem δ_one_toReal_le_one : (δ p 1).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (δ_le_one 1)

/-- `δ_p(1)` is finite, being at most `1`. -/
theorem δ_one_ne_top : δ p 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (δ_le_one 1)

/-- For `p ≥ 5`, `1 - (δ_p(1)).toReal ≤ 3/p²`. -/
theorem one_sub_δ_one_toReal_le (hp : 5 ≤ p) : 1 - (δ p 1).toReal ≤ 3 / (p : ℝ) ^ 2 := by
  have hp0 : ((p : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using (by omega : p ≠ 0))
  have hdiv : (3 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.div_ne_top (by norm_num) hp0
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨δ_one_ne_top, hdiv⟩) (one_le_δ_one_add hp)
  rw [ENNReal.toReal_one, ENNReal.toReal_add δ_one_ne_top hdiv, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at h
  linarith

/-- The local tail mass, as a real-valued family over `ℕ`: at a prime `p` it is
`1 - (δ_p(1)).toReal`, the mass of the short Weierstrass models over `ℤ_p` whose local Tamagawa
number is not `1`; at a non-prime index it is `0`. -/
noncomputable def tamagawaLocalTailMass (p : ℕ) : ℝ :=
  if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0

/-- At a prime index the local tail mass is `1 - (δ_p(1)).toReal`. -/
theorem tamagawaLocalTailMass_of_prime (p : ℕ) [Fact p.Prime] :
    tamagawaLocalTailMass p = 1 - (δ p 1).toReal :=
  dite_eq_left Fact.out

/-- At a non-prime index the local tail mass is the neutral value `0`. -/
theorem tamagawaLocalTailMass_of_not_prime {p : ℕ} (hp : ¬ p.Prime) :
    tamagawaLocalTailMass p = 0 :=
  dite_eq_right hp

/-- Every local tail mass is nonnegative. -/
theorem tamagawaLocalTailMass_nonneg (p : ℕ) : 0 ≤ tamagawaLocalTailMass p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTailMass_of_prime]
    linarith [δ_one_toReal_le_one (p := p)]
  · simp [tamagawaLocalTailMass_of_not_prime hp]

/-- For every index `p ≥ 5`, `tamagawaLocalTailMass p ≤ 3 · primeSq p`. -/
theorem tamagawaLocalTailMass_le_primeSq {p : ℕ} (hp : 5 ≤ p) :
    tamagawaLocalTailMass p ≤ 3 * primeSq p := by
  by_cases h : p.Prime
  · have : Fact p.Prime := ⟨h⟩
    have hps : primeSq p = 1 / (p : ℝ) ^ 2 := by rw [primeSq]; exact ite_eq_left h
    rw [tamagawaLocalTailMass_of_prime, hps, mul_one_div]
    exact one_sub_δ_one_toReal_le hp
  · simp [tamagawaLocalTailMass_of_not_prime h, primeSq, h]

/-! ### Summability -/

/-- The family of local tail masses `(1 - δ_p(1))_p` is summable. -/
@[bsd_tamagawa "T041e"]
theorem summable_tamagawaLocalTailMass : Summable tamagawaLocalTailMass := by
  have hshift : Summable (fun n : ℕ => 3 * primeSq (n + 5)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 3 * primeSq n) 5).mpr (summable_primeSq.mul_left 3)
  rw [← summable_nat_add_iff 5]
  exact Summable.of_nonneg_of_le (fun n => tamagawaLocalTailMass_nonneg _)
    (fun n => tamagawaLocalTailMass_le_primeSq (by omega)) hshift

/-- The `ℝ≥0∞`-valued local tail mass is `ENNReal.ofReal` of the real one. -/
theorem dite_one_sub_δ_one_eq_ofReal (p : ℕ) :
    (if h : p.Prime then 1 - @δ p ⟨h⟩ 1 else 0) = ENNReal.ofReal (tamagawaLocalTailMass p) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have h1 : (1 : ℝ≥0∞) - δ p 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hsub : (1 : ℝ) - (δ p 1).toReal = ((1 : ℝ≥0∞) - δ p 1).toReal := by
      rw [ENNReal.toReal_sub_of_le (δ_le_one 1) ENNReal.one_ne_top, ENNReal.toReal_one]
    rw [dite_eq_left hp, tamagawaLocalTailMass_of_prime, hsub, ENNReal.ofReal_toReal h1]
  · simp [dite_eq_right hp, tamagawaLocalTailMass_of_not_prime hp]

/-- `∑_p (1 - δ_p(1)) < ∞` in `ℝ≥0∞`, the sum being over the primes (the summand is `0` at a
non-prime index). -/
@[bsd_tamagawa "T041e"]
theorem tsum_one_sub_δ_one_lt_top :
    (∑' p : ℕ, if h : p.Prime then 1 - @δ p ⟨h⟩ 1 else 0) < ⊤ := by
  rw [tsum_congr dite_one_sub_δ_one_eq_ofReal, ← ENNReal.ofReal_tsum_of_nonneg
    tamagawaLocalTailMass_nonneg summable_tamagawaLocalTailMass]
  exact ENNReal.ofReal_lt_top

/-! ### The local Euler factor -/

/-- The deviation of the local Euler factor from `1` is the local tail mass times `u - 1`:
`F_p(u) - 1 = (1 - δ_p(1))(u - 1)` at every index `p : ℕ`. -/
theorem tamagawaOmegaEulerFactor_sub_one (p : ℕ) (u : ℂ) :
    tamagawaOmegaEulerFactor p u - 1 = (tamagawaLocalTailMass p : ℂ) * (u - 1) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaOmegaEulerFactor_of_prime, tamagawaLocalTailMass_of_prime]
    push_cast
    ring
  · rw [tamagawaOmegaEulerFactor_of_not_prime hp, tamagawaLocalTailMass_of_not_prime hp]
    simp

end WeierstrassCurve
