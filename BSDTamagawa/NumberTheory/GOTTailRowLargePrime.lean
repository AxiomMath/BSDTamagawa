/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.ExplicitTailConstant
public import BSDTamagawa.NumberTheory.TateTailLawUnconditional

/-!
# The tail densities `δ_p(t)` for `t ≥ 5` at primes `p ≥ 5`

For a prime `p ≥ 5` and `t ≥ 5`, the Haar density `δ_p(t)` equals the table value `gotδ p t`,
namely `(p¹⁰ - 2p⁹ + p⁸)/(2 p^t (p¹⁰ - 1))`. Thus, for `HasGOTDensities p` at `p ≥ 5`, only the
head values `t ≤ 4` remain to be compared with the table.

## Main results

* `WeierstrassCurve.δ_eq_ofReal_gotδ_of_five_le`: for every prime `p ≥ 5` and every `t ≥ 5`,
  `δ_p(t) = gotδ p t`.

## Implementation notes

The tail law `δ_p(t) = a_p p^{-t}` for `t ≥ 5`, with `a_p = 2N²p⁻²(1 - p⁻¹⁰)⁻¹` and
`N = |goodRes p|`, holds under scale invariance of the stratification, which is unconditional at
`p ≥ 5`; the constant `a_p` equals `gotα p = p⁸(p-1)²/(2(p¹⁰-1))`. Every difference in the
statements lives inside `ENNReal.ofReal` and is a real difference.

At `p = 2` the two multiplicative shells `I_t^{sp}` and `I_t^{ns}` have densities in ratio `1 : 3`
rather than `1 : 1`, since `-1 ≡ 1 mod 2` and no non-square unit exchanges them; the value
`δ_2(t) = 1/(2^{t+1} · 1023)` is unaffected.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The tail at `p ≥ 5` -/

/-- For every prime `p ≥ 5` and every `t ≥ 5`, the Haar density `δ_p(t)` equals the table value
`gotδ p t`. -/
theorem δ_eq_ofReal_gotδ_of_five_le (hp : 5 ≤ p) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = ENNReal.ofReal (gotδ p t) := by
  have hprime : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hinv : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  have harith : gotα p * ((p : ℝ)⁻¹) ^ t = gotδ p t := by
    rw [gotδ_tail ht, div_eq_mul_inv, inv_pow]
  rw [δ_eq_tailConstant_mul hp (stratScaleInvariant_of_five_le hp) ht,
    tailConstant_eq_ofReal_gotα hp, hinv, ← ENNReal.ofReal_pow (le_of_lt (inv_pos.2 hp0)),
    ← ENNReal.ofReal_mul (gotα_pos hprime).le, harith]

end WeierstrassCurve
