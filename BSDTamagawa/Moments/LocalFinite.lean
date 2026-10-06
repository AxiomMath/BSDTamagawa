/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.LocalFiniteConditional
public import BSDTamagawa.NumberTheory.SmallPrimeTailDecay

/-!
# Finiteness of the local moments at every prime

For every prime `p` and every real number `x`, the family `t ↦ δ_p(t) t^x` is summable in `ℝ`, its
`ℂ`-valued counterpart is absolutely summable, its terms are nonnegative, and the local moment
factor `G_p(x)` is its sum. The comparison is termwise against the integer power `t^{⌈x⌉₊}`, using
`t^x ≤ t^{⌈x⌉₊}` for `t ≥ 1` and `δ_p(0) = 0`.

## Main results

* `WeierstrassCurve.summable_δ_toReal_mul_rpow`: the family `t ↦ δ_p(t) t^x` is summable in `ℝ`.
* `WeierstrassCurve.summable_norm_δ_toReal_mul_cpow`: the `ℂ`-valued family `t ↦ δ_p(t) t^x` is
  absolutely summable.
* `WeierstrassCurve.momentLocalFactor_summable_and_eq`: summability, absolute summability,
  nonnegativity of the terms, and `G_p(x) = ∑' t, δ_p(t) t^x`.

## Implementation notes

Both sums are `∑'` over all of `ℕ`. The `ℝ≥0∞`-valued `δ_p(t)` is coerced to `ℝ` by
`ENNReal.toReal` before any arithmetic, and the exponent `x` is real of either sign.
-/

@[expose] public section

namespace WeierstrassCurve

/-- For every prime `p` and every real `x`, the family `t ↦ δ_p(t) t^x` is summable in `ℝ`. -/
theorem summable_δ_toReal_mul_rpow (p : ℕ) [Fact p.Prime] (x : ℝ) :
    Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ x := by
  refine Summable.of_nonneg_of_le
    (fun t => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) x))
    (fun t => ?_) (summable_δ_toReal_mul_pow (p := p) ⌈x⌉₊)
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [δ_zero]
  · have hb : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hpow : (t : ℝ) ^ x ≤ (t : ℝ) ^ (⌈x⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast (t : ℝ) ⌈x⌉₊]
      exact Real.rpow_le_rpow_of_exponent_le hb (Nat.le_ceil x)
    exact mul_le_mul_of_nonneg_left hpow ENNReal.toReal_nonneg

/-- For every prime `p` and every real `x`, the `ℂ`-valued family `t ↦ δ_p(t) t^x` is absolutely
summable. -/
theorem summable_norm_δ_toReal_mul_cpow (p : ℕ) [Fact p.Prime] (x : ℝ) :
    Summable fun t : ℕ => ‖((δ p t).toReal : ℂ) * (t : ℂ) ^ (x : ℂ)‖ := by
  refine (summable_δ_toReal_mul_rpow p x).congr fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp [δ_zero]
  · rw [show ((δ p t).toReal : ℂ) * (t : ℂ) ^ (x : ℂ)
        = (((δ p t).toReal * (t : ℝ) ^ x : ℝ) : ℂ) by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg t), Complex.ofReal_natCast],
      Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg t) x))]

/-- For every prime `p` and every real number `x`, the family `t ↦ δ_p(t) t^x` is summable in `ℝ`,
its `ℂ`-valued counterpart is absolutely summable, its terms are nonnegative, and the local moment
factor `G_p(x)` is the sum `∑' t, δ_p(t) t^x`. -/
@[bsd_tamagawa "T059e"]
theorem momentLocalFactor_summable_and_eq (p : ℕ) [Fact p.Prime] (x : ℝ) :
    (Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ x) ∧
      (Summable fun t : ℕ => ‖((δ p t).toReal : ℂ) * (t : ℂ) ^ (x : ℂ)‖) ∧
        (∀ t : ℕ, 0 ≤ (δ p t).toReal * (t : ℝ) ^ x) ∧
          momentLocalFactor p x = ((∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ x : ℝ) : ℂ) :=
  ⟨summable_δ_toReal_mul_rpow p x, summable_norm_δ_toReal_mul_cpow p x,
    fun t => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) x),
    momentLocalFactor_eq_ofReal p x⟩

end WeierstrassCurve
