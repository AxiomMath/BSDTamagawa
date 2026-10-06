/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.UniformLocalEstimate

/-!
# The moment estimate for `δ_p` under the geometric tail law

Under the geometric tail law `HasTailGeometricLaw p` (there is `a ≤ 1` with `δ_p(t) = a p^{-t}` for
all `t ≥ 5`), the moments of the scalar local density satisfy, for every prime `p` and every
`k ≥ 0`,

`∑_{t ≥ 1} δ_p(t) t^k ≤ 1 + momentBoundConst k / p²`,

with a constant `momentBoundConst k` independent of `p`. The sum is split at `t = 5`: the `t = 0`
term vanishes since `δ_p(0) = 0`; the `t = 1` term is `δ_p(1) ≤ 1`; the terms `t ∈ {2, 3, 4}`
contribute at most `4^k · 25/p²`, since `δ_p(2) + δ_p(3) + δ_p(4) ≤ 1 - δ_p(1)`; and the tail
`t ≥ 5` contributes at most `5^k C'_k/p²`, where `C'_k = ∑_{s ≥ 0} (1+s)^k 2^{-s}`.

## Main results

* `WeierstrassCurve.summable_δ_toReal_mul_pow_of_tailLaw`: the family `t ↦ δ_p(t) t^k` is summable
  in `ℝ`.
* `WeierstrassCurve.tsum_δ_toReal_mul_pow_le_of_tailLaw`:
  `∑_t δ_p(t) t^k ≤ 1 + momentBoundConst k / p²` at every prime.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-! ### The convergence clause -/

/-- Under `HasTailGeometricLaw p`, the family `t ↦ δ_p(t) t^k` is summable in `ℝ`. -/
theorem summable_δ_toReal_mul_pow_of_tailLaw (h : HasTailGeometricLaw p) (k : ℕ) :
    Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ k :=
  (summable_δ_toReal_mul_rpow_of_tailLaw p h (k : ℝ)).congr fun t => by
    rw [Real.rpow_natCast]

/-! ### The moment estimate -/

/-- Under `HasTailGeometricLaw p`, for every prime `p` and every `k : ℕ`,

`∑_{t ≥ 1} δ_p(t) t^k ≤ 1 + momentBoundConst k / p²`,

where `momentBoundConst k = 25 · 4^k + 5^k C'_k` and `C'_k = ∑_{s ≥ 0} (1+s)^k 2^{-s}`. -/
theorem tsum_δ_toReal_mul_pow_le_of_tailLaw (h : HasTailGeometricLaw p) (k : ℕ) :
    (∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ k) ≤ 1 + momentBoundConst k / (p : ℝ) ^ 2 := by
  have hsum := summable_δ_toReal_mul_pow_of_tailLaw p h k
  have hsplit := hsum.sum_add_tsum_nat_add 5
  have hhead : ∑ t ∈ Finset.range 5, (δ p t).toReal * (t : ℝ) ^ k
      ≤ 1 + (4 : ℝ) ^ k * (25 / (p : ℝ) ^ 2) := by
    have hexp : ∑ t ∈ Finset.range 5, (δ p t).toReal * (t : ℝ) ^ k
        = (δ p 0).toReal * ((0 : ℕ) : ℝ) ^ k
          + (δ p 1).toReal * ((1 : ℕ) : ℝ) ^ k
          + (δ p 2).toReal * ((2 : ℕ) : ℝ) ^ k
          + (δ p 3).toReal * ((3 : ℕ) : ℝ) ^ k
          + (δ p 4).toReal * ((4 : ℕ) : ℝ) ^ k := by
      simp [Finset.sum_range_succ]
    have e0 : (δ p 0).toReal * ((0 : ℕ) : ℝ) ^ k = 0 := by
      rw [δ_zero, ENNReal.toReal_zero, zero_mul]
    have e1 : (δ p 1).toReal * ((1 : ℕ) : ℝ) ^ k = (δ p 1).toReal := by
      rw [Nat.cast_one, one_pow, mul_one]
    have b : ∀ t : ℕ, t ≤ 4 → (δ p t).toReal * ((t : ℕ) : ℝ) ^ k
        ≤ (4 : ℝ) ^ k * (δ p t).toReal := by
      intro t ht
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg t) (by exact_mod_cast ht) k) ENNReal.toReal_nonneg
    have hthree : (4 : ℝ) ^ k * (δ p 2).toReal + (4 : ℝ) ^ k * (δ p 3).toReal
        + (4 : ℝ) ^ k * (δ p 4).toReal ≤ (4 : ℝ) ^ k * (25 / (p : ℝ) ^ 2) := by
      rw [← mul_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left (sum_three_δ_toReal_le p) (by positivity)
    have hb2 := b 2 (by norm_num)
    have hb3 := b 3 (by norm_num)
    have hb4 := b 4 (by norm_num)
    have h1 := δ_one_toReal_le_one (p := p)
    rw [hexp, e0, e1]
    push_cast at hb2 hb3 hb4 ⊢
    linarith
  have htail : (∑' s : ℕ, (δ p (s + 5)).toReal * ((s + 5 : ℕ) : ℝ) ^ k)
      ≤ (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k / (p : ℝ) ^ 2 :=
    le_of_eq_of_le (tsum_congr fun s => by rw [← Real.rpow_natCast ((s + 5 : ℕ) : ℝ) k])
      (tsum_δ_toReal_mul_pow_tail_le_of_tailLaw p h k)
  rw [← hsplit, momentBoundConst, add_div]
  have h4 : (4 : ℝ) ^ k * (25 / (p : ℝ) ^ 2) = 25 * (4 : ℝ) ^ k / (p : ℝ) ^ 2 := by field_simp
  linarith [hhead, htail, h4]

end WeierstrassCurve
