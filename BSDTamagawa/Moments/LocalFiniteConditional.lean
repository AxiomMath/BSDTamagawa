/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.PolynomialGeometricTail
public import BSDTamagawa.LocalDensity.AdditiveDecomposition
public import BSDTamagawa.Moments.LocalFactor

/-!
# Finiteness of the local moments, under the geometric tail law

Granted the geometric tail law `HasTailGeometricLaw p`, i.e. `δ_p(t) = a p^{-t}` for `t ≥ 5` with
`a ≤ 1`, for every real `x` the family `t ↦ δ_p(t) t^x` is summable, and the moment local factor
`G_p(x)` is the sum of this absolutely convergent series of nonnegative terms. The tail `t ≥ 5` is
dominated termwise by `t^k p^{-t}` for any integer `k ≥ x`.

## Main results

* `WeierstrassCurve.tsum_δ_toReal`: the real densities sum to `1`.
* `WeierstrassCurve.summable_δ_toReal_mul_rpow_of_tailLaw`: the family `t ↦ δ_p(t) t^x` is summable
  in `ℝ`.
* `WeierstrassCurve.momentLocalFactor_eq_ofReal`: `G_p(x)` is the coercion of
  `∑' t, δ_p(t) t^x`, with no hypothesis.
* `WeierstrassCurve.tsum_δ_toReal_mul_rpow_nonneg`: that sum is nonnegative.
* `WeierstrassCurve.tsum_δ_toReal_mul_pow_tail_le_of_tailLaw`: the tail estimate
  `∑_{t ≥ 5} δ_p(t) t^k ≤ 5^k C_k / p²`.
-/

@[expose] public section

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-! ### Total mass in `ℝ` -/

/-- The real densities sum to `1`: `∑_t δ_p(t) = 1` in `ℝ`. -/
theorem tsum_δ_toReal : ∑' t : ℕ, (δ p t).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (δ_ne_top p), tsum_δ p, ENNReal.toReal_one]

/-! ### The geometric majorant of the tail -/

/-- The family `s ↦ (s + 5)^k p^{-(s+5)}` is summable. -/
theorem summable_natCast_add_five_pow_mul_inv_pow (k : ℕ) :
    Summable fun s : ℕ => ((s + 5 : ℕ) : ℝ) ^ k * ((p : ℝ)⁻¹) ^ (s + 5) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hx : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    calc ((p : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr
      _ < 1 := by norm_num
  refine ((BSDTamagawa.PolyGeomTail.summable_add_pow_mul_geometric_of_norm_lt_one 5 k
    hx).mul_right (((p : ℝ)⁻¹) ^ 5)).congr fun s => ?_
  rw [pow_add]
  ring

/-- Granted the geometric tail law, for `t = s + 5` and any real `x ≤ k`,

`δ_p(t) t^x ≤ t^k p^{-t}`. -/
theorem δ_toReal_mul_rpow_le_of_tailLaw (h : HasTailGeometricLaw p) {x : ℝ} {k : ℕ}
    (hxk : x ≤ (k : ℝ)) (s : ℕ) :
    (δ p (s + 5)).toReal * ((s + 5 : ℕ) : ℝ) ^ x
      ≤ ((s + 5 : ℕ) : ℝ) ^ k * ((p : ℝ)⁻¹) ^ (s + 5) := by
  obtain ⟨a, ha, hgeom⟩ := h
  have hbase : (1 : ℝ) ≤ ((s + 5 : ℕ) : ℝ) := by norm_cast; omega
  have hpow : ((s + 5 : ℕ) : ℝ) ^ x ≤ ((s + 5 : ℕ) : ℝ) ^ k := by
    rw [← Real.rpow_natCast ((s + 5 : ℕ) : ℝ) k]
    exact Real.rpow_le_rpow_of_exponent_le hbase hxk
  have hδ : (δ p (s + 5)).toReal ≤ ((p : ℝ)⁻¹) ^ (s + 5) := by
    rw [hgeom (s + 5) (by omega), ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    refine mul_le_of_le_one_left (by positivity) ?_
    simpa using ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using ha)
  calc (δ p (s + 5)).toReal * ((s + 5 : ℕ) : ℝ) ^ x
      ≤ ((p : ℝ)⁻¹) ^ (s + 5) * ((s + 5 : ℕ) : ℝ) ^ k :=
        mul_le_mul hδ hpow (Real.rpow_nonneg (by positivity) x) (by positivity)
    _ = ((s + 5 : ℕ) : ℝ) ^ k * ((p : ℝ)⁻¹) ^ (s + 5) := mul_comm _ _

/-! ### Summability of the local moments -/

/-- Granted the geometric tail law, for every real `x` the family `t ↦ δ_p(t) t^x` is summable in
`ℝ`. -/
theorem summable_δ_toReal_mul_rpow_of_tailLaw (h : HasTailGeometricLaw p) (x : ℝ) :
    Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ x := by
  refine (summable_nat_add_iff 5).mp (Summable.of_nonneg_of_le (fun s => ?_)
    (δ_toReal_mul_rpow_le_of_tailLaw p h (Nat.le_ceil x))
    (summable_natCast_add_five_pow_mul_inv_pow p ⌈x⌉₊))
  exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) x)

/-- For every real `x`, `∑' t, δ_p(t) t^x` is nonnegative. -/
theorem tsum_δ_toReal_mul_rpow_nonneg (x : ℝ) :
    0 ≤ ∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ x :=
  tsum_nonneg fun t => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) x)

/-- The moment local factor `G_p(x)` is the coercion of the real sum `∑_{t ≥ 1} δ_p(t) t^x`. -/
theorem momentLocalFactor_eq_ofReal (x : ℝ) :
    momentLocalFactor p x = ((∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ x : ℝ) : ℂ) := by
  rw [momentLocalFactor_of_prime, Complex.ofReal_tsum]
  refine tsum_congr fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp [δ_zero]
  · rw [ite_eq_right ht, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg t),
      Complex.ofReal_natCast]

/-! ### The quantitative tail estimate -/

/-- Granted the geometric tail law, `∑_{t ≥ 5} δ_p(t) t^k ≤ 5^k C_k / p²`, where
`C_k = ∑_{s ≥ 0} (1 + s)^k 2^{-s}`. -/
theorem tsum_δ_toReal_mul_pow_tail_le_of_tailLaw (h : HasTailGeometricLaw p) (k : ℕ) :
    (∑' s : ℕ, (δ p (s + 5)).toReal * ((s + 5 : ℕ) : ℝ) ^ (k : ℝ))
      ≤ (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hterm := δ_toReal_mul_rpow_le_of_tailLaw p h (le_refl (k : ℝ))
  have hsum : Summable fun s : ℕ => (δ p (s + 5)).toReal * ((s + 5 : ℕ) : ℝ) ^ (k : ℝ) :=
    Summable.of_nonneg_of_le
      (fun s => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) _))
      hterm (summable_natCast_add_five_pow_mul_inv_pow p k)
  have hmaj2 : ∀ s : ℕ, ((s + 5 : ℕ) : ℝ) ^ k * ((p : ℝ)⁻¹) ^ (s + 5)
      ≤ ((p : ℝ)⁻¹) ^ 5 * (5 : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s) := by
    intro s
    have h1 : ((s + 5 : ℕ) : ℝ) ^ k ≤ (5 : ℝ) ^ k * (1 + s : ℝ) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) s]
    have hinv : ((p : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr
    have h2 : ((p : ℝ)⁻¹) ^ (s + 5) ≤ ((p : ℝ)⁻¹) ^ 5 * (2 : ℝ)⁻¹ ^ s := by
      rw [pow_add, mul_comm (((p : ℝ)⁻¹) ^ s) (((p : ℝ)⁻¹) ^ 5)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv s) (by positivity)
    calc ((s + 5 : ℕ) : ℝ) ^ k * ((p : ℝ)⁻¹) ^ (s + 5)
        ≤ ((5 : ℝ) ^ k * (1 + s : ℝ) ^ k) * (((p : ℝ)⁻¹) ^ 5 * (2 : ℝ)⁻¹ ^ s) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((p : ℝ)⁻¹) ^ 5 * (5 : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s) := by ring
  have hsum2 : Summable fun s : ℕ =>
      ((p : ℝ)⁻¹) ^ 5 * (5 : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s) :=
    (BSDTamagawa.PolyGeomTail.ck_summable k).mul_left _
  calc (∑' s : ℕ, (δ p (s + 5)).toReal * ((s + 5 : ℕ) : ℝ) ^ (k : ℝ))
      ≤ ∑' s : ℕ, ((p : ℝ)⁻¹) ^ 5 * (5 : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s) :=
        Summable.tsum_le_tsum (fun s => (hterm s).trans (hmaj2 s)) hsum hsum2
    _ = ((p : ℝ)⁻¹) ^ 5 * (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k := by
        rw [tsum_mul_left, BSDTamagawa.PolyGeomTail.ck]
    _ ≤ (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k / (p : ℝ) ^ 2 := by
        have hA : (0 : ℝ) ≤ (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k :=
          mul_nonneg (by positivity) (BSDTamagawa.PolyGeomTail.ck_pos k).le
        have h5 : ((p : ℝ)⁻¹) ^ 5 ≤ ((p : ℝ)⁻¹) ^ 2 :=
          pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by linarith)) (by norm_num)
        calc ((p : ℝ)⁻¹) ^ 5 * (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k
            = ((p : ℝ)⁻¹) ^ 5 * ((5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k) := by ring
          _ ≤ ((p : ℝ)⁻¹) ^ 2 * ((5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k) :=
              mul_le_mul_of_nonneg_right h5 hA
          _ = (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k / (p : ℝ) ^ 2 := by
              rw [div_eq_mul_inv, ← inv_pow]; ring

end WeierstrassCurve
