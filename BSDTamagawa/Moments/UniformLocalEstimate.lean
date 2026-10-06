/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.SummableTailMass
public import BSDTamagawa.Moments.LocalFiniteConditional
public import BSDTamagawa.GeneratingFunction.ScalarLocalFactorSummable

/-!
# The uniform local moment estimate, under the geometric tail law

Granted the geometric tail law `HasTailGeometricLaw p`, for every prime `p`, every `k : ℕ` and
every real `x ≤ k`,

`|G_p(x) - 1| ≤ C_k / p²`,

where `G_p(x)` is the moment local factor and `C_k = 25 · 4^k + 5^k C'_k` is explicit. Since
`G_p(x) - 1 = ∑_t δ_p(t)(t^x - 1)` and the `t = 1` term vanishes, the head terms `t ∈ {2, 3, 4}`
are bounded by `4^k (1 - δ_p(1)) ≤ 4^k · 25/p²`, and the tail `t ≥ 5` by `5^k C'_k / p²`.

## Main definitions

* `WeierstrassCurve.momentBoundConst`: the constant `C_k`.

## Main results

* `WeierstrassCurve.norm_momentLocalFactor_sub_one_le_of_tailLaw`: the estimate at every prime.

## Implementation notes

The estimate holds at every prime, with no threshold `p₀`, because the bound `25/p²` on
`1 - δ_p(1)` is trivial at the primes `p < 5`. The lower bound `-1 ≤ x` is not needed, since
`|t^x - 1| ≤ t^k` for `t ≥ 1` and `x ≤ k`.
-/

@[expose] public section

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-! ### The elementary estimate on `|t^x - 1|` -/

/-- For `t ≥ 1` and `x ≤ k`, `|t^x - 1| ≤ t^k`. -/
theorem abs_rpow_sub_one_le_rpow (k : ℕ) {x : ℝ} (hxk : x ≤ (k : ℝ)) {t : ℕ} (ht : 1 ≤ t) :
    |(t : ℝ) ^ x - 1| ≤ (t : ℝ) ^ (k : ℝ) := by
  have hb : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h1 : (1 : ℝ) ≤ (t : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
    exact one_le_pow₀ hb
  have h2 : (t : ℝ) ^ x ≤ (t : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hxk
  have h3 : (0 : ℝ) ≤ (t : ℝ) ^ x := Real.rpow_nonneg (by positivity) x
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- For `1 ≤ t ≤ 4` and `x ≤ k`, `|t^x - 1| ≤ 4^k`. -/
theorem abs_rpow_sub_one_le_four_pow (k : ℕ) {x : ℝ} (hxk : x ≤ (k : ℝ)) {t : ℕ} (ht : 1 ≤ t)
    (ht4 : t ≤ 4) : |(t : ℝ) ^ x - 1| ≤ (4 : ℝ) ^ k := by
  refine (abs_rpow_sub_one_le_rpow k hxk ht).trans ?_
  rw [Real.rpow_natCast]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast ht4) k

/-! ### The mass off `t = 1` -/

/-- For every prime `p`, the real number `1 - δ_p(1)` is at most `25/p²`. -/
theorem one_sub_δ_one_toReal_le_twentyfive : 1 - (δ p 1).toReal ≤ 25 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℕ) ≤ p := (Fact.out : p.Prime).two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  rcases le_or_gt 5 p with hp5 | hp5
  · have h3 := one_sub_δ_one_toReal_le hp5
    have h25 : (3 : ℝ) / (p : ℝ) ^ 2 ≤ 25 / (p : ℝ) ^ 2 := by gcongr; norm_num
    linarith
  · have hp4 : (p : ℝ) ≤ 4 := by
      have : p ≤ 4 := by omega
      exact_mod_cast this
    have h1 : (1 : ℝ) ≤ 25 / (p : ℝ) ^ 2 := by
      rw [le_div_iff₀ hsq]
      nlinarith
    have := ENNReal.toReal_nonneg (a := δ p 1)
    linarith

/-! ### The three head terms -/

/-- Every finite partial sum `∑_{t < n} δ_p(t)` of the real densities is at most `1`. -/
theorem sum_δ_toReal_range_le_one (n : ℕ) : ∑ t ∈ Finset.range n, (δ p t).toReal ≤ 1 := by
  rw [← tsum_δ_toReal p]
  exact (summable_δ_toReal p).sum_le_tsum _ (fun _ _ => ENNReal.toReal_nonneg)

/-- `δ_p(2) + δ_p(3) + δ_p(4) ≤ 25/p²`. -/
theorem sum_three_δ_toReal_le : (δ p 2).toReal + (δ p 3).toReal + (δ p 4).toReal
    ≤ 25 / (p : ℝ) ^ 2 := by
  have hexp : ∑ t ∈ Finset.range 5, (δ p t).toReal
      = (δ p 0).toReal + (δ p 1).toReal + (δ p 2).toReal + (δ p 3).toReal + (δ p 4).toReal := by
    simp [Finset.sum_range_succ]
  have hle := sum_δ_toReal_range_le_one p 5
  rw [hexp, δ_zero, ENNReal.toReal_zero] at hle
  have := one_sub_δ_one_toReal_le_twentyfive p
  linarith

/-! ### The uniform estimate -/

/-- The constant `C_k = 25 · 4^k + 5^k C'_k`, where `C'_k = ∑_{s ≥ 0} (1 + s)^k 2^{-s}`. -/
noncomputable def momentBoundConst (k : ℕ) : ℝ :=
  25 * (4 : ℝ) ^ k + (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k

/-- `momentBoundConst k > 0`. -/
theorem momentBoundConst_pos (k : ℕ) : 0 < momentBoundConst k := by
  have := BSDTamagawa.PolyGeomTail.ck_pos k
  rw [momentBoundConst]
  positivity

/-- Granted the geometric tail law at `p`, for every `k : ℕ` and every real `x ≤ k`,

`|G_p(x) - 1| ≤ momentBoundConst k / p²`. -/
theorem norm_momentLocalFactor_sub_one_le_of_tailLaw (h : HasTailGeometricLaw p) (k : ℕ)
    {x : ℝ} (hxk : x ≤ (k : ℝ)) :
    ‖momentLocalFactor p x - 1‖ ≤ momentBoundConst k / (p : ℝ) ^ 2 := by
  have hsq : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
    positivity
  have hS1 : Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ x :=
    summable_δ_toReal_mul_rpow_of_tailLaw p h x
  have hS0 : Summable fun t : ℕ => (δ p t).toReal := summable_δ_toReal p
  have hSk : Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ (k : ℝ) :=
    summable_δ_toReal_mul_rpow_of_tailLaw p h (k : ℝ)
  have hsub : Summable fun t : ℕ => (δ p t).toReal * ((t : ℝ) ^ x - 1) :=
    (hS1.sub hS0).congr fun t => by ring
  have habs : Summable fun t : ℕ => (δ p t).toReal * |(t : ℝ) ^ x - 1| :=
    hsub.abs.congr fun t => by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hstep1 : (∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ x) - 1
      = ∑' t : ℕ, (δ p t).toReal * ((t : ℝ) ^ x - 1) := by
    have hd := Summable.tsum_sub hS1 hS0
    rw [tsum_δ_toReal p] at hd
    rw [← hd]
    exact tsum_congr fun t => by ring
  have hstep2 : |(∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ x) - 1|
      ≤ ∑' t : ℕ, (δ p t).toReal * |(t : ℝ) ^ x - 1| := by
    rw [hstep1, abs_le]
    refine ⟨?_, Summable.tsum_le_tsum (fun t =>
      mul_le_mul_of_nonneg_left (le_abs_self _) ENNReal.toReal_nonneg) hsub habs⟩
    rw [← tsum_neg]
    refine Summable.tsum_le_tsum (fun t => ?_) habs.neg hsub
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_abs_le _) ENNReal.toReal_nonneg
  have hsplit := habs.sum_add_tsum_nat_add 5
  have hhead : ∑ t ∈ Finset.range 5, (δ p t).toReal * |(t : ℝ) ^ x - 1|
      ≤ (4 : ℝ) ^ k * (25 / (p : ℝ) ^ 2) := by
    have hexp : ∑ t ∈ Finset.range 5, (δ p t).toReal * |(t : ℝ) ^ x - 1|
        = (δ p 0).toReal * |((0 : ℕ) : ℝ) ^ x - 1|
          + (δ p 1).toReal * |((1 : ℕ) : ℝ) ^ x - 1|
          + (δ p 2).toReal * |((2 : ℕ) : ℝ) ^ x - 1|
          + (δ p 3).toReal * |((3 : ℕ) : ℝ) ^ x - 1|
          + (δ p 4).toReal * |((4 : ℕ) : ℝ) ^ x - 1| := by
      simp [Finset.sum_range_succ]
    have e0 : (δ p 0).toReal * |((0 : ℕ) : ℝ) ^ x - 1| = 0 := by
      rw [δ_zero, ENNReal.toReal_zero, zero_mul]
    have e1 : (δ p 1).toReal * |((1 : ℕ) : ℝ) ^ x - 1| = 0 := by
      rw [Nat.cast_one, Real.one_rpow, sub_self, abs_zero, mul_zero]
    have b2 := mul_le_mul_of_nonneg_left (abs_rpow_sub_one_le_four_pow k hxk
      (t := 2) (by norm_num) (by norm_num)) (ENNReal.toReal_nonneg (a := δ p 2))
    have b3 := mul_le_mul_of_nonneg_left (abs_rpow_sub_one_le_four_pow k hxk
      (t := 3) (by norm_num) (by norm_num)) (ENNReal.toReal_nonneg (a := δ p 3))
    have b4 := mul_le_mul_of_nonneg_left (abs_rpow_sub_one_le_four_pow k hxk
      (t := 4) (by norm_num) (by norm_num)) (ENNReal.toReal_nonneg (a := δ p 4))
    have hthree := mul_le_mul_of_nonneg_left (sum_three_δ_toReal_le p)
      (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ k)
    rw [hexp, e0, e1]
    refine le_trans ?_ hthree
    linarith [b2, b3, b4]
  have htail : (∑' s : ℕ, (δ p (s + 5)).toReal * |((s + 5 : ℕ) : ℝ) ^ x - 1|)
      ≤ (5 : ℝ) ^ k * BSDTamagawa.PolyGeomTail.ck k / (p : ℝ) ^ 2 := by
    refine le_trans (Summable.tsum_le_tsum (fun s => ?_) ((summable_nat_add_iff 5).mpr habs)
      ((summable_nat_add_iff 5).mpr hSk)) (tsum_δ_toReal_mul_pow_tail_le_of_tailLaw p h k)
    exact mul_le_mul_of_nonneg_left
      (abs_rpow_sub_one_le_rpow k hxk (t := s + 5) (by omega)) ENNReal.toReal_nonneg
  rw [momentLocalFactor_eq_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  refine hstep2.trans ?_
  rw [← hsplit, momentBoundConst, add_div]
  have h4 : (4 : ℝ) ^ k * (25 / (p : ℝ) ^ 2) = 25 * (4 : ℝ) ^ k / (p : ℝ) ^ 2 := by
    field_simp
  rw [← h4]
  exact add_le_add hhead htail

end WeierstrassCurve
