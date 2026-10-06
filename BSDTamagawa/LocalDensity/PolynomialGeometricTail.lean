/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import BSDTamagawa.Attr

/-!
# Polynomial-weighted geometric tail bounds

For an integer `k ≥ 0` there is a constant `C_k > 0`, depending only on `k`, with
`∑_{t ≥ t₀} t^k / q^t ≤ C_k · t₀^k / q^{t₀}` for every integer `t₀ ≥ 1` and every real `q ≥ 2`. One
may take `C_k := ∑_{s ≥ 0} (1 + s)^k 2^{-s}`; for `k = 0` this is `2`. Specialising to `t₀ ≥ 5`
gives `D_k > 0` with `∑_{t ≥ t₀} t^k / q^t ≤ D_k / q^5` for all `t₀ ≥ 5` and `q ≥ 2`.

## Main definitions

* `BSDTamagawa.PolyGeomTail.ck`: the constant `C_k = ∑_{s ≥ 0} (1 + s)^k 2^{-s}`.

## Main results

* `BSDTamagawa.PolyGeomTail.polynomial_geometric_tail_bound_explicit`:
  `∑_{t ≥ t₀} t^k / q^t ≤ C_k · t₀^k / q^{t₀}`.
* `BSDTamagawa.PolyGeomTail.polynomial_geometric_tail_O5`: `∑_{t ≥ t₀} t^k / q^t ≤ D_k / q^5` for
  `t₀ ≥ 5`.

## Implementation notes

The tail `∑_{t ≥ t₀}` is a `tsum` over the subtype `{t : ℕ // t₀ ≤ t}`; since `q > 1` the series
converges absolutely. The bound is sometimes stated as `∑_{t ≥ t₀} t^k / q^t ≤ C_k / q^{t₀}`,
without the factor `t₀^k`. That is true for `k = 0` but false for every `k ≥ 1`: the left side
times `q^{t₀}` is at least `t₀^k`, which is unbounded in `t₀`.
-/

@[expose] public section

namespace BSDTamagawa.PolyGeomTail

/-- The constant `C_k := ∑_{s ≥ 0} (1 + s)^k 2^{-s}`. -/
noncomputable def ck (k : ℕ) : ℝ := ∑' s : ℕ, (1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s

/-- The equivalence `ℕ ≃ {t : ℕ // t₀ ≤ t}`, `s ↦ t₀ + s`. -/
def tailEquiv (t₀ : ℕ) : ℕ ≃ {t : ℕ // t₀ ≤ t} where
  toFun s := ⟨t₀ + s, Nat.le_add_right _ _⟩
  invFun t := t.1 - t₀
  left_inv s := by simp
  right_inv t := Subtype.ext (Nat.add_sub_cancel' t.2)

/-- `∑ (n + c)^k x^n` converges for `‖x‖ < 1`. -/
theorem summable_add_pow_mul_geometric_of_norm_lt_one (c k : ℕ) {x : ℝ} (hx : ‖x‖ < 1) :
    Summable fun n : ℕ => ((n + c : ℕ) : ℝ) ^ k * x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx0
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rw [zero_pow (by simpa using hn), mul_zero]
  · refine (summable_mul_right_iff (pow_ne_zero c hx0)).1
      (((summable_nat_add_iff c).2
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hx)).congr fun n => ?_)
    rw [pow_add]
    ring

/-- The series defining `ck k` is summable. -/
theorem ck_summable (k : ℕ) :
    Summable (fun s : ℕ => (1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s) :=
  (summable_add_pow_mul_geometric_of_norm_lt_one (x := (2 : ℝ)⁻¹) 1 k (by norm_num)).congr
    fun s => by push_cast; ring

/-- `ck k` is strictly positive: all its terms are nonnegative and the `s = 0` term is `1`. -/
theorem ck_pos (k : ℕ) : 0 < ck k :=
  Summable.tsum_pos (ck_summable k) (fun s => by positivity) 0 (by norm_num)

/-- `ck 0 = 2`, so one may take `C_0 = 2`. -/
@[simp]
theorem ck_zero : ck 0 = 2 := by
  simpa only [ck, pow_zero, one_mul] using tsum_geometric_inv_two

/-- For all `t₀ ≥ 1` and `q ≥ 2`, `∑_{t ≥ t₀} t^k / q^t ≤ ck k · t₀^k / q^{t₀}`. -/
@[bsd_tamagawa "T022c"]
theorem polynomial_geometric_tail_bound_explicit (k t₀ : ℕ) (ht₀ : 1 ≤ t₀) (q : ℝ) (hq : 2 ≤ q) :
    (∑' t : {t : ℕ // t₀ ≤ t}, ((t : ℕ) : ℝ) ^ k / q ^ (t : ℕ))
      ≤ ck k * (t₀ : ℝ) ^ k / q ^ t₀ := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hreindex : (∑' t : {t : ℕ // t₀ ≤ t}, ((t : ℕ) : ℝ) ^ k / q ^ (t : ℕ))
      = ∑' s : ℕ, ((t₀ + s : ℕ) : ℝ) ^ k / q ^ (t₀ + s) := by
    rw [← Equiv.tsum_eq (tailEquiv t₀)]
    rfl
  rw [hreindex]
  have hterm : ∀ s : ℕ, ((t₀ + s : ℕ) : ℝ) ^ k / q ^ (t₀ + s)
      ≤ (q ^ t₀)⁻¹ * ((t₀ : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s)) := by
    intro s
    have ht0R : (1 : ℝ) ≤ (t₀ : ℝ) := by exact_mod_cast ht₀
    have hnum : ((t₀ + s : ℕ) : ℝ) ^ k ≤ (t₀ : ℝ) ^ k * (1 + s : ℝ) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) s, ht0R]
    have hden : (q ^ t₀ * 2 ^ s : ℝ) ≤ q ^ (t₀ + s) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hq s) (by positivity)
    rw [show (q ^ t₀)⁻¹ * ((t₀ : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s))
        = (t₀ : ℝ) ^ k * (1 + s : ℝ) ^ k / (q ^ t₀ * 2 ^ s) by rw [inv_pow]; field_simp]
    gcongr
  have hsummR : Summable
      (fun s : ℕ => (q ^ t₀)⁻¹ * ((t₀ : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s))) :=
    ((ck_summable k).mul_left _).mul_left _
  calc ∑' s : ℕ, ((t₀ + s : ℕ) : ℝ) ^ k / q ^ (t₀ + s)
      ≤ ∑' s : ℕ, (q ^ t₀)⁻¹ * ((t₀ : ℝ) ^ k * ((1 + s : ℝ) ^ k * (2 : ℝ)⁻¹ ^ s)) :=
        (hsummR.of_nonneg_of_le (fun s => by positivity) hterm).tsum_le_tsum hterm hsummR
    _ = ck k * (t₀ : ℝ) ^ k / q ^ t₀ := by
        rw [tsum_mul_left, tsum_mul_left, ck]
        field_simp

/-- The sequence `t₀ ↦ t₀^k 2^{-(t₀ - 5)}` is bounded above by a positive constant depending only
on `k`, uniformly over `t₀ ≥ 5`. -/
theorem exists_bound_pow_mul_geometric_shift (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t₀ : ℕ, 5 ≤ t₀ → (t₀ : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (t₀ - 5) ≤ M := by
  have hsum : Summable (fun n : ℕ => ((n + 5 : ℕ) : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) :=
    summable_add_pow_mul_geometric_of_norm_lt_one 5 k (by norm_num)
  have hnn : (0 : ℝ) ≤ ∑' n : ℕ, ((n + 5 : ℕ) : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n :=
    tsum_nonneg fun n => by positivity
  refine ⟨1 + ∑' n : ℕ, ((n + 5 : ℕ) : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n, by linarith,
    fun t₀ ht₀ => ?_⟩
  have hterm := hsum.le_tsum (t₀ - 5) fun m _ => by positivity
  rw [Nat.sub_add_cancel ht₀] at hterm
  linarith

/-- For every `k` there is a constant `D > 0`, depending only on `k`, with
`∑_{t ≥ t₀} t^k / q^t ≤ D / q^5` for all `t₀ ≥ 5` and `q ≥ 2`. -/
@[bsd_tamagawa "T022c"]
theorem polynomial_geometric_tail_O5 (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t₀ : ℕ, 5 ≤ t₀ → ∀ q : ℝ, 2 ≤ q →
      (∑' t : {t : ℕ // t₀ ≤ t}, ((t : ℕ) : ℝ) ^ k / q ^ (t : ℕ)) ≤ D / q ^ 5 := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_pow_mul_geometric_shift k
  have hCk := ck_pos k
  refine ⟨ck k * M, by positivity, fun t₀ ht₀ q hq => ?_⟩
  have hq0 : (0 : ℝ) < q := by linarith
  refine (polynomial_geometric_tail_bound_explicit k t₀ (by omega) q hq).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (t₀ : ℝ) ^ k * q ^ 5 ≤ M * q ^ t₀ := by
    have h2q : (2 : ℝ) ^ (t₀ - 5) ≤ q ^ (t₀ - 5) := pow_le_pow_left₀ (by norm_num) hq _
    have htk : (t₀ : ℝ) ^ k ≤ M * 2 ^ (t₀ - 5) := by
      have hMt := hM t₀ ht₀
      rwa [inv_pow, mul_inv_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (t₀ - 5))] at hMt
    have htk2 : (t₀ : ℝ) ^ k ≤ M * q ^ (t₀ - 5) :=
      htk.trans (mul_le_mul_of_nonneg_left h2q hM0.le)
    rw [show q ^ t₀ = q ^ 5 * q ^ (t₀ - 5) by rw [← pow_add]; congr 1; omega]
    nlinarith [pow_pos hq0 5, htk2]
  nlinarith [hCk, key]

end BSDTamagawa.PolyGeomTail
