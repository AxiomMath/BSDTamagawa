/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import BSDTamagawa.Attr

/-!
# Convergence of `∑_p p⁻²` and vanishing of its tail

The sum `∑_p p⁻²` over the primes converges and is at most `ζ(2) = π²/6`, by termwise comparison
with the Basel series; consequently its tail `∑_{p > Y} p⁻²` tends to `0` as `Y → ∞`.

## Main definitions

* `BSDTamagawa.PrimeSqTail.primeSq`: `primeSq n = 1/n²` if `n` is prime and `0` otherwise.
* `BSDTamagawa.PrimeSqTail.primeTail`: `primeTail Y = ∑_{p prime, p > Y} p⁻²`.

## Main results

* `BSDTamagawa.PrimeSqTail.prime_sq_summable_le_zeta`: `primeSq` is summable and
  `∑_{p prime} p⁻² ≤ π²/6`.
* `BSDTamagawa.PrimeSqTail.prime_tail_tendsto_zero`: `primeTail Y → 0` as `Y → ∞`.
-/

@[expose] public section

namespace BSDTamagawa.PrimeSqTail

open scoped Real

/-! ### Definitions -/

/-- `primeSq n = 1/n²` if `n` is prime and `0` otherwise. -/
noncomputable def primeSq (n : ℕ) : ℝ := if n.Prime then 1 / (n : ℝ) ^ 2 else 0

/-- The tail `∑_{p prime, p > Y} p⁻²` of the prime sum past a real cutoff `Y`. -/
noncomputable def primeTail (Y : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime ∧ Y < (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0

/-! ### Basic properties -/

/-- `primeSq n` is nonnegative. -/
theorem primeSq_nonneg (n : ℕ) : 0 ≤ primeSq n := by
  rw [primeSq]; split <;> positivity

/-- `primeSq n ≤ 1/n²`. -/
theorem primeSq_le_inv_sq (n : ℕ) : primeSq n ≤ 1 / (n : ℝ) ^ 2 := by
  rw [primeSq]; split
  · exact le_rfl
  · positivity

/-- `primeSq` is summable. -/
theorem summable_primeSq : Summable primeSq :=
  Summable.of_nonneg_of_le primeSq_nonneg primeSq_le_inv_sq
    (Real.summable_one_div_nat_pow.mpr one_lt_two)

/-- `primeTail Y` is the sum of `primeSq` cut off at `Y`. -/
theorem primeTail_eq_tsum_ite (Y : ℝ) :
    primeTail Y = ∑' n : ℕ, if Y < (n : ℝ) then primeSq n else 0 :=
  tsum_congr fun n => by
    by_cases hp : n.Prime <;> by_cases hY : Y < (n : ℝ) <;> simp [primeSq, hp, hY]

/-- The family `primeSq` truncated to `n > Y` is summable. -/
theorem summable_primeSq_cutoff (Y : ℝ) :
    Summable (fun n : ℕ => if Y < (n : ℝ) then primeSq n else 0) :=
  summable_primeSq.of_nonneg_of_le
    (fun n => by split; exacts [primeSq_nonneg n, le_rfl])
    (fun n => by split; exacts [le_rfl, primeSq_nonneg n])

/-- For `Y ≥ 0`, `primeTail Y` is the sum of `primeSq` over the complement of
`Finset.range (⌊Y⌋₊ + 1)`. -/
theorem primeTail_eq_tsum_compl (Y : ℝ) (hY : 0 ≤ Y) :
    primeTail Y = ∑' (n : {x : ℕ // x ∉ Finset.range (⌊Y⌋₊ + 1)}), primeSq n := by
  rw [primeTail_eq_tsum_ite,
    show (∑' (n : {x : ℕ // x ∉ Finset.range (⌊Y⌋₊ + 1)}), primeSq n)
        = ∑' (n : ↑({x : ℕ | x ∉ Finset.range (⌊Y⌋₊ + 1)})), primeSq n from rfl,
    tsum_subtype]
  refine tsum_congr fun n => ?_
  rw [Set.indicator_apply]
  refine if_congr ?_ rfl rfl
  simp only [Set.mem_ofPred_eq, Finset.mem_range, not_lt, ← Nat.floor_lt hY]
  omega

/-- For a finite set `s` of primes all exceeding `Y`, `∑_{p ∈ s} 1/p² ≤ primeTail Y`. -/
theorem sum_inv_sq_le_primeTail {Y : ℝ} (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Y < (p : ℝ)) :
    ∑ p ∈ s, (1 / (p : ℝ) ^ 2) ≤ primeTail Y := by
  rw [primeTail_eq_tsum_ite]
  have heq : ∑ p ∈ s, (1 / (p : ℝ) ^ 2)
      = ∑ p ∈ s, (if Y < (p : ℝ) then primeSq p else 0) :=
    Finset.sum_congr rfl fun p hp => by
      obtain ⟨h1, h2⟩ := hs p hp; simp [primeSq, h1, h2]
  rw [heq]
  exact (summable_primeSq_cutoff Y).sum_le_tsum _
    (fun n _ => by split; exacts [primeSq_nonneg n, le_rfl])

/-! ### Main statements -/

/-- The family `primeSq` is summable and `∑_{p prime} p⁻² ≤ ζ(2) = π²/6`. -/
@[bsd_tamagawa "T022d"]
theorem prime_sq_summable_le_zeta :
    Summable primeSq ∧ ∑' n, primeSq n ≤ Real.pi ^ 2 / 6 := by
  refine ⟨summable_primeSq, ?_⟩
  rw [← hasSum_zeta_two.tsum_eq]
  exact Summable.tsum_mono summable_primeSq
    (Real.summable_one_div_nat_pow.mpr one_lt_two) primeSq_le_inv_sq

/-- The prime tail `primeTail Y` tends to `0` as `Y → ∞`. -/
@[bsd_tamagawa "T022d"]
theorem prime_tail_tendsto_zero :
    Filter.Tendsto primeTail Filter.atTop (nhds 0) := by
  refine ((tendsto_tsum_compl_atTop_zero primeSq).comp (Filter.tendsto_finset_range.comp
    ((Filter.tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop))).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with Y hY
  exact (primeTail_eq_tsum_compl Y hY).symm

end BSDTamagawa.PrimeSqTail
