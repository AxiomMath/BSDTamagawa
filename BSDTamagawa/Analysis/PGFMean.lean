/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.Tannery
public import BSDTamagawa.Attr

/-!
# Abel-type mean theorem for probability generating functions

Let `X` be a random variable on `ℤ≥0` with probability mass function `p : ℕ → ℝ` (`0 ≤ p n`,
`∑ p n = 1`) and probability generating function `F(u) = E[u^X] = ∑' n, p n * u ^ n`. If `F` is
differentiable from the left at `u = 1` with finite derivative `L`, then `E[X] = ∑' n, n * p n`
converges and equals `L`.

## Main definitions

* `BSDTamagawa.PGFMean.pgf`: the probability generating function `∑' n, p n * u ^ n`.

## Main results

* `BSDTamagawa.PGFMean.summable_of_deriv`: a finite left derivative at `1` forces a finite mean.
* `BSDTamagawa.PGFMean.main_theorem`: `E[X] = F'(1⁻)`.

## Implementation notes

The left derivative is `HasDerivWithinAt (pgf p) L (Set.Iio 1) 1`, i.e. the difference quotient
`(F u - F 1) / (u - 1)` tends to `L` as `u → 1⁻`. The convention `(0 : ℝ) ^ 0 = 1` gives
`pgf p 0 = p 0`.
-/

@[expose] public section

namespace BSDTamagawa.PGFMean

open Filter Topology

/-- Probability generating function `F(u) = ∑' n, p n * u ^ n` of a pmf `p : ℕ → ℝ`. -/
noncomputable def pgf (p : ℕ → ℝ) (u : ℝ) : ℝ := ∑' n, p n * u ^ n

/-! ## The slope of the pgf at `1` -/

/-- The finite geometric sum `∑ k ∈ Finset.range n, u ^ k` tends to `n` as `u → 1⁻`. -/
lemma tendsto_geom_sum (n : ℕ) :
    Tendsto (fun u : ℝ => ∑ k ∈ Finset.range n, u ^ k) (𝓝[<] (1 : ℝ)) (𝓝 (n : ℝ)) := by
  rw [show (n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) ^ k by simp]
  exact tendsto_finsetSum _ fun k _ =>
    ((continuous_pow k).continuousAt.tendsto).mono_left nhdsWithin_le_nhds

/-- Normalization: `pgf p 1 = ∑' n, p n = 1`. -/
lemma pgf_one {p : ℕ → ℝ} (hsum : HasSum p 1) : pgf p 1 = 1 := by
  simpa [pgf] using hsum.tsum_eq

/-- For `u ∈ [0, 1)` the slope of `pgf p` at `1` is the nonnegative double sum
`∑' n, p n * (∑ k ∈ Finset.range n, u ^ k)`. -/
lemma slope_eq_double_sum {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    slope (pgf p) 1 u = ∑' n : ℕ, p n * (∑ k ∈ Finset.range n, u ^ k) := by
  have hsummu : Summable (fun n => p n * u ^ n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hp n) (pow_nonneg hu0 n))
      (fun n => by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hu0 hu1.le) (hp n))
      hsum.summable
  have hnum : pgf p u - pgf p 1 = ∑' n, (p n * u ^ n - p n) := by
    rw [pgf_one hsum, hsummu.tsum_sub hsum.summable, hsum.tsum_eq]
    rfl
  rw [slope_def_field, hnum, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [div_eq_iff (sub_ne_zero_of_ne hu1.ne), mul_assoc, geom_sum_mul]
  ring

/-- If `fun n => n * p n` is summable, the double sum `∑' n, p n * (∑ k ∈ Finset.range n, u ^ k)`
tends to `E[X] = ∑' n, n * p n` as `u ↑ 1`. -/
lemma tendsto_double_sum {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n)
    (hsumm : Summable (fun n : ℕ => (n : ℝ) * p n)) :
    Tendsto (fun u : ℝ => ∑' n : ℕ, p n * (∑ k ∈ Finset.range n, u ^ k))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' n : ℕ, (n : ℝ) * p n)) := by
  apply tendsto_tsum_of_dominated_convergence hsumm
  · intro n
    rw [mul_comm (n : ℝ) (p n)]
    exact tendsto_const_nhds.mul (tendsto_geom_sum n)
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with u hu n
    have hu0 : 0 ≤ u := hu.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp n)
      (Finset.sum_nonneg fun k _ => pow_nonneg hu0 k)), mul_comm (n : ℝ) (p n)]
    refine mul_le_mul_of_nonneg_left ?_ (hp n)
    simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => pow_le_one₀ hu0 hu.2.le

/-- **Finiteness of the mean.** A finite left derivative `L` at `1` forces `fun n => n * p n` to be
summable. -/
lemma summable_of_deriv {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    {L : ℝ} (hL : HasDerivWithinAt (pgf p) L (Set.Iio 1) 1) :
    Summable (fun n : ℕ => (n : ℝ) * p n) := by
  have hslope : Tendsto (slope (pgf p) 1) (𝓝[<] (1 : ℝ)) (𝓝 L) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hL
  refine summable_of_sum_range_le (c := L) (fun n => mul_nonneg n.cast_nonneg (hp n)) fun N => ?_
  have hleft : Tendsto
      (fun u : ℝ => ∑ n ∈ Finset.range N, p n * (∑ k ∈ Finset.range n, u ^ k))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑ n ∈ Finset.range N, (n : ℝ) * p n)) := by
    rw [Finset.sum_congr rfl fun (n : ℕ) _ => mul_comm (n : ℝ) (p n)]
    exact tendsto_finsetSum _ fun n _ => tendsto_const_nhds.mul (tendsto_geom_sum n)
  have hineq : ∀ᶠ u in 𝓝[<] (1 : ℝ),
      (∑ n ∈ Finset.range N, p n * (∑ k ∈ Finset.range n, u ^ k)) ≤
        slope (pgf p) 1 u := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hd : (0 : ℝ) < 1 - u := by linarith [hu.2]
    rw [slope_eq_double_sum hp hsum hu0 hu.2]
    have hnn : ∀ n : ℕ, 0 ≤ p n * (∑ k ∈ Finset.range n, u ^ k) := fun n =>
      mul_nonneg (hp n) (Finset.sum_nonneg fun k _ => pow_nonneg hu0 k)
    have hbound : ∀ n : ℕ, p n * (∑ k ∈ Finset.range n, u ^ k) ≤ p n * (1 / (1 - u)) := by
      intro n
      refine mul_le_mul_of_nonneg_left ?_ (hp n)
      have hgeom : ∑ k ∈ Finset.range n, u ^ k = (1 - u ^ n) / (1 - u) := by
        rw [geom_sum_eq hu.2.ne, div_eq_div_iff (sub_ne_zero_of_ne hu.2.ne) hd.ne']
        ring
      rw [hgeom, div_le_div_iff_of_pos_right hd]
      linarith [pow_nonneg hu0 n]
    exact Summable.sum_le_tsum (Finset.range N) (fun n _ => hnn n)
      (Summable.of_nonneg_of_le hnn hbound (hsum.summable.mul_right (1 / (1 - u))))
  exact le_of_tendsto_of_tendsto hleft hslope hineq

/-! ## The theorem -/

/-- Abel-type mean theorem for PGFs. Let `p : ℕ → ℝ` be a pmf (`0 ≤ p n` and `HasSum p 1`) with pgf
`F = pgf p`. If `F` is differentiable from the left at `u = 1` with finite derivative `L` (i.e.
`HasDerivWithinAt (pgf p) L (Set.Iio 1) 1`, equivalently the difference quotient
`(F u - F 1) / (u - 1) → L` as `u → 1⁻`), then `∑ n * p n` converges and equals `L`. -/
@[bsd_tamagawa "T037a"]
theorem main_theorem (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) (L : ℝ)
    (hL : HasDerivWithinAt (pgf p) L (Set.Iio 1) 1) :
    Summable (fun n : ℕ => (n : ℝ) * p n) ∧ ∑' n : ℕ, (n : ℝ) * p n = L := by
  have hsumm := summable_of_deriv hp hsum hL
  refine ⟨hsumm, tendsto_nhds_unique (tendsto_double_sum hp hsumm) ?_⟩
  refine ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hL).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with u hu
  exact slope_eq_double_sum hp hsum hu.1.le hu.2

end BSDTamagawa.PGFMean
