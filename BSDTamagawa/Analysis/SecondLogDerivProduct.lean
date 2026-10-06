/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Analysis.LogDerivProduct

/-!
# Termwise second logarithmic differentiation of an infinite product at `w = 1`

Let `(h i)` be a family of real functions on `[0,1]` with `h i 1 = 1`, `|(h i)'| ≤ A i` and `A`
summable, and let `η ∈ (0,1]` with `2 A_sup η ≤ 1`. Assume in addition that each `h i` is twice
differentiable on `[0,1]` with `|(h i)''| ≤ B i` and `B` summable. Then `G = ∏' i, h i` is twice
differentiable at `w = 1` from the left and

  `G''(1) = ∑ᵢ (h i)''(1) + (∑ᵢ (h i)'(1))² − ∑ᵢ (h i)'(1)².`

## Main definitions

* `BSDTamagawa.SecondLogDerivProduct.DerivHyp`: the second-order hypotheses on `h` and `B`.

## Main results

* `BSDTamagawa.SecondLogDerivProduct.hasDerivWithinAt_logDerivSum`: the left derivative at `1` of
  `M = ∑ᵢ (h i)'/h i` is `∑ᵢ ((h i)''(1) − (h i)'(1)²)`.
* `BSDTamagawa.SecondLogDerivProduct.hasDerivWithinAt_derivWithin_prodG`: the second left
  derivative of `G` at `1` exists, with the value above.
* `BSDTamagawa.SecondLogDerivProduct.derivWithin_derivWithin_prodG_one`: the identity for `G''(1)`
  above.

## Implementation notes

Since `w = 1` is the right endpoint of the domain, both derivatives are one-sided. The first
derivative of `G` is `derivWithin (prodG h) (Set.Iic 1)`, whose value at `1` is determined because
`Set.Iic 1` has `UniqueDiffWithinAt` at `1`.
-/

@[expose] public section

namespace BSDTamagawa.SecondLogDerivProduct

open Filter Set BSDTamagawa.LogDerivProduct
open scoped Topology

/-! ## §1. The second-order hypothesis package -/

/-- The second-order hypotheses: each `h i` is twice differentiable on `[0,1]` with
`|(h i)''| ≤ B i` for a summable non-negative `B`. -/
structure DerivHyp {ι : Type*} (h : ι → ℝ → ℝ) (B : ι → ℝ) : Prop where
  /-- Each `(h i)'` is differentiable on the closed unit interval. -/
  diff2 : ∀ i, ∀ w ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (deriv (h i)) w
  /-- Uniform bound `|(h i)''| ≤ B i` on the closed unit interval. -/
  bound_deriv2 : ∀ i, ∀ w ∈ Icc (0:ℝ) 1, |deriv (deriv (h i)) w| ≤ B i
  /-- The bound family `B` is non-negative. -/
  B_nonneg : ∀ i, 0 ≤ B i
  /-- The bound family `B` is summable. -/
  summable_B : Summable B

variable {ι : Type*} {h : ι → ℝ → ℝ} {A B : ι → ℝ} {A_sup η : ℝ}
  (H : ProdHyp h A A_sup η) (HB : DerivHyp h B)

include H HB

/-! ## §2. The quotient-rule term and its uniform bound -/

/-- **The termwise derivative of the logarithmic-derivative series.** On the window the `i`-th term
`(h i)'/h i` of `M` is differentiable, with the quotient-rule derivative

  `((h i)''(w) · h i w − (h i)'(w)²) / (h i w)²`. -/
theorem hasDerivAt_logDerivTerm (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    HasDerivAt (fun x => deriv (h i) x / h i x)
      ((deriv (deriv (h i)) w * h i w - deriv (h i) w ^ 2) / h i w ^ 2) w := by
  have hnum : HasDerivAt (deriv (h i)) (deriv (deriv (h i)) w) w :=
    (HB.diff2 i w (subset_unitInterval H hw)).hasDerivAt
  have hden : HasDerivAt (h i) (deriv (h i) w) w :=
    (H.diff i w (subset_unitInterval H hw)).hasDerivAt
  exact (hnum.div hden (factor_pos H i hw).ne').congr_deriv (by ring)

/-- The derivative of the `i`-th term in closed form. -/
theorem deriv_logDerivTerm (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    deriv (fun x => deriv (h i) x / h i x) w
      = (deriv (deriv (h i)) w * h i w - deriv (h i) w ^ 2) / h i w ^ 2 :=
  (hasDerivAt_logDerivTerm H HB i hw).deriv

/-- **The quotient-rule estimate.** On the window

  `|((h i)'' · h i − ((h i)')²) / (h i)²| ≤ 6 B i + 4 A_sup A i`. -/
theorem abs_quotient_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |(deriv (deriv (h i)) w * h i w - deriv (h i) w ^ 2) / h i w ^ 2|
      ≤ 6 * B i + 4 * A_sup * A i := by
  have hpos := factor_pos H i hw
  have hb := factor_bounds H i hw
  have hmem := subset_unitInterval H hw
  have hB := HB.bound_deriv2 i w hmem
  have hA := H.bound_deriv i w hmem
  have hAnn := H.A_nonneg i
  have hBnn := HB.B_nonneg i
  have hsq : (0:ℝ) < h i w ^ 2 := by positivity
  rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
  have hnum : |deriv (deriv (h i)) w * h i w - deriv (h i) w ^ 2|
      ≤ 3 / 2 * B i + A i * A i := by
    have hhabs : |h i w| ≤ 3 / 2 := (abs_of_pos hpos).trans_le hb.2
    calc |deriv (deriv (h i)) w * h i w - deriv (h i) w ^ 2|
        ≤ |deriv (deriv (h i)) w * h i w| + |deriv (h i) w ^ 2| := abs_sub _ _
      _ = |deriv (deriv (h i)) w| * |h i w| + |deriv (h i) w| * |deriv (h i) w| := by
          rw [abs_mul, abs_pow, pow_two]
      _ ≤ B i * (3 / 2) + A i * A i :=
          add_le_add (mul_le_mul hB hhabs (abs_nonneg _) hBnn)
            (mul_le_mul hA hA (abs_nonneg _) hAnn)
      _ = 3 / 2 * B i + A i * A i := by ring
  have hAA : A i * A i ≤ A_sup * A i := mul_le_mul_of_nonneg_right (H.A_sup_bound i) hAnn
  have hcoeff : (0:ℝ) ≤ 6 * B i + 4 * A_sup * A i := by
    nlinarith [mul_nonneg H.A_sup_nonneg hAnn]
  have hh2 : (1 / 4 : ℝ) ≤ h i w ^ 2 := by nlinarith [hb.1]
  linarith [mul_le_mul_of_nonneg_left hh2 hcoeff]

/-- The mean value theorem applied to the `i`-th term of `M`, measured from `w = 1`: the term moves
by at most `(6 B i + 4 A_sup A i) |w - 1|`. -/
theorem abs_sub_logDerivTerm_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |deriv (h i) w / h i w - deriv (h i) 1| ≤ (6 * B i + 4 * A_sup * A i) * |w - 1| := by
  have hkey := abs_sub_one_le_of_deriv_le (f := fun x => deriv (h i) x / h i x)
    (M := 6 * B i + 4 * A_sup * A i) H.eta_pos.le
    (fun x hx => (hasDerivAt_logDerivTerm H HB i hx).differentiableAt)
    (fun x hx => deriv_logDerivTerm H HB i hx ▸ abs_quotient_le H HB i hx) hw
  rwa [H.normalisation i, div_one] at hkey

/-- The difference quotient of the `i`-th term of `M` at `1` is bounded by `6 B i + 4 A_sup A i` on
the window. At `w = 1` the quotient is `0` by the `0⁻¹ = 0` convention. -/
theorem abs_slope_logDerivTerm_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |(w - 1)⁻¹ * (deriv (h i) w / h i w - deriv (h i) 1)| ≤ 6 * B i + 4 * A_sup * A i := by
  have hcoeff : (0:ℝ) ≤ 6 * B i + 4 * A_sup * A i := by
    nlinarith [mul_nonneg H.A_sup_nonneg (H.A_nonneg i), HB.B_nonneg i]
  rcases eq_or_ne w 1 with rfl | hne
  · rw [H.normalisation i]
    simpa using hcoeff
  · have hpos : 0 < |w - 1| := abs_pos.mpr (sub_ne_zero_of_ne hne)
    have hstep := abs_sub_logDerivTerm_le H HB i hw
    rw [abs_mul, abs_inv, inv_mul_eq_div, div_le_iff₀ hpos]
    linarith

/-! ## §3. Summability of the corner series -/

omit H in
/-- `∑ᵢ (h i)''(1)` converges absolutely. -/
theorem summable_deriv2_one : Summable fun i => deriv (deriv (h i)) 1 := by
  refine Summable.of_norm_bounded (g := B) HB.summable_B fun i => ?_
  rw [Real.norm_eq_abs]
  exact HB.bound_deriv2 i 1 one_mem_unitInterval

omit HB in
/-- `∑ᵢ (h i)'(1)²` converges absolutely, because `(h i)'(1)² ≤ A_sup · A i`. -/
theorem summable_deriv_one_sq : Summable fun i => deriv (h i) 1 ^ 2 := by
  refine Summable.of_norm_bounded (g := fun i => A_sup * A i)
    (H.summable_A.mul_left A_sup) fun i => ?_
  rw [Real.norm_eq_abs]
  have hA := H.bound_deriv i 1 one_mem_unitInterval
  calc |deriv (h i) 1 ^ 2| = |deriv (h i) 1| * |deriv (h i) 1| := by rw [abs_pow, pow_two]
    _ ≤ A_sup * A i := mul_le_mul (hA.trans (H.A_sup_bound i)) hA (abs_nonneg _) H.A_sup_nonneg

/-- `∑ᵢ ((h i)''(1) − (h i)'(1)²) = ∑ᵢ (h i)''(1) − ∑ᵢ (h i)'(1)²`. -/
theorem tsum_secondLogDeriv :
    (∑' i, (deriv (deriv (h i)) 1 - deriv (h i) 1 ^ 2))
      = (∑' i, deriv (deriv (h i)) 1) - ∑' i, deriv (h i) 1 ^ 2 :=
  (summable_deriv2_one HB).tsum_sub (summable_deriv_one_sq H)

/-! ## §4. The left derivative of `M` at `w = 1` -/

/-- **`M'(1) = ∑ᵢ ((h i)''(1) − (h i)'(1)²)`.** The logarithmic-derivative series
`M w = ∑ᵢ (h i)'(w) / h i w` is differentiable at `w = 1` from the left. -/
theorem hasDerivWithinAt_logDerivSum :
    HasDerivWithinAt (fun w => ∑' i, deriv (h i) w / h i w)
      (∑' i, (deriv (deriv (h i)) 1 - deriv (h i) 1 ^ 2)) (Iio 1) 1 := by
  have hnotmem : (1:ℝ) ∉ Iio (1:ℝ) := by simp
  rw [hasDerivWithinAt_iff_tendsto_slope' hnotmem]
  have hterm : ∀ i, Tendsto (fun w : ℝ => (w - 1)⁻¹ * (deriv (h i) w / h i w - deriv (h i) 1))
      (𝓝[Iio (1:ℝ)] 1) (𝓝 (deriv (deriv (h i)) 1 - deriv (h i) 1 ^ 2)) := by
    intro i
    have hd := hasDerivAt_logDerivTerm H HB i (one_mem_window H)
    rw [H.normalisation i, mul_one, one_pow, div_one] at hd
    have hslope := hd.hasDerivWithinAt (s := Iio (1:ℝ))
    rw [hasDerivWithinAt_iff_tendsto_slope' hnotmem] at hslope
    refine hslope.congr fun w => ?_
    rw [slope_def_field, H.normalisation i, div_one, div_eq_inv_mul]
  have hbnd : ∀ᶠ w in 𝓝[Iio (1:ℝ)] 1,
      ∀ i, ‖(w - 1)⁻¹ * (deriv (h i) w / h i w - deriv (h i) 1)‖ ≤ 6 * B i + 4 * A_sup * A i := by
    filter_upwards [Ioo_mem_nhdsLT (window_lt_one H)] with w hw i
    rw [Real.norm_eq_abs]
    exact abs_slope_logDerivTerm_le H HB i ⟨hw.1.le, hw.2.le⟩
  have hconv := tendsto_tsum_of_dominated_convergence
    (f := fun (w : ℝ) (i : ι) => (w - 1)⁻¹ * (deriv (h i) w / h i w - deriv (h i) 1))
    (g := fun i => deriv (deriv (h i)) 1 - deriv (h i) 1 ^ 2)
    (bound := fun i => 6 * B i + 4 * A_sup * A i)
    ((HB.summable_B.mul_left 6).add (H.summable_A.mul_left (4 * A_sup))) hterm hbnd
  refine hconv.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (window_lt_one H)] with w hw
  rw [tsum_mul_left,
    Summable.tsum_sub (summable_logDeriv H ⟨hw.1.le, hw.2.le⟩) (summable_deriv_one H),
    slope_def_field, logDerivSum_one H, div_eq_inv_mul]

/-! ## §5. The second derivative of `G` at `w = 1` -/

/-- The product rule on `G' = G · M` at the corner:

  `(G · M)'(1) = G'(1) M(1) + G(1) M'(1) = (∑ᵢ (h i)'(1))² + ∑ᵢ ((h i)''(1) − (h i)'(1)²)`,

using `G(1) = 1` and `M(1) = ∑ᵢ (h i)'(1) = G'(1)`. -/
theorem hasDerivWithinAt_prodG_mul_logDerivSum :
    HasDerivWithinAt (fun w => prodG h w * ∑' i, deriv (h i) w / h i w)
      ((∑' i, deriv (h i) 1) * (∑' i, deriv (h i) 1)
        + ∑' i, (deriv (deriv (h i)) 1 - deriv (h i) 1 ^ 2)) (Iio 1) 1 := by
  have hmul := (hasDerivWithinAt_prodG H).mul (hasDerivWithinAt_logDerivSum H HB)
  rwa [logDerivSum_one H, prodG_one H, one_mul] at hmul

/-- `G` is twice differentiable at `w = 1` from the left: its first derivative
`derivWithin (prodG h) (Set.Iic 1)` has a left derivative at `1`, equal to

  `∑ᵢ (h i)''(1) + (∑ᵢ (h i)'(1))² − ∑ᵢ (h i)'(1)²`. -/
@[bsd_tamagawa "T047d"]
theorem hasDerivWithinAt_derivWithin_prodG :
    HasDerivWithinAt (fun w => derivWithin (prodG h) (Iic 1) w)
      ((∑' i, deriv (deriv (h i)) 1) + (∑' i, deriv (h i) 1) ^ 2
        - ∑' i, deriv (h i) 1 ^ 2) (Iio 1) 1 := by
  have hvalue : (∑' i, deriv (h i) 1) * (∑' i, deriv (h i) 1)
        + ∑' i, (deriv (deriv (h i)) 1 - deriv (h i) 1 ^ 2)
      = (∑' i, deriv (deriv (h i)) 1) + (∑' i, deriv (h i) 1) ^ 2
        - ∑' i, deriv (h i) 1 ^ 2 := by
    rw [tsum_secondLogDeriv H HB]
    ring
  rw [← hvalue]
  refine (hasDerivWithinAt_prodG_mul_logDerivSum H HB).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (window_lt_one H)] with w hw
    exact derivWithin_prodG_of_mem_Ioo H hw
  · rw [derivWithin_prodG_one H, prodG_one H, one_mul, logDerivSum_one H]

/-- `G''(1) = ∑ᵢ (h i)''(1) + (∑ᵢ (h i)'(1))² − ∑ᵢ (h i)'(1)²`, with both derivatives taken within
`Set.Iic 1`. -/
@[bsd_tamagawa "T047d"]
theorem derivWithin_derivWithin_prodG_one :
    derivWithin (derivWithin (prodG h) (Iic 1)) (Iic 1) 1
      = (∑' i, deriv (deriv (h i)) 1) + (∑' i, deriv (h i) 1) ^ 2
        - ∑' i, deriv (h i) 1 ^ 2 :=
  (hasDerivWithinAt_derivWithin_prodG H HB).Iic_of_Iio.derivWithin
    (uniqueDiffOn_Iic 1 1 (mem_Iic.mpr le_rfl))

end BSDTamagawa.SecondLogDerivProduct
