/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import BSDTamagawa.Attr

/-!
# Termwise logarithmic differentiation of an infinite product at `w = 1`

Let `(h i)` be a family of real functions on `[0,1]` with `h i 1 = 1` and
`A i := sup_{[0,1]} |(h i)'|` summable. Then for `η ∈ (0,1]` with `2 A_sup η ≤ 1`:

* the series `L w = ∑ᵢ log (h i w)` converges uniformly on `[1-η, 1]`;
* the product `G w = ∏ᵢ h i w` is well defined there and equals `exp (L w)`;
* `G` is differentiable at `w = 1` from the left, with `G'(1) = G(1) · L'(1) = ∑ᵢ (h i)'(1)`.

## Main definitions

* `BSDTamagawa.LogDerivProduct.ProdHyp`: the hypotheses on `h`, `A`, `A_sup` and `η`.
* `BSDTamagawa.LogDerivProduct.prodG`: the infinite product `G w = exp (∑' i, log (h i w))`.

## Main results

* `BSDTamagawa.LogDerivProduct.tendstoUniformlyOn_logSum`: uniform convergence of `L` on the window
  `[1-η, 1]`.
* `BSDTamagawa.LogDerivProduct.hasProd_prodG`: the partial products converge to `prodG h w`.
* `BSDTamagawa.LogDerivProduct.hasDerivWithinAt_logSum`: `L'(1⁻) = ∑ᵢ (h i)'(1)`.
* `BSDTamagawa.LogDerivProduct.hasDerivWithinAt_prodG`: `G'(1⁻) = ∑ᵢ (h i)'(1)`.
* `BSDTamagawa.LogDerivProduct.hasDerivAt_prodG`: `G'(w) = G(w) · ∑ᵢ (h i)'(w) / h i w` in the
  interior of the window.

## Implementation notes

Since `w = 1` is the right endpoint of the domain and nothing is assumed to the right of `1`, the
derivative there is one-sided: `HasDerivWithinAt (prodG h) _ (Set.Iio 1) 1`. The `Set.Iic 1`
variant `hasDerivWithinAt_Iic_prodG` determines `derivWithin`, since `Set.Iic 1` has
`UniqueDiffWithinAt` at `1`.
-/

@[expose] public section

namespace BSDTamagawa.LogDerivProduct

open Filter Set
open scoped Topology

/-! ## §0. Two analytic lemmas -/

/-- `|log x| ≤ 2 |x - 1|` for `x ≥ 1/2`. -/
theorem abs_log_le_two_abs_sub_one {x : ℝ} (h1 : 1 / 2 ≤ x) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hx : 0 < x := by linarith
  have hupper : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  have hlower : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx
  have hinv : x⁻¹ ≤ 2 := by rw [inv_le_comm₀ hx (by norm_num)]; linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hlow : -(2 * |x - 1|) ≤ 1 - x⁻¹ := by
      have hxx : (1:ℝ) - x⁻¹ = (x - 1) / x := by field_simp
      rw [hxx]
      rcases le_or_gt x 1 with hle | hgt
      · rw [abs_of_nonpos (by linarith), le_div_iff₀ hx]; nlinarith
      · rw [abs_of_pos (by linarith), le_div_iff₀ hx]; nlinarith
    linarith
  · calc Real.log x ≤ x - 1 := hupper
      _ ≤ |x - 1| := le_abs_self _
      _ ≤ 2 * |x - 1| := by nlinarith [abs_nonneg (x - 1)]

/-- Mean value theorem on `[1 - η, 1]`, measured from the right endpoint: a function differentiable
there with derivative bounded by `M` moves by at most `M |y - 1|`. -/
theorem abs_sub_one_le_of_deriv_le {f : ℝ → ℝ} {M y η : ℝ} (hη : 0 ≤ η)
    (hdiff : ∀ x ∈ Icc (1 - η) 1, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ Icc (1 - η) 1, |deriv f x| ≤ M) (hy : y ∈ Icc (1 - η) 1) :
    |f y - f 1| ≤ M * |y - 1| := by
  have h1 : (1:ℝ) ∈ Icc (1 - η) 1 := ⟨by linarith, le_rfl⟩
  simpa [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le hdiff
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx) (convex_Icc _ _) h1 hy

/-- **Termwise logarithmic differentiation of an infinite product on an open interval.** If a
family `f i` of nowhere-vanishing differentiable functions has logarithmic derivatives dominated by
a summable family `u`, then `x ↦ exp (∑' i, log (f i x))` — that is, `∏' i, f i x` — is
differentiable with the expected logarithmic derivative. -/
private lemma hasDerivAt_exp_tsum_log {ι : Type*} {f f' : ι → ℝ → ℝ} {u : ι → ℝ} {a b w : ℝ}
    (hu : Summable u) (hw : w ∈ Ioo a b)
    (hf : ∀ i, ∀ x ∈ Ioo a b, HasDerivAt (f i) (f' i x) x)
    (hne : ∀ i, ∀ x ∈ Ioo a b, f i x ≠ 0)
    (hbound : ∀ i, ∀ x ∈ Ioo a b, |f' i x / f i x| ≤ u i)
    (hlog : Summable fun i => Real.log (f i w)) :
    HasDerivAt (fun x => Real.exp (∑' i, Real.log (f i x)))
      (Real.exp (∑' i, Real.log (f i w)) * ∑' i, f' i w / f i w) w :=
  (hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun i x hx => (hf i x hx).log (hne i x hx))
    (fun i x hx => by rw [Real.norm_eq_abs]; exact hbound i x hx) hw hlog hw).exp

/-! ## §1. The hypothesis package and the product -/

/-- The hypotheses on the family `h`: normalised at `1`, differentiable at each point of `[0,1]`,
with `|(h i)'| ≤ A i` on `[0,1]` for a summable non-negative family `A` bounded by `A_sup`, and a
window radius `η ∈ (0, 1]` with `2 · A_sup · η ≤ 1`. -/
structure ProdHyp {ι : Type*} (h : ι → ℝ → ℝ) (A : ι → ℝ) (A_sup η : ℝ) : Prop where
  /-- Normalisation: `h i 1 = 1`. -/
  normalisation : ∀ i, h i 1 = 1
  /-- Each `h i` is differentiable on the closed unit interval. -/
  diff : ∀ i, ∀ w ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (h i) w
  /-- Uniform bound `|(h i)'| ≤ A i` on the closed unit interval. -/
  bound_deriv : ∀ i, ∀ w ∈ Icc (0:ℝ) 1, |deriv (h i) w| ≤ A i
  /-- The bound family `A` is non-negative. -/
  A_nonneg : ∀ i, 0 ≤ A i
  /-- The bound family `A` is summable. -/
  summable_A : Summable A
  /-- `A_sup` is non-negative. -/
  A_sup_nonneg : 0 ≤ A_sup
  /-- `A_sup` dominates every `A i`. -/
  A_sup_bound : ∀ i, A i ≤ A_sup
  /-- The window radius is positive. -/
  eta_pos : 0 < η
  /-- The window radius is at most `1`. -/
  eta_le_one : η ≤ 1
  /-- Window constant: `2 · A_sup · η ≤ 1`, i.e. `η ≤ 1 / (2 A_sup)`. -/
  domain_const : 2 * A_sup * η ≤ 1

/-- The infinite product `G w = ∏' i, h i w`, defined as `exp (∑' i, log (h i w))`. -/
noncomputable def prodG {ι : Type*} (h : ι → ℝ → ℝ) (w : ℝ) : ℝ :=
  Real.exp (∑' i, Real.log (h i w))

/-- The normalisation point `1` lies in the closed unit interval, where the bounds of `ProdHyp`
live. -/
theorem one_mem_unitInterval : (1:ℝ) ∈ Icc (0:ℝ) 1 :=
  ⟨zero_le_one, le_rfl⟩

variable {ι : Type*} {h : ι → ℝ → ℝ} {A : ι → ℝ} {A_sup η : ℝ} (H : ProdHyp h A A_sup η)

include H

/-- The window `[1 - η, 1]` sits inside `[0, 1]`, where the hypotheses of `ProdHyp` live. -/
theorem subset_unitInterval : Icc (1 - η) 1 ⊆ Icc (0:ℝ) 1 :=
  fun _ hx => ⟨by linarith [hx.1, H.eta_le_one], hx.2⟩

/-- The normalisation point `1` lies in the window. -/
theorem one_mem_window : (1:ℝ) ∈ Icc (1 - η) 1 :=
  ⟨by linarith [H.eta_pos], le_rfl⟩

/-- The left endpoint of the window is to the left of `1`. -/
theorem window_lt_one : 1 - η < 1 := by linarith [H.eta_pos]

/-! ## §2. Uniform local bounds on the window `[1-η, 1]` -/

/-- `|h i w - 1| ≤ A i |w - 1|` on the window. -/
theorem abs_sub_one_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |h i w - 1| ≤ A i * |w - 1| := by
  have hkey := abs_sub_one_le_of_deriv_le (f := h i) (M := A i) H.eta_pos.le
    (fun x hx => H.diff i x (subset_unitInterval H hx))
    (fun x hx => H.bound_deriv i x (subset_unitInterval H hx)) hw
  rwa [H.normalisation i] at hkey

/-- No factor comes near `0` on the window: `h i w ∈ [1/2, 3/2]`. -/
theorem factor_bounds (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    1 / 2 ≤ h i w ∧ h i w ≤ 3 / 2 := by
  have hd : |w - 1| ≤ η := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2, H.eta_pos]⟩
  have h1 : A i * |w - 1| ≤ A_sup * η := mul_le_mul (H.A_sup_bound i) hd (abs_nonneg _)
    ((H.A_nonneg i).trans (H.A_sup_bound i))
  have hfin := abs_le.1 (show |h i w - 1| ≤ 1 / 2 by
    linarith [H.domain_const, abs_sub_one_le H i hw])
  constructor <;> linarith [hfin.1, hfin.2]

/-- Positivity of each factor on the window. -/
theorem factor_pos (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) : 0 < h i w := by
  linarith [(factor_bounds H i hw).1]

/-- `|log (h i w)| ≤ 2 A i |w - 1|` on the window. -/
theorem abs_log_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |Real.log (h i w)| ≤ 2 * A i * |w - 1| := by
  linarith [abs_log_le_two_abs_sub_one (factor_bounds H i hw).1, abs_sub_one_le H i hw]

/-- The window-uniform form of `abs_log_le`: `|log (h i w)| ≤ 2 η A i`. -/
theorem abs_log_le_window (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |Real.log (h i w)| ≤ 2 * η * A i := by
  have hd : |w - 1| ≤ η := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2, H.eta_pos]⟩
  linarith [abs_log_le H i hw, mul_le_mul_of_nonneg_left hd (H.A_nonneg i)]

/-- `|(h i)'(w) / h i w| ≤ 2 A i` on the window. -/
theorem abs_logDeriv_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |deriv (h i) w / h i w| ≤ 2 * A i := by
  have hpos := factor_pos H i hw
  have hb := (factor_bounds H i hw).1
  have hA := H.A_nonneg i
  have hd := H.bound_deriv i w (subset_unitInterval H hw)
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith [mul_nonneg hA (show (0:ℝ) ≤ 2 * h i w - 1 by linarith)]

/-! ## §3. Summability and uniform convergence -/

/-- The log-series converges at every point of the window. -/
theorem summable_log {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    Summable fun i => Real.log (h i w) := by
  refine Summable.of_norm_bounded (g := fun i => 2 * η * A i)
    (H.summable_A.mul_left (2 * η)) fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_log_le_window H i hw

/-- The logarithmic-derivative series converges at every point of the window. -/
theorem summable_logDeriv {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    Summable fun i => deriv (h i) w / h i w := by
  refine Summable.of_norm_bounded (g := fun i => 2 * A i)
    (H.summable_A.mul_left 2) fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_logDeriv_le H i hw

/-- The corner series `∑ᵢ (h i)'(1)` converges absolutely. -/
theorem summable_deriv_one : Summable fun i => deriv (h i) 1 := by
  refine Summable.of_norm_bounded (g := A) H.summable_A fun i => ?_
  rw [Real.norm_eq_abs]
  exact H.bound_deriv i 1 (one_mem_unitInterval)

/-- Uniform convergence: the partial sums of `L w = ∑ᵢ log (h i w)` converge to `L` uniformly on
the window `[1-η, 1]`. -/
@[bsd_tamagawa "T047"]
theorem tendstoUniformlyOn_logSum :
    TendstoUniformlyOn (fun s : Finset ι => fun w => ∑ i ∈ s, Real.log (h i w))
      (fun w => ∑' i, Real.log (h i w)) atTop (Icc (1 - η) 1) :=
  tendstoUniformlyOn_tsum (u := fun i => 2 * η * A i) (H.summable_A.mul_left (2 * η))
    fun i w hw => by rw [Real.norm_eq_abs]; exact abs_log_le_window H i hw

/-- The product is well defined: on the window the net of finite partial products
`s ↦ ∏ i ∈ s, h i w` converges to `prodG h w`; that is, `prodG h w` *is* the infinite product
`∏' i, h i w`, and it equals `exp (L w)` by definition of `prodG`. -/
@[bsd_tamagawa "T047"]
theorem hasProd_prodG {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    HasProd (fun i => h i w) (prodG h w) :=
  Real.hasProd_of_hasSum_log (fun i => factor_pos H i hw) (summable_log H hw).hasSum

/-- `L 1 = 0`: every factor is normalised at `w = 1`. -/
theorem logSum_one : (∑' i, Real.log (h i 1)) = 0 := by
  simp [H.normalisation]

/-- `G 1 = 1`. -/
theorem prodG_one : prodG h 1 = 1 := by
  simp [prodG, H.normalisation]

/-- At `w = 1` the logarithmic-derivative series is the corner series `∑ᵢ (h i)'(1)`. -/
theorem logDerivSum_one : (∑' i, deriv (h i) 1 / h i 1) = ∑' i, deriv (h i) 1 := by
  simp [H.normalisation]

/-! ## §4. The left derivative at `w = 1` -/

/-- The difference quotient of `log (h i)` at `1` is bounded by `2 A i` on the window. At `w = 1`
the quotient is `0` by the `0⁻¹ = 0` convention. -/
theorem abs_slope_log_le (i : ι) {w : ℝ} (hw : w ∈ Icc (1 - η) 1) :
    |(w - 1)⁻¹ * Real.log (h i w)| ≤ 2 * A i := by
  rcases eq_or_ne w 1 with rfl | hne
  · rw [H.normalisation i]
    simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (H.A_nonneg i)
  · have hpos : 0 < |w - 1| := abs_pos.mpr (sub_ne_zero_of_ne hne)
    have hlog := abs_log_le H i hw
    rw [abs_mul, abs_inv, inv_mul_eq_div, div_le_iff₀ hpos]
    linarith

/-- `L w = ∑ᵢ log (h i w)` is differentiable at `w = 1` from the left, with
`L'(1) = ∑ᵢ (h i)'(1) / h i 1 = ∑ᵢ (h i)'(1)`. -/
theorem hasDerivWithinAt_logSum :
    HasDerivWithinAt (fun w => ∑' i, Real.log (h i w)) (∑' i, deriv (h i) 1) (Iio 1) 1 := by
  have hnotmem : (1:ℝ) ∉ Iio (1:ℝ) := by simp
  rw [hasDerivWithinAt_iff_tendsto_slope' hnotmem]
  have hterm : ∀ i, Tendsto (fun w : ℝ => (w - 1)⁻¹ * Real.log (h i w))
      (𝓝[Iio (1:ℝ)] 1) (𝓝 (deriv (h i) 1)) := by
    intro i
    have hd : HasDerivAt (fun w => Real.log (h i w)) (deriv (h i) 1 / h i 1) 1 :=
      ((H.diff i 1 (one_mem_unitInterval)).hasDerivAt).log
        (by rw [H.normalisation i]; norm_num)
    rw [H.normalisation i, div_one] at hd
    have hslope := hd.hasDerivWithinAt (s := Iio (1:ℝ))
    rw [hasDerivWithinAt_iff_tendsto_slope' hnotmem] at hslope
    refine hslope.congr fun w => ?_
    rw [slope_def_field, H.normalisation i, Real.log_one, sub_zero, div_eq_inv_mul]
  have hbnd : ∀ᶠ w in 𝓝[Iio (1:ℝ)] 1, ∀ i, ‖(w - 1)⁻¹ * Real.log (h i w)‖ ≤ 2 * A i := by
    filter_upwards [Ioo_mem_nhdsLT (window_lt_one H)] with w hw i
    rw [Real.norm_eq_abs]
    exact abs_slope_log_le H i ⟨hw.1.le, hw.2.le⟩
  have hconv := tendsto_tsum_of_dominated_convergence
    (f := fun (w : ℝ) (i : ι) => (w - 1)⁻¹ * Real.log (h i w))
    (g := fun i => deriv (h i) 1) (bound := fun i => 2 * A i)
    (H.summable_A.mul_left 2) hterm hbnd
  refine hconv.congr fun w => ?_
  rw [tsum_mul_left, slope_def_field, logSum_one H, sub_zero, div_eq_inv_mul]

/-- `G = ∏' i, h i` is differentiable at `w = 1` from the left, with

  `G'(1) = G(1) · L'(1) = ∑ᵢ (h i)'(1)`,

the factor `G(1) = 1` coming from the normalisation. -/
@[bsd_tamagawa "T047"]
theorem hasDerivWithinAt_prodG :
    HasDerivWithinAt (prodG h) (∑' i, deriv (h i) 1) (Iio 1) 1 := by
  have hexp := (hasDerivWithinAt_logSum H).exp
  rw [logSum_one H, Real.exp_zero, one_mul] at hexp
  exact hexp

/-- The `Set.Iic 1` form of `hasDerivWithinAt_prodG`. -/
theorem hasDerivWithinAt_Iic_prodG :
    HasDerivWithinAt (prodG h) (∑' i, deriv (h i) 1) (Iic 1) 1 :=
  (hasDerivWithinAt_prodG H).Iic_of_Iio

/-- `derivWithin (prodG h) (Set.Iic 1) 1 = ∑ᵢ (h i)'(1)`. -/
theorem derivWithin_prodG_one :
    derivWithin (prodG h) (Iic 1) 1 = ∑' i, deriv (h i) 1 :=
  (hasDerivWithinAt_Iic_prodG H).derivWithin (uniqueDiffOn_Iic 1 1 (mem_Iic.mpr le_rfl))

/-! ## §5. The interior derivative -/

/-- **Termwise logarithmic differentiation in the interior.** For `1 - η < w < 1`,

  `G'(w) = G(w) · ∑ᵢ (h i)'(w) / h i w`. -/
theorem hasDerivAt_prodG {w : ℝ} (hw : w ∈ Ioo (1 - η) 1) :
    HasDerivAt (prodG h) (prodG h w * ∑' i, deriv (h i) w / h i w) w :=
  hasDerivAt_exp_tsum_log (f := h) (f' := fun i => deriv (h i))
    (H.summable_A.mul_left 2) hw
    (fun i x hx => (H.diff i x (subset_unitInterval H (Ioo_subset_Icc_self hx))).hasDerivAt)
    (fun i _ hx => (factor_pos H i (Ioo_subset_Icc_self hx)).ne')
    (fun i _ hx => abs_logDeriv_le H i (Ioo_subset_Icc_self hx))
    (summable_log H (Ioo_subset_Icc_self hw))

/-- `derivWithin (prodG h) (Set.Iic 1) w = G(w) · ∑ᵢ (h i)'(w) / h i w` at interior points: there
`Set.Iic 1` is a neighbourhood of `w`, so the one-sided derivative is the two-sided one. -/
theorem derivWithin_prodG_of_mem_Ioo {w : ℝ} (hw : w ∈ Ioo (1 - η) 1) :
    derivWithin (prodG h) (Iic 1) w = prodG h w * ∑' i, deriv (h i) w / h i w :=
  (hasDerivAt_prodG H hw).hasDerivWithinAt.derivWithin (uniqueDiffOn_Iic 1 w hw.2.le)

end BSDTamagawa.LogDerivProduct
