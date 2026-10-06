/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.PGFMean
public import BSDTamagawa.PrimeCount.GeneratingFunctionIdentity
public import BSDTamagawa.Analysis.LogDerivProduct

/-!
# The first derivative of the Euler product `F` at `u = 1`

The restriction of the Euler product `F(u) = ∏_p (δ_p(1) + (1 - δ_p(1)) u)` to `[0,1]` is
differentiable at `u = 1` from the left, and

  `F'(1) = ∑_p (1 - δ_p(1)) < ∞`.

On the reals `F` agrees with the probability generating function `∑_r π_r u^r` of the limiting
densities `π_r`, and on `[1/2, 1]` with the real product `∏' p, (1 + a_p (w - 1))`,
`a_p = 1 - δ_p(1)`, to which the termwise differentiation of infinite products applies.

## Main definitions

* `WeierstrassCurve.tamagawaOmegaRealFactor`: the real affine local factor `1 + a_p (w - 1)`.

## Main results

* `WeierstrassCurve.ofReal_pgf_tamagawaOmegaDensity`: `↑(∑_r π_r u^r) = F(↑u)` for real `u`.
* `WeierstrassCurve.hasDerivWithinAt_pgf_tamagawaOmegaDensity`: the real-valued form, `∑_r π_r u^r`
  has left derivative `∑_p (1 - δ_p(1))` at `u = 1`.
* `WeierstrassCurve.hasDerivWithinAt_ofReal_tamagawaOmegaEulerProduct`: `u ↦ F(↑u)` has left
  derivative `∑_p (1 - δ_p(1))` at `u = 1`.

## Implementation notes

The derivative is one-sided, `HasDerivWithinAt _ _ (Set.Iio 1) 1`, since `u = 1` is the right
endpoint of `[0,1]`.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter Set
open scoped Topology
open BSDTamagawa

/-! ### The affine local factor as a real function -/

/-- **The local Euler factor as a function of a real variable**: `h_p(w) = 1 + a_p (w - 1)`, with
`a_p = 1 - δ_p(1)` the local tail mass. -/
noncomputable def tamagawaOmegaRealFactor (p : ℕ) (w : ℝ) : ℝ :=
  1 + tamagawaLocalTailMass p * (w - 1)

/-- Every local tail mass is at most `1`, since `δ_p(1) ≥ 0`. -/
theorem tamagawaLocalTailMass_le_one (p : ℕ) : tamagawaLocalTailMass p ≤ 1 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTailMass_of_prime]
    linarith [ENNReal.toReal_nonneg (a := δ p 1)]
  · simp [tamagawaLocalTailMass_of_not_prime hp]

/-- `h_p` is affine, hence differentiable at every real point with derivative the constant
`a_p`. -/
theorem hasDerivAt_tamagawaOmegaRealFactor (p : ℕ) (w : ℝ) :
    HasDerivAt (tamagawaOmegaRealFactor p) (tamagawaLocalTailMass p) w := by
  have h1 : HasDerivAt (fun w : ℝ => w - 1) 1 w := (hasDerivAt_id w).sub_const 1
  have h2 : HasDerivAt (fun w : ℝ => tamagawaLocalTailMass p * (w - 1))
      (tamagawaLocalTailMass p * 1) w := h1.const_mul _
  have h3 : HasDerivAt (fun w : ℝ => 1 + tamagawaLocalTailMass p * (w - 1))
      (tamagawaLocalTailMass p * 1) w := h2.const_add 1
  rw [mul_one] at h3
  exact h3

/-- The derivative of `h_p` is the constant function `a_p`. -/
theorem deriv_tamagawaOmegaRealFactor (p : ℕ) :
    deriv (tamagawaOmegaRealFactor p) = fun _ : ℝ => tamagawaLocalTailMass p :=
  funext fun w => (hasDerivAt_tamagawaOmegaRealFactor p w).deriv

/-- The affine family `h_p` satisfies `LogDerivProduct.ProdHyp` with bound family the local tail
masses `a_p`, `A_sup = 1` and window radius `η = 1/2`; the window is `[1/2, 1]`. -/
theorem prodHyp_tamagawaOmegaRealFactor :
    LogDerivProduct.ProdHyp tamagawaOmegaRealFactor tamagawaLocalTailMass 1 (1 / 2) where
  normalisation p := by simp [tamagawaOmegaRealFactor]
  diff p w _ := (hasDerivAt_tamagawaOmegaRealFactor p w).differentiableAt
  bound_deriv p w _ := by
    rw [(hasDerivAt_tamagawaOmegaRealFactor p w).deriv]
    exact (abs_of_nonneg (tamagawaLocalTailMass_nonneg p)).le
  A_nonneg := tamagawaLocalTailMass_nonneg
  summable_A := summable_tamagawaLocalTailMass
  A_sup_nonneg := zero_le_one
  A_sup_bound := tamagawaLocalTailMass_le_one
  eta_pos := by norm_num
  eta_le_one := by norm_num
  domain_const := by norm_num

/-- Membership in the window `Icc (1 - 1/2) 1`, from membership in `[1/2, 1]`. -/
theorem mem_window_of_mem_Icc {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    w ∈ Icc (1 - 1 / 2 : ℝ) 1 :=
  ⟨by linarith [hw.1], hw.2⟩

/-! ### The real product and the complex Euler product -/

/-- The coerced real factor is the complex local factor at the real point: `↑(h_p w) = F_p(↑w)`. -/
theorem ofReal_tamagawaOmegaRealFactor (p : ℕ) (w : ℝ) :
    ((tamagawaOmegaRealFactor p w : ℝ) : ℂ) = tamagawaOmegaEulerFactor p (w : ℂ) := by
  rw [tamagawaOmegaEulerFactor_eq_one_add, tamagawaOmegaRealFactor]
  push_cast
  ring

/-- On the window `[1/2, 1]` the real infinite product `LogDerivProduct.prodG` of the affine family
coerces to the Euler product `F` at the real point:

  `↑(∏' p, h_p w) = F(↑w)`. -/
theorem ofReal_prodG_tamagawaOmegaRealFactor {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    ((LogDerivProduct.prodG tamagawaOmegaRealFactor w : ℝ) : ℂ) =
      tamagawaOmegaEulerProduct (w : ℂ) := by
  have hmap := (LogDerivProduct.hasProd_prodG prodHyp_tamagawaOmegaRealFactor
    (mem_window_of_mem_Icc hw)).map Complex.ofRealHom Complex.continuous_ofReal
  rw [tamagawaOmegaEulerProduct]
  refine ((hmap.congr_fun fun p => ?_).tprod_eq).symm
  simpa using (ofReal_tamagawaOmegaRealFactor p w).symm

/-- **`PGFMean.pgf π` is the real restriction of `F`.** For every real `u`,

  `↑(∑_r π_r u^r) = F(↑u)`,

with `π_r` the limiting densities. -/
theorem ofReal_pgf_tamagawaOmegaDensity (u : ℝ) :
    ((PGFMean.pgf tamagawaOmegaDensity u : ℝ) : ℂ) = tamagawaOmegaEulerProduct (u : ℂ) := by
  have habs : Summable fun r : ℕ => |tamagawaOmegaDensity r * u ^ r| := by
    refine (summable_norm_tamagawaOmegaDensity_mul_pow (u : ℂ)).congr fun r => ?_
    rw [show ((tamagawaOmegaDensity r : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ r
        = ((tamagawaOmegaDensity r * u ^ r : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hreal : HasSum (fun r : ℕ => tamagawaOmegaDensity r * u ^ r)
      (PGFMean.pgf tamagawaOmegaDensity u) := by
    rw [PGFMean.pgf]
    exact (Summable.of_abs habs).hasSum
  refine (Complex.hasSum_ofReal.mpr hreal).unique ?_
  refine (hasSum_tamagawaOmegaDensity_mul_pow (u : ℂ)).congr_fun fun r => ?_
  push_cast
  ring

/-- On the window `[1/2, 1]` the generating function `PGFMean.pgf π` is the real product
`LogDerivProduct.prodG` of the affine family. -/
theorem pgf_eq_prodG_tamagawaOmegaRealFactor {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    PGFMean.pgf tamagawaOmegaDensity w = LogDerivProduct.prodG tamagawaOmegaRealFactor w :=
  Complex.ofReal_inj.mp
    ((ofReal_pgf_tamagawaOmegaDensity w).trans (ofReal_prodG_tamagawaOmegaRealFactor hw).symm)

/-! ### The first derivative at `u = 1` -/

/-- `∑_p h_p'(1) = ∑_p a_p` for the affine family. -/
theorem tsum_deriv_tamagawaOmegaRealFactor :
    (∑' p : ℕ, deriv (tamagawaOmegaRealFactor p) 1) = ∑' p : ℕ, tamagawaLocalTailMass p :=
  tsum_congr fun p => (hasDerivAt_tamagawaOmegaRealFactor p 1).deriv

/-- The generating function `∑_r π_r u^r` of the limiting densities, which is the restriction of
`F` to the reals, is differentiable at `u = 1` from the left, with

  `F'(1) = ∑_p (1 - δ_p(1))`. -/
@[bsd_tamagawa "T041n"]
theorem hasDerivWithinAt_pgf_tamagawaOmegaDensity :
    HasDerivWithinAt (PGFMean.pgf tamagawaOmegaDensity) (∑' p : ℕ, tamagawaLocalTailMass p)
      (Iio 1) 1 := by
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG prodHyp_tamagawaOmegaRealFactor
  rw [tsum_deriv_tamagawaOmegaRealFactor] at hprod
  refine hprod.congr_of_eventuallyEq ?_
    (pgf_eq_prodG_tamagawaOmegaRealFactor ⟨by norm_num, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
  exact pgf_eq_prodG_tamagawaOmegaRealFactor ⟨hx.1.le, hx.2.le⟩

/-- The restriction of the Euler product `F` to the reals is differentiable at `u = 1` from the
left, with

  `F'(1) = ∑_p (1 - δ_p(1)) < ∞`. -/
@[bsd_tamagawa "T041n"]
theorem hasDerivWithinAt_ofReal_tamagawaOmegaEulerProduct :
    HasDerivWithinAt (fun u : ℝ => tamagawaOmegaEulerProduct (u : ℂ))
      ((∑' p : ℕ, tamagawaLocalTailMass p : ℝ) : ℂ) (Iio 1) 1 := by
  rw [show (fun u : ℝ => tamagawaOmegaEulerProduct (u : ℂ))
      = fun u : ℝ => ((PGFMean.pgf tamagawaOmegaDensity u : ℝ) : ℂ) from
    funext fun u => (ofReal_pgf_tamagawaOmegaDensity u).symm]
  exact hasDerivWithinAt_pgf_tamagawaOmegaDensity.ofReal_comp

end WeierstrassCurve
