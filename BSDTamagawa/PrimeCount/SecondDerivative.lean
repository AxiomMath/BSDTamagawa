/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.PrimeCount.FirstDerivative
public import BSDTamagawa.Analysis.SecondLogDerivProduct

/-!
# The second derivative of the Euler product `F` at `u = 1`

With `a_p := 1 - δ_p(1)`, the restriction of the Euler product `F` to `[0,1]` is twice
differentiable at `u = 1` from the left, and

  `F''(1) = (∑_p a_p)² - ∑_p a_p²`.

The local factors `h_p(w) = 1 + a_p (w - 1)` are affine, so `h_p'' ≡ 0`, and the second-order
termwise differentiation of infinite products gives
`G''(1) = ∑_p h_p''(1) + (∑_p h_p'(1))² - ∑_p h_p'(1)²`, which collapses to the right-hand side.

## Main results

* `WeierstrassCurve.summable_tamagawaLocalTailMass_sq`: `∑_p a_p² < ∞`.
* `WeierstrassCurve.hasDerivWithinAt_derivWithin_pgf_tamagawaOmegaDensity`: the first derivative of
  `F` on the reals, taken within `Set.Iic 1`, has left derivative `(∑_p a_p)² - ∑_p a_p²` at
  `u = 1`.
* `WeierstrassCurve.derivWithin_derivWithin_pgf_tamagawaOmegaDensity_one`:
  `F''(1) = (∑_p a_p)² - ∑_p a_p²`.

## Implementation notes

The first derivative is `derivWithin _ (Set.Iic 1)`, not `derivWithin _ (Set.Iio 1)`: `Set.Iic 1`
has `UniqueDiffWithinAt` at `1`, so it determines the value of the first derivative at the corner.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter Set
open scoped Topology
open BSDTamagawa

/-! ### The second-order hypothesis package -/

/-- The affine family `h_p` satisfies `SecondLogDerivProduct.DerivHyp` with bound family `B = 0`:
each `h_p'` is the constant `a_p`, so `h_p''` vanishes identically. -/
theorem derivHyp_tamagawaOmegaRealFactor :
    SecondLogDerivProduct.DerivHyp tamagawaOmegaRealFactor 0 where
  diff2 p w _ := by
    rw [deriv_tamagawaOmegaRealFactor]
    exact differentiableAt_const _
  bound_deriv2 p w _ := by
    rw [deriv_tamagawaOmegaRealFactor, deriv_const]
    simp
  B_nonneg p := le_rfl
  summable_B := summable_zero

/-- The second-order corner series vanishes: `∑_p h_p''(1) = 0`. -/
theorem tsum_deriv2_tamagawaOmegaRealFactor :
    (∑' p : ℕ, deriv (deriv (tamagawaOmegaRealFactor p)) 1) = 0 := by
  simp [deriv_tamagawaOmegaRealFactor]

/-- `∑_p h_p'(1)² = ∑_p a_p²` for the affine family. -/
theorem tsum_deriv_tamagawaOmegaRealFactor_sq :
    (∑' p : ℕ, deriv (tamagawaOmegaRealFactor p) 1 ^ 2)
      = ∑' p : ℕ, tamagawaLocalTailMass p ^ 2 :=
  tsum_congr fun p => by rw [(hasDerivAt_tamagawaOmegaRealFactor p 1).deriv]

/-- `∑_p a_p² < ∞`. -/
theorem summable_tamagawaLocalTailMass_sq :
    Summable fun p : ℕ => tamagawaLocalTailMass p ^ 2 := by
  have h := SecondLogDerivProduct.summable_deriv_one_sq prodHyp_tamagawaOmegaRealFactor
  refine h.congr fun p => ?_
  rw [(hasDerivAt_tamagawaOmegaRealFactor p 1).deriv]

/-! ### Transporting the first derivative from `LogDerivProduct.prodG` to `F` -/

/-- On `(1/2, 1]` the first derivative of `PGFMean.pgf π` within `Set.Iic 1` is that of the real
product `LogDerivProduct.prodG` of the affine family. -/
theorem derivWithin_pgf_eq_derivWithin_prodG {w : ℝ} (hw : w ∈ Ioc (1 / 2 : ℝ) 1) :
    derivWithin (PGFMean.pgf tamagawaOmegaDensity) (Iic 1) w
      = derivWithin (LogDerivProduct.prodG tamagawaOmegaRealFactor) (Iic 1) w := by
  refine Filter.EventuallyEq.derivWithin_eq ?_
    (pgf_eq_prodG_tamagawaOmegaRealFactor ⟨hw.1.le, hw.2⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hw.1), self_mem_nhdsWithin]
    with x hx1 hx2
  exact pgf_eq_prodG_tamagawaOmegaRealFactor ⟨hx1.le, hx2⟩

/-! ### The second derivative at `u = 1` -/

/-- The first derivative of the restriction of `F` to the reals — the function
`u ↦ derivWithin (F|_ℝ) (Set.Iic 1) u`, with `F|_ℝ = PGFMean.pgf π` — is itself differentiable at
`u = 1` from the left, with value

  `F''(1) = (∑_p a_p)² - ∑_p a_p²,  a_p = 1 - δ_p(1).` -/
@[bsd_tamagawa "T041o"]
theorem hasDerivWithinAt_derivWithin_pgf_tamagawaOmegaDensity :
    HasDerivWithinAt (derivWithin (PGFMean.pgf tamagawaOmegaDensity) (Iic 1))
      ((∑' p : ℕ, tamagawaLocalTailMass p) ^ 2 - ∑' p : ℕ, tamagawaLocalTailMass p ^ 2)
      (Iio 1) 1 := by
  have h := SecondLogDerivProduct.hasDerivWithinAt_derivWithin_prodG prodHyp_tamagawaOmegaRealFactor
    derivHyp_tamagawaOmegaRealFactor
  rw [tsum_deriv2_tamagawaOmegaRealFactor, tsum_deriv_tamagawaOmegaRealFactor,
    tsum_deriv_tamagawaOmegaRealFactor_sq, zero_add] at h
  refine h.congr_of_eventuallyEq ?_ (derivWithin_pgf_eq_derivWithin_prodG ⟨by norm_num, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
  exact derivWithin_pgf_eq_derivWithin_prodG ⟨hx.1, hx.2.le⟩

/-- `F''(1) = (∑_p a_p)² - ∑_p a_p²`, both derivatives taken within `Set.Iic 1`. -/
@[bsd_tamagawa "T041o"]
theorem derivWithin_derivWithin_pgf_tamagawaOmegaDensity_one :
    derivWithin (derivWithin (PGFMean.pgf tamagawaOmegaDensity) (Iic 1)) (Iic 1) 1
      = (∑' p : ℕ, tamagawaLocalTailMass p) ^ 2 - ∑' p : ℕ, tamagawaLocalTailMass p ^ 2 :=
  hasDerivWithinAt_derivWithin_pgf_tamagawaOmegaDensity.Iic_of_Iio.derivWithin
    (uniqueDiffOn_Iic 1 1 (mem_Iic.mpr le_rfl))

end WeierstrassCurve
