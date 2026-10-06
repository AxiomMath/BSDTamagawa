/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.PrimeCount.LimitingDensityExists

/-!
# The generating-function identity for `π_r` on all of `ℂ`

Let `π_r` be the limiting density of the integral short Weierstrass models with `ω_Tam = r`, and
let `F(u) = ∏'_p (δ_p(1) + (1 - δ_p(1))u)` be the associated Euler product. This file proves that
`F` is entire and that for every `u : ℂ` the series `∑_{r ≥ 0} π_r u^r` converges absolutely, with

`∑_{r ≥ 0} π_r u^r = F(u)`.

## Main results

* `WeierstrassCurve.differentiable_tamagawaOmegaEulerProduct`: `F` is entire.
* `WeierstrassCurve.iteratedDeriv_tamagawaOmegaEulerProduct_eq_tamagawaOmegaDensity`: the Taylor
  coefficients of `F` at the origin are the densities `π_r`.
* `WeierstrassCurve.hasSum_tamagawaOmegaDensity_mul_pow`: the series `∑_r π_r u^r` has sum `F(u)`
  for every `u : ℂ`.
* `WeierstrassCurve.summable_norm_tamagawaOmegaDensity_mul_pow`: the series `∑_r π_r u^r` converges
  absolutely for every `u : ℂ`.
* `WeierstrassCurve.tsum_tamagawaOmegaDensity_mul_pow`: `∑_r π_r u^r = F(u)` for every `u : ℂ`.

## Implementation notes

The partial products of `F` are finite products of affine functions of `u` converging to `F`
locally uniformly on `ℂ`, so `F` is entire and is the sum of its Taylor series at `0` everywhere.
The Taylor coefficients are identified with `π_r` by uniqueness of the coefficients of an expansion
on the open unit disc, the one-variable series being indexed by `Unit →₀ ℕ`. Since `π_r ≥ 0`,
absolute convergence at `u` is convergence of the identity at the real point `‖u‖`.

The Euler product is a `tprod`: its multiplicative support is infinite for generic `u`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex BSDTamagawa.CoeffExtraction BSDTamagawa.FiberCount
open BSDTamagawa.PrimeCountDensity

/-! ### `F` is entire -/

/-- Each local Euler factor `F_p`, equal to `u ↦ δ_p(1) + (1 - δ_p(1))u` at a prime `p` and to `1`
otherwise, is differentiable on all of `ℂ`. -/
theorem differentiable_tamagawaOmegaEulerFactor (p : ℕ) :
    Differentiable ℂ (tamagawaOmegaEulerFactor p) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [show tamagawaOmegaEulerFactor p =
        fun u : ℂ => ((δ p 1).toReal : ℂ) + (1 - ((δ p 1).toReal : ℂ)) * u from
      funext fun u => tamagawaOmegaEulerFactor_of_prime p u]
    exact (differentiable_const _).add ((differentiable_const _).mul differentiable_id)
  · rw [show tamagawaOmegaEulerFactor p = fun _ : ℂ => (1 : ℂ) from
      funext fun u => tamagawaOmegaEulerFactor_of_not_prime hp u]
    exact differentiable_const _

/-- The Euler product `F(u) = ∏'_p (δ_p(1) + (1 - δ_p(1))u)` is differentiable on all of `ℂ`. -/
theorem differentiable_tamagawaOmegaEulerProduct :
    Differentiable ℂ tamagawaOmegaEulerProduct := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn
    (F := fun S : Finset ℕ => fun u : ℂ => ∏ p ∈ S, tamagawaOmegaEulerFactor p u)
    hasProdLocallyUniformly_tamagawaOmegaEulerFactor.hasProdLocallyUniformlyOn
    (Eventually.of_forall fun S => ?_) isOpen_univ
  exact DifferentiableOn.fun_finsetProd fun p _ =>
    (differentiable_tamagawaOmegaEulerFactor p).differentiableOn

/-! ### The Taylor series of `F` at the origin, everywhere on `ℂ` -/

/-- The Euler product `F` is the sum of its Taylor series at `0` at every `u : ℂ`:
`∑_{r ≥ 0} (r!)⁻¹ F^{(r)}(0) u^r = F(u)`. -/
theorem hasSum_taylor_tamagawaOmegaEulerProduct (u : ℂ) :
    HasSum (fun r : ℕ =>
        ((r.factorial : ℂ)⁻¹ * iteratedDeriv r tamagawaOmegaEulerProduct 0) * u ^ r)
      (tamagawaOmegaEulerProduct u) := by
  refine (Complex.hasSum_taylorSeries_of_entire differentiable_tamagawaOmegaEulerProduct 0
    u).congr_fun fun r => ?_
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The Taylor coefficients `j ↦ (j()!)⁻¹ F^{(j())}(0)`, indexed by `Unit →₀ ℕ`, form a polydisc
coefficient family for `z ↦ F(z())` on the open unit disc. -/
theorem hasPolydiscExpansion_taylor_tamagawaOmegaEulerProduct :
    HasPolydiscExpansion
      (fun j : Unit →₀ ℕ =>
        ((j ()).factorial : ℂ)⁻¹ * iteratedDeriv (j ()) tamagawaOmegaEulerProduct 0)
      (fun z : Unit → ℂ => tamagawaOmegaEulerProduct (z ())) := by
  intro z _
  refine (Equiv.hasSum_iff (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm).mp ?_
  refine (hasSum_taylor_tamagawaOmegaEulerProduct (z ())).congr_fun fun r => ?_
  simp [smul_eq_mul]

/-! ### `(π_r)_r` expands `F` on the open unit disc -/

/-- For `j : Unit →₀ ℕ`, the limit as `X → ∞` of the proportion of models of height at most `X` in
the integral short Weierstrass family whose `ω_Tam`, as a `Unit`-multi-index, equals `j` is the
density `π_{j()}`. -/
theorem limUnder_ncard_fiber_tamagawaOmegaIndex (j : Unit →₀ ℕ) :
    (limUnder atTop fun X : ℝ =>
      (({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily} ∧
          Finsupp.equivFunOnFinite.symm (fun _ : Unit => tamagawaOmega q.1 q.2) = j}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ)))
      = tamagawaOmegaDensity (j ()) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, j = Finsupp.equivFunOnFinite.symm (fun _ : Unit => r) := by
    refine ⟨j (), ?_⟩
    rw [show (fun _ : Unit => j ()) = ⇑j from funext fun i => by cases i; rfl]
    exact (Finsupp.equivFunOnFinite_symm_coe j).symm
  change _ = tamagawaOmegaDensity r
  rw [tamagawaOmegaDensity]
  refine congrArg (limUnder atTop) (funext fun X => ?_)
  rw [setOf_mem_and_tamagawaOmegaIndex_eq r X, ncard_setOf_height_le_and_mem_family,
    tamagawaOmegaProportion]

/-- The densities `(π_r)_r`, indexed by `Unit →₀ ℕ`, take values in `[0, 1]`, are summable with
total mass at most `1`, and form a polydisc coefficient family for `z ↦ F(z())` on the open unit
disc. -/
theorem hasPolydiscExpansion_tamagawaOmegaDensity :
    (∀ j : Unit →₀ ℕ, tamagawaOmegaDensity (j ()) ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun j : Unit →₀ ℕ => tamagawaOmegaDensity (j ())) ∧
      (∑' j : Unit →₀ ℕ, tamagawaOmegaDensity (j ())) ≤ 1 ∧
      HasPolydiscExpansion (fun j : Unit →₀ ℕ => ((tamagawaOmegaDensity (j ()) : ℝ) : ℂ))
        (fun z : Unit → ℂ => tamagawaOmegaEulerProduct (z ())) := by
  have h := hasPolydiscExpansion_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (fun q : ℤ × ℤ => Finsupp.equivFunOnFinite.symm (fun _ : Unit => tamagawaOmega q.1 q.2))
    (fun z : Unit → ℂ => tamagawaOmegaEulerProduct (z ())) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_tamagawaOmegaMonomial_div z hz)
  simpa only [limUnder_ncard_fiber_tamagawaOmegaIndex] using h

/-- The density `π_r` lies in `[0, 1]`. -/
theorem tamagawaOmegaDensity_mem_Icc (r : ℕ) : tamagawaOmegaDensity r ∈ Set.Icc (0 : ℝ) 1 :=
  hasPolydiscExpansion_tamagawaOmegaDensity.1 (Finsupp.equivFunOnFinite.symm fun _ : Unit => r)

/-! ### `[u^r]F = π_r` -/

/-- The Taylor coefficients of `F` at the origin are the densities: `(r!)⁻¹ F^{(r)}(0) = π_r`. -/
theorem iteratedDeriv_tamagawaOmegaEulerProduct_eq_tamagawaOmegaDensity (r : ℕ) :
    (r.factorial : ℂ)⁻¹ * iteratedDeriv r tamagawaOmegaEulerProduct 0
      = ((tamagawaOmegaDensity r : ℝ) : ℂ) :=
  congrFun (coeff_eq_of_hasPolydiscExpansion hasPolydiscExpansion_taylor_tamagawaOmegaEulerProduct
    hasPolydiscExpansion_tamagawaOmegaDensity.2.2.2)
    (Finsupp.equivFunOnFinite.symm fun _ : Unit => r)

/-! ### The generating-function identity on all of `ℂ` -/

/-- For every `u : ℂ`, the series `∑_{r ≥ 0} π_r u^r` has sum `F(u)`. -/
theorem hasSum_tamagawaOmegaDensity_mul_pow (u : ℂ) :
    HasSum (fun r : ℕ => ((tamagawaOmegaDensity r : ℝ) : ℂ) * u ^ r)
      (tamagawaOmegaEulerProduct u) := by
  refine (hasSum_taylor_tamagawaOmegaEulerProduct u).congr_fun fun r => ?_
  rw [iteratedDeriv_tamagawaOmegaEulerProduct_eq_tamagawaOmegaDensity r]

/-- For every `u : ℂ` the series `∑_{r ≥ 0} π_r u^r` converges absolutely. -/
@[bsd_tamagawa "T041l"]
theorem summable_norm_tamagawaOmegaDensity_mul_pow (u : ℂ) :
    Summable fun r : ℕ => ‖((tamagawaOmegaDensity r : ℝ) : ℂ) * u ^ r‖ := by
  have h := (hasSum_tamagawaOmegaDensity_mul_pow ((‖u‖ : ℝ) : ℂ)).summable
  rw [show (fun r : ℕ => ((tamagawaOmegaDensity r : ℝ) : ℂ) * ((‖u‖ : ℝ) : ℂ) ^ r)
      = fun r : ℕ => ((tamagawaOmegaDensity r * ‖u‖ ^ r : ℝ) : ℂ) from
    funext fun r => by push_cast; ring] at h
  rw [Complex.summable_ofReal] at h
  refine h.congr fun r => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tamagawaOmegaDensity_mem_Icc r).1]

/-- For every `u : ℂ`, the limiting densities `π_r` and the Euler product `F` satisfy
`∑_{r ≥ 0} π_r u^r = F(u)`. -/
@[bsd_tamagawa "T041l"]
theorem tsum_tamagawaOmegaDensity_mul_pow (u : ℂ) :
    (∑' r : ℕ, ((tamagawaOmegaDensity r : ℝ) : ℂ) * u ^ r) = tamagawaOmegaEulerProduct u :=
  (hasSum_tamagawaOmegaDensity_mul_pow u).tsum_eq

end WeierstrassCurve
