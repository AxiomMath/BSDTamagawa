/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.PGFSecondDeriv
public import BSDTamagawa.ReductionCount.JointLawProbability
public import BSDTamagawa.Analysis.SecondLogDerivProduct

/-!
# Marginal mean and variance of `ω_K(E)`

Let `K ∈ 𝒦 ∖ 𝒦₀` and let `P` be the probability measure on `ℤ_{≥0}` with `P({r}) = π_{{K}}(r)`,
the marginal of the limiting joint law at `Λ = {K}`. Then

  `𝔼_P[ω_K(E)] = ∑_p δ_p(K)`,  `Var_P(ω_K(E)) = ∑_p δ_p(K)(1 - δ_p(K))`,

and both sums converge absolutely. With `a_p := δ_p(K)` and `h_p(w) := 1 + a_p (w - 1)`, the
probability generating function of `P` agrees with `∏_p h_p` on `[1/2, 1]`, so its one-sided
derivatives at `1` are `F'(1) = ∑_p a_p` and `F''(1) = (∑_p a_p)² - ∑_p a_p²`; the mean and
variance follow from Abel-type theorems for probability generating functions.

## Main definitions

* `WeierstrassCurve.singletonIndexEquiv`: the reindexing `ℤ_{≥0}^{{K}} ≃ ℕ`.
* `WeierstrassCurve.marginalReductionOmegaPMF`: the marginal law `P` as a `PMF ℕ`.
* `WeierstrassCurve.stratumRealFactor`: the real local factor `h_p(w) = 1 + δ_p(K)(w - 1)`.

## Main results

* `WeierstrassCurve.integral_marginalReductionOmega`: `(δ_p(K))_p` is summable and
  `𝔼_P[ω_K] = ∑_p δ_p(K)`.
* `WeierstrassCurve.variance_marginalReductionOmega`: `(δ_p(K)(1 - δ_p(K)))_p` is summable and
  `Var_P(ω_K) = ∑_p δ_p(K)(1 - δ_p(K))`.

## Implementation notes

All terms of both series are nonnegative, so `Summable` is absolute convergence. Every
`1 - δ_p(K)` is a subtraction in `ℝ` on `stratumLocalMass K p = (δ_p(K)).toReal`; in `ℝ≥0∞` it
would truncate. The marginal density `marginalReductionOmegaDensity` is defined in
`BSDTamagawa.Defs`.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology
open BSDTamagawa BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

variable {K : ReductionData}

/-! ### The singleton index set `Λ = {K}` -/

/-- If `K ∉ 𝒦₀`, then `Λ = {K}` is an admissible index set. -/
theorem admissible_singleton (hK : K ∉ (K0 : Set ReductionData)) :
    Admissible ({K} : Finset ReductionData) := fun _ hK' =>
  Finset.mem_singleton.mp hK' ▸ hK

/-- The unique element of `↥{K}` is `K`. -/
theorem coe_default_singleton (K : ReductionData) :
    ((default : ({K} : Finset ReductionData)) : ReductionData) = K :=
  Finset.mem_singleton.mp (default : ({K} : Finset ReductionData)).property

/-- A multi-index on `↥{K}` is the constant function at its unique value. -/
theorem eq_const_of_singleton (K : ReductionData) (r : ({K} : Finset ReductionData) → ℕ) :
    r = fun _ => r default :=
  funext fun x => congrArg r (Subsingleton.elim x default)

/-- The multi-monomial on `↥{K}` at a constant vector is an ordinary power. -/
theorem multiMonomial_singleton (K : ReductionData) (r : ({K} : Finset ReductionData) → ℕ)
    (z : ℂ) : multiMonomial r (fun _ => z) = z ^ r default := by
  rw [multiMonomial]
  exact Fintype.prod_unique _

/-- The equivalence `ℤ_{≥0}^{{K}} ≃ ℕ` sending a multi-index to its unique value. -/
noncomputable def singletonIndexEquiv (K : ReductionData) :
    (({K} : Finset ReductionData) → ℕ) ≃ ℕ :=
  Equiv.funUnique (({K} : Finset ReductionData)) ℕ

/-! ### The marginal density `π_{{K}}(r)` -/

/-- The joint density at `Λ = {K}` is the marginal density at the multi-index's unique value. -/
theorem jointReductionOmegaDensity_singleton (K : ReductionData)
    (r : ({K} : Finset ReductionData) → ℕ) :
    jointReductionOmegaDensity {K} r = marginalReductionOmegaDensity K (r default) := by
  rw [marginalReductionOmegaDensity, eq_const_of_singleton K r]

/-- The marginal densities are nonnegative. -/
theorem marginalReductionOmegaDensity_nonneg (hK : K ∉ (K0 : Set ReductionData)) (r : ℕ) :
    0 ≤ marginalReductionOmegaDensity K r :=
  jointReductionOmegaDensity_nonneg (admissible_singleton hK) _

/-- For `K ∉ 𝒦₀`, the marginal densities `π_{{K}}(r)` have total mass `1`. -/
theorem hasSum_marginalReductionOmegaDensity_one (hK : K ∉ (K0 : Set ReductionData)) :
    HasSum (marginalReductionOmegaDensity K) 1 := by
  refine (singletonIndexEquiv K).hasSum_iff.mp ?_
  refine (hasSum_jointReductionOmegaDensity_one (admissible_singleton hK)).congr_fun fun r => ?_
  exact (jointReductionOmegaDensity_singleton K r).symm

/-! ### The marginal law `P`, as a `PMF ℕ` -/

/-- The marginal law `P` of `ω_K(E)` as a `PMF ℕ`: the mass at `r` is
`ENNReal.ofReal π_{{K}}(r)`. -/
noncomputable def marginalReductionOmegaPMF (hK : K ∉ (K0 : Set ReductionData)) : PMF ℕ :=
  ⟨fun r => ENNReal.ofReal (marginalReductionOmegaDensity K r),
    ENNReal.summable.hasSum_iff.mpr <| by
      rw [← ENNReal.ofReal_tsum_of_nonneg (marginalReductionOmegaDensity_nonneg hK)
          (hasSum_marginalReductionOmegaDensity_one hK).summable,
        (hasSum_marginalReductionOmegaDensity_one hK).tsum_eq, ENNReal.ofReal_one]⟩

/-- The masses of `P`, read back in `ℝ`, are the marginal densities. -/
theorem marginalReductionOmegaPMF_apply_toReal (hK : K ∉ (K0 : Set ReductionData)) (r : ℕ) :
    ((marginalReductionOmegaPMF hK) r).toReal = marginalReductionOmegaDensity K r :=
  ENNReal.toReal_ofReal (marginalReductionOmegaDensity_nonneg hK r)

/-- The `ℝ`-valued mass family of `P` is the marginal density family. -/
theorem marginalReductionOmegaPMF_toReal (hK : K ∉ (K0 : Set ReductionData)) :
    (fun r : ℕ => ((marginalReductionOmegaPMF hK) r).toReal)
      = marginalReductionOmegaDensity K :=
  funext (marginalReductionOmegaPMF_apply_toReal hK)

/-! ### The local factor `h_p(u) = 1 + δ_p(K)(u - 1)` as a real function -/

/-- The real local factor `h_p(w) = 1 + a_p (w - 1)`, with `a_p = δ_p(K)`. -/
noncomputable def stratumRealFactor (K : ReductionData) (p : ℕ) (w : ℝ) : ℝ :=
  1 + stratumLocalMass K p * (w - 1)

/-- Every local mass `δ_p(K)` is at most `1`. -/
theorem stratumLocalMass_le_one (K : ReductionData) (p : ℕ) : stratumLocalMass K p ≤ 1 := by
  have h := sum_stratumLocalMass_le_one {K} p
  rwa [Fintype.sum_unique, coe_default_singleton] at h

/-- `h_p` is affine, hence differentiable at every real point, with derivative `a_p`. -/
theorem hasDerivAt_stratumRealFactor (K : ReductionData) (p : ℕ) (w : ℝ) :
    HasDerivAt (stratumRealFactor K p) (stratumLocalMass K p) w := by
  have h1 : HasDerivAt (fun w : ℝ => w - 1) 1 w := (hasDerivAt_id w).sub_const 1
  have h2 : HasDerivAt (fun w : ℝ => 1 + stratumLocalMass K p * (w - 1))
      (stratumLocalMass K p * 1) w := (h1.const_mul _).const_add 1
  rwa [mul_one] at h2

/-- The derivative of `h_p` is the constant function `a_p`. -/
theorem deriv_stratumRealFactor (K : ReductionData) (p : ℕ) :
    deriv (stratumRealFactor K p) = fun _ : ℝ => stratumLocalMass K p :=
  funext fun w => (hasDerivAt_stratumRealFactor K p w).deriv

/-- The family `h_p` satisfies `LogDerivProduct.ProdHyp` with bound family `a_p`, `A_sup = 1` and
window radius `η = 1/2`. -/
theorem prodHyp_stratumRealFactor (hK : K ∉ (K0 : Set ReductionData)) :
    LogDerivProduct.ProdHyp (stratumRealFactor K) (stratumLocalMass K) 1 (1 / 2) where
  normalisation p := by simp [stratumRealFactor]
  diff p w _ := (hasDerivAt_stratumRealFactor K p w).differentiableAt
  bound_deriv p w _ := by
    rw [(hasDerivAt_stratumRealFactor K p w).deriv]
    exact (abs_of_nonneg (stratumLocalMass_nonneg K p)).le
  A_nonneg := stratumLocalMass_nonneg K
  summable_A := summable_stratumLocalMass hK
  A_sup_nonneg := zero_le_one
  A_sup_bound := stratumLocalMass_le_one K
  eta_pos := by norm_num
  eta_le_one := by norm_num
  domain_const := by norm_num

/-- The family `h_p` satisfies `SecondLogDerivProduct.DerivHyp` with bound family `0`. -/
theorem derivHyp_stratumRealFactor (K : ReductionData) :
    SecondLogDerivProduct.DerivHyp (stratumRealFactor K) 0 where
  diff2 p w _ := by
    rw [deriv_stratumRealFactor]
    exact differentiableAt_const _
  bound_deriv2 p w _ := by
    rw [deriv_stratumRealFactor, deriv_const]
    simp
  B_nonneg p := le_rfl
  summable_B := summable_zero

/-- A point of `[1/2, 1]` lies in `Icc (1 - 1/2) 1`. -/
private theorem mem_window_of_mem_Icc {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    w ∈ Icc (1 - 1 / 2 : ℝ) 1 :=
  ⟨by linarith [hw.left], hw.right⟩

/-! ### The real product and the complex Euler product -/

/-- The coerced real factor is the complex joint local factor at `Λ = {K}` and the real
diagonal point: `↑(h_p w) = F_{{K},p}(↑w)`. -/
theorem ofReal_stratumRealFactor (K : ReductionData) (p : ℕ) (w : ℝ) :
    ((stratumRealFactor K p w : ℝ) : ℂ)
      = jointReductionOmegaEulerFactor {K} p (fun _ => (w : ℂ)) := by
  rw [jointReductionOmegaEulerFactor_eq_one_add, Fintype.sum_unique, coe_default_singleton,
    stratumRealFactor]
  push_cast
  ring

/-- On `[1/2, 1]` the real infinite product `LogDerivProduct.prodG` of the family `h_p` coerces
to the joint Euler product `F_{{K}}` at the real diagonal point: `↑(∏' p, h_p w) = F_{{K}}(↑w)`. -/
theorem ofReal_prodG_stratumRealFactor (hK : K ∉ (K0 : Set ReductionData)) {w : ℝ}
    (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    ((LogDerivProduct.prodG (stratumRealFactor K) w : ℝ) : ℂ)
      = jointReductionOmegaEulerProduct {K} (fun _ => (w : ℂ)) := by
  have hmap := (LogDerivProduct.hasProd_prodG (prodHyp_stratumRealFactor hK)
    (mem_window_of_mem_Icc hw)).map Complex.ofRealHom Complex.continuous_ofReal
  rw [jointReductionOmegaEulerProduct]
  refine ((hmap.congr_fun fun p => ?_).tprod_eq).symm
  simpa using (ofReal_stratumRealFactor K p w).symm

/-! ### The marginal generating identity `∑_r π_{{K}}(r) u^r = F_{{K}}(u)` -/

/-- For `K ∉ 𝒦₀` and every `z ∈ ℂ`, the marginal power series `∑_r π_{{K}}(r) z^r` converges
absolutely. -/
theorem summable_norm_marginalReductionOmegaDensity_mul_pow
    (hK : K ∉ (K0 : Set ReductionData)) (z : ℂ) :
    Summable fun r : ℕ => ‖((marginalReductionOmegaDensity K r : ℝ) : ℂ) * z ^ r‖ := by
  refine (singletonIndexEquiv K).summable_iff.mp ?_
  refine (summable_norm_jointReductionOmegaDensity_multiMonomial (admissible_singleton hK)
    fun _ => z).congr fun r => ?_
  rw [jointReductionOmegaDensity_singleton, multiMonomial_singleton]
  rfl

/-- For `K ∉ 𝒦₀` and every `z ∈ ℂ`, `∑_r π_{{K}}(r) z^r = F_{{K}}(z · 𝟏)`. -/
theorem hasSum_marginalReductionOmegaDensity_mul_pow (hK : K ∉ (K0 : Set ReductionData))
    (z : ℂ) :
    HasSum (fun r : ℕ => ((marginalReductionOmegaDensity K r : ℝ) : ℂ) * z ^ r)
      (jointReductionOmegaEulerProduct {K} (fun _ => z)) := by
  refine (singletonIndexEquiv K).hasSum_iff.mp ?_
  refine (hasSum_jointReductionOmegaDensity_multiMonomial (admissible_singleton hK)
    fun _ => z).congr_fun fun r => ?_
  rw [jointReductionOmegaDensity_singleton, multiMonomial_singleton]
  rfl

/-- For every real `u`, `↑(∑_r π_{{K}}(r) u^r) = F_{{K}}(↑u · 𝟏)`. -/
theorem ofReal_pgf_marginalReductionOmegaDensity (hK : K ∉ (K0 : Set ReductionData)) (u : ℝ) :
    ((PGFMean.pgf (marginalReductionOmegaDensity K) u : ℝ) : ℂ)
      = jointReductionOmegaEulerProduct {K} (fun _ => (u : ℂ)) := by
  have habs : Summable fun r : ℕ => |marginalReductionOmegaDensity K r * u ^ r| := by
    refine (summable_norm_marginalReductionOmegaDensity_mul_pow hK (u : ℂ)).congr fun r => ?_
    rw [show ((marginalReductionOmegaDensity K r : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ r
        = ((marginalReductionOmegaDensity K r * u ^ r : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hreal : HasSum (fun r : ℕ => marginalReductionOmegaDensity K r * u ^ r)
      (PGFMean.pgf (marginalReductionOmegaDensity K) u) := by
    rw [PGFMean.pgf]
    exact (Summable.of_abs habs).hasSum
  refine (Complex.hasSum_ofReal.mpr hreal).unique ?_
  refine (hasSum_marginalReductionOmegaDensity_mul_pow hK (u : ℂ)).congr_fun fun r => ?_
  push_cast
  ring

/-- On `[1/2, 1]` the generating function `PGFMean.pgf π_{{K}}` equals the real product
`LogDerivProduct.prodG` of the family `h_p`. -/
theorem pgf_eq_prodG_stratumRealFactor (hK : K ∉ (K0 : Set ReductionData)) {w : ℝ}
    (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    PGFMean.pgf (marginalReductionOmegaDensity K) w =
      LogDerivProduct.prodG (stratumRealFactor K) w :=
  Complex.ofReal_inj.mp ((ofReal_pgf_marginalReductionOmegaDensity hK w).trans
    (ofReal_prodG_stratumRealFactor hK hw).symm)

/-! ### The two one-sided derivatives of the marginal pgf at `u = 1` -/

/-- `∑_p h_p'(1) = ∑_p a_p`. -/
theorem tsum_deriv_stratumRealFactor (K : ReductionData) :
    (∑' p : ℕ, deriv (stratumRealFactor K p) 1) = ∑' p : ℕ, stratumLocalMass K p :=
  tsum_congr fun p => (hasDerivAt_stratumRealFactor K p 1).deriv

/-- `∑_p h_p''(1) = 0`, the factors `h_p` being affine. -/
theorem tsum_deriv2_stratumRealFactor (K : ReductionData) :
    (∑' p : ℕ, deriv (deriv (stratumRealFactor K p)) 1) = 0 := by
  simp [deriv_stratumRealFactor]

/-- `∑_p h_p'(1)² = ∑_p a_p²`. -/
theorem tsum_deriv_stratumRealFactor_sq (K : ReductionData) :
    (∑' p : ℕ, deriv (stratumRealFactor K p) 1 ^ 2) = ∑' p : ℕ, stratumLocalMass K p ^ 2 :=
  tsum_congr fun p => by rw [(hasDerivAt_stratumRealFactor K p 1).deriv]

/-- For `K ∉ 𝒦₀`, `∑_p a_p²` converges. -/
theorem summable_stratumLocalMass_sq (hK : K ∉ (K0 : Set ReductionData)) :
    Summable fun p : ℕ => stratumLocalMass K p ^ 2 := by
  refine (SecondLogDerivProduct.summable_deriv_one_sq (prodHyp_stratumRealFactor hK)).congr
    fun p => ?_
  rw [(hasDerivAt_stratumRealFactor K p 1).deriv]

/-- `F'(1) = ∑_p δ_p(K)`: the marginal generating function `∑_r π_{{K}}(r) u^r` has left
derivative `∑_p a_p` at `u = 1`. -/
theorem hasDerivWithinAt_pgf_marginalReductionOmegaDensity
    (hK : K ∉ (K0 : Set ReductionData)) :
    HasDerivWithinAt (PGFMean.pgf (marginalReductionOmegaDensity K))
      (∑' p : ℕ, stratumLocalMass K p) (Iio 1) 1 := by
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG (prodHyp_stratumRealFactor hK)
  rw [tsum_deriv_stratumRealFactor] at hprod
  refine hprod.congr_of_eventuallyEq ?_
    (pgf_eq_prodG_stratumRealFactor hK ⟨by norm_num, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
  exact pgf_eq_prodG_stratumRealFactor hK ⟨hx.left.le, hx.right.le⟩

/-- On `(1/2, 1]` the derivative within `Set.Iic 1` of the marginal pgf equals that of
`LogDerivProduct.prodG` of the family `h_p`. -/
theorem derivWithin_pgf_marginal_eq_derivWithin_prodG (hK : K ∉ (K0 : Set ReductionData)) {w : ℝ}
    (hw : w ∈ Ioc (1 / 2 : ℝ) 1) :
    derivWithin (PGFMean.pgf (marginalReductionOmegaDensity K)) (Iic 1) w
      = derivWithin (LogDerivProduct.prodG (stratumRealFactor K)) (Iic 1) w := by
  refine Filter.EventuallyEq.derivWithin_eq ?_
    (pgf_eq_prodG_stratumRealFactor hK ⟨hw.left.le, hw.right⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hw.left), self_mem_nhdsWithin]
    with x hx1 hx2
  exact pgf_eq_prodG_stratumRealFactor hK ⟨hx1.le, hx2⟩

/-- `F''(1) = (∑_p δ_p(K))² - ∑_p δ_p(K)²`: the function `u ↦ derivWithin F (Set.Iic 1) u`, with
`F` the marginal pgf, has left derivative `(∑_p a_p)² - ∑_p a_p²` at `u = 1`. -/
theorem hasDerivWithinAt_derivWithin_pgf_marginalReductionOmegaDensity
    (hK : K ∉ (K0 : Set ReductionData)) :
    HasDerivWithinAt (derivWithin (PGFMean.pgf (marginalReductionOmegaDensity K)) (Iic 1))
      ((∑' p : ℕ, stratumLocalMass K p) ^ 2 - ∑' p : ℕ, stratumLocalMass K p ^ 2) (Iio 1) 1 := by
  have h := SecondLogDerivProduct.hasDerivWithinAt_derivWithin_prodG (prodHyp_stratumRealFactor hK)
    (derivHyp_stratumRealFactor K)
  rw [tsum_deriv2_stratumRealFactor, tsum_deriv_stratumRealFactor,
    tsum_deriv_stratumRealFactor_sq, zero_add] at h
  refine h.congr_of_eventuallyEq ?_
    (derivWithin_pgf_marginal_eq_derivWithin_prodG hK ⟨by norm_num, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
  exact derivWithin_pgf_marginal_eq_derivWithin_prodG hK ⟨hx.left, hx.right.le⟩

/-! ### The two derivatives for the mass family of `P` -/

/-- The pgf of the `ℝ`-valued mass family of `P` has left derivative `∑_p δ_p(K)` at `1`. -/
theorem hasDerivWithinAt_pgf_marginalReductionOmegaPMF (hK : K ∉ (K0 : Set ReductionData)) :
    HasDerivWithinAt (PGFMean.pgf fun r : ℕ => ((marginalReductionOmegaPMF hK) r).toReal)
      (∑' p : ℕ, stratumLocalMass K p) (Iio 1) 1 := by
  rw [marginalReductionOmegaPMF_toReal]
  exact hasDerivWithinAt_pgf_marginalReductionOmegaDensity hK

/-- The derivative within `Set.Iic 1` of the pgf of the `ℝ`-valued mass family of `P` has left
derivative `(∑_p δ_p(K))² - ∑_p δ_p(K)²` at `1`. -/
theorem hasDerivWithinAt_derivWithin_pgf_marginalReductionOmegaPMF
    (hK : K ∉ (K0 : Set ReductionData)) :
    HasDerivWithinAt
      (derivWithin (PGFMean.pgf fun r : ℕ => ((marginalReductionOmegaPMF hK) r).toReal) (Iic 1))
      ((∑' p : ℕ, stratumLocalMass K p) ^ 2 - ∑' p : ℕ, stratumLocalMass K p ^ 2) (Iio 1) 1 := by
  rw [marginalReductionOmegaPMF_toReal]
  exact hasDerivWithinAt_derivWithin_pgf_marginalReductionOmegaDensity hK

/-! ### The variance series `∑_p δ_p(K)(1 - δ_p(K))` -/

/-- For `K ∉ 𝒦₀`, the variance series `∑_p a_p(1 - a_p)` converges. -/
theorem summable_stratumLocalMass_mul_one_sub (hK : K ∉ (K0 : Set ReductionData)) :
    Summable fun p : ℕ => stratumLocalMass K p * (1 - stratumLocalMass K p) := by
  refine ((summable_stratumLocalMass hK).sub (summable_stratumLocalMass_sq hK)).congr fun p => ?_
  ring

/-- For `K ∉ 𝒦₀`, `∑_p a_p(1 - a_p) = ∑_p a_p - ∑_p a_p²`. -/
theorem tsum_stratumLocalMass_mul_one_sub (hK : K ∉ (K0 : Set ReductionData)) :
    (∑' p : ℕ, stratumLocalMass K p * (1 - stratumLocalMass K p))
      = (∑' p : ℕ, stratumLocalMass K p) - ∑' p : ℕ, stratumLocalMass K p ^ 2 := by
  rw [← (summable_stratumLocalMass hK).tsum_sub (summable_stratumLocalMass_sq hK)]
  exact tsum_congr fun p => by ring

/-! ### The marginal mean and variance -/

/-- Let `K ∈ 𝒦 ∖ 𝒦₀` and let `P` be the probability measure on `ℤ_{≥0}` with `P({r}) = π_{{K}}(r)`.
Then the series `∑_p δ_p(K)` converges absolutely and `𝔼_P[ω_K(E)] = ∑_{p ∈ 𝒫} δ_p(K)`. -/
@[bsd_tamagawa "T040b"]
theorem integral_marginalReductionOmega (hK : K ∉ (K0 : Set ReductionData)) :
    Summable (stratumLocalMass K) ∧
      ∫ n, (n : ℝ) ∂ (marginalReductionOmegaPMF hK).toMeasure
        = ∑' p : ℕ, stratumLocalMass K p := by
  refine ⟨summable_stratumLocalMass hK, ?_⟩
  have hderiv := hasDerivWithinAt_pgf_marginalReductionOmegaPMF hK
  have hint := BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt
    (marginalReductionOmegaPMF hK) hderiv
  obtain ⟨-, hmean⟩ := PGFMean.main_theorem _ (fun _ => ENNReal.toReal_nonneg)
    (BSDTamagawa.PGFSecondDeriv.hasSum_toReal_pmf (marginalReductionOmegaPMF hK)) _ hderiv
  rw [← PGFVariance.pgfDeriv_eq_mean _ hint, PGFVariance.pgfDeriv, hmean]

/-- With `K` and `P` as in `integral_marginalReductionOmega`, the series `∑_p δ_p(K)(1 - δ_p(K))`
converges absolutely and `Var_P(ω_K(E)) = ∑_{p ∈ 𝒫} δ_p(K)(1 - δ_p(K))`. -/
@[bsd_tamagawa "T040b"]
theorem variance_marginalReductionOmega (hK : K ∉ (K0 : Set ReductionData)) :
    Summable (fun p : ℕ => stratumLocalMass K p * (1 - stratumLocalMass K p)) ∧
      variance (fun n : ℕ => (n : ℝ)) (marginalReductionOmegaPMF hK).toMeasure
        = ∑' p : ℕ, stratumLocalMass K p * (1 - stratumLocalMass K p) := by
  refine ⟨summable_stratumLocalMass_mul_one_sub hK, ?_⟩
  rw [BSDTamagawa.PGFSecondDeriv.variance_eq_of_hasDerivWithinAt_derivWithin'
      (marginalReductionOmegaPMF hK) (hasDerivWithinAt_pgf_marginalReductionOmegaPMF hK)
      (hasDerivWithinAt_derivWithin_pgf_marginalReductionOmegaPMF hK),
    tsum_stratumLocalMass_mul_one_sub hK]
  ring

end WeierstrassCurve
