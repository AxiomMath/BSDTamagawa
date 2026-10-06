/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.ReductionCount.MarginalMoments

/-!
# Pairwise covariance of `ω_K(E)` and `ω_{K'}(E)`

Let `K, K' ∈ 𝒦 ∖ 𝒦₀` be distinct and let `P` be the joint probability measure on `ℤ_{≥0}²` with
`P({(r, r')}) = π_{{K, K'}}(r, r')`, the limiting joint law at `Λ = {K, K'}`. Then

  `Cov_P(ω_K(E), ω_{K'}(E)) = -∑_{p ∈ 𝒫} δ_p(K) δ_p(K')`,

the sum converging absolutely. The proof is by polarisation. For a `0/1`-weight vector `t` on
`Λ`, the probability generating function of `weightSum t 𝐫 = ∑_j t_j 𝐫_j` is the Euler product
`∏_p (1 + m_p(w - 1))` with `m_p = ∑_j t_j δ_p(j)`, whence `Var(weightSum t) = ∑_p m_p(1 - m_p)`.
Taking `t = e_K`, `e_{K'}` and `1` and using
`(a + a')(1 - a - a') - a(1 - a) - a'(1 - a') = -2 a a'` gives the covariance.

## Main definitions

* `WeierstrassCurve.affineFactor`: the affine local factor `1 + m_p(w - 1)`.
* `WeierstrassCurve.jointReductionOmegaPMF`: the joint law `π_Λ` as a `PMF (↥Λ → ℕ)`.
* `WeierstrassCurve.weightSum`, `WeierstrassCurve.weightMass`: the weighted coordinate sum and the
  weighted local mass.
* `WeierstrassCurve.weightReductionOmegaPMF`: the law of `weightSum t`.
* `WeierstrassCurve.fstWeight`, `WeierstrassCurve.sndWeight`, `WeierstrassCurve.totalWeight`: the
  weight vectors `e_K`, `e_{K'}` and `1` on `Λ = {K, K'}`.

## Main results

* `WeierstrassCurve.jointReductionOmegaPMF_toMeasure`: the measure of the joint pmf is the joint
  law `jointReductionOmegaMeasure Λ`.
* `WeierstrassCurve.variance_weightSum`: `Var(weightSum t) = ∑_p m_p(1 - m_p)`.
* `WeierstrassCurve.covariance_pairReductionOmega`: the covariance identity against the joint law
  on `↥{K, K'} → ℕ`, with absolute convergence of `∑_p δ_p(K) δ_p(K')`.
* `WeierstrassCurve.covariance_pairReductionOmega_prod`: the same on `ℤ_{≥0}²`, with the two
  coordinate projections of `ℕ × ℕ` as the random variables.

## Implementation notes

`ReductionData = KodairaSymbol × ℕ` has no `DecidableEq` instance, so `{K, K'}` is
`pairFinset K K' hne`, built with `Finset.cons`; its two elements `pairIndexFst K K' hne` and
`pairIndexSnd K K' hne` coerce to `K` and `K'` by `rfl`. These, `pairIndexEquiv` and
`pairReductionOmegaMeasure` are defined in `BSDTamagawa.Defs`. All masses are real
(`stratumLocalMass K p = (δ_p(K)).toReal`), so no `ℝ≥0∞` subtraction occurs.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology
open BSDTamagawa BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

/-! ### The affine local factor `1 + m_p(w - 1)` at an arbitrary mass family -/

variable {m : ℕ → ℝ}

/-- The affine local factor `h_p(w) = 1 + m_p(w - 1)` of a real mass family `m`. -/
noncomputable def affineFactor (m : ℕ → ℝ) (p : ℕ) (w : ℝ) : ℝ := 1 + m p * (w - 1)

/-- `h_p` is affine, hence differentiable at every real point, with derivative `m_p`. -/
theorem hasDerivAt_affineFactor (m : ℕ → ℝ) (p : ℕ) (w : ℝ) :
    HasDerivAt (affineFactor m p) (m p) w := by
  have h1 : HasDerivAt (fun w : ℝ => w - 1) 1 w := (hasDerivAt_id w).sub_const 1
  have h2 : HasDerivAt (fun w : ℝ => 1 + m p * (w - 1)) (m p * 1) w :=
    (h1.const_mul _).const_add 1
  rwa [mul_one] at h2

/-- The derivative of `h_p` is the constant function `m_p`. -/
theorem deriv_affineFactor (m : ℕ → ℝ) (p : ℕ) :
    deriv (affineFactor m p) = fun _ : ℝ => m p :=
  funext fun w => (hasDerivAt_affineFactor m p w).deriv

/-- For a nonnegative summable family `m` bounded by `1`, the family `h_p` satisfies
`LogDerivProduct.ProdHyp` with bound family `m`, `A_sup = 1` and window radius `η = 1/2`. -/
theorem prodHyp_affineFactor (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1) (hms : Summable m) :
    LogDerivProduct.ProdHyp (affineFactor m) m 1 (1 / 2) where
  normalisation p := by simp [affineFactor]
  diff p w _ := (hasDerivAt_affineFactor m p w).differentiableAt
  bound_deriv p w _ := by
    rw [(hasDerivAt_affineFactor m p w).deriv]
    exact (abs_of_nonneg (hm0 p)).le
  A_nonneg := hm0
  summable_A := hms
  A_sup_nonneg := zero_le_one
  A_sup_bound := hm1
  eta_pos := by norm_num
  eta_le_one := by norm_num
  domain_const := by norm_num

/-- The family `h_p` satisfies `SecondLogDerivProduct.DerivHyp` with bound family `0`. -/
theorem derivHyp_affineFactor (m : ℕ → ℝ) : SecondLogDerivProduct.DerivHyp (affineFactor m) 0 where
  diff2 p w _ := by
    rw [deriv_affineFactor]
    exact differentiableAt_const _
  bound_deriv2 p w _ := by
    rw [deriv_affineFactor, deriv_const]
    simp
  B_nonneg p := le_rfl
  summable_B := summable_zero

/-- A point of `[1/2, 1]` lies in `Icc (1 - 1/2) 1`. -/
private theorem mem_window_of_mem_Icc_half {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    w ∈ Icc (1 - 1 / 2 : ℝ) 1 :=
  ⟨by linarith [hw.left], hw.right⟩

/-- `∑_p h_p'(1) = ∑_p m_p`. -/
theorem tsum_deriv_affineFactor (m : ℕ → ℝ) :
    (∑' p : ℕ, deriv (affineFactor m p) 1) = ∑' p : ℕ, m p :=
  tsum_congr fun p => (hasDerivAt_affineFactor m p 1).deriv

/-- `∑_p h_p''(1) = 0`, the factors `h_p` being affine. -/
theorem tsum_deriv2_affineFactor (m : ℕ → ℝ) :
    (∑' p : ℕ, deriv (deriv (affineFactor m p)) 1) = 0 := by
  simp [deriv_affineFactor]

/-- `∑_p h_p'(1)² = ∑_p m_p²`. -/
theorem tsum_deriv_affineFactor_sq (m : ℕ → ℝ) :
    (∑' p : ℕ, deriv (affineFactor m p) 1 ^ 2) = ∑' p : ℕ, m p ^ 2 :=
  tsum_congr fun p => by rw [(hasDerivAt_affineFactor m p 1).deriv]

/-- For a nonnegative summable family `m` bounded by `1`, `∑_p m_p²` converges. -/
theorem summable_affineMass_sq (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1) (hms : Summable m) :
    Summable fun p : ℕ => m p ^ 2 := by
  refine (SecondLogDerivProduct.summable_deriv_one_sq (prodHyp_affineFactor hm0 hm1 hms)).congr
    fun p => ?_
  rw [(hasDerivAt_affineFactor m p 1).deriv]

/-- For a nonnegative summable family `m` bounded by `1`, `∑_p m_p(1 - m_p)` converges. -/
theorem summable_affineMass_mul_one_sub (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1)
    (hms : Summable m) : Summable fun p : ℕ => m p * (1 - m p) := by
  refine (hms.sub (summable_affineMass_sq hm0 hm1 hms)).congr fun p => ?_
  ring

/-- For a nonnegative summable family `m` bounded by `1`,
`∑_p m_p(1 - m_p) = ∑_p m_p - ∑_p m_p²`. -/
theorem tsum_affineMass_mul_one_sub (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1) (hms : Summable m) :
    (∑' p : ℕ, m p * (1 - m p)) = (∑' p : ℕ, m p) - ∑' p : ℕ, m p ^ 2 := by
  rw [← hms.tsum_sub (summable_affineMass_sq hm0 hm1 hms)]
  exact tsum_congr fun p => by ring

/-! ### Variance and `L²` for a pmf whose pgf is an affine Euler product -/

section PGFCore

variable {q : PMF ℕ}

/-- If the pgf `F` of `q` agrees on `[1/2, 1]` with `∏_p (1 + m_p(w - 1))`, then `F` has left
derivative `∑_p m_p` at `1`. -/
theorem hasDerivWithinAt_pgf_of_eq_prodG (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1)
    (hms : Summable m) (hpgf : ∀ w ∈ Icc (1 / 2 : ℝ) 1,
      PGFMean.pgf (fun n : ℕ => (q n).toReal) w = LogDerivProduct.prodG (affineFactor m) w) :
    HasDerivWithinAt (PGFMean.pgf fun n : ℕ => (q n).toReal) (∑' p : ℕ, m p) (Iio 1) 1 := by
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG (prodHyp_affineFactor hm0 hm1 hms)
  rw [tsum_deriv_affineFactor] at hprod
  refine hprod.congr_of_eventuallyEq ?_ (hpgf 1 ⟨by norm_num, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
  exact hpgf x ⟨hx.left.le, hx.right.le⟩

/-- If the pgf of `q` agrees on `[1/2, 1]` with `LogDerivProduct.prodG (affineFactor m)`, then
so do their derivatives within `Set.Iic 1` on `(1/2, 1]`. -/
theorem derivWithin_pgf_eq_derivWithin_prodG_of_eq (hpgf : ∀ w ∈ Icc (1 / 2 : ℝ) 1,
    PGFMean.pgf (fun n : ℕ => (q n).toReal) w = LogDerivProduct.prodG (affineFactor m) w) {w : ℝ}
    (hw : w ∈ Ioc (1 / 2 : ℝ) 1) :
    derivWithin (PGFMean.pgf fun n : ℕ => (q n).toReal) (Iic 1) w
      = derivWithin (LogDerivProduct.prodG (affineFactor m)) (Iic 1) w := by
  refine Filter.EventuallyEq.derivWithin_eq ?_ (hpgf w ⟨hw.left.le, hw.right⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hw.left), self_mem_nhdsWithin]
    with x hx1 hx2
  exact hpgf x ⟨hx1.le, hx2⟩

/-- If the pgf `F` of `q` agrees on `[1/2, 1]` with `∏_p (1 + m_p(w - 1))`, then
`u ↦ derivWithin F (Set.Iic 1) u` has left derivative `(∑_p m_p)² - ∑_p m_p²` at `1`. -/
theorem hasDerivWithinAt_derivWithin_pgf_of_eq_prodG (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1)
    (hms : Summable m) (hpgf : ∀ w ∈ Icc (1 / 2 : ℝ) 1,
      PGFMean.pgf (fun n : ℕ => (q n).toReal) w = LogDerivProduct.prodG (affineFactor m) w) :
    HasDerivWithinAt (derivWithin (PGFMean.pgf fun n : ℕ => (q n).toReal) (Iic 1))
      ((∑' p : ℕ, m p) ^ 2 - ∑' p : ℕ, m p ^ 2) (Iio 1) 1 := by
  have h := SecondLogDerivProduct.hasDerivWithinAt_derivWithin_prodG
    (prodHyp_affineFactor hm0 hm1 hms) (derivHyp_affineFactor m)
  rw [tsum_deriv2_affineFactor, tsum_deriv_affineFactor, tsum_deriv_affineFactor_sq,
    zero_add] at h
  refine h.congr_of_eventuallyEq ?_
    (derivWithin_pgf_eq_derivWithin_prodG_of_eq hpgf ⟨by norm_num, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
  exact derivWithin_pgf_eq_derivWithin_prodG_of_eq hpgf ⟨hx.left, hx.right.le⟩

/-- If the pgf of `q` agrees on `[1/2, 1]` with `∏_p (1 + m_p(w - 1))`, then the inclusion
variable has variance `∑_p m_p(1 - m_p)` under `q`. -/
theorem variance_of_pgf_eq_prodG (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1) (hms : Summable m)
    (hpgf : ∀ w ∈ Icc (1 / 2 : ℝ) 1,
      PGFMean.pgf (fun n : ℕ => (q n).toReal) w = LogDerivProduct.prodG (affineFactor m) w) :
    variance (fun n : ℕ => (n : ℝ)) q.toMeasure = ∑' p : ℕ, m p * (1 - m p) := by
  rw [BSDTamagawa.PGFSecondDeriv.variance_eq_of_hasDerivWithinAt_derivWithin' q
      (hasDerivWithinAt_pgf_of_eq_prodG hm0 hm1 hms hpgf)
      (hasDerivWithinAt_derivWithin_pgf_of_eq_prodG hm0 hm1 hms hpgf),
    tsum_affineMass_mul_one_sub hm0 hm1 hms]
  ring

/-- If the pgf of `q` agrees on `[1/2, 1]` with `∏_p (1 + m_p(w - 1))`, then the inclusion
variable is in `L²(q)`. -/
theorem memLp_two_of_pgf_eq_prodG (hm0 : ∀ p, 0 ≤ m p) (hm1 : ∀ p, m p ≤ 1) (hms : Summable m)
    (hpgf : ∀ w ∈ Icc (1 / 2 : ℝ) 1,
      PGFMean.pgf (fun n : ℕ => (q n).toReal) w = LogDerivProduct.prodG (affineFactor m) w) :
    MemLp (fun n : ℕ => (n : ℝ)) 2 q.toMeasure := by
  have h₁ := hasDerivWithinAt_pgf_of_eq_prodG hm0 hm1 hms hpgf
  have h₂ := hasDerivWithinAt_derivWithin_pgf_of_eq_prodG hm0 hm1 hms hpgf
  have hint := BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt q h₁
  obtain ⟨hF'', -⟩ :=
    BSDTamagawa.PGFSecondDeriv.summable_and_tsum_eq_of_hasDerivWithinAt_derivWithin _
      (fun _ => ENNReal.toReal_nonneg)
      (BSDTamagawa.PGFSecondDeriv.hasSum_toReal_pmf q) h₁ h₂
  exact (memLp_two_iff_integrable_sq measurable_from_top.aestronglyMeasurable).mpr
    ((PGFVariance.pgfDeriv2_summable_iff_integrable_sq q hint).mp hF'')

end PGFCore

/-! ### The joint law as a `PMF`, and the weighted coordinate sums -/

section Joint

variable {Λ : Finset ReductionData}

/-- The joint law as a `PMF (↥Λ → ℕ)`: the mass at the multi-index `𝐫` is
`ENNReal.ofReal π_Λ(𝐫)`. -/
noncomputable def jointReductionOmegaPMF (hΛ : Admissible Λ) : PMF (↥Λ → ℕ) :=
  ⟨fun r => ENNReal.ofReal (jointReductionOmegaDensity Λ r),
    ENNReal.summable.hasSum_iff.mpr <| by
      rw [← ENNReal.ofReal_tsum_of_nonneg (jointReductionOmegaDensity_nonneg hΛ)
          (summable_jointReductionOmegaDensity hΛ),
        tsum_jointReductionOmegaDensity_eq_one hΛ, ENNReal.ofReal_one]⟩

/-- The mass of the joint pmf at `𝐫` is `ENNReal.ofReal (π_Λ(𝐫))`, by definition. -/
theorem jointReductionOmegaPMF_apply (hΛ : Admissible Λ) (r : ↥Λ → ℕ) :
    (jointReductionOmegaPMF hΛ) r = ENNReal.ofReal (jointReductionOmegaDensity Λ r) := rfl

/-- The masses of the joint pmf, read back in `ℝ`, are the joint densities. -/
theorem jointReductionOmegaPMF_apply_toReal (hΛ : Admissible Λ) (r : ↥Λ → ℕ) :
    ((jointReductionOmegaPMF hΛ) r).toReal = jointReductionOmegaDensity Λ r :=
  ENNReal.toReal_ofReal (jointReductionOmegaDensity_nonneg hΛ r)

/-- The measure of the joint pmf is the joint law `jointReductionOmegaMeasure Λ`. -/
theorem jointReductionOmegaPMF_toMeasure (hΛ : Admissible Λ) :
    (jointReductionOmegaPMF hΛ).toMeasure = jointReductionOmegaMeasure Λ := by
  refine Measure.ext fun s hs => ?_
  rw [PMF.toMeasure_apply_eq_tsum, jointReductionOmegaMeasure, Measure.sum_apply _ hs]
  refine tsum_congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases h : r ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, mul_one,
      jointReductionOmegaPMF_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- The weighted coordinate sum `weightSum t 𝐫 = ∑_j t_j 𝐫_j`. -/
def weightSum (t : ↥Λ → ℕ) (r : ↥Λ → ℕ) : ℕ := ∑ j, t j * r j

/-- The weighted local mass `weightMass t p = ∑_j t_j δ_p(j)`. -/
noncomputable def weightMass (t : ↥Λ → ℕ) (p : ℕ) : ℝ :=
  ∑ j, (t j : ℝ) * stratumLocalMass (j : ReductionData) p

/-- `0 ≤ weightMass t p`. -/
theorem weightMass_nonneg (t : ↥Λ → ℕ) (p : ℕ) : 0 ≤ weightMass t p :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (stratumLocalMass_nonneg _ p)

/-- `weightMass t p ≤ 1` for a `0/1`-weight vector `t`. -/
theorem weightMass_le_one {t : ↥Λ → ℕ} (hone : ∀ j, t j ≤ 1) (p : ℕ) : weightMass t p ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_stratumLocalMass_le_one Λ p)
  calc (t j : ℝ) * stratumLocalMass (j : ReductionData) p
      ≤ 1 * stratumLocalMass (j : ReductionData) p :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hone j) (stratumLocalMass_nonneg _ p)
    _ = stratumLocalMass (j : ReductionData) p := one_mul _

/-- For admissible `Λ`, the family `p ↦ weightMass t p` is summable. -/
theorem summable_weightMass (hΛ : Admissible Λ) (t : ↥Λ → ℕ) : Summable (weightMass t) := by
  have h : Summable fun p : ℕ =>
      ∑ j : ↥Λ, (t j : ℝ) * stratumLocalMass (j : ReductionData) p :=
    summable_sum fun j _ =>
      (summable_stratumLocalMass (hΛ (j : ReductionData) j.property)).mul_left (t j : ℝ)
  exact h

/-- For a `0/1`-weight vector `t`,
`1 + weightMass t p * (w - 1) = 1 + ∑_j δ_p(j)(w^{t_j} - 1)`. -/
theorem affineFactor_weightMass_eq {t : ↥Λ → ℕ} (hone : ∀ j, t j ≤ 1) (p : ℕ) (w : ℝ) :
    affineFactor (weightMass t) p w
      = 1 + ∑ j : ↥Λ, stratumLocalMass (j : ReductionData) p * (w ^ t j - 1) := by
  rw [affineFactor, weightMass, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hone j) with h | h <;> rw [h] <;> simp

/-- For a `0/1`-weight vector `t`, the coerced affine factor is the complex joint local factor at
the diagonal point `u_j = w^{t_j}`. -/
theorem ofReal_affineFactor_weightMass {t : ↥Λ → ℕ} (hone : ∀ j, t j ≤ 1) (p : ℕ) (w : ℝ) :
    ((affineFactor (weightMass t) p w : ℝ) : ℂ)
      = jointReductionOmegaEulerFactor Λ p (fun j => ((w ^ t j : ℝ) : ℂ)) := by
  rw [jointReductionOmegaEulerFactor_eq_one_add, affineFactor_weightMass_eq hone,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- On `[1/2, 1]` the real infinite product `LogDerivProduct.prodG` of
`affineFactor (weightMass t)` coerces to the joint Euler product at the diagonal point
`u_j = w^{t_j}`. -/
theorem ofReal_prodG_affineFactor_weightMass (hΛ : Admissible Λ) {t : ↥Λ → ℕ}
    (hone : ∀ j, t j ≤ 1) {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    ((LogDerivProduct.prodG (affineFactor (weightMass t)) w : ℝ) : ℂ)
      = jointReductionOmegaEulerProduct Λ (fun j => ((w ^ t j : ℝ) : ℂ)) := by
  have hmap := (LogDerivProduct.hasProd_prodG (prodHyp_affineFactor (weightMass_nonneg t)
    (weightMass_le_one hone) (summable_weightMass hΛ t))
    (mem_window_of_mem_Icc_half hw)).map Complex.ofRealHom Complex.continuous_ofReal
  rw [jointReductionOmegaEulerProduct]
  refine ((hmap.congr_fun fun p => ?_).tprod_eq).symm
  simpa using (ofReal_affineFactor_weightMass hone p w).symm

/-- The multi-monomial at the diagonal point `u_j = w^{t_j}` is the ordinary power
`w^{weightSum t 𝐫}`: `∏_j (w^{t_j})^{𝐫_j} = w^{∑_j t_j 𝐫_j}`. -/
theorem multiMonomial_weightSum (t r : ↥Λ → ℕ) (w : ℝ) :
    multiMonomial r (fun j => ((w ^ t j : ℝ) : ℂ)) = ((w ^ weightSum t r : ℝ) : ℂ) := by
  have hterm : ∀ j : ↥Λ, (((w ^ t j : ℝ) : ℂ)) ^ r j = (((w ^ t j) ^ r j : ℝ) : ℂ) := fun j => by
    push_cast
    ring
  rw [multiMonomial, Finset.prod_congr rfl fun j _ => hterm j, ← Complex.ofReal_prod]
  congr 1
  rw [weightSum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun j _ => (pow_mul w (t j) (r j)).symm

/-- For `w ∈ [0, 1]`, the series `∑_𝐫 π_Λ(𝐫) w^{weightSum t 𝐫}` is summable. -/
theorem summable_density_mul_pow_weightSum (hΛ : Admissible Λ) (t : ↥Λ → ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Summable fun r : ↥Λ → ℕ => jointReductionOmegaDensity Λ r * w ^ weightSum t r :=
  Summable.of_nonneg_of_le
    (fun r => mul_nonneg (jointReductionOmegaDensity_nonneg hΛ r) (pow_nonneg hw0 _))
    (fun r => mul_le_of_le_one_right (jointReductionOmegaDensity_nonneg hΛ r)
      (pow_le_one₀ hw0 hw1))
    (summable_jointReductionOmegaDensity hΛ)

/-- For `w ∈ [0, 1]`, `∑_𝐫 π_Λ(𝐫) w^{weightSum t 𝐫} = F_Λ(w^t)`. -/
theorem ofReal_tsum_density_mul_pow_weightSum (hΛ : Admissible Λ) (t : ↥Λ → ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ((∑' r : ↥Λ → ℕ, jointReductionOmegaDensity Λ r * w ^ weightSum t r : ℝ) : ℂ)
      = jointReductionOmegaEulerProduct Λ (fun j => ((w ^ t j : ℝ) : ℂ)) := by
  refine (Complex.hasSum_ofReal.mpr
    (summable_density_mul_pow_weightSum hΛ t hw0 hw1).hasSum).unique ?_
  refine (hasSum_jointReductionOmegaDensity_multiMonomial hΛ _).congr_fun fun r => ?_
  rw [multiMonomial_weightSum]
  push_cast
  ring

/-- The law of `weightSum t`: the pushforward of the joint pmf along `weightSum t`. -/
noncomputable def weightReductionOmegaPMF (hΛ : Admissible Λ) (t : ↥Λ → ℕ) : PMF ℕ :=
  (jointReductionOmegaPMF hΛ).map (weightSum t)

/-- The measure of the law of `weightSum t` is the pushforward of the joint pmf's measure. -/
theorem weightReductionOmegaPMF_toMeasure_map (hΛ : Admissible Λ) (t : ↥Λ → ℕ) :
    (weightReductionOmegaPMF hΛ t).toMeasure
      = (jointReductionOmegaPMF hΛ).toMeasure.map (weightSum t) := by
  rw [weightReductionOmegaPMF]
  exact (PMF.toMeasure_map _ _ (measurable_of_countable _)).symm

/-- The measure of the law of `weightSum t` is the pushforward of the joint law `P_Λ`. -/
theorem weightReductionOmegaPMF_toMeasure (hΛ : Admissible Λ) (t : ↥Λ → ℕ) :
    (weightReductionOmegaPMF hΛ t).toMeasure
      = (jointReductionOmegaMeasure Λ).map (weightSum t) := by
  rw [weightReductionOmegaPMF_toMeasure_map, jointReductionOmegaPMF_toMeasure]

/-- For `w ∈ [0, 1]`, the pgf of `weightSum t` at `w` is `∑_𝐫 π_Λ(𝐫) w^{weightSum t 𝐫}`. -/
theorem pgf_weightReductionOmegaPMF (hΛ : Admissible Λ) (t : ↥Λ → ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    PGFMean.pgf (fun n : ℕ => ((weightReductionOmegaPMF hΛ t) n).toReal) w
      = ∑' r : ↥Λ → ℕ, jointReductionOmegaDensity Λ r * w ^ weightSum t r := by
  have habs : ∀ n : ℕ, ‖w ^ n‖ ≤ 1 := fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw0 n)]
    exact pow_le_one₀ hw0 hw1
  have hqint : Integrable (fun n : ℕ => w ^ n) (weightReductionOmegaPMF hΛ t).toMeasure :=
    (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable
      (.of_forall habs)
  have hpint : Integrable (fun r : ↥Λ → ℕ => w ^ weightSum t r)
      (jointReductionOmegaPMF hΛ).toMeasure :=
    (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (.of_forall fun r => habs _)
  rw [PGFMean.pgf]
  calc (∑' n : ℕ, ((weightReductionOmegaPMF hΛ t) n).toReal * w ^ n)
      = ∫ n, w ^ n ∂ (weightReductionOmegaPMF hΛ t).toMeasure := by
        rw [PMF.integral_eq_tsum _ _ hqint]
        exact tsum_congr fun n => by rw [smul_eq_mul]
    _ = ∫ r, w ^ weightSum t r ∂ (jointReductionOmegaPMF hΛ).toMeasure := by
        rw [weightReductionOmegaPMF_toMeasure_map,
          integral_map (measurable_of_countable _).aemeasurable
            measurable_from_top.aestronglyMeasurable]
    _ = ∑' r : ↥Λ → ℕ, jointReductionOmegaDensity Λ r * w ^ weightSum t r := by
        rw [PMF.integral_eq_tsum _ _ hpint]
        exact tsum_congr fun r => by
          rw [smul_eq_mul, jointReductionOmegaPMF_apply_toReal]

/-- On `[1/2, 1]` the pgf of `weightSum t` equals
`LogDerivProduct.prodG (affineFactor (weightMass t))`. -/
theorem pgf_weightReductionOmegaPMF_eq_prodG (hΛ : Admissible Λ) {t : ↥Λ → ℕ}
    (hone : ∀ j, t j ≤ 1) {w : ℝ} (hw : w ∈ Icc (1 / 2 : ℝ) 1) :
    PGFMean.pgf (fun n : ℕ => ((weightReductionOmegaPMF hΛ t) n).toReal) w
      = LogDerivProduct.prodG (affineFactor (weightMass t)) w := by
  have hw0 : (0 : ℝ) ≤ w := by linarith [hw.left]
  rw [pgf_weightReductionOmegaPMF hΛ t hw0 hw.right]
  exact Complex.ofReal_inj.mp
    ((ofReal_tsum_density_mul_pow_weightSum hΛ t hw0 hw.right).trans
      (ofReal_prodG_affineFactor_weightMass hΛ hone hw).symm)

/-- For a `0/1`-weight vector `t`, `Var_{P_Λ}(weightSum t) = ∑_p m_p(1 - m_p)` with
`m = weightMass t`. -/
theorem variance_weightSum (hΛ : Admissible Λ) {t : ↥Λ → ℕ} (hone : ∀ j, t j ≤ 1) :
    variance (fun r : ↥Λ → ℕ => (weightSum t r : ℝ)) (jointReductionOmegaMeasure Λ)
      = ∑' p : ℕ, weightMass t p * (1 - weightMass t p) := by
  have hvar := variance_of_pgf_eq_prodG (weightMass_nonneg t) (weightMass_le_one hone)
    (summable_weightMass hΛ t) fun w hw => pgf_weightReductionOmegaPMF_eq_prodG hΛ hone hw
  rw [weightReductionOmegaPMF_toMeasure hΛ t,
    variance_map measurable_from_top.aemeasurable
      (measurable_of_countable _).aemeasurable] at hvar
  exact hvar

/-- For a `0/1`-weight vector `t`, `weightSum t ∈ L²(P_Λ)`. -/
theorem memLp_two_weightSum (hΛ : Admissible Λ) {t : ↥Λ → ℕ} (hone : ∀ j, t j ≤ 1) :
    MemLp (fun r : ↥Λ → ℕ => (weightSum t r : ℝ)) 2 (jointReductionOmegaMeasure Λ) := by
  have h := memLp_two_of_pgf_eq_prodG (weightMass_nonneg t) (weightMass_le_one hone)
    (summable_weightMass hΛ t) fun w hw => pgf_weightReductionOmegaPMF_eq_prodG hΛ hone hw
  rw [weightReductionOmegaPMF_toMeasure hΛ t] at h
  exact (memLp_map_measure_iff measurable_from_top.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mp h

end Joint

/-! ### The two-element index set `Λ = {K, K'}` -/

section Pair

variable {K K' : ReductionData}

/-- If neither `K` nor `K'` lies in `𝒦₀`, then `Λ = {K, K'}` is an admissible index set. -/
theorem admissible_pairFinset (hK : K ∉ (K0 : Set ReductionData))
    (hK' : K' ∉ (K0 : Set ReductionData)) (hne : K ≠ K') :
    Admissible (pairFinset K K' hne) := by
  intro L hL
  rcases (mem_pairFinset hne).mp hL with h | h
  · exact h ▸ hK
  · exact h ▸ hK'

/-- The index `pairIndexFst K K' hne` coerces to `K`. -/
theorem coe_pairIndexFst (hne : K ≠ K') :
    ((pairIndexFst K K' hne : ↥(pairFinset K K' hne)) : ReductionData) = K := rfl

/-- The index `pairIndexSnd K K' hne` coerces to `K'`. -/
theorem coe_pairIndexSnd (hne : K ≠ K') :
    ((pairIndexSnd K K' hne : ↥(pairFinset K K' hne)) : ReductionData) = K' := rfl

/-- A sum over `↥{K, K'}` is the sum of its two terms. -/
theorem sum_over_pairIndex {M : Type*} [AddCommMonoid M] (hne : K ≠ K')
    (f : ↥(pairFinset K K' hne) → M) :
    ∑ j, f j = f (pairIndexFst K K' hne) + f (pairIndexSnd K K' hne) := by
  have hu : (Finset.univ : Finset ↥(pairFinset K K' hne))
      = Finset.cons (pairIndexFst K K' hne) {pairIndexSnd K K' hne}
        (by simpa using pairIndexFst_ne_pairIndexSnd hne) := by
    refine Finset.ext fun j => ?_
    simp only [Finset.mem_univ, true_iff, Finset.mem_cons, Finset.mem_singleton]
    by_cases h : j = pairIndexFst K K' hne
    · exact Or.inl h
    · exact Or.inr (eq_pairIndexSnd_of_ne hne h)
  rw [hu, Finset.sum_cons, Finset.sum_singleton]

/-- The weight vector `e_K` picking out the `K`-coordinate. -/
noncomputable def fstWeight (K K' : ReductionData) (hne : K ≠ K')
    (j : ↥(pairFinset K K' hne)) : ℕ :=
  open scoped Classical in if j = pairIndexFst K K' hne then 1 else 0

/-- The weight vector `e_{K'}` picking out the `K'`-coordinate. -/
noncomputable def sndWeight (K K' : ReductionData) (hne : K ≠ K')
    (j : ↥(pairFinset K K' hne)) : ℕ :=
  open scoped Classical in if j = pairIndexSnd K K' hne then 1 else 0

/-- The all-ones weight vector, whose weighted sum is `ω_K + ω_{K'}`. -/
def totalWeight (K K' : ReductionData) (hne : K ≠ K') : ↥(pairFinset K K' hne) → ℕ := fun _ => 1

/-- `e_K` is a `0/1`-weight vector. -/
theorem fstWeight_le_one (hne : K ≠ K') (j : ↥(pairFinset K K' hne)) :
    fstWeight K K' hne j ≤ 1 := by
  rw [fstWeight]
  split_ifs <;> norm_num

/-- `e_{K'}` is a `0/1`-weight vector. -/
theorem sndWeight_le_one (hne : K ≠ K') (j : ↥(pairFinset K K' hne)) :
    sndWeight K K' hne j ≤ 1 := by
  rw [sndWeight]
  split_ifs <;> norm_num

/-- The all-ones vector is a `0/1`-weight vector. -/
theorem totalWeight_le_one (hne : K ≠ K') (j : ↥(pairFinset K K' hne)) :
    totalWeight K K' hne j ≤ 1 := le_rfl

/-- The weighted sum against `e_K` is the `K`-coordinate `ω_K`. -/
theorem weightSum_fstWeight (hne : K ≠ K') (r : ↥(pairFinset K K' hne) → ℕ) :
    weightSum (fstWeight K K' hne) r = r (pairIndexFst K K' hne) := by
  rw [weightSum, Finset.sum_eq_single (pairIndexFst K K' hne)
    (fun j _ hj => by simp [fstWeight, hj]) fun h => absurd (Finset.mem_univ _) h]
  simp [fstWeight]

/-- The weighted sum against `e_{K'}` is the `K'`-coordinate `ω_{K'}`. -/
theorem weightSum_sndWeight (hne : K ≠ K') (r : ↥(pairFinset K K' hne) → ℕ) :
    weightSum (sndWeight K K' hne) r = r (pairIndexSnd K K' hne) := by
  rw [weightSum, Finset.sum_eq_single (pairIndexSnd K K' hne)
    (fun j _ hj => by simp [sndWeight, hj]) fun h => absurd (Finset.mem_univ _) h]
  simp [sndWeight]

/-- The weighted sum against the all-ones vector is `ω_K + ω_{K'}`. -/
theorem weightSum_totalWeight (hne : K ≠ K') (r : ↥(pairFinset K K' hne) → ℕ) :
    weightSum (totalWeight K K' hne) r
      = r (pairIndexFst K K' hne) + r (pairIndexSnd K K' hne) := by
  rw [weightSum]
  simp only [totalWeight, one_mul]
  exact sum_over_pairIndex hne r

/-- `weightMass e_K = δ_·(K)`. -/
theorem weightMass_fstWeight (hne : K ≠ K') (p : ℕ) :
    weightMass (fstWeight K K' hne) p = stratumLocalMass K p := by
  rw [weightMass, Finset.sum_eq_single (pairIndexFst K K' hne)
    (fun j _ hj => by simp [fstWeight, hj]) fun h => absurd (Finset.mem_univ _) h]
  simp [fstWeight, coe_pairIndexFst hne]

/-- `weightMass e_{K'} = δ_·(K')`. -/
theorem weightMass_sndWeight (hne : K ≠ K') (p : ℕ) :
    weightMass (sndWeight K K' hne) p = stratumLocalMass K' p := by
  rw [weightMass, Finset.sum_eq_single (pairIndexSnd K K' hne)
    (fun j _ hj => by simp [sndWeight, hj]) fun h => absurd (Finset.mem_univ _) h]
  simp [sndWeight, coe_pairIndexSnd hne]

/-- `weightMass 1 = δ_·(K) + δ_·(K')`. -/
theorem weightMass_totalWeight (hne : K ≠ K') (p : ℕ) :
    weightMass (totalWeight K K' hne) p = stratumLocalMass K p + stratumLocalMass K' p := by
  rw [weightMass]
  simp only [totalWeight, Nat.cast_one, one_mul]
  exact sum_over_pairIndex hne fun j => stratumLocalMass (j : ReductionData) p

/-! ### The product series `∑_p δ_p(K) δ_p(K')` -/

/-- For `K ∉ 𝒦₀` and any `K'`, the series `∑_p δ_p(K) δ_p(K')` converges. -/
theorem summable_stratumLocalMass_mul (hK : K ∉ (K0 : Set ReductionData)) (K' : ReductionData) :
    Summable fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p :=
  Summable.of_nonneg_of_le
    (fun p => mul_nonneg (stratumLocalMass_nonneg K p) (stratumLocalMass_nonneg K' p))
    (fun p => mul_le_of_le_one_right (stratumLocalMass_nonneg K p)
      (stratumLocalMass_le_one K' p))
    (summable_stratumLocalMass hK)

/-- `δ_p(K) + δ_p(K') ≤ 1` for distinct `K, K'`. -/
theorem stratumLocalMass_add_le_one (hne : K ≠ K') (p : ℕ) :
    stratumLocalMass K p + stratumLocalMass K' p ≤ 1 := by
  have h := sum_stratumLocalMass_le_one (pairFinset K K' hne) p
  rwa [sum_over_pairIndex hne fun j => stratumLocalMass (j : ReductionData) p,
    coe_pairIndexFst hne, coe_pairIndexSnd hne] at h

/-- For distinct `K, K' ∉ 𝒦₀`, with `a_p = δ_p(K)` and `a'_p = δ_p(K')`,
`∑_p (a_p + a'_p)(1 - a_p - a'_p) - ∑_p a_p(1 - a_p) - ∑_p a'_p(1 - a'_p) = -2 ∑_p a_p a'_p`. -/
theorem tsum_variance_polarisation (hK : K ∉ (K0 : Set ReductionData))
    (hK' : K' ∉ (K0 : Set ReductionData)) (hne : K ≠ K') :
    (∑' p : ℕ, (stratumLocalMass K p + stratumLocalMass K' p)
        * (1 - (stratumLocalMass K p + stratumLocalMass K' p)))
      - (∑' p : ℕ, stratumLocalMass K p * (1 - stratumLocalMass K p))
      - (∑' p : ℕ, stratumLocalMass K' p * (1 - stratumLocalMass K' p))
      = -2 * ∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p := by
  have hsum : Summable fun p : ℕ => stratumLocalMass K p + stratumLocalMass K' p :=
    (summable_stratumLocalMass hK).add (summable_stratumLocalMass hK')
  have hnn : ∀ p : ℕ, 0 ≤ stratumLocalMass K p + stratumLocalMass K' p := fun p =>
    add_nonneg (stratumLocalMass_nonneg K p) (stratumLocalMass_nonneg K' p)
  have h1 := summable_affineMass_mul_one_sub hnn (stratumLocalMass_add_le_one hne) hsum
  have h2 := summable_affineMass_mul_one_sub (stratumLocalMass_nonneg K)
    (stratumLocalMass_le_one K) (summable_stratumLocalMass hK)
  have h3 := summable_affineMass_mul_one_sub (stratumLocalMass_nonneg K')
    (stratumLocalMass_le_one K') (summable_stratumLocalMass hK')
  rw [← h1.tsum_sub h2, ← (h1.sub h2).tsum_sub h3,
    ← (summable_stratumLocalMass_mul hK K').tsum_mul_left]
  exact tsum_congr fun p => by ring

end Pair

/-! ### The covariance -/

section Main

variable {K K' : ReductionData}

/-- Let `K, K' ∈ 𝒦 ∖ 𝒦₀` be distinct and let `P` be the joint law
`P_{{K, K'}} = jointReductionOmegaMeasure (pairFinset K K' hne)` on `↥{K, K'} → ℕ`, so that
`P({𝐫}) = π_{{K, K'}}(𝐫)`. Then the series `∑_p δ_p(K) δ_p(K')` converges absolutely and
`Cov_P(ω_K(E), ω_{K'}(E)) = -∑_{p ∈ 𝒫} δ_p(K) δ_p(K')`, where `ω_K` and `ω_{K'}` are the
coordinates at `pairIndexFst K K' hne` and `pairIndexSnd K K' hne`. -/
@[bsd_tamagawa "T040c"]
theorem covariance_pairReductionOmega (hK : K ∉ (K0 : Set ReductionData))
    (hK' : K' ∉ (K0 : Set ReductionData)) (hne : K ≠ K') :
    Summable (fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p) ∧
      covariance (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexFst K K' hne) : ℝ))
          (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexSnd K K' hne) : ℝ))
          (jointReductionOmegaMeasure (pairFinset K K' hne))
        = -∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p := by
  refine ⟨summable_stratumLocalMass_mul hK K', ?_⟩
  have hΛ : Admissible (pairFinset K K' hne) := admissible_pairFinset hK hK' hne
  have := isProbabilityMeasure_jointReductionOmegaMeasure hΛ
  have hX : MemLp (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexFst K K' hne) : ℝ)) 2
      (jointReductionOmegaMeasure (pairFinset K K' hne)) := by
    have h := memLp_two_weightSum hΛ (fstWeight_le_one hne)
    simpa only [weightSum_fstWeight hne] using h
  have hY : MemLp (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexSnd K K' hne) : ℝ)) 2
      (jointReductionOmegaMeasure (pairFinset K K' hne)) := by
    have h := memLp_two_weightSum hΛ (sndWeight_le_one hne)
    simpa only [weightSum_sndWeight hne] using h
  have hvarX : variance (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexFst K K' hne) : ℝ))
      (jointReductionOmegaMeasure (pairFinset K K' hne))
      = ∑' p : ℕ, stratumLocalMass K p * (1 - stratumLocalMass K p) := by
    have h := variance_weightSum hΛ (fstWeight_le_one hne)
    simpa only [weightSum_fstWeight hne, weightMass_fstWeight hne] using h
  have hvarY : variance (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexSnd K K' hne) : ℝ))
      (jointReductionOmegaMeasure (pairFinset K K' hne))
      = ∑' p : ℕ, stratumLocalMass K' p * (1 - stratumLocalMass K' p) := by
    have h := variance_weightSum hΛ (sndWeight_le_one hne)
    simpa only [weightSum_sndWeight hne, weightMass_sndWeight hne] using h
  have hvarS : variance (fun r : ↥(pairFinset K K' hne) → ℕ =>
      ((r (pairIndexFst K K' hne) : ℝ) + (r (pairIndexSnd K K' hne) : ℝ)))
      (jointReductionOmegaMeasure (pairFinset K K' hne))
      = ∑' p : ℕ, (stratumLocalMass K p + stratumLocalMass K' p)
          * (1 - (stratumLocalMass K p + stratumLocalMass K' p)) := by
    have h := variance_weightSum hΛ (totalWeight_le_one hne)
    simpa only [weightSum_totalWeight hne, weightMass_totalWeight hne, Nat.cast_add] using h
  have hadd := variance_fun_add hX hY
  rw [hvarS, hvarX, hvarY] at hadd
  have hpol := tsum_variance_polarisation hK hK' hne
  linarith [hadd, hpol]

/-- `pairIndexEquiv hne` sends a multi-index `r` to `(r K, r K')`. -/
@[simp]
theorem pairIndexEquiv_apply (hne : K ≠ K') (r : ↥(pairFinset K K' hne) → ℕ) :
    pairIndexEquiv hne r = (r (pairIndexFst K K' hne), r (pairIndexSnd K K' hne)) := rfl

/-- The inverse of `pairIndexEquiv hne` sends a pair `q` to `pairIndexOfProd hne q`. -/
@[simp]
theorem pairIndexEquiv_symm_apply (hne : K ≠ K') (q : ℕ × ℕ) :
    (pairIndexEquiv hne).symm q = pairIndexOfProd hne q := rfl

/-- Let `K, K' ∈ 𝒦 ∖ 𝒦₀` be distinct and let `P` be the joint probability measure on `ℤ_{≥0}²` with
`P({(r, r')}) = π_{{K, K'}}(r, r')` (`pairReductionOmegaMeasure`). Then the series
`∑_p δ_p(K) δ_p(K')` converges absolutely and
`Cov_P(ω_K(E), ω_{K'}(E)) = -∑_{p ∈ 𝒫} δ_p(K) δ_p(K')`, the two random variables being the
coordinate projections `(r, r') ↦ r` and `(r, r') ↦ r'`. -/
@[bsd_tamagawa "T040c"]
theorem covariance_pairReductionOmega_prod (hK : K ∉ (K0 : Set ReductionData))
    (hK' : K' ∉ (K0 : Set ReductionData)) (hne : K ≠ K') :
    Summable (fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p) ∧
      covariance (fun q : ℕ × ℕ => (q.1 : ℝ)) (fun q : ℕ × ℕ => (q.2 : ℝ))
          (pairReductionOmegaMeasure K K' hne)
        = -∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p := by
  refine ⟨summable_stratumLocalMass_mul hK K', ?_⟩
  rw [pairReductionOmegaMeasure,
    covariance_map_fun (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
  exact (covariance_pairReductionOmega hK hK' hne).right

end Main

end WeierstrassCurve
