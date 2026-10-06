/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.JointLawProbability

/-!
# The bivariate generating-function identity on the *closed* bidisc

Let `π(r, b)` be the joint limiting density of `(ω_Tam(E), Ω(Tam(E)))`. The identity

`∑_{(r, b)} π(r, b) u^r w^b = ∏_{p ∈ 𝒫} g_p(u, w)`,
`g_p(u, w) = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`,

holds on the *open* bidisc `‖u‖ < 1`, `‖w‖ < 1`, and extends to the *closed* bidisc `‖u‖ ≤ 1`,
`‖w‖ ≤ 1`: both sides are continuous there, and the closed bidisc lies in the closure of the open
one.

## Main definitions

* `WeierstrassCurve.omegaCardFactorsFaceParam`: the embedding `(u, w) ↦ (0, u, w, ∅, ∅)` of the
  bidisc into the parameter space of the multivariate Euler product.

## Main results

* `WeierstrassCurve.tsum_jointOmegaCardFactorsDensity_mul_pow`: the identity on the closed bidisc.
* `WeierstrassCurve.hasSum_jointOmegaCardFactorsDensity_mul_pow_of_lt_one`: the identity on the
  open bidisc, indexed by `ℤ_{≥0}²`.
* `WeierstrassCurve.continuousOn_tsum_jointOmegaCardFactorsDensity_mul_pow`: the left side is
  continuous on the closed bidisc.
* `WeierstrassCurve.continuousOn_omegaCardFactorsEulerProduct`: the right side is continuous on the
  closed bidisc.
* `WeierstrassCurve.mem_closure_setOf_norm_lt_one_prod`: the closed bidisc lies in the closure of
  the open one.

## Implementation notes

The sum is a `tsum` over `ℤ_{≥0}²` and the product is a `tprod` over the primes. The multiplicative
support of `p ↦ g_p(u, w)` is infinite for generic `(u, w)`, so the product cannot be a `finprod`,
which would be identically `1`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex

/-! ### §1. The open-bidisc expansion on the index space `ℤ_{≥0}²` -/

/-- **The open-bidisc identity, indexed by `ℤ_{≥0}²`.** For `‖u‖ < 1` and `‖w‖ < 1`,

`∑_{(r, b)} π(r, b) u^r w^b = ∏_{p ∈ 𝒫} g_p(u, w)`, as a `HasSum`. -/
theorem hasSum_jointOmegaCardFactorsDensity_mul_pow_of_lt_one {u w : ℂ} (hu : ‖u‖ < 1)
    (hw : ‖w‖ < 1) :
    HasSum (fun rb : ℕ × ℕ =>
        ((jointOmegaCardFactorsDensity rb.1 rb.2 : ℝ) : ℂ) * u ^ rb.1 * w ^ rb.2)
      (omegaCardFactorsEulerProduct u w) := by
  have hz : ∀ i : Bool, ‖(bif i then w else u)‖ < 1 := by
    rintro (_ | _)
    · simpa using hu
    · simpa using hw
  have h := hasPolydiscExpansion_jointOmegaCardFactorsDensity.2.2.2
    (fun i : Bool => bif i then w else u) hz
  refine (boolFinsuppEquivProd.hasSum_iff).mp (h.congr_fun fun j => ?_)
  simp only [Function.comp_apply, boolFinsuppEquivProd, Equiv.coe_fn_mk, Fintype.prod_bool,
    smul_eq_mul, Bool.cond_true, Bool.cond_false]
  ring

/-! ### §2. The left side on the closed bidisc: termwise bound and continuity -/

/-- For `0 ≤ c`, `‖u‖ ≤ 1` and `‖w‖ ≤ 1`, `‖c u^r w^b‖ ≤ c`. -/
theorem norm_ofReal_mul_pow_mul_pow_le {u w : ℂ} (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (r b : ℕ) : ‖((c : ℝ) : ℂ) * u ^ r * w ^ b‖ ≤ c := by
  have h1 : ‖u‖ ^ r ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
  have h2 : ‖w‖ ^ b ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
  have hbn : (0 : ℝ) ≤ ‖w‖ ^ b := pow_nonneg (norm_nonneg _) b
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc]
  simpa using mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 hbn
    (by positivity : (0 : ℝ) ≤ c * 1)

/-- **The sum is continuous on the closed bidisc.** The function
`(u, w) ↦ ∑_{(r, b)} π(r, b) u^r w^b` is continuous on `‖u‖ ≤ 1`, `‖w‖ ≤ 1`. -/
theorem continuousOn_tsum_jointOmegaCardFactorsDensity_mul_pow :
    ContinuousOn (fun q : ℂ × ℂ => ∑' rb : ℕ × ℕ,
        ((jointOmegaCardFactorsDensity rb.1 rb.2 : ℝ) : ℂ) * q.1 ^ rb.1 * q.2 ^ rb.2)
      {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1} :=
  continuousOn_tsum (u := fun rb : ℕ × ℕ => jointOmegaCardFactorsDensity rb.1 rb.2)
    (fun rb => ((continuous_const.mul ((continuous_fst).pow rb.1)).mul
      ((continuous_snd).pow rb.2)).continuousOn)
    summable_jointOmegaCardFactorsDensity
    fun rb _ hq => norm_ofReal_mul_pow_mul_pow_le hq.1 hq.2
      (jointOmegaCardFactorsDensity_nonneg rb.1 rb.2) rb.1 rb.2

/-! ### §3. The right side on the closed bidisc: continuity of the Euler product -/

/-- At a non-prime index `p`, `g_p = 1`. -/
theorem omegaCardFactorsEulerFactor_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (u w : ℂ) :
    omegaCardFactorsEulerFactor p u w = 1 :=
  dite_eq_right hp

/-- **The tail series is continuous on the closed unit disc.** `w ↦ ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}` is
continuous on `‖w‖ ≤ 1`. -/
theorem continuousOn_tsum_δ_toReal_mul_pow_cardFactors (p : ℕ) [Fact p.Prime] :
    ContinuousOn (fun w : ℂ => ∑' t : ℕ,
        if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0)
      {w : ℂ | ‖w‖ ≤ 1} := by
  refine continuousOn_tsum (u := fun t : ℕ => (δ p t).toReal) (fun t => ?_)
    (hasSum_δ_toReal p).summable fun t w hw => ?_
  · by_cases ht : 2 ≤ t
    · simp only [ite_eq_left ht]
      exact (continuous_const.mul (continuous_pow _)).continuousOn
    · simp only [ite_eq_right ht]
      exact continuousOn_const
  · by_cases ht : 2 ≤ t
    · rw [ite_eq_left ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
        norm_pow]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ (norm_nonneg _) hw)
    · rw [ite_eq_right ht]
      simp

/-- **Each local factor is continuous on the closed bidisc.** For every `p`, the function
`(u, w) ↦ g_p(u, w)` is continuous on `‖u‖ ≤ 1`, `‖w‖ ≤ 1`. -/
theorem continuousOn_omegaCardFactorsEulerFactor (p : ℕ) :
    ContinuousOn (fun q : ℂ × ℂ => omegaCardFactorsEulerFactor p q.1 q.2)
      {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1} := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hrw : (fun q : ℂ × ℂ => omegaCardFactorsEulerFactor p q.1 q.2)
        = fun q : ℂ × ℂ => ((δ p 1).toReal : ℂ) + q.1 * ∑' t : ℕ,
            if 2 ≤ t then ((δ p t).toReal : ℂ) * q.2 ^ ArithmeticFunction.cardFactors t
              else 0 :=
      funext fun q => omegaCardFactorsEulerFactor_of_prime p q.1 q.2
    rw [hrw]
    exact continuousOn_const.add (continuous_fst.continuousOn.mul
      ((continuousOn_tsum_δ_toReal_mul_pow_cardFactors p).comp
        continuous_snd.continuousOn fun q hq => hq.2))
  · simp only [omegaCardFactorsEulerFactor_of_not_prime hp]
    exact continuousOn_const

/-- **Each partial product is continuous on the closed bidisc.** For a finite set `T` of primes,
`(u, w) ↦ ∏_{p ∈ T} g_p(u, w)` is continuous on `‖u‖ ≤ 1`, `‖w‖ ≤ 1`. -/
theorem continuousOn_prod_omegaCardFactorsEulerFactor (T : Finset {q : ℕ // q.Prime}) :
    ContinuousOn (fun q : ℂ × ℂ => ∏ p ∈ T, omegaCardFactorsEulerFactor (p : ℕ) q.1 q.2)
      {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1} :=
  continuousOn_finsetProd T fun p _ => continuousOn_omegaCardFactorsEulerFactor (p : ℕ)

/-- **The face embedding `(u, w) ↦ (0, u, w, ∅, ∅)`** of the bidisc into the parameter space
`ℂ × ℂ × ℂ × (Λ → ℂ) × (Π → ℂ)` with `Λ = Π = ∅` and `s = 0`. -/
def omegaCardFactorsFaceParam (q : ℂ × ℂ) :
    ℂ × ℂ × ℂ × ((∅ : Finset ℕ) → ℂ) × ((∅ : Finset ReductionData) → ℂ) :=
  (0, q.1, q.2, fun _ => 0, fun _ => 0)

/-- The face embedding is continuous. -/
theorem continuous_omegaCardFactorsFaceParam : Continuous omegaCardFactorsFaceParam := by
  unfold omegaCardFactorsFaceParam
  fun_prop

/-- **The closed bidisc is compact**, a product of two closed balls. -/
theorem isCompact_setOf_norm_le_one_prod :
    IsCompact {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1} := by
  simpa [Metric.closedBall, Prod.norm_def] using isCompact_closedBall (0 : ℂ × ℂ) 1

/-- **The face image of the closed bidisc lies in the parameter polydisc `𝒟`**: every point
`(s, u, w, 𝐳, 𝐮)` of it has `0 ≤ Re s` and all remaining coordinates of norm at most `1`. -/
theorem omegaCardFactorsFaceParam_image_subset_polydisc :
    ∀ x ∈ omegaCardFactorsFaceParam '' {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1},
      0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
        (∀ ℓ : (∅ : Finset ℕ), ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧
          ∀ K : (∅ : Finset ReductionData), ‖x.2.2.2.2 K‖ ≤ 1 := by
  rintro x ⟨q, hq, rfl⟩
  exact ⟨by simp [omegaCardFactorsFaceParam], hq.1, hq.2,
    fun ℓ => (Finset.notMem_empty _ ℓ.2).elim, fun K => (Finset.notMem_empty _ K.2).elim⟩

/-- **The Euler product is continuous on the closed bidisc.** The function
`(u, w) ↦ ∏_{p ∈ 𝒫} g_p(u, w)` is continuous on `‖u‖ ≤ 1`, `‖w‖ ≤ 1`. -/
theorem continuousOn_omegaCardFactorsEulerProduct :
    ContinuousOn (fun q : ℂ × ℂ => omegaCardFactorsEulerProduct q.1 q.2)
      {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1} := by
  have h0 := hasProdUniformlyOn_localFactor ∅ ∅
    (isCompact_setOf_norm_le_one_prod.image continuous_omegaCardFactorsFaceParam)
    omegaCardFactorsFaceParam_image_subset_polydisc
  have h2 := (h0.tendstoUniformlyOn.comp omegaCardFactorsFaceParam).mono
    (Set.subset_preimage_image omegaCardFactorsFaceParam _)
  refine (h2.continuousOn (Frequently.of_forall fun T => ?_)).congr fun q hq => ?_
  · refine (continuousOn_prod_omegaCardFactorsEulerFactor T).congr fun q hq => ?_
    simp only [Function.comp_apply, omegaCardFactorsFaceParam]
    refine Finset.prod_congr rfl fun p _ => ?_
    exact @localFactor_collapse_omegaCardFactors (p : ℕ) ⟨p.2⟩ q.1 q.2 hq.1 hq.2
      (fun _ => 0) (fun _ => 0)
  · simp only [Function.comp_apply, omegaCardFactorsFaceParam]
    exact (tprod_localFactor_omegaCardFactorsFace hq.1 hq.2 (fun _ => (0 : ℂ))
      (fun _ => (0 : ℂ))).symm

/-! ### §4. The closed bidisc is the closure of the open one -/

/-- **The closed bidisc lies in the closure of the open one.** If `‖u‖ ≤ 1` and `‖w‖ ≤ 1`, then
`(u, w)` lies in the closure of `{(u', w') | ‖u'‖ < 1 ∧ ‖w'‖ < 1}`. -/
theorem mem_closure_setOf_norm_lt_one_prod {q : ℂ × ℂ} (hq1 : ‖q.1‖ ≤ 1) (hq2 : ‖q.2‖ ≤ 1) :
    q ∈ closure {v : ℂ × ℂ | ‖v.1‖ < 1 ∧ ‖v.2‖ < 1} := by
  have := closure_ball (0 : ℂ × ℂ) one_ne_zero
  simp only [Metric.ball, Metric.closedBall, dist_zero_right, Prod.norm_def,
    max_lt_iff, max_le_iff] at this
  exact this ▸ ⟨hq1, hq2⟩

/-! ### §5. The identity on the closed bidisc -/

/-- **The bivariate generating-function identity on the closed bidisc.** For `‖u‖ ≤ 1` and
`‖w‖ ≤ 1`,

`∑_{(r, b)} π(r, b) u^r w^b = ∏_{p ∈ 𝒫} g_p(u, w)`,
`g_p(u, w) = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`,

with `π(r, b)` the joint limiting density of `(ω_Tam(E), Ω(Tam(E)))`. -/
theorem tsum_jointOmegaCardFactorsDensity_mul_pow {u w : ℂ} (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (∑' rb : ℕ × ℕ, ((jointOmegaCardFactorsDensity rb.1 rb.2 : ℝ) : ℂ) * u ^ rb.1 * w ^ rb.2)
      = omegaCardFactorsEulerProduct u w :=
  Set.EqOn.of_subset_closure
    (fun _ hv => (hasSum_jointOmegaCardFactorsDensity_mul_pow_of_lt_one hv.1 hv.2).tsum_eq)
    continuousOn_tsum_jointOmegaCardFactorsDensity_mul_pow
    continuousOn_omegaCardFactorsEulerProduct
    (fun _ hv => ⟨hv.1.le, hv.2.le⟩)
    (fun _ hv => mem_closure_setOf_norm_lt_one_prod hv.1 hv.2)
    (show ((u, w) : ℂ × ℂ) ∈ {q : ℂ × ℂ | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1} from ⟨hu, hw⟩)

end WeierstrassCurve
