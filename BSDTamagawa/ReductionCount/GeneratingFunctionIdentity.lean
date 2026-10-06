/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.ReductionCount.LimitingJointDensityExists

/-!
# The joint generating-function identity on all of `ℂ^Λ`

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every `𝐮 ∈ ℂ^Λ`, not only on the unit
polydisc, the family `(π_Λ(𝐫) 𝐮^𝐫)_{𝐫 ∈ ℤ_{≥0}^Λ}` is absolutely summable and
`∑_𝐫 π_Λ(𝐫) 𝐮^𝐫 = F_Λ(𝐮)`, where `π_Λ(𝐫)` is the limiting joint density
`jointReductionOmegaDensity` and `F_Λ` is the joint Euler product
`jointReductionOmegaEulerProduct`.

## Main results

* `WeierstrassCurve.summable_norm_jointReductionOmegaDensity_multiMonomial`: absolute summability
  of `(π_Λ(𝐫) 𝐮^𝐫)_𝐫` at every `𝐮 ∈ ℂ^Λ`.
* `WeierstrassCurve.hasSum_jointReductionOmegaDensity_multiMonomial`: the identity, as a `HasSum`
  with sum `F_Λ(𝐮)`.

## Implementation notes

The proof does not use holomorphy of `F_Λ` in several variables. The finite partial products are
polynomials with nonnegative coefficients (since `∑_{K ∈ Λ} δ_p(K) ≤ 1`), their coefficients
converge to the densities by Cauchy coefficient extraction, and the bound
`‖c_S(𝐫) 𝐮^𝐫‖ ≤ F_Λ(2M · 𝟏) · 2^{-|𝐫|}`, uniform in `S`, lets Tannery's theorem pass to the limit.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex
open BSDTamagawa.SubprobLimit

/-! ### The local masses have total at most one -/

/-- For every finite set `Λ` of local reduction data and every index `p : ℕ`,
`∑_{K ∈ Λ} δ_p(K) ≤ 1`, with `δ_p(K)` read as `stratumLocalMass K p`. -/
theorem sum_stratumLocalMass_le_one (Λ : Finset ReductionData) (p : ℕ) :
    ∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p ≤ 1 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    calc ∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p
        = ∑ K ∈ Λ, (deltaP p K).toReal := by
          rw [Finset.sum_coe_sort Λ (stratumLocalMass · p)]
          exact Finset.sum_congr rfl fun K _ => stratumLocalMass_of_prime K p
      _ = (∑ K ∈ Λ, deltaP p K).toReal :=
          (ENNReal.toReal_sum fun K _ => deltaP_ne_top p K).symm
      _ ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top
          ((ENNReal.sum_le_tsum Λ).trans_eq (tsum_deltaP p))
      _ = 1 := ENNReal.toReal_one
  · simp [stratumLocalMass_of_not_prime _ hp]

/-! ### Generic facts about real multivariate polynomials with nonnegative coefficients -/

section MvPolynomialAux

variable {σ : Type*}

/-- A finite product of real multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
private theorem coeff_prod_nonneg {ι : Type*} {s : Finset ι} (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i ∈ s, ∀ j, 0 ≤ (f i).coeff j) (j : σ →₀ ℕ) :
    0 ≤ (∏ i ∈ s, f i).coeff j := by
  classical
  refine Finset.prod_induction f (fun P => ∀ j, 0 ≤ P.coeff j)
    (fun a b ha hb j => ?_) (fun j => ?_) hf j
  · rw [MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ha _) (hb _)
  · rw [MvPolynomial.coeff_one]
    split_ifs <;> norm_num

/-- At every `u ∈ ℂ^σ`, the coefficients of a real polynomial `P`, cast to `ℂ` and multiplied by
the monomials `∏ i, u i ^ j i`, have sum `aeval u P`. -/
private theorem hasSum_ofReal_coeff_mul_prod [Fintype σ] (P : MvPolynomial σ ℝ) (u : σ → ℂ) :
    HasSum (fun j : σ →₀ ℕ => ((P.coeff j : ℝ) : ℂ) * ∏ i, u i ^ (j i))
      (MvPolynomial.aeval u P) := by
  have hzero : ∀ j ∉ P.support,
      ((P.coeff j : ℝ) : ℂ) * ∏ i, u i ^ (j i) = 0 := by
    intro j hj
    rw [MvPolynomial.notMem_support_iff.mp hj]
    simp
  have hval : ∑ j ∈ P.support, ((P.coeff j : ℝ) : ℂ) * ∏ i, u i ^ (j i)
      = MvPolynomial.aeval u P := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    exact Finset.sum_congr rfl fun d _ => by rw [Complex.coe_algebraMap]
  exact hval ▸ hasSum_sum_of_ne_finset_zero hzero

/-- If every coefficient of `P` is nonnegative and `t ≥ 0`, then each term `coeff j P · t^{|j|}` is
at most `P(t, …, t)`. -/
private theorem coeff_mul_prod_pow_le_eval [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : ∀ j, 0 ≤ P.coeff j) {t : ℝ} (ht : 0 ≤ t) (j : σ →₀ ℕ) :
    P.coeff j * ∏ i, t ^ (j i) ≤ MvPolynomial.eval (fun _ => t) P := by
  have hterm : ∀ d : σ →₀ ℕ, 0 ≤ P.coeff d * ∏ i, t ^ (d i) :=
    fun d => mul_nonneg (hP d) (Finset.prod_nonneg fun i _ => pow_nonneg ht _)
  rw [MvPolynomial.eval_eq']
  by_cases hj : j ∈ P.support
  · exact Finset.single_le_sum (fun d _ => hterm d) hj
  · rw [MvPolynomial.notMem_support_iff.mp hj, zero_mul]
    exact Finset.sum_nonneg fun d _ => hterm d

/-- Evaluating a real polynomial at real arguments and casting to `ℂ` equals evaluating it at the
casts. -/
private theorem ofReal_eval_eq_aeval [Finite σ] (P : MvPolynomial σ ℝ) (u : σ → ℝ) :
    ((MvPolynomial.eval u P : ℝ) : ℂ) = MvPolynomial.aeval (fun i => ((u i : ℝ) : ℂ)) P := by
  have := Fintype.ofFinite σ
  simp only [MvPolynomial.eval_eq', MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    Complex.coe_algebraMap, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_pow]

end MvPolynomialAux

/-! ### The local factor as a genuine polynomial -/

variable {Λ : Finset ReductionData}

/-- The affine polynomial `(1 - ∑_{K ∈ Λ} δ_p(K)) + ∑_{K ∈ Λ} δ_p(K) X_K` in `MvPolynomial ↥Λ ℝ`,
whose evaluation at `𝐮 ∈ ℂ^Λ` is `jointReductionOmegaEulerFactor Λ p 𝐮`. -/
private noncomputable def jointFactorPoly (Λ : Finset ReductionData) (p : ℕ) :
    MvPolynomial ↥Λ ℝ :=
  MvPolynomial.C (1 - ∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p)
    + ∑ K : ↥Λ, MvPolynomial.C (stratumLocalMass (K : ReductionData) p) * MvPolynomial.X K

/-- Every coefficient of `jointFactorPoly Λ p` is nonnegative. -/
private theorem jointFactorPoly_coeff_nonneg (Λ : Finset ReductionData) (p : ℕ)
    (j : ↥Λ →₀ ℕ) : 0 ≤ (jointFactorPoly Λ p).coeff j := by
  classical
  rw [jointFactorPoly, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  have hC : 0 ≤
      (MvPolynomial.C (1 - ∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p)).coeff j := by
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · linarith [sum_stratumLocalMass_le_one Λ p]
    · exact le_rfl
  have hlin : 0 ≤ (∑ K : ↥Λ,
      MvPolynomial.C (stratumLocalMass (K : ReductionData) p) * MvPolynomial.X K).coeff j := by
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_nonneg fun K _ => ?_
    rw [MvPolynomial.coeff_C_mul]
    refine mul_nonneg (stratumLocalMass_nonneg _ p) ?_
    rw [MvPolynomial.coeff_X]
    split_ifs <;> norm_num
  linarith

/-- The polynomial `jointFactorPoly Λ p` evaluates at `𝐮` to
`jointReductionOmegaEulerFactor Λ p 𝐮`. -/
private theorem aeval_jointFactorPoly (Λ : Finset ReductionData) (p : ℕ) (u : Λ → ℂ) :
    MvPolynomial.aeval u (jointFactorPoly Λ p) = jointReductionOmegaEulerFactor Λ p u := by
  rw [jointReductionOmegaEulerFactor_eq_one_add, jointFactorPoly]
  have hsplit : ∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * (u K - 1)
      = (∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * u K)
        - ∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hsplit]
  simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Complex.coe_algebraMap, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum]
  ring

/-- At the real diagonal point `t · 𝟏`, `jointFactorPoly Λ p` takes the value
`1 + (∑_{K ∈ Λ} δ_p(K))(t - 1)`. -/
private theorem eval_jointFactorPoly (Λ : Finset ReductionData) (p : ℕ) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (jointFactorPoly Λ p)
      = 1 + (∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p) * (t - 1) := by
  rw [jointFactorPoly]
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [← Finset.sum_mul]
  ring

/-- At a real diagonal point `t · 𝟏` with `t ≥ 1`, the value of `jointFactorPoly Λ p` is at least
`1`. -/
private theorem one_le_eval_jointFactorPoly (Λ : Finset ReductionData) (p : ℕ) {t : ℝ}
    (ht : 1 ≤ t) : 1 ≤ MvPolynomial.eval (fun _ => t) (jointFactorPoly Λ p) := by
  rw [eval_jointFactorPoly]
  refine le_add_of_nonneg_right (mul_nonneg ?_ (by linarith))
  exact Finset.sum_nonneg fun K _ => stratumLocalMass_nonneg _ p

/-! ### The partial products, and their coefficients `c_S(𝐫)` -/

/-- The partial product `∏_{p < n} F_{Λ,p}` as a polynomial in `MvPolynomial ↥Λ ℝ`. -/
private noncomputable def jointPartialPoly (Λ : Finset ReductionData) (n : ℕ) :
    MvPolynomial ↥Λ ℝ :=
  ∏ p ∈ Finset.range n, jointFactorPoly Λ p

/-- The coefficient `c_S(𝐫)` of `𝐮^𝐫` in the partial product over `S = {p < n}`. -/
private noncomputable def jointPartialCoeff (Λ : Finset ReductionData) (n : ℕ)
    (j : ↥Λ →₀ ℕ) : ℝ :=
  (jointPartialPoly Λ n).coeff j

/-- The partial product `P_S(𝐮) = ∏_{p < n} F_{Λ,p}(𝐮)` of the local factors. -/
private noncomputable def jointPartialProd (Λ : Finset ReductionData) (n : ℕ) (u : Λ → ℂ) : ℂ :=
  ∏ p ∈ Finset.range n, jointReductionOmegaEulerFactor Λ p u

/-- The coefficients `c_S(𝐫)` are nonnegative. -/
private theorem jointPartialCoeff_nonneg (Λ : Finset ReductionData) (n : ℕ) (j : ↥Λ →₀ ℕ) :
    0 ≤ jointPartialCoeff Λ n j :=
  coeff_prod_nonneg _ (fun p _ => jointFactorPoly_coeff_nonneg Λ p) j

/-- The polynomial partial product evaluates to the analytic one. -/
private theorem aeval_jointPartialPoly (Λ : Finset ReductionData) (n : ℕ) (u : Λ → ℂ) :
    MvPolynomial.aeval u (jointPartialPoly Λ n) = jointPartialProd Λ n u := by
  rw [jointPartialPoly, jointPartialProd, map_prod]
  exact Finset.prod_congr rfl fun p _ => aeval_jointFactorPoly Λ p u

/-- The real diagonal evaluation of the polynomial partial product is the product of the local
evaluations. -/
private theorem eval_jointPartialPoly (Λ : Finset ReductionData) (n : ℕ) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (jointPartialPoly Λ n)
      = ∏ p ∈ Finset.range n, MvPolynomial.eval (fun _ => t) (jointFactorPoly Λ p) := by
  rw [jointPartialPoly, map_prod]

/-- For `t ≥ 1` the real diagonal values `P_S(t · 𝟏)` are monotone in `n`, where `S = {p < n}`. -/
private theorem monotone_eval_jointPartialPoly (Λ : Finset ReductionData) {t : ℝ} (ht : 1 ≤ t) :
    Monotone fun n => MvPolynomial.eval (fun _ => t) (jointPartialPoly Λ n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [eval_jointPartialPoly, eval_jointPartialPoly, Finset.prod_range_succ]
  refine le_mul_of_one_le_right ?_ (one_le_eval_jointFactorPoly Λ n ht)
  exact Finset.prod_nonneg fun p _ =>
    le_trans zero_le_one (one_le_eval_jointFactorPoly Λ p ht)

/-- The partial product has the polydisc expansion `P_S(𝐮) = ∑_𝐫 c_S(𝐫) 𝐮^𝐫`. -/
private theorem hasPolydiscExpansion_jointPartialCoeff (Λ : Finset ReductionData) (n : ℕ) :
    HasPolydiscExpansion (fun j : ↥Λ →₀ ℕ => ((jointPartialCoeff Λ n j : ℝ) : ℂ))
      (jointPartialProd Λ n) := by
  intro z _
  simpa only [smul_eq_mul, jointPartialCoeff, ← aeval_jointPartialPoly Λ n z] using
    hasSum_ofReal_coeff_mul_prod (jointPartialPoly Λ n) z

/-! ### Convergence of the partial products along the exhaustion `S = {p < n}` -/

/-- The partial products `P_S(𝐮)`, `S = {p < n}`, converge to `F_Λ(𝐮)` as `n → ∞`. -/
private theorem tendsto_jointPartialProd (hΛ : Admissible Λ) (u : Λ → ℂ) :
    Tendsto (fun n => jointPartialProd Λ n u) atTop
      (𝓝 (jointReductionOmegaEulerProduct Λ u)) := by
  have h : HasProd (fun p : ℕ => jointReductionOmegaEulerFactor Λ p u)
      (jointReductionOmegaEulerProduct Λ u) :=
    (multipliable_jointReductionOmegaEulerFactor hΛ u).hasProd
  simpa only [jointPartialProd] using h.tendsto_prod_nat

/-- A polytorus `{𝐳 : ∀ K, ‖z_K‖ = ρ_K}` in `ℂ^Λ` is compact. -/
private theorem isCompact_polytorus (ρ : ↥Λ → ℝ) :
    IsCompact {z : ↥Λ → ℂ | ∀ i, ‖z i‖ = ρ i} := by
  have hset : {z : ↥Λ → ℂ | ∀ i, ‖z i‖ = ρ i}
      = Set.univ.pi fun i => Metric.sphere (0 : ℂ) (ρ i) := by
    ext z
    simp
  rw [hset]
  exact isCompact_univ_pi fun i => isCompact_sphere 0 (ρ i)

/-- The partial products converge to `F_Λ` uniformly on every polytorus with radii in `(0, 1)`. -/
private theorem tendstoUniformlyOnPolytori_jointPartialProd (hΛ : Admissible Λ) :
    TendstoUniformlyOnPolytori (jointPartialProd Λ) (jointReductionOmegaEulerProduct Λ) := by
  intro ρ _ _ U hU
  exact tendsto_finset_range.eventually
    (tendstoUniformlyOn_finsetProd_jointReductionOmegaEulerFactor hΛ (isCompact_polytorus ρ) U hU)

/-- For each multi-index `𝐫`, the coefficients `c_S(𝐫)` converge to `π_Λ(𝐫)` as `S = {p < n}`
grows. -/
private theorem tendsto_jointPartialCoeff (hΛ : Admissible Λ) (j : ↥Λ →₀ ℕ) :
    Tendsto (fun n => ((jointPartialCoeff Λ n j : ℝ) : ℂ)) atTop
      (𝓝 ((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ)) := by
  classical
  exact cauchy_coeff_convergence_multivar (jointPartialProd Λ)
    (fun n j => ((jointPartialCoeff Λ n j : ℝ) : ℂ)) (jointReductionOmegaEulerProduct Λ)
    (fun j => ((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ))
    (hasPolydiscExpansion_jointPartialCoeff Λ)
    (hasPolydiscExpansion_jointReductionOmegaDensity hΛ)
    (tendstoUniformlyOnPolytori_jointPartialProd hΛ) j

/-! ### The `S`-free dominating bound -/

/-- The real part of `F_Λ` at the real diagonal point `t · 𝟏`. -/
private noncomputable def jointRadiusBound (Λ : Finset ReductionData) (t : ℝ) : ℝ :=
  (jointReductionOmegaEulerProduct Λ fun _ => (t : ℂ)).re

/-- For `t ≥ 1` and every `n`, `P_S(t · 𝟏) ≤ F_Λ(t · 𝟏)` where `S = {p < n}`. -/
private theorem eval_jointPartialPoly_le_jointRadiusBound (hΛ : Admissible Λ) {t : ℝ}
    (ht : 1 ≤ t) (n : ℕ) :
    MvPolynomial.eval (fun _ => t) (jointPartialPoly Λ n) ≤ jointRadiusBound Λ t := by
  refine (monotone_eval_jointPartialPoly Λ ht).ge_of_tendsto ?_ n
  have hC : Tendsto (fun n => ((MvPolynomial.eval (fun _ => t) (jointPartialPoly Λ n) : ℝ) : ℂ))
      atTop (𝓝 (jointReductionOmegaEulerProduct Λ fun _ => (t : ℂ))) := by
    simpa only [ofReal_eval_eq_aeval, aeval_jointPartialPoly] using
      tendsto_jointPartialProd hΛ fun _ => (t : ℂ)
  have hre := (Complex.continuous_re.tendsto
    (jointReductionOmegaEulerProduct Λ fun _ => (t : ℂ))).comp hC
  simpa only [Function.comp_def, Complex.ofReal_re, jointRadiusBound] using hre

/-- Every `𝐮 ∈ ℂ^Λ` admits `M ≥ 1` with `‖u_K‖ ≤ M` for all `K`. -/
private theorem exists_one_le_forall_norm_le (u : Λ → ℂ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, ‖u i‖ ≤ M := by
  refine ⟨1 + ∑ i : ↥Λ, ‖u i‖, ?_, fun i => ?_⟩
  · have h : 0 ≤ ∑ i : ↥Λ, ‖u i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg (u i)
    linarith
  · have h : ‖u i‖ ≤ ∑ i : ↥Λ, ‖u i‖ :=
      Finset.single_le_sum (f := fun i : ↥Λ => ‖u i‖) (fun i _ => norm_nonneg (u i))
        (Finset.mem_univ i)
    linarith

/-- If `M ≥ 1` and `‖u_K‖ ≤ M` for all `K`, then for every `n` and `𝐫`,
`‖c_S(𝐫) 𝐮^𝐫‖ ≤ F_Λ(2M · 𝟏) · 2^{-|𝐫|}` where `S = {p < n}`. -/
private theorem norm_jointPartialCoeff_mul_prod_le (hΛ : Admissible Λ) {u : Λ → ℂ} {M : ℝ}
    (hM : 1 ≤ M) (hMu : ∀ i, ‖u i‖ ≤ M) (n : ℕ) (j : ↥Λ →₀ ℕ) :
    ‖((jointPartialCoeff Λ n j : ℝ) : ℂ) * ∏ i, u i ^ (j i)‖
      ≤ jointRadiusBound Λ (2 * M) * ∏ i, (1 / 2 : ℝ) ^ (j i) := by
  have ht : (1 : ℝ) ≤ 2 * M := by linarith
  have hhalf : 0 ≤ ∏ i : ↥Λ, (1 / 2 : ℝ) ^ (j i) :=
    Finset.prod_nonneg fun i _ => by positivity
  have hnorm : ‖((jointPartialCoeff Λ n j : ℝ) : ℂ) * ∏ i, u i ^ (j i)‖
      = jointPartialCoeff Λ n j * ∏ i, ‖u i‖ ^ (j i) := by
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (jointPartialCoeff_nonneg Λ n j), norm_prod]
    simp only [norm_pow]
  have hsplit : ∏ i : ↥Λ, M ^ (j i)
      = (∏ i : ↥Λ, (2 * M) ^ (j i)) * ∏ i : ↥Λ, (1 / 2 : ℝ) ^ (j i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_pow]
    congr 1
    ring
  rw [hnorm]
  calc jointPartialCoeff Λ n j * ∏ i, ‖u i‖ ^ (j i)
      ≤ jointPartialCoeff Λ n j * ∏ i : ↥Λ, M ^ (j i) :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (norm_nonneg _) _)
            (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hMu i) _))
          (jointPartialCoeff_nonneg Λ n j)
    _ = (jointPartialCoeff Λ n j * ∏ i : ↥Λ, (2 * M) ^ (j i))
          * ∏ i : ↥Λ, (1 / 2 : ℝ) ^ (j i) := by rw [hsplit, mul_assoc]
    _ ≤ jointRadiusBound Λ (2 * M) * ∏ i : ↥Λ, (1 / 2 : ℝ) ^ (j i) :=
        mul_le_mul_of_nonneg_right
          ((coeff_mul_prod_pow_le_eval (jointPartialCoeff_nonneg Λ n) (by linarith) j).trans
            (eval_jointPartialPoly_le_jointRadiusBound hΛ ht n))
          hhalf

/-! ### The identity and absolute convergence, on `Finsupp` multi-indices -/

/-- For every `𝐮 ∈ ℂ^Λ`, the family `(π_Λ(𝐫) 𝐮^𝐫)_𝐫` indexed by `↥Λ →₀ ℕ` is absolutely summable
with sum `F_Λ(𝐮)`. -/
private theorem summable_norm_and_hasSum_density_finsupp (hΛ : Admissible Λ) (u : Λ → ℂ) :
    (Summable fun j : ↥Λ →₀ ℕ =>
        ‖((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ) * ∏ i, u i ^ (j i)‖) ∧
      HasSum (fun j : ↥Λ →₀ ℕ =>
        ((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ) * ∏ i, u i ^ (j i))
          (jointReductionOmegaEulerProduct Λ u) := by
  obtain ⟨M, hM, hMu⟩ := exists_one_le_forall_norm_le u
  have hbound : Summable fun j : ↥Λ →₀ ℕ =>
      jointRadiusBound Λ (2 * M) * ∏ i, (1 / 2 : ℝ) ^ (j i) :=
    (summable_prod_pow_finsupp (fun _ : ↥Λ => (1 / 2 : ℝ)) (fun _ => by norm_num)
      fun _ => by norm_num).mul_left _
  have hpt : ∀ j : ↥Λ →₀ ℕ,
      Tendsto (fun n => ((jointPartialCoeff Λ n j : ℝ) : ℂ) * ∏ i, u i ^ (j i)) atTop
        (𝓝 (((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ) * ∏ i, u i ^ (j i))) :=
    fun j => (tendsto_jointPartialCoeff hΛ j).mul_const _
  have hfb : ∀ n : ℕ, ∀ j : ↥Λ →₀ ℕ,
      ‖((jointPartialCoeff Λ n j : ℝ) : ℂ) * ∏ i, u i ^ (j i)‖
        ≤ jointRadiusBound Λ (2 * M) * ∏ i, (1 / 2 : ℝ) ^ (j i) :=
    fun n j => norm_jointPartialCoeff_mul_prod_le hΛ hM hMu n j
  have heq : ∀ n : ℕ, (∑' j : ↥Λ →₀ ℕ,
      ((jointPartialCoeff Λ n j : ℝ) : ℂ) * ∏ i, u i ^ (j i)) = jointPartialProd Λ n u :=
    fun n => (hasSum_ofReal_coeff_mul_prod (jointPartialPoly Λ n) u).tsum_eq.trans
      (aeval_jointPartialPoly Λ n u)
  have hlim : (∑' j : ↥Λ →₀ ℕ,
      ((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ) * ∏ i, u i ^ (j i))
        = jointReductionOmegaEulerProduct Λ u := by
    have htan := tendsto_tsum_of_dominated_convergence hbound hpt
      (Filter.Eventually.of_forall hfb)
    exact tendsto_nhds_unique (htan.congr heq) (tendsto_jointPartialProd hΛ u)
  have hgb : ∀ j : ↥Λ →₀ ℕ,
      ‖((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ) * ∏ i, u i ^ (j i)‖
        ≤ jointRadiusBound Λ (2 * M) * ∏ i, (1 / 2 : ℝ) ^ (j i) := fun j =>
    le_of_tendsto (hpt j).norm (Filter.Eventually.of_forall (hfb · j))
  have hns : Summable fun j : ↥Λ →₀ ℕ =>
      ‖((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ) * ∏ i, u i ^ (j i)‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hgb hbound
  exact ⟨hns, hlim ▸ hns.of_norm.hasSum⟩

/-! ### The identity on all of `ℂ^Λ` -/

/-- For every `𝐮 ∈ ℂ^Λ` the family `(π_Λ(𝐫) 𝐮^𝐫)_{𝐫 ∈ ℤ_{≥0}^Λ}` is absolutely summable, where
`π_Λ(𝐫)` is `jointReductionOmegaDensity Λ 𝐫` and `𝐮^𝐫` is `multiMonomial 𝐫 𝐮`. -/
@[bsd_tamagawa "T040o"]
theorem summable_norm_jointReductionOmegaDensity_multiMonomial (hΛ : Admissible Λ) (u : Λ → ℂ) :
    Summable fun r : Λ → ℕ =>
      ‖((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u‖ :=
  (Finsupp.equivFunOnFinite (α := ↥Λ) (M := ℕ)).summable_iff
      (f := fun r : ↥Λ → ℕ => ‖((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u‖)
    |>.mp (summable_norm_and_hasSum_density_finsupp hΛ u).left

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every `𝐮 ∈ ℂ^Λ`,
`∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫) 𝐮^𝐫 = F_Λ(𝐮)`, where `π_Λ(𝐫)` is `jointReductionOmegaDensity Λ 𝐫`, `𝐮^𝐫`
is `multiMonomial 𝐫 𝐮` and `F_Λ` is the joint Euler product `jointReductionOmegaEulerProduct Λ`. -/
@[bsd_tamagawa "T040o"]
theorem hasSum_jointReductionOmegaDensity_multiMonomial (hΛ : Admissible Λ) (u : Λ → ℂ) :
    HasSum (fun r : Λ → ℕ => ((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u)
      (jointReductionOmegaEulerProduct Λ u) :=
  (Finsupp.equivFunOnFinite (α := ↥Λ) (M := ℕ)).hasSum_iff
      (f := fun r : ↥Λ → ℕ => ((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u)
    |>.mp (summable_norm_and_hasSum_density_finsupp hΛ u).right

end WeierstrassCurve
