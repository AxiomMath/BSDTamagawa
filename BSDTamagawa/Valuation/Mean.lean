/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.MeanConditional
public import BSDTamagawa.NumberTheory.SmallPrimeTailDecay
public import BSDTamagawa.NumberTheory.TateTailLawUnconditional
public import BSDTamagawa.Analysis.LogDerivProduct
public import BSDTamagawa.Analysis.PGFSecondDeriv

/-!
# The mean of `v_ℓ(Tam(E))`

For a fixed prime `ℓ`, let `P = P_{{ℓ}}` be the limiting law of the `ℓ`-adic valuation
`v_ℓ(Tam(E))` of the Tamagawa product of short Weierstrass curves ordered by height. Then

`𝔼_P[v_ℓ(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) v_ℓ(t) < ∞`,

where `δ_p(t)` is the local density of Tamagawa number `t` at `p`. The mean is the left derivative
at `1` of the generating function of `P`, which is the Euler product
`∏_p ∑_t δ_p(t) w^{v_ℓ(t)}`; the local densities decay geometrically at every prime, and
`∑_t δ_p(t) v_ℓ(t) ≤ 37/p²` for `p ≥ 5`.

## Main results

* `BSDTamagawa.ValuationMeanUnconditional.massFamily_δ`: the local densities `(δ_p(t))_t` form a
  `MassFamily` at every prime.
* `BSDTamagawa.ValuationMeanUnconditional.prodHyp_valExp'`: the Euler factors
  `∑_t δ_p(t) w^{v_ℓ(t)}` satisfy `LogDerivProduct.ProdHyp`.
* `WeierstrassCurve.summable_tsum_δ_mul_factorization`: the double series
  `∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) v_ℓ(t)` converges.
* `WeierstrassCurve.integral_coord_tamagawaValuationMeasure_val`: `𝔼_P[v_ℓ(Tam(E))]` equals that
  double series.
* `WeierstrassCurve.valuation_mean`: the two together.
-/

@[expose] public section

namespace BSDTamagawa.ValuationMeanUnconditional

open Set MeasureTheory WeierstrassCurve BSDTamagawa.ValuationMean

open scoped ENNReal

/-! ### The mass family -/

/-- At every prime `p`, the local densities `(δ_p(t))_t` form a `MassFamily` for every exponent
function `k` with `k(t) ≤ t + 1` and `2^{k(t)} ≤ t + 1`. -/
theorem massFamily_δ {p : ℕ} [Fact p.Prime] {k : ℕ → ℕ}
    (hk1 : ∀ t, (k t : ℝ) ≤ (t : ℝ) + 1) (hk2 : ∀ t, (2 : ℝ) ^ k t ≤ (t : ℝ) + 1) :
    MassFamily (fun t : ℕ => (δ p t).toReal) k where
  nonneg _ := ENNReal.toReal_nonneg
  hasSum_one := hasSum_toReal_δ p
  exp_le := hk1
  two_pow_exp_le := hk2
  summable_sq := summable_δ_toReal_mul_add_one_sq

/-! ### The hypotheses of the logarithmic-derivative product theorem -/

/-- For an exponent function `k` with `k(t) ≤ t + 1`, `2^{k(t)} ≤ t + 1` and
`∑_t δ_q(t) k(t) ≤ 37/q²` at every prime `q ≥ 5`, the Euler factors `h_p(w) = ∑_t δ_p(t) w^{k(t)}`
with moments `A_p` satisfy `LogDerivProduct.ProdHyp`. -/
theorem prodHyp_eulerFactor' {k : ℕ → ℕ}
    (hk1 : ∀ t, (k t : ℝ) ≤ (t : ℝ) + 1) (hk2 : ∀ t, (2 : ℝ) ^ k t ≤ (t : ℝ) + 1)
    (hmom : ∀ (q : ℕ) [Fact q.Prime], 5 ≤ q →
      (∑' t : ℕ, δ q t * (k t : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2) :
    LogDerivProduct.ProdHyp (eulerFactor k) (eulerMoment k) (eulerSup k) (eulerEta k) where
  normalisation p := by
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      rw [eulerFactor_of_prime]
      exact localFactor_one (massFamily_δ hk1 hk2)
    · rw [eulerFactor_of_not_prime hp]
  diff p w hw := by
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      rw [eulerFactor_of_prime]
      exact (hasDerivAt_localFactor (massFamily_δ hk1 hk2)
        (mem_Ioo_of_mem_unitInterval hw)).differentiableAt
    · rw [eulerFactor_of_not_prime hp]
      exact differentiableAt_const 1
  bound_deriv p w hw := by
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      have HM := massFamily_δ (p := p) hk1 hk2
      rw [eulerFactor_of_prime, (hasDerivAt_localFactor HM
        (mem_Ioo_of_mem_unitInterval hw)).deriv, eulerMoment_of_prime]
      exact abs_localDeriv_le HM hw
    · rw [eulerFactor_of_not_prime hp, eulerMoment_of_not_prime hp]
      simp
  A_nonneg := eulerMoment_nonneg k
  summable_A := summable_eulerMoment hmom
  A_sup_nonneg := by linarith [two_le_eulerSup k]
  A_sup_bound := eulerMoment_le_eulerSup hmom
  eta_pos := eulerEta_pos k
  eta_le_one := by linarith [eulerEta_le_quarter k]
  domain_const := by
    rw [eulerEta, mul_inv_cancel₀ (by linarith [two_le_eulerSup k] : 2 * eulerSup k ≠ 0)]

/-- At `w = 1` the derivative of the Euler factor is the moment `A_p`. -/
theorem deriv_eulerFactor_one' {k : ℕ → ℕ}
    (hk1 : ∀ t, (k t : ℝ) ≤ (t : ℝ) + 1) (hk2 : ∀ t, (2 : ℝ) ^ k t ≤ (t : ℝ) + 1) (p : ℕ) :
    deriv (eulerFactor k p) 1 = eulerMoment k p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have HM := massFamily_δ (p := p) hk1 hk2
    rw [eulerFactor_of_prime, (hasDerivAt_localFactor HM
      (mem_Ioo_of_mem_unitInterval ⟨zero_le_one, le_rfl⟩)).deriv, localDeriv_one,
      eulerMoment_of_prime]
  · rw [eulerFactor_of_not_prime hp, eulerMoment_of_not_prime hp, deriv_const]

/-- `∑_p h_p'(1) = ∑_p A_p`. -/
theorem tsum_deriv_eulerFactor' {k : ℕ → ℕ}
    (hk1 : ∀ t, (k t : ℝ) ≤ (t : ℝ) + 1) (hk2 : ∀ t, (2 : ℝ) ^ k t ≤ (t : ℝ) + 1) :
    (∑' p : ℕ, deriv (eulerFactor k p) 1) = ∑' p : ℕ, eulerMoment k p :=
  tsum_congr (deriv_eulerFactor_one' hk1 hk2)

/-! ### The moment bound at `q ≥ 5` -/

/-- `∑_t δ_q(t) v_ℓ(t) ≤ 37/q²` at every prime `q ≥ 5`. -/
theorem tsum_δ_mul_factorization_le (ℓ : ℕ) (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) :
    (∑' t : ℕ, δ q t * ((t.factorization) ℓ : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2 :=
  tsum_δ_mul_factorization_le_of_tailLaw hq (hasTailGeometricLaw_of_five_le hq) ℓ

/-- `∑_t δ_q(t) Ω(t) ≤ 37/q²` at every prime `q ≥ 5`. -/
theorem tsum_δ_mul_cardFactors_le (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) :
    (∑' t : ℕ, δ q t * (ArithmeticFunction.cardFactors t : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2 :=
  tsum_δ_mul_cardFactors_le_of_tailLaw hq (hasTailGeometricLaw_of_five_le hq)

/-! ### The valuation exponent -/

/-- The Euler factors `h_p(w) = ∑_t δ_p(t) w^{v_ℓ(t)}` satisfy `LogDerivProduct.ProdHyp`. -/
theorem prodHyp_valExp' (ℓ : ℕ) :
    LogDerivProduct.ProdHyp (eulerFactor (valExp ℓ)) (eulerMoment (valExp ℓ)) (eulerSup (valExp ℓ))
      (eulerEta (valExp ℓ)) :=
  prodHyp_eulerFactor' (valExp_cast_le ℓ) (two_pow_valExp_cast_le ℓ)
    fun q _ hq => tsum_δ_mul_factorization_le ℓ q hq

/-- On the window `[1 - η, 1]`, the real product `∏_p h_p(w)` is the scalar Euler product at
`Π = {ℓ}`, `s = 0`, `w = 1` with the constant vector `𝐳 = w`. -/
theorem ofReal_prodG_valExp' {ℓ : ℕ} (hℓ : ℓ.Prime) {w : ℝ}
    (hw : w ∈ Icc (1 - eulerEta (valExp ℓ)) 1) :
    ((LogDerivProduct.prodG (eulerFactor (valExp ℓ)) w : ℝ) : ℂ)
      = ∏' p : ℕ, scalarLocalFactor {ℓ} p 0 1 (fun _ => (w : ℂ)) := by
  have hmap := (LogDerivProduct.hasProd_prodG (prodHyp_valExp' ℓ) hw).map Complex.ofRealHom
    Complex.continuous_ofReal
  refine ((hmap.congr_fun fun p => ?_).tprod_eq).symm
  simpa using
    (ofReal_eulerFactor_eq_scalarLocalFactor hℓ p (abs_le_one_of_mem_window hw)).symm

/-- On the window `[1 - η, 1]`, the generating function `PGFMean.pgf Q_{{ℓ}}` equals the real
product `LogDerivProduct.prodG`. -/
theorem pgf_eq_prodG_valExp' {ℓ : ℕ} (hℓ : ℓ.Prime) {w : ℝ}
    (hw : w ∈ Icc (1 - eulerEta (valExp ℓ)) 1) :
    PGFMean.pgf (valuationDensity ℓ) w = LogDerivProduct.prodG (eulerFactor (valExp ℓ)) w :=
  Complex.ofReal_inj.mp
    ((ofReal_pgf_valuationDensity hℓ (abs_le_one_of_mem_window hw)).trans
      (ofReal_prodG_valExp' hℓ hw).symm)

/-- The generating function `J_ℓ` of `Q_{{ℓ}}` has left derivative
`J_ℓ'(1) = ∑_p ∑_t δ_p(t) v_ℓ(t)` at `1`. -/
theorem hasDerivWithinAt_pgf_valuationDensity' {ℓ : ℕ} (hℓ : ℓ.Prime) :
    HasDerivWithinAt (PGFMean.pgf (valuationDensity ℓ))
      (∑' p : ℕ, eulerMoment (valExp ℓ) p) (Iio 1) 1 := by
  have hη := eulerEta_pos (valExp ℓ)
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG (prodHyp_valExp' ℓ)
  rw [tsum_deriv_eulerFactor' (valExp_cast_le ℓ) (two_pow_valExp_cast_le ℓ)] at hprod
  refine hprod.congr_of_eventuallyEq ?_ (pgf_eq_prodG_valExp' hℓ ⟨by linarith, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT (show 1 - eulerEta (valExp ℓ) < 1 by linarith)] with x hx
  exact pgf_eq_prodG_valExp' hℓ ⟨hx.1.le, hx.2.le⟩

/-- `v_ℓ(Tam(E))` is `P_{{ℓ}}`-integrable. -/
theorem integrable_coord_tamagawaValuationMeasure' {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Integrable (fun j : ↥({ℓ} : Finset ℕ) → ℕ => ((j (singletonIdx ℓ) : ℕ) : ℝ))
      (tamagawaValuationMeasure {ℓ}) := by
  have hint : Integrable (fun n : ℕ => (n : ℝ)) (valuationPMF ℓ hℓ).toMeasure :=
    BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt (valuationPMF ℓ hℓ)
      (by rw [toReal_valuationPMF hℓ]; exact hasDerivWithinAt_pgf_valuationDensity' hℓ)
  rw [← map_tamagawaValuationMeasure hℓ] at hint
  exact (integrable_map_equiv (singletonMeasurableEquiv ℓ) _).mp hint

/-- `𝔼_{P_{{ℓ}}}[v_ℓ(Tam(E))] = ∑_p A_p`. -/
theorem integral_coord_tamagawaValuationMeasure' {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∫ j, ((j (singletonIdx ℓ) : ℕ) : ℝ) ∂(tamagawaValuationMeasure {ℓ})
      = ∑' p : ℕ, eulerMoment (valExp ℓ) p := by
  have hintP : Integrable (fun n : ℕ => (n : ℝ)) (valuationPMF ℓ hℓ).toMeasure := by
    rw [← map_tamagawaValuationMeasure hℓ]
    exact (integrable_map_equiv (singletonMeasurableEquiv ℓ) _).mpr
      (integrable_coord_tamagawaValuationMeasure' hℓ)
  have htransport : ∫ j, ((j (singletonIdx ℓ) : ℕ) : ℝ) ∂(tamagawaValuationMeasure {ℓ})
      = ∫ n, (n : ℝ) ∂((valuationPMF ℓ hℓ).toMeasure) := by
    rw [← map_tamagawaValuationMeasure hℓ, integral_map_equiv]
    rfl
  rw [htransport, ← PGFVariance.pgfDeriv_eq_mean (valuationPMF ℓ hℓ) hintP, PGFVariance.pgfDeriv]
  simp_rw [toReal_valuationPMF_apply hℓ]
  exact (PGFMean.main_theorem (valuationDensity ℓ) (valuationDensity_nonneg hℓ)
    (hasSum_valuationDensity hℓ) _ (hasDerivWithinAt_pgf_valuationDensity' hℓ)).2

end BSDTamagawa.ValuationMeanUnconditional

namespace WeierstrassCurve

open BSDTamagawa.ValuationMean BSDTamagawa.ValuationMeanUnconditional MeasureTheory

/-- The double series `∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) v_ℓ(t)` converges. -/
theorem summable_tsum_δ_mul_factorization (ℓ : ℕ) :
    Summable fun p : ℕ => if h : p.Prime then
      ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0 :=
  summable_eulerMoment (k := valExp ℓ) fun q _ hq => tsum_δ_mul_factorization_le ℓ q hq

/-- For a prime `ℓ`, with `P = P_{{ℓ}}` the limiting joint valuation law at `Π = {ℓ}`,

`𝔼_P[v_ℓ(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) v_ℓ(t)`. -/
theorem integral_coord_tamagawaValuationMeasure_val {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∫ j, ((j (singletonIdx ℓ) : ℕ) : ℝ) ∂(tamagawaValuationMeasure {ℓ})
      = ∑' p : ℕ, if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0 :=
  BSDTamagawa.ValuationMeanUnconditional.integral_coord_tamagawaValuationMeasure' hℓ

/-- For any fixed prime `ℓ`, with `P` the probability measure on `ℤ_{≥0}` with
`P({j}) = Q_{{ℓ}}(j)`,

`𝔼_P[v_ℓ(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) v_ℓ(t) < ∞`. -/
@[bsd_tamagawa "T043"]
theorem valuation_mean {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (Summable fun p : ℕ => if h : p.Prime then
        ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0) ∧
      ∫ j, ((j (singletonIdx ℓ) : ℕ) : ℝ) ∂(tamagawaValuationMeasure {ℓ})
        = ∑' p : ℕ, if h : p.Prime then
            ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0 :=
  ⟨summable_tsum_δ_mul_factorization ℓ, integral_coord_tamagawaValuationMeasure_val hℓ⟩

end WeierstrassCurve
