/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.FormulaConditional
public import BSDTamagawa.NumberTheory.SmallPrimeTailDecay
public import BSDTamagawa.NumberTheory.TateTailLawUnconditional

/-!
# The covariance formula for Tamagawa valuations

For distinct primes `ℓ ≠ ℓ'`, the sum `∑_p C_p(ℓ, ℓ')` of the local covariances converges
absolutely and

  `Cov(v_ℓ(Tam(E)), v_{ℓ'}(Tam(E))) = ∑_{p ∈ 𝒫} C_p(ℓ, ℓ')`

in the limiting joint valuation law `P_{{ℓ,ℓ'}}`. The statements here carry no tail-law hypothesis:
the moments `∑_t δ_p(t) (t + 1)^k` are finite at every prime, and the bound `S_p(e) ≤ 150/p²` is
needed only for `p ≥ 5`.

## Main results

* `WeierstrassCurve.summable_abs_localCov`: `∑_p |C_p(ℓ, ℓ')| < ∞`.
* `WeierstrassCurve.variance_valWeightSum'`: `Var_P(∑_i t_i 𝐣_i) = ∑_p (S_p(E_t) - m_p(E_t)²)`.
* `WeierstrassCurve.covariance_tamagawaValuation`: the covariance formula against the joint
  valuation law `P_{{ℓ,ℓ'}}`.
* `WeierstrassCurve.covariance_tamagawaValuation_prod`: the same on the index space `ℤ_{≥0}²`.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open BSDTamagawa BSDTamagawa.CovarianceFormula

/-! ### §1. The factor hypotheses at `δ_p` -/

section Moments

variable {p : ℕ} [Fact p.Prime]

/-- **The `FactorHyp` package holds at `δ_p` for every prime `p`**, for an exponent function `e`
with `2^{e(t)} ≤ max 1 t`. -/
theorem factorHyp_δ {e : ℕ → ℕ} (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    FactorHyp (scalarLocalMassReal p) e where
  nonneg := scalarLocalMassReal_nonneg
  total := hasSum_scalarLocalMassReal
  growth := he
  moment k := summable_δ_toReal_mul_add_one_pow k

/-- **The marginal family `valuationTerm p r` is summable** for every prime `r`. -/
theorem summable_valuationTerm' {r : ℕ} (hr : r.Prime) : Summable (valuationTerm p r) :=
  summable_valuationTerm p r
    (tsum_δ_mul_natCast_ne_top_of_summable
      (factorHyp_δ (p := p) (e := fun t => padicValNat r t)
        (two_pow_padicValNat_le hr)).summable_moment1Term)

/-- **The cross family `crossValuationTerm p ℓ ℓ'` is summable** for distinct primes `ℓ ≠ ℓ'`. -/
theorem summable_crossValuationTerm' {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    Summable (crossValuationTerm p ℓ ℓ') := by
  have hfac := factorHyp_δ (p := p) (e := fun t => padicValNat ℓ t + padicValNat ℓ' t)
    (two_pow_padicValNat_add_le hℓ hℓ' hne)
  have hb : ∀ t : ℕ, ‖crossValuationTerm p ℓ ℓ' t‖
      ≤ scalarLocalMassReal p t * ((padicValNat ℓ t + padicValNat ℓ' t : ℕ) : ℝ) ^ 2 := fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (crossValuationTerm_nonneg p ℓ ℓ' t), crossValuationTerm,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (natCast_mul_le_natCast_add_sq _ _) ENNReal.toReal_nonneg
  exact summable_crossValuationTerm p ℓ ℓ'
    (tsum_δ_mul_natCast_mul_natCast_ne_top_of_summable
      (Summable.of_norm_bounded hfac.summable_moment2Term hb))

/-- `m_p(v_ℓ + v_{ℓ'}) = μ_{p,ℓ} + μ_{p,ℓ'}`. -/
theorem expMoment1_add' {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) :
    expMoment1 (scalarLocalMassReal p) (fun t => padicValNat ℓ t + padicValNat ℓ' t)
      = valuationMoment p ℓ + valuationMoment p ℓ' := by
  have h1 := (factorHyp_δ (p := p) (e := fun t => padicValNat ℓ t)
    (two_pow_padicValNat_le hℓ)).summable_moment1Term
  have h2 := (factorHyp_δ (p := p) (e := fun t => padicValNat ℓ' t)
    (two_pow_padicValNat_le hℓ')).summable_moment1Term
  rw [← expMoment1_padicValNat (p := p) ℓ, ← expMoment1_padicValNat (p := p) ℓ', expMoment1,
    expMoment1, expMoment1, ← h1.tsum_add h2]
  exact tsum_congr fun t => by push_cast; ring

/-- **The polarisation of the second moment.**
`S_p(v_ℓ + v_{ℓ'}) = S_p(v_ℓ) + 2 (cross moment) + S_p(v_{ℓ'})`. -/
theorem expMoment2_add' {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    expMoment2 (scalarLocalMassReal p) (fun t => padicValNat ℓ t + padicValNat ℓ' t)
      = expMoment2 (scalarLocalMassReal p) (fun t => padicValNat ℓ t)
        + 2 * crossValuationMoment p ℓ ℓ'
        + expMoment2 (scalarLocalMassReal p) (fun t => padicValNat ℓ' t) := by
  have h1 := (factorHyp_δ (p := p) (e := fun t => padicValNat ℓ t)
    (two_pow_padicValNat_le hℓ)).summable_moment2Term
  have h2 := (factorHyp_δ (p := p) (e := fun t => padicValNat ℓ' t)
    (two_pow_padicValNat_le hℓ')).summable_moment2Term
  have hx := summable_crossValuationTerm' (p := p) hℓ hℓ' hne
  have hx2 : Summable fun t : ℕ => 2 * crossValuationTerm p ℓ ℓ' t := hx.mul_left 2
  rw [crossValuationMoment, ← hx.tsum_mul_left 2, expMoment2, expMoment2, expMoment2,
    ← h1.tsum_add hx2, ← (h1.add hx2).tsum_add h2]
  refine tsum_congr fun t => ?_
  rw [crossValuationTerm, scalarLocalMassReal]
  push_cast
  ring

/-- **`S_p(e) ≤ 150/p²` for `p ≥ 5`**, uniformly in the exponent function `e`. -/
theorem expMoment2_le (hp : 5 ≤ p) {e : ℕ → ℕ} (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    expMoment2 (scalarLocalMassReal p) e ≤ 150 / (p : ℝ) ^ 2 :=
  expMoment2_le_of_tailLaw hp (hasTailGeometricLaw_of_five_le hp) he

/-- `∑_τ δ_p(τ) v_ℓ(τ) v_{ℓ'}(τ) ≤ ∑_τ δ_p(τ) (v_ℓ(τ) + v_{ℓ'}(τ))²`. -/
theorem crossValuationMoment_le_expMoment2' {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') :
    crossValuationMoment p ℓ ℓ'
      ≤ expMoment2 (scalarLocalMassReal p) (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) := by
  have hfac := factorHyp_δ (p := p) (e := fun τ => padicValNat ℓ τ + padicValNat ℓ' τ)
    (two_pow_padicValNat_add_le hℓ hℓ' hne)
  refine Summable.tsum_le_tsum (fun t => ?_)
    (summable_crossValuationTerm' (p := p) hℓ hℓ' hne) hfac.summable_moment2Term
  rw [crossValuationTerm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (natCast_mul_le_natCast_add_sq _ _) ENNReal.toReal_nonneg

/-- **The local polarisation identity.**
`(S_p(a+b) - m_p(a+b)²) - (S_p(a) - m_p(a)²) - (S_p(b) - m_p(b)²) = 2 C_p(ℓ, ℓ')`, with `a = v_ℓ`,
`b = v_{ℓ'}`. -/
theorem varLocal_polarisation' {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    (expMoment2 (scalarLocalMassReal p) (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ)
          - expMoment1 (scalarLocalMassReal p)
              (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) ^ 2)
        - (expMoment2 (scalarLocalMassReal p) (fun τ => padicValNat ℓ τ)
          - expMoment1 (scalarLocalMassReal p) (fun τ => padicValNat ℓ τ) ^ 2)
        - (expMoment2 (scalarLocalMassReal p) (fun τ => padicValNat ℓ' τ)
          - expMoment1 (scalarLocalMassReal p) (fun τ => padicValNat ℓ' τ) ^ 2)
      = 2 * localCov p ℓ ℓ' := by
  rw [expMoment2_add' hℓ hℓ' hne, expMoment1_add' hℓ hℓ', expMoment1_padicValNat,
    expMoment1_padicValNat, localCov]
  ring

end Moments

/-! ### §2. The Euler product over the primes -/

section PrimeProduct

variable {e : ℕ → ℕ}

/-- The `FactorHyp` package at the prime `q`, with the instance pinned to `⟨q.2⟩`. -/
theorem factorHyp_prime' (he : ∀ t, 2 ^ e t ≤ max 1 t) (q : {n : ℕ // n.Prime}) :
    FactorHyp (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) e :=
  @factorHyp_δ (q : ℕ) ⟨q.2⟩ e he

/-- The primes below `5` form a finite subset of the prime index type. -/
theorem finite_small_primes' : {q : {n : ℕ // n.Prime} | (q : ℕ) < 5}.Finite := by
  have hsub : {q : {n : ℕ // n.Prime} | (q : ℕ) < 5}
      ⊆ (Subtype.val : {n : ℕ // n.Prime} → ℕ) ⁻¹' Set.Iio 5 := fun q hq => hq
  exact Set.Finite.subset ((Set.finite_Iio 5).preimage Subtype.val_injective.injOn) hsub

/-- `∑_p 150/p² < ∞` over the primes. -/
theorem summable_const_div_primeSq' :
    Summable fun q : {n : ℕ // n.Prime} => 150 / ((q : ℕ) : ℝ) ^ 2 := by
  have hb : Summable fun n : ℕ => 150 / (n : ℝ) ^ 2 := by
    refine ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 150).congr fun n => ?_
    rw [mul_one_div]
  exact hb.subtype Nat.Prime

/-- **`∑_p S_p(e) < ∞`.** -/
theorem summable_primeMoment2' (he : ∀ t, 2 ^ e t ≤ max 1 t) : Summable (primeMoment2 e) := by
  refine Summable.of_norm_bounded_eventually summable_const_div_primeSq' ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset finite_small_primes' fun q hq => ?_
  by_contra hcon
  have h5 : 5 ≤ (q : ℕ) := not_lt.mp hcon
  have hnn := @FactorHyp.expMoment2_nonneg _ _ (factorHyp_prime' he q)
  have hle := @expMoment2_le (q : ℕ) ⟨q.2⟩ h5 e he
  exact hq (by rw [Real.norm_eq_abs, primeMoment2, abs_of_nonneg hnn]; exact hle)

/-- **`∑_p m_p(e) < ∞`.** -/
theorem summable_primeMoment1' (he : ∀ t, 2 ^ e t ≤ max 1 t) : Summable (primeMoment1 e) :=
  Summable.of_nonneg_of_le
    (fun q => @FactorHyp.expMoment1_nonneg _ _ (factorHyp_prime' he q))
    (fun q => @FactorHyp.expMoment1_le_expMoment2 _ _ (factorHyp_prime' he q))
    (summable_primeMoment2' he)

/-- **The `LogDerivProduct.ProdHyp` package holds for the local factors `h_p` of the Euler
product.** -/
theorem prodHyp_primeFactor' (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    LogDerivProduct.ProdHyp (primeFactor e) (primeMoment1 e)
      (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) (windowRadius e) := by
  have hsum := summable_primeMoment1' he
  have hnn : ∀ q, 0 ≤ primeMoment1 e q := fun q =>
    @FactorHyp.expMoment1_nonneg _ _ (factorHyp_prime' he q)
  have hsup : 0 ≤ ∑' q : {n : ℕ // n.Prime}, primeMoment1 e q := tsum_nonneg hnn
  have hmem : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| < 2 := fun w hw => by
    rw [abs_of_nonneg hw.1]; linarith [hw.2]
  have hmem1 : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| ≤ 1 := fun w hw => by
    rw [abs_of_nonneg hw.1]; exact hw.2
  refine
    { normalisation := fun q => @FactorHyp.powFactor_one _ _ (factorHyp_prime' he q)
      diff := fun q w hw =>
        @FactorHyp.differentiableAt_powFactor _ _ (factorHyp_prime' he q) w (hmem w hw)
      bound_deriv := fun q w hw => ?_
      A_nonneg := hnn
      summable_A := hsum
      A_sup_nonneg := hsup
      A_sup_bound := fun q => hsum.le_tsum q fun j _ => hnn j
      eta_pos := lt_min zero_lt_one (by positivity)
      eta_le_one := min_le_left _ _
      domain_const := ?_ }
  · have H := factorHyp_prime' he q
    rw [show deriv (primeFactor e q) w = _ from H.deriv_powFactor (hmem w hw)]
    exact H.abs_powFactorDeriv_le (hmem1 w hw)
  · have h1 : windowRadius e ≤ 1 / (2 * (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) + 1) :=
      min_le_right _ _
    have hden : (0 : ℝ) < 2 * (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) + 1 := by linarith
    have h2 : 2 * (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) * windowRadius e
        ≤ 2 * (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q)
          * (1 / (2 * (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    refine h2.trans ?_
    rw [mul_one_div, div_le_one hden]
    linarith

/-- **The `SecondLogDerivProduct.DerivHyp` package holds for the local factors**: the second
derivatives are bounded on `[0,1]` by `S_p(e)`. -/
theorem derivHyp_primeFactor' (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    SecondLogDerivProduct.DerivHyp (primeFactor e) (primeMoment2 e) := by
  have hmem : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| < 2 := fun w hw => by
    rw [abs_of_nonneg hw.1]; linarith [hw.2]
  have hmem1 : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| ≤ 1 := fun w hw => by
    rw [abs_of_nonneg hw.1]; exact hw.2
  refine
    { diff2 := fun q w hw =>
        @FactorHyp.differentiableAt_deriv_powFactor _ _ (factorHyp_prime' he q) w (hmem w hw)
      bound_deriv2 := fun q w hw => ?_
      B_nonneg := fun q => @FactorHyp.expMoment2_nonneg _ _ (factorHyp_prime' he q)
      summable_B := summable_primeMoment2' he }
  have H := factorHyp_prime' he q
  rw [show deriv (deriv (primeFactor e q)) w = _ from H.deriv_deriv_powFactor (hmem w hw)]
  exact H.abs_powFactorDeriv2_le (hmem1 w hw)

/-- `h_q'(1) = m_q(e)`. -/
theorem deriv_primeFactor_one' (he : ∀ t, 2 ^ e t ≤ max 1 t) (q : {n : ℕ // n.Prime}) :
    deriv (primeFactor e q) 1 = primeMoment1 e q := by
  have H := factorHyp_prime' he q
  rw [show deriv (primeFactor e q) 1 = _ from H.deriv_powFactor (by rw [abs_one]; norm_num)]
  exact FactorHyp.powFactorDeriv_one

/-- `h_q''(1) = S_q(e) - m_q(e)`. -/
theorem deriv_deriv_primeFactor_one' (he : ∀ t, 2 ^ e t ≤ max 1 t) (q : {n : ℕ // n.Prime}) :
    deriv (deriv (primeFactor e q)) 1 = primeMoment2 e q - primeMoment1 e q := by
  have H := factorHyp_prime' he q
  rw [show deriv (deriv (primeFactor e q)) 1 = _ from
    H.deriv_deriv_powFactor (by rw [abs_one]; norm_num)]
  have h := H.powFactorDeriv2_one_add
  rw [primeMoment2, primeMoment1, ← h]
  ring

/-- `∑_p h_p'(1) = ∑_p m_p(e)`. -/
theorem tsum_deriv_primeFactor_one' (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    (∑' q : {n : ℕ // n.Prime}, deriv (primeFactor e q) 1)
      = ∑' q : {n : ℕ // n.Prime}, primeMoment1 e q :=
  tsum_congr fun q => deriv_primeFactor_one' he q

/-- `∑_p (h_p'(1))² = ∑_p m_p(e)²`. -/
theorem tsum_deriv_primeFactor_one_sq' (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    (∑' q : {n : ℕ // n.Prime}, deriv (primeFactor e q) 1 ^ 2)
      = ∑' q : {n : ℕ // n.Prime}, primeMoment1 e q ^ 2 :=
  tsum_congr fun q => by rw [deriv_primeFactor_one' he q]

/-- `∑_p h_p''(1) = ∑_p (S_p(e) - m_p(e))`. -/
theorem tsum_deriv_deriv_primeFactor_one' (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    (∑' q : {n : ℕ // n.Prime}, deriv (deriv (primeFactor e q)) 1)
      = ∑' q : {n : ℕ // n.Prime}, (primeMoment2 e q - primeMoment1 e q) :=
  tsum_congr fun q => deriv_deriv_primeFactor_one' he q

/-- `∑_p m_p(e)² < ∞`. -/
theorem summable_primeMoment1_sq' (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    Summable fun q : {n : ℕ // n.Prime} => primeMoment1 e q ^ 2 :=
  (SecondLogDerivProduct.summable_deriv_one_sq (prodHyp_primeFactor' he)).congr fun q => by
    rw [deriv_primeFactor_one' he q]

section PGFCore

variable {μ : PMF ℕ}

/-- **`F'(1) = ∑_p m_p(e)`.** -/
theorem hasDerivWithinAt_pgf' (he : ∀ t, 2 ^ e t ≤ max 1 t)
    (hpgf : ∀ w ∈ Set.Icc (1 - windowRadius e) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG (primeFactor e) w) :
    HasDerivWithinAt (PGFMean.pgf fun n : ℕ => (μ n).toReal)
      (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) (Set.Iio 1) 1 := by
  have H := prodHyp_primeFactor' he
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG H
  rw [tsum_deriv_primeFactor_one' he] at hprod
  refine hprod.congr_of_eventuallyEq ?_ (hpgf 1 (LogDerivProduct.one_mem_window H))
  filter_upwards [Ioo_mem_nhdsLT (LogDerivProduct.window_lt_one H)] with x hx
  exact hpgf x ⟨hx.left.le, hx.right.le⟩

/-- **`F''(1) = ∑_p (S_p - m_p) + (∑_p m_p)² - ∑_p m_p²`.** -/
theorem hasDerivWithinAt_derivWithin_pgf' (he : ∀ t, 2 ^ e t ≤ max 1 t)
    (hpgf : ∀ w ∈ Set.Icc (1 - windowRadius e) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG (primeFactor e) w) :
    HasDerivWithinAt (derivWithin (PGFMean.pgf fun n : ℕ => (μ n).toReal) (Set.Iic 1))
      ((∑' q : {n : ℕ // n.Prime}, (primeMoment2 e q - primeMoment1 e q))
        + (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) ^ 2
        - ∑' q : {n : ℕ // n.Prime}, primeMoment1 e q ^ 2) (Set.Iio 1) 1 := by
  have h := SecondLogDerivProduct.hasDerivWithinAt_derivWithin_prodG (prodHyp_primeFactor' he)
    (derivHyp_primeFactor' he)
  rw [tsum_deriv_deriv_primeFactor_one' he, tsum_deriv_primeFactor_one' he,
    tsum_deriv_primeFactor_one_sq' he] at h
  have hlt := LogDerivProduct.window_lt_one (prodHyp_primeFactor' he)
  refine h.congr_of_eventuallyEq ?_ (derivWithin_pgf_eq hpgf ⟨hlt, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT hlt] with x hx
  exact derivWithin_pgf_eq hpgf ⟨hx.left, hx.right.le⟩

/-- **`Var = ∑_p (S_p(e) - m_p(e)²)`.** -/
theorem variance_of_pgf' (he : ∀ t, 2 ^ e t ≤ max 1 t)
    (hpgf : ∀ w ∈ Set.Icc (1 - windowRadius e) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG (primeFactor e) w) :
    variance (fun n : ℕ => (n : ℝ)) μ.toMeasure
      = ∑' q : {n : ℕ // n.Prime}, (primeMoment2 e q - primeMoment1 e q ^ 2) := by
  rw [BSDTamagawa.PGFSecondDeriv.variance_eq_of_hasDerivWithinAt_derivWithin' μ
    (hasDerivWithinAt_pgf' he hpgf) (hasDerivWithinAt_derivWithin_pgf' he hpgf)]
  have h1 := summable_primeMoment1' he
  have h2 := summable_primeMoment2' he
  have hsplit : (∑' q : {n : ℕ // n.Prime}, (primeMoment2 e q - primeMoment1 e q))
      + (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q)
      = ∑' q : {n : ℕ // n.Prime}, primeMoment2 e q := by
    rw [← (h2.sub h1).tsum_add h1]
    exact tsum_congr fun q => by ring
  rw [h2.tsum_sub (summable_primeMoment1_sq' he), ← hsplit]
  ring

/-- **The inclusion variable is in `L²`.** -/
theorem memLp_two_of_pgf' (he : ∀ t, 2 ^ e t ≤ max 1 t)
    (hpgf : ∀ w ∈ Set.Icc (1 - windowRadius e) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG (primeFactor e) w) :
    MemLp (fun n : ℕ => (n : ℝ)) 2 μ.toMeasure := by
  have h₁ := hasDerivWithinAt_pgf' he hpgf
  have h₂ := hasDerivWithinAt_derivWithin_pgf' he hpgf
  have hint := BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt μ h₁
  obtain ⟨hF'', -⟩ :=
    BSDTamagawa.PGFSecondDeriv.summable_and_tsum_eq_of_hasDerivWithinAt_derivWithin _
      (fun _ => ENNReal.toReal_nonneg)
      (BSDTamagawa.PGFSecondDeriv.hasSum_toReal_pmf μ) h₁ h₂
  exact (memLp_two_iff_integrable_sq measurable_from_top.aestronglyMeasurable).mpr
    ((PGFVariance.pgfDeriv2_summable_iff_integrable_sq μ hint).mp hF'')

end PGFCore

end PrimeProduct

/-! ### §3. The joint law and the weighted coordinate sums -/

section Joint

variable {P : Finset ℕ}

/-- On the window `[1 - windowRadius, 1]` the real infinite product `LogDerivProduct.prodG` of the
power factors coerces to the joint valuation Euler product at `z_i = w^{t_i}`. -/
theorem ofReal_prodG_primeFactor' {t : ↥P → ℕ}
    (he : ∀ τ, 2 ^ valExpWeight P t τ ≤ max 1 τ) {w : ℝ}
    (hw : w ∈ Set.Icc (1 - windowRadius (valExpWeight P t)) 1) :
    ((LogDerivProduct.prodG (primeFactor (valExpWeight P t)) w : ℝ) : ℂ)
      = ∏' q : {n : ℕ // n.Prime}, ∑' τ : ℕ, ((@δ (q : ℕ) ⟨q.2⟩ τ).toReal : ℂ)
          * ∏ i : ↥P, ((w ^ t i : ℝ) : ℂ) ^ padicValNat (i : ℕ) τ := by
  have hmap := (LogDerivProduct.hasProd_prodG (prodHyp_primeFactor' he) hw).map Complex.ofRealHom
    Complex.continuous_ofReal
  refine ((hmap.congr_fun fun q => ?_).tprod_eq).symm
  simpa using (ofReal_primeFactor_eq t q w).symm

/-- **On the window `[1 - windowRadius, 1]` the pgf of the weighted coordinate sum is the real
Euler product.** -/
theorem pgf_valWeightPMF_eq_prodG' (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {t : ↥P → ℕ}
    (he : ∀ τ, 2 ^ valExpWeight P t τ ≤ max 1 τ) {w : ℝ}
    (hw : w ∈ Set.Icc (1 - windowRadius (valExpWeight P t)) 1) :
    PGFMean.pgf (fun n : ℕ => ((valWeightPMF hP t) n).toReal) w
      = LogDerivProduct.prodG (primeFactor (valExpWeight P t)) w := by
  have hunit := LogDerivProduct.subset_unitInterval (prodHyp_primeFactor' he) hw
  rw [pgf_valWeightPMF hP t hunit.1 hunit.2]
  exact Complex.ofReal_inj.mp
    ((ofReal_tsum_density_mul_pow_valWeightSum hP t hunit.1 hunit.2).trans
      (ofReal_prodG_primeFactor' he hw).symm)

/-- **`Var_P(∑_i t_i 𝐣_i) = ∑_p (S_p(E_t) - m_p(E_t)²)`**, against the joint valuation law `P`. -/
theorem variance_valWeightSum' (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {t : ↥P → ℕ}
    (he : ∀ τ, 2 ^ valExpWeight P t τ ≤ max 1 τ) :
    variance (fun j : ↥P → ℕ => (valWeightSum t j : ℝ)) (tamagawaValuationMeasure P)
      = ∑' q : {n : ℕ // n.Prime},
          (primeMoment2 (valExpWeight P t) q - primeMoment1 (valExpWeight P t) q ^ 2) := by
  have hvar := variance_of_pgf' (μ := valWeightPMF hP t) he
    fun w hw => pgf_valWeightPMF_eq_prodG' hP he hw
  rw [valWeightPMF_toMeasure hP t,
    variance_map measurable_from_top.aemeasurable
      (measurable_of_countable _).aemeasurable] at hvar
  exact hvar

/-- **`∑_i t_i 𝐣_i ∈ L²(P_Π)`.** -/
theorem memLp_two_valWeightSum' (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {t : ↥P → ℕ}
    (he : ∀ τ, 2 ^ valExpWeight P t τ ≤ max 1 τ) :
    MemLp (fun j : ↥P → ℕ => (valWeightSum t j : ℝ)) 2 (tamagawaValuationMeasure P) := by
  have h := memLp_two_of_pgf' (μ := valWeightPMF hP t) he
    fun w hw => pgf_valWeightPMF_eq_prodG' hP he hw
  rw [valWeightPMF_toMeasure hP t] at h
  exact (memLp_map_measure_iff measurable_from_top.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mp h

end Joint

/-! ### §4. Summability over the primes, and the covariance formula -/

section Main

variable {ℓ ℓ' : ℕ}

/-- `∑_p μ_{p,r} < ∞` for every prime `r`. -/
theorem summable_valuationMoment' {r : ℕ} (hr : r.Prime) :
    Summable fun q : {n : ℕ // n.Prime} => @valuationMoment (q : ℕ) ⟨q.2⟩ r :=
  (summable_primeMoment1' (two_pow_padicValNat_le hr)).congr fun q =>
    @expMoment1_padicValNat (q : ℕ) ⟨q.2⟩ r

/-- `∑_p (∑_τ δ_p(τ) v_ℓ(τ) v_{ℓ'}(τ)) < ∞`. -/
theorem summable_crossValuationMoment' (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    Summable fun q : {n : ℕ // n.Prime} => @crossValuationMoment (q : ℕ) ⟨q.2⟩ ℓ ℓ' :=
  Summable.of_nonneg_of_le
    (fun q => @crossValuationMoment_nonneg (q : ℕ) ⟨q.2⟩ ℓ ℓ')
    (fun q => @crossValuationMoment_le_expMoment2' (q : ℕ) ⟨q.2⟩ ℓ ℓ' hℓ hℓ' hne)
    (summable_primeMoment2' (two_pow_padicValNat_add_le hℓ hℓ' hne))

/-- `∑_p μ_{p,ℓ} μ_{p,ℓ'} < ∞`. -/
theorem summable_valuationMoment_mul' (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) :
    Summable fun q : {n : ℕ // n.Prime} =>
      @valuationMoment (q : ℕ) ⟨q.2⟩ ℓ * @valuationMoment (q : ℕ) ⟨q.2⟩ ℓ' := by
  have hA := summable_valuationMoment' hℓ
  have hB := summable_valuationMoment' hℓ'
  have hnnA : ∀ q : {n : ℕ // n.Prime}, 0 ≤ @valuationMoment (q : ℕ) ⟨q.2⟩ ℓ := fun q =>
    tsum_nonneg fun t => @valuationTerm_nonneg (q : ℕ) ⟨q.2⟩ ℓ t
  have hnnB : ∀ q : {n : ℕ // n.Prime}, 0 ≤ @valuationMoment (q : ℕ) ⟨q.2⟩ ℓ' := fun q =>
    tsum_nonneg fun t => @valuationTerm_nonneg (q : ℕ) ⟨q.2⟩ ℓ' t
  refine Summable.of_nonneg_of_le (fun q => mul_nonneg (hnnA q) (hnnB q)) (fun q => ?_)
    (hB.mul_left (∑' r : {n : ℕ // n.Prime}, @valuationMoment (r : ℕ) ⟨r.2⟩ ℓ))
  exact mul_le_mul_of_nonneg_right (hA.le_tsum q fun j _ => hnnA j) (hnnB q)

/-- **Absolute convergence.** `∑_p |C_p(ℓ, ℓ')| < ∞` for distinct primes `ℓ ≠ ℓ'`. -/
theorem summable_abs_localCov (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'| := by
  refine Summable.of_nonneg_of_le (fun q => abs_nonneg _) (fun q => ?_)
    ((summable_crossValuationMoment' hℓ hℓ' hne).add (summable_valuationMoment_mul' hℓ hℓ'))
  have hc : 0 ≤ @crossValuationMoment (q : ℕ) ⟨q.2⟩ ℓ ℓ' :=
    @crossValuationMoment_nonneg (q : ℕ) ⟨q.2⟩ ℓ ℓ'
  have hm : 0 ≤ @valuationMoment (q : ℕ) ⟨q.2⟩ ℓ * @valuationMoment (q : ℕ) ⟨q.2⟩ ℓ' :=
    mul_nonneg (tsum_nonneg fun t => @valuationTerm_nonneg (q : ℕ) ⟨q.2⟩ ℓ t)
      (tsum_nonneg fun t => @valuationTerm_nonneg (q : ℕ) ⟨q.2⟩ ℓ' t)
  rw [localCov]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hc, abs_of_nonneg hm]

/-- `∑_p C_p(ℓ, ℓ')` converges. -/
theorem summable_localCov (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    Summable fun q : {n : ℕ // n.Prime} => @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' :=
  Summable.of_abs (summable_abs_localCov hℓ hℓ' hne)

/-- **The polarisation identity, summed over the primes.** -/
theorem tsum_varLocal_polarisation' (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    (∑' q : {n : ℕ // n.Prime}, (primeMoment2 (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) q
          - primeMoment1 (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) q ^ 2))
        - (∑' q : {n : ℕ // n.Prime}, (primeMoment2 (fun τ => padicValNat ℓ τ) q
          - primeMoment1 (fun τ => padicValNat ℓ τ) q ^ 2))
        - (∑' q : {n : ℕ // n.Prime}, (primeMoment2 (fun τ => padicValNat ℓ' τ) q
          - primeMoment1 (fun τ => padicValNat ℓ' τ) q ^ 2))
      = 2 * ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' := by
  have hT : Summable fun q : {n : ℕ // n.Prime} =>
      primeMoment2 (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) q
        - primeMoment1 (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) q ^ 2 :=
    (summable_primeMoment2' (two_pow_padicValNat_add_le hℓ hℓ' hne)).sub
      (summable_primeMoment1_sq' (two_pow_padicValNat_add_le hℓ hℓ' hne))
  have hA : Summable fun q : {n : ℕ // n.Prime} =>
      primeMoment2 (fun τ => padicValNat ℓ τ) q - primeMoment1 (fun τ => padicValNat ℓ τ) q ^ 2 :=
    (summable_primeMoment2' (two_pow_padicValNat_le hℓ)).sub
      (summable_primeMoment1_sq' (two_pow_padicValNat_le hℓ))
  have hB : Summable fun q : {n : ℕ // n.Prime} =>
      primeMoment2 (fun τ => padicValNat ℓ' τ) q
        - primeMoment1 (fun τ => padicValNat ℓ' τ) q ^ 2 :=
    (summable_primeMoment2' (two_pow_padicValNat_le hℓ')).sub
      (summable_primeMoment1_sq' (two_pow_padicValNat_le hℓ'))
  rw [← hT.tsum_sub hA, ← (hT.sub hA).tsum_sub hB,
    ← (summable_localCov hℓ hℓ' hne).tsum_mul_left 2]
  refine tsum_congr fun q => ?_
  exact @varLocal_polarisation' (q : ℕ) ⟨q.2⟩ ℓ ℓ' hℓ hℓ' hne

/-- Let `ℓ ≠ ℓ'` be distinct primes and let `P` be the limiting joint valuation law `P_{{ℓ,ℓ'}}` on
`ℤ_{≥0}^{{ℓ,ℓ'}}`. Then the sum `∑_p C_p(ℓ, ℓ')` converges absolutely and

  `Cov_P(v_ℓ(Tam(E)), v_{ℓ'}(Tam(E))) = ∑_{p ∈ 𝒫} C_p(ℓ, ℓ')`,

with `C_p(ℓ, ℓ')` the local covariance `localCov`. The two random variables are the two coordinates
of the multi-index space, read off by the indices `valPairFst ℓ ℓ' ↦ ℓ` and `valPairSnd ℓ ℓ' ↦ ℓ'`.
-/
@[bsd_tamagawa "T057a"]
theorem covariance_tamagawaValuation (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
      covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))
        = ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' := by
  refine ⟨summable_abs_localCov hℓ hℓ' hne, ?_⟩
  have hP := prime_mem_pair hℓ hℓ'
  have := isProbabilityMeasure_tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ) hP
  have heA : ∀ τ, 2 ^ valExpWeight {ℓ, ℓ'} (valFstWeight ℓ ℓ') τ ≤ max 1 τ := fun τ => by
    rw [valExpWeight_fst hne]; exact two_pow_padicValNat_le hℓ τ
  have heB : ∀ τ, 2 ^ valExpWeight {ℓ, ℓ'} (valSndWeight ℓ ℓ') τ ≤ max 1 τ := fun τ => by
    rw [valExpWeight_snd hne]; exact two_pow_padicValNat_le hℓ' τ
  have heT : ∀ τ, 2 ^ valExpWeight {ℓ, ℓ'} (valTotalWeight ℓ ℓ') τ ≤ max 1 τ := fun τ => by
    rw [valExpWeight_total hne]; exact two_pow_padicValNat_add_le hℓ hℓ' hne τ
  have hX : MemLp (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ)) 2
      (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)) := by
    have h := memLp_two_valWeightSum' hP heA
    simpa only [valWeightSum_fst hne] using h
  have hY : MemLp (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ)) 2
      (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)) := by
    have h := memLp_two_valWeightSum' hP heB
    simpa only [valWeightSum_snd hne] using h
  have hvarX : variance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
      (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))
      = ∑' q : {n : ℕ // n.Prime}, (primeMoment2 (fun τ => padicValNat ℓ τ) q
          - primeMoment1 (fun τ => padicValNat ℓ τ) q ^ 2) := by
    have h := variance_valWeightSum' hP heA
    rw [valExpWeight_fst_eq hne] at h
    simpa only [valWeightSum_fst hne] using h
  have hvarY : variance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
      (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))
      = ∑' q : {n : ℕ // n.Prime}, (primeMoment2 (fun τ => padicValNat ℓ' τ) q
          - primeMoment1 (fun τ => padicValNat ℓ' τ) q ^ 2) := by
    have h := variance_valWeightSum' hP heB
    rw [valExpWeight_snd_eq hne] at h
    simpa only [valWeightSum_snd hne] using h
  have hvarS : variance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ =>
      ((j (valPairFst ℓ ℓ') : ℝ) + (j (valPairSnd ℓ ℓ') : ℝ)))
      (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))
      = ∑' q : {n : ℕ // n.Prime},
          (primeMoment2 (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) q
            - primeMoment1 (fun τ => padicValNat ℓ τ + padicValNat ℓ' τ) q ^ 2) := by
    have h := variance_valWeightSum' hP heT
    rw [valExpWeight_total_eq hne] at h
    simpa only [valWeightSum_total hne, Nat.cast_add] using h
  have hadd := variance_fun_add hX hY
  rw [hvarS, hvarX, hvarY] at hadd
  have hpol := tsum_varLocal_polarisation' hℓ hℓ' hne
  linarith [hadd, hpol]

/-- The covariance formula on the index space `ℤ_{≥0}²`: the same two clauses as
`covariance_tamagawaValuation`, with the two random variables the coordinate projections of
`ℤ_{≥0}²`, the first being the `ℓ`-valuation. -/
@[bsd_tamagawa "T057a"]
theorem covariance_tamagawaValuation_prod (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
      covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
          (tamagawaValuationProdMeasure ℓ ℓ' hne)
        = ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ' := by
  refine ⟨summable_abs_localCov hℓ hℓ' hne, ?_⟩
  rw [tamagawaValuationProdMeasure,
    covariance_map_fun (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
  exact (covariance_tamagawaValuation hℓ hℓ' hne).right

end Main

end WeierstrassCurve
