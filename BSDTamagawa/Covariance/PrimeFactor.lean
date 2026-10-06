/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.SumVariance

/-!
# The covariance and correlation of `ω_Tam(E)` and `Ω(Tam(E))`

Let `P_joint = jointOmegaCardFactorsMeasure` be the joint limiting law on `ℕ × ℕ` of the number
`ω_Tam(E)` of primes dividing the Tamagawa product and the number `Ω(Tam(E))` of its prime factors
counted with multiplicity. For an exponent `e : ℕ → ℕ` write `m_p(e) = ∑_t δ_p(t) e(t)` and
`S_p(e) = ∑_t δ_p(t) e(t)²`, and let `ω_{Tam,t}` be `0` at `t = 1` and `1` otherwise. Then

  `Cov(ω_Tam(E), Ω(Tam(E))) = ∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)`,

an absolutely convergent sum. The proof polarises `Var(ω_Tam + Ω(Tam))`, each of the three
variances being a sum over the primes of local variances `S_p(e) - m_p(e)²`. Both marginal
variances are strictly positive, as their terms at `p = 7` show, so the linear correlation
`Cov / sqrt(Var(ω_Tam(E)) Var(Ω(Tam(E))))` is a well-defined real number.

## Main results

* `WeierstrassCurve.covariance_omegaCardFactorsTamagawa`: the covariance formula, with absolute
  convergence of the series.
* `WeierstrassCurve.corr_omegaCardFactorsTamagawa`: both variances, and the square root of their
  product, are positive, and the correlation has the series as numerator.
* `WeierstrassCurve.tsum_centeredMomentTerm`: `S_p(e) - m_p(e)² = ∑_t δ_p(t)(e(t) - m_p(e))²`.
* `WeierstrassCurve.toReal_δ_one_mem_Ioo`: `0 < δ_q(1) < 1` at every prime `q ≥ 7`.

## Implementation notes

Mathlib has no correlation coefficient, so the correlation statement is the positivity of the two
variances together with the value of the quotient.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open BSDTamagawa BSDTamagawa.ValuationMean BSDTamagawa.ValuationMeanUnconditional
open BSDTamagawa.FactorCountMean BSDTamagawa.CovarianceFormula BSDTamagawa.PrimeFactorCovariance
open BSDTamagawa.PrimeFactorCovarianceUnconditional

/-! ### Square integrability of the coordinates -/

/-- `ω_Tam(E)` is square integrable under its limiting law `tamagawaOmegaMeasure`. -/
theorem memLp_two_natCast_tamagawaOmegaMeasure :
    MemLp (fun n : ℕ => (n : ℝ)) 2 tamagawaOmegaMeasure := by
  rw [← tamagawaOmegaPMF_toMeasure]
  have h₁ := hasDerivWithinAt_pgf_toReal_tamagawaOmegaPMF
  have h₂ := hasDerivWithinAt_derivWithin_pgf_toReal_tamagawaOmegaPMF
  have hint := BSDTamagawa.PGFSecondDeriv.integrable_of_hasDerivWithinAt tamagawaOmegaPMF h₁
  obtain ⟨hF'', -⟩ :=
    BSDTamagawa.PGFSecondDeriv.summable_and_tsum_eq_of_hasDerivWithinAt_derivWithin _
      (fun _ => ENNReal.toReal_nonneg)
      (BSDTamagawa.PGFSecondDeriv.hasSum_toReal_pmf tamagawaOmegaPMF) h₁ h₂
  exact (memLp_two_iff_integrable_sq measurable_from_top.aestronglyMeasurable).mpr
    ((PGFVariance.pgfDeriv2_summable_iff_integrable_sq tamagawaOmegaPMF hint).mp hF'')

/-- The first coordinate is square integrable under `P_joint`. -/
theorem memLp_two_fst_jointOmegaCardFactorsMeasure :
    MemLp (fun rb : ℕ × ℕ => (rb.1 : ℝ)) 2 jointOmegaCardFactorsMeasure := by
  have hfun : ((fun n : ℕ => (n : ℝ)) ∘ Prod.fst) = fun rb : ℕ × ℕ => ((rb.1 : ℕ) : ℝ) := rfl
  have h : MemLp (fun n : ℕ => (n : ℝ)) 2 (jointOmegaCardFactorsMeasure.map Prod.fst) := by
    rw [map_fst_jointOmegaCardFactorsMeasure]
    exact memLp_two_natCast_tamagawaOmegaMeasure
  have h2 := (memLp_map_measure_iff measurable_from_top.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mp h
  rwa [hfun] at h2

/-- The second coordinate is square integrable under `P_joint`. -/
theorem memLp_two_snd_jointOmegaCardFactorsMeasure :
    MemLp (fun rb : ℕ × ℕ => (rb.2 : ℝ)) 2 jointOmegaCardFactorsMeasure := by
  have hfun : ((fun n : ℕ => (n : ℝ)) ∘ Prod.snd) = fun rb : ℕ × ℕ => ((rb.2 : ℕ) : ℝ) := rfl
  have h : MemLp (fun n : ℕ => (n : ℝ)) 2 (jointOmegaCardFactorsMeasure.map Prod.snd) := by
    rw [map_snd_jointOmegaCardFactorsMeasure]
    exact memLp_two_natCast_cardFactorsTamagawaMeasure
  have h2 := (memLp_map_measure_iff measurable_from_top.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mp h
  rwa [hfun] at h2

/-! ### The variance of `ω_Tam` under `P_joint` -/

/-- At a prime `q`, `primeMoment1 k q` equals `eulerMoment k q`. -/
theorem primeMoment1_eq_eulerMoment (k : ℕ → ℕ) (q : {n : ℕ // n.Prime}) :
    primeMoment1 k q = eulerMoment k (q : ℕ) :=
  (@eulerMoment_of_prime k (q : ℕ) ⟨q.2⟩).symm

/-- `m_q(ω_{Tam,·}) = 1 - δ_q(1)`. -/
theorem primeMoment1_omegaIndicator (q : {n : ℕ // n.Prime}) :
    primeMoment1 omegaIndicator q = 1 - (@δ (q : ℕ) ⟨q.2⟩ 1).toReal := by
  rw [primeMoment1_eq_eulerMoment]
  exact @eulerMoment_omegaIndicator_of_prime (q : ℕ) ⟨q.2⟩

/-- `S_q(ω_{Tam,·}) = m_q(ω_{Tam,·})`, the exponent taking only the values `0` and `1`. -/
theorem primeMoment2_omegaIndicator (q : {n : ℕ // n.Prime}) :
    primeMoment2 omegaIndicator q = primeMoment1 omegaIndicator q := by
  rw [primeMoment2, primeMoment1, expMoment2, expMoment1]
  refine tsum_congr fun t => ?_
  rcases le_or_gt t 1 with h | h
  · rw [omegaIndicator_of_le_one h]
    norm_num
  · rw [omegaIndicator_of_two_le h]
    norm_num

/-- The local variance of `ω_{Tam,·}` is `δ_q(1)(1 - δ_q(1))`. -/
theorem primeMomentVar_omegaIndicator (q : {n : ℕ // n.Prime}) :
    primeMoment2 omegaIndicator q - primeMoment1 omegaIndicator q ^ 2
      = (@δ (q : ℕ) ⟨q.2⟩ 1).toReal * (1 - (@δ (q : ℕ) ⟨q.2⟩ 1).toReal) := by
  rw [primeMoment2_omegaIndicator, primeMoment1_omegaIndicator]
  ring

/-- A family vanishing off the primes has the same sum over `ℕ` and over the prime subtype. -/
theorem tsum_primeSubtype_eq_tsum {f : ℕ → ℝ} (hf : ∀ p : ℕ, ¬ p.Prime → f p = 0) :
    (∑' q : {n : ℕ // n.Prime}, f (q : ℕ)) = ∑' p : ℕ, f p := by
  have hsupp : Function.support f ⊆ {p : ℕ | p.Prime} := by
    intro p hp
    by_contra hcon
    exact hp (hf p hcon)
  exact tsum_subtype_eq_of_support_subset hsupp

/-- `Var_{P_joint}(ω_Tam(E)) = Var_P(ω_Tam(E))`: the first marginal of `P_joint` is `P`. -/
theorem variance_fst_eq_variance_tamagawaOmegaMeasure :
    variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
      = variance (fun n : ℕ => (n : ℝ)) tamagawaOmegaMeasure := by
  have hfun : ((fun n : ℕ => (n : ℝ)) ∘ Prod.fst) = fun rb : ℕ × ℕ => ((rb.1 : ℕ) : ℝ) := rfl
  have h := variance_map (X := fun n : ℕ => (n : ℝ)) (Y := Prod.fst)
    (μ := jointOmegaCardFactorsMeasure) measurable_from_top.aemeasurable
    (measurable_of_countable _).aemeasurable
  rw [hfun, map_fst_jointOmegaCardFactorsMeasure] at h
  exact h.symm

/-- `Var_{P_joint}(ω_Tam(E)) = ∑_{q prime} (S_q(ω_{Tam,·}) - m_q(ω_{Tam,·})²)`. -/
theorem variance_fst_jointOmegaCardFactorsMeasure :
    variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
      = ∑' q : {n : ℕ // n.Prime},
          (primeMoment2 omegaIndicator q - primeMoment1 omegaIndicator q ^ 2) := by
  rw [variance_fst_eq_variance_tamagawaOmegaMeasure, variance_natCast_tamagawaOmegaMeasure,
    ← tsum_primeSubtype_eq_tsum
      (f := fun p : ℕ => if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal)
        else 0) fun p hp => dite_eq_right hp]
  refine (tsum_congr fun q => ?_).symm
  rw [primeMomentVar_omegaIndicator q, dite_eq_left q.2]

/-! ### The variance of `Ω(Tam)` under `P_joint` -/

/-- `Var_{P_joint}(Ω(Tam(E))) = Var_{P_Ω}(Ω(Tam(E)))`: the second marginal of `P_joint` is the
limiting law `cardFactorsTamagawaMeasure` of `Ω(Tam(E))`. -/
theorem variance_snd_eq_variance_cardFactorsTamagawaMeasure :
    variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure
      = variance (fun n : ℕ => (n : ℝ)) cardFactorsTamagawaMeasure := by
  have hfun : ((fun n : ℕ => (n : ℝ)) ∘ Prod.snd) = fun rb : ℕ × ℕ => ((rb.2 : ℕ) : ℝ) := rfl
  have h := variance_map (X := fun n : ℕ => (n : ℝ)) (Y := Prod.snd)
    (μ := jointOmegaCardFactorsMeasure) measurable_from_top.aemeasurable
    (measurable_of_countable _).aemeasurable
  rw [hfun, map_snd_jointOmegaCardFactorsMeasure] at h
  exact h.symm

/-- `Var_{P_joint}(Ω(Tam(E))) = ∑_{q prime} (S_q(Ω) - m_q(Ω)²)`. -/
theorem variance_snd_jointOmegaCardFactorsMeasure :
    variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure
      = ∑' q : {n : ℕ // n.Prime}, (primeMoment2 omegaExp q - primeMoment1 omegaExp q ^ 2) := by
  rw [variance_snd_eq_variance_cardFactorsTamagawaMeasure, ← cardFactorsPMF_toMeasure]
  exact variance_cardFactorsPMF'

/-! ### The local polarisation at a prime -/

/-- `2^{ω_{Tam,t} Ω(t)} ≤ max 1 t`. -/
theorem two_pow_crossExp_le (t : ℕ) : 2 ^ crossExp t ≤ max 1 t := by
  rw [crossExp_eq_omegaExp]
  exact two_pow_omegaExp_le t

/-- `m_p(ω_{Tam,·} + Ω) = m_p(ω_{Tam,·}) + m_p(Ω)`. -/
theorem expMoment1_sumExp (p : ℕ) [Fact p.Prime] :
    expMoment1 (scalarLocalMassReal p) sumExp
      = expMoment1 (scalarLocalMassReal p) omegaIndicator
        + expMoment1 (scalarLocalMassReal p) omegaExp := by
  have h1 := (factorHyp_δ (p := p) two_pow_omegaIndicator_le).summable_moment1Term
  have h2 := (factorHyp_δ (p := p) two_pow_omegaExp_le).summable_moment1Term
  rw [expMoment1, expMoment1, expMoment1, ← h1.tsum_add h2]
  refine tsum_congr fun t => ?_
  rw [sumExp]
  push_cast
  ring

/-- `S_p(ω_{Tam,·} + Ω) = S_p(ω_{Tam,·}) + 2 m_p(ω_{Tam,·} Ω) + S_p(Ω)`. -/
theorem expMoment2_sumExp (p : ℕ) [Fact p.Prime] :
    expMoment2 (scalarLocalMassReal p) sumExp
      = expMoment2 (scalarLocalMassReal p) omegaIndicator
        + 2 * expMoment1 (scalarLocalMassReal p) crossExp
        + expMoment2 (scalarLocalMassReal p) omegaExp := by
  have h1 := (factorHyp_δ (p := p) two_pow_omegaIndicator_le).summable_moment2Term
  have h2 := (factorHyp_δ (p := p) two_pow_omegaExp_le).summable_moment2Term
  have hx := (factorHyp_δ (p := p) two_pow_crossExp_le).summable_moment1Term
  have hx2 : Summable fun t : ℕ => 2 * (scalarLocalMassReal p t * (crossExp t : ℝ)) :=
    hx.mul_left 2
  rw [expMoment1, ← hx.tsum_mul_left 2, expMoment2, expMoment2, expMoment2,
    ← h1.tsum_add hx2, ← (h1.add hx2).tsum_add h2]
  refine tsum_congr fun t => ?_
  rw [sumExp, crossExp]
  push_cast
  ring

/-- At every prime `q`, with `e = ω_{Tam,·} + Ω`,

  `(S_q(e) - m_q(e)²) - (S_q(ω) - m_q(ω)²) - (S_q(Ω) - m_q(Ω)²) = 2 δ_q(1) ∑_t δ_q(t) Ω(t)`. -/
theorem varLocal_polarisation_omegaCardFactors (q : {n : ℕ // n.Prime}) :
    (sumMoment2 q - sumMoment1 q ^ 2)
        - (primeMoment2 omegaIndicator q - primeMoment1 omegaIndicator q ^ 2)
        - (primeMoment2 omegaExp q - primeMoment1 omegaExp q ^ 2)
      = 2 * covSeriesTerm (q : ℕ) := by
  have h2 : sumMoment2 q = primeMoment2 omegaIndicator q
      + 2 * primeMoment1 crossExp q + primeMoment2 omegaExp q :=
    @expMoment2_sumExp (q : ℕ) ⟨q.2⟩
  have h1 : sumMoment1 q = primeMoment1 omegaIndicator q + primeMoment1 omegaExp q :=
    @expMoment1_sumExp (q : ℕ) ⟨q.2⟩
  have hcov : primeMoment1 crossExp q
      - primeMoment1 omegaIndicator q * primeMoment1 omegaExp q = covSeriesTerm (q : ℕ) := by
    rw [primeMoment1_eq_eulerMoment, primeMoment1_eq_eulerMoment, primeMoment1_eq_eulerMoment,
      ← localCovOmega]
    exact localCovOmega_eq_covSeriesTerm _
  rw [h1, h2, ← hcov]
  ring

/-! ### The covariance -/

/-- The series `∑_p covSeriesTerm p` has the same sum over `ℕ` and over the primes. -/
theorem tsum_covSeriesTerm_primeSubtype :
    (∑' q : {n : ℕ // n.Prime}, covSeriesTerm (q : ℕ)) = ∑' p : ℕ, covSeriesTerm p :=
  tsum_primeSubtype_eq_tsum fun p hp => by rw [covSeriesTerm, dite_eq_right hp]

/-- The local polarisation summed over the primes: the three variance series combine to
`2 ∑_p covSeriesTerm p`. -/
theorem tsum_varLocal_polarisation_omegaCardFactors :
    (∑' q : {n : ℕ // n.Prime}, (sumMoment2 q - sumMoment1 q ^ 2))
        - (∑' q : {n : ℕ // n.Prime},
            (primeMoment2 omegaIndicator q - primeMoment1 omegaIndicator q ^ 2))
        - (∑' q : {n : ℕ // n.Prime}, (primeMoment2 omegaExp q - primeMoment1 omegaExp q ^ 2))
      = 2 * ∑' p : ℕ, covSeriesTerm p := by
  have hT : Summable fun q : {n : ℕ // n.Prime} => sumMoment2 q - sumMoment1 q ^ 2 :=
    summable_sumMoment2.sub summable_sumMoment1_sq
  have hA : Summable fun q : {n : ℕ // n.Prime} =>
      primeMoment2 omegaIndicator q - primeMoment1 omegaIndicator q ^ 2 :=
    (summable_primeMoment2' two_pow_omegaIndicator_le).sub
      (summable_primeMoment1_sq' two_pow_omegaIndicator_le)
  have hB : Summable fun q : {n : ℕ // n.Prime} =>
      primeMoment2 omegaExp q - primeMoment1 omegaExp q ^ 2 :=
    (summable_primeMoment2' two_pow_omegaExp_le).sub
      (summable_primeMoment1_sq' two_pow_omegaExp_le)
  have hC : Summable fun q : {n : ℕ // n.Prime} => covSeriesTerm (q : ℕ) :=
    summable_covSeriesTerm'.comp_injective Subtype.val_injective
  rw [← hT.tsum_sub hA, ← (hT.sub hA).tsum_sub hB, ← tsum_covSeriesTerm_primeSubtype,
    ← hC.tsum_mul_left 2]
  exact tsum_congr varLocal_polarisation_omegaCardFactors

/-- `Cov_{P_joint}(ω_Tam(E), Ω(Tam(E))) = ∑_p covSeriesTerm p`. -/
theorem covariance_omegaCardFactors_eq_tsum :
    covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
        jointOmegaCardFactorsMeasure
      = ∑' p : ℕ, covSeriesTerm p := by
  have hadd := variance_fun_add memLp_two_fst_jointOmegaCardFactorsMeasure
    memLp_two_snd_jointOmegaCardFactorsMeasure
  rw [variance_jointOmegaCardFactorsSum, variance_fst_jointOmegaCardFactorsMeasure,
    variance_snd_jointOmegaCardFactorsMeasure] at hadd
  have hpol := tsum_varLocal_polarisation_omegaCardFactors
  linarith

/-! ### The centred second moment and positivity of the local variances -/

/-- For an exponent with `2^{e(t)} ≤ max 1 t`, the family `t ↦ δ_p(t)(e(t) - m_p(e))²` is summable.
-/
theorem summable_centeredMomentTerm (p : ℕ) [Fact p.Prime] {e : ℕ → ℕ}
    (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    Summable fun t : ℕ => scalarLocalMassReal p t
      * ((e t : ℝ) - expMoment1 (scalarLocalMassReal p) e) ^ 2 := by
  have H := factorHyp_δ (p := p) he
  exact ((H.summable_moment2Term.sub (H.summable_moment1Term.mul_left
    (2 * expMoment1 (scalarLocalMassReal p) e))).add
      (H.total.summable.mul_left (expMoment1 (scalarLocalMassReal p) e ^ 2))).congr
        fun t => by ring

/-- For an exponent with `2^{e(t)} ≤ max 1 t`, `S_p(e) - m_p(e)² = ∑_t δ_p(t)(e(t) - m_p(e))²`. -/
theorem tsum_centeredMomentTerm (p : ℕ) [Fact p.Prime] {e : ℕ → ℕ}
    (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    (∑' t : ℕ, scalarLocalMassReal p t
        * ((e t : ℝ) - expMoment1 (scalarLocalMassReal p) e) ^ 2)
      = expMoment2 (scalarLocalMassReal p) e - expMoment1 (scalarLocalMassReal p) e ^ 2 := by
  have H := factorHyp_δ (p := p) he
  convert ((H.summable_moment2Term.hasSum.sub (H.summable_moment1Term.hasSum.mul_left
    (2 * expMoment1 (scalarLocalMassReal p) e))).add
      (H.total.mul_left (expMoment1 (scalarLocalMassReal p) e ^ 2))).tsum_eq using 1
  · exact tsum_congr fun t => by ring
  · simp only [expMoment2, expMoment1]
    ring

/-- For an exponent with `2^{e(t)} ≤ max 1 t`, every local variance `S_q(e) - m_q(e)²` is
nonnegative. -/
theorem primeMomentVar_nonneg {e : ℕ → ℕ} (he : ∀ t, 2 ^ e t ≤ max 1 t)
    (q : {n : ℕ // n.Prime}) : 0 ≤ primeMoment2 e q - primeMoment1 e q ^ 2 := by
  rw [primeMoment2, primeMoment1, ← @tsum_centeredMomentTerm (q : ℕ) ⟨q.2⟩ e he]
  exact tsum_nonneg fun t =>
    mul_nonneg (@scalarLocalMassReal_nonneg (q : ℕ) ⟨q.2⟩ t) (sq_nonneg _)

/-- For an exponent with `2^{e(t)} ≤ max 1 t`, the local variance `S_q(e) - m_q(e)²` is at least
`δ_q(2)(e(2) - m_q(e))²`. -/
theorem le_primeMomentVar {e : ℕ → ℕ} (he : ∀ t, 2 ^ e t ≤ max 1 t)
    (q : {n : ℕ // n.Prime}) :
    @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ 2 * ((e 2 : ℝ) - primeMoment1 e q) ^ 2
      ≤ primeMoment2 e q - primeMoment1 e q ^ 2 := by
  rw [primeMoment2, primeMoment1, ← @tsum_centeredMomentTerm (q : ℕ) ⟨q.2⟩ e he]
  exact (@summable_centeredMomentTerm (q : ℕ) ⟨q.2⟩ e he).le_tsum 2 fun t _ =>
    mul_nonneg (@scalarLocalMassReal_nonneg (q : ℕ) ⟨q.2⟩ t) (sq_nonneg _)

/-- `0 < δ_p(2)` at every prime `p ≥ 5`. -/
theorem zero_lt_toReal_δ_two (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : 0 < (δ p 2).toReal := by
  have hden : (2 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p))
  have hlt : (0 : ℝ≥0∞) < 1 / (2 * (p : ℝ≥0∞) ^ 2) := ENNReal.div_pos one_ne_zero hden
  exact ENNReal.toReal_pos (hlt.trans_le (inv_two_mul_sq_le_δ_two hp)).ne' (δ_ne_top' p 2)

/-- `m_q(Ω) ≤ 37/q²` at every prime `q ≥ 5`. -/
theorem primeMoment1_omegaExp_le (q : {n : ℕ // n.Prime}) (hq : 5 ≤ (q : ℕ)) :
    primeMoment1 omegaExp q ≤ 37 / ((q : ℕ) : ℝ) ^ 2 := by
  rw [primeMoment1_eq_eulerMoment]
  exact @eulerMoment_le_of_tsum_le omegaExp (q : ℕ) ⟨q.2⟩
    (@tsum_δ_mul_cardFactors_le (q : ℕ) ⟨q.2⟩ hq)

/-- `m_q(Ω) < 1` at every prime `q ≥ 7`. -/
theorem primeMoment1_omegaExp_lt_one (q : {n : ℕ // n.Prime}) (hq : 7 ≤ (q : ℕ)) :
    primeMoment1 omegaExp q < 1 := by
  have h7 : (7 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hq
  refine (primeMoment1_omegaExp_le q (by omega)).trans_lt ?_
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- `m_q(ω_{Tam,·}) ≤ m_q(Ω)`. -/
theorem primeMoment1_omegaIndicator_le_omegaExp (q : {n : ℕ // n.Prime}) :
    primeMoment1 omegaIndicator q ≤ primeMoment1 omegaExp q := by
  rw [primeMoment1, primeMoment1, expMoment1, expMoment1]
  refine Summable.tsum_le_tsum (fun t => ?_)
    (@factorHyp_δ (q : ℕ) ⟨q.2⟩ omegaIndicator two_pow_omegaIndicator_le).summable_moment1Term
    (@factorHyp_δ (q : ℕ) ⟨q.2⟩ omegaExp two_pow_omegaExp_le).summable_moment1Term
  refine mul_le_mul_of_nonneg_left ?_ (@scalarLocalMassReal_nonneg (q : ℕ) ⟨q.2⟩ t)
  exact_mod_cast omegaIndicator_le_omegaExp t

/-- `0 < δ_q(1) < 1` at every prime `q ≥ 7`. -/
theorem toReal_δ_one_mem_Ioo (q : {n : ℕ // n.Prime}) (hq : 7 ≤ (q : ℕ)) :
    0 < (@δ (q : ℕ) ⟨q.2⟩ 1).toReal ∧ (@δ (q : ℕ) ⟨q.2⟩ 1).toReal < 1 := by
  have hω := primeMoment1_omegaIndicator q
  have hle := (primeMoment1_omegaIndicator_le_omegaExp q).trans_lt
    (primeMoment1_omegaExp_lt_one q hq)
  have hlow : @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ 2 ≤ primeMoment1 omegaIndicator q := by
    rw [primeMoment1, expMoment1]
    have h := (@factorHyp_δ (q : ℕ) ⟨q.2⟩ omegaIndicator
      two_pow_omegaIndicator_le).summable_moment1Term.le_tsum 2 fun t _ =>
        mul_nonneg (@scalarLocalMassReal_nonneg (q : ℕ) ⟨q.2⟩ t) (Nat.cast_nonneg _)
    rwa [omegaIndicator_of_two_le le_rfl, Nat.cast_one, mul_one] at h
  have hδ2 : 0 < @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ 2 :=
    @zero_lt_toReal_δ_two (q : ℕ) ⟨q.2⟩ (by omega)
  constructor
  · linarith [hω, hle]
  · linarith [hω, hlow, hδ2]

/-! ### Positivity of the variances -/

/-- `Var_{P_joint}(ω_Tam(E)) > 0`. -/
theorem zero_lt_variance_fst_jointOmegaCardFactorsMeasure :
    0 < variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure := by
  rw [variance_fst_jointOmegaCardFactorsMeasure]
  refine Summable.tsum_pos
    ((summable_primeMoment2' two_pow_omegaIndicator_le).sub
      (summable_primeMoment1_sq' two_pow_omegaIndicator_le))
    (primeMomentVar_nonneg two_pow_omegaIndicator_le) ⟨7, by decide⟩ ?_
  obtain ⟨h0, h1⟩ := toReal_δ_one_mem_Ioo ⟨7, by decide⟩ le_rfl
  rw [primeMomentVar_omegaIndicator]
  exact mul_pos h0 (by linarith)

/-- `Var_{P_joint}(Ω(Tam(E))) > 0`. -/
theorem zero_lt_variance_snd_jointOmegaCardFactorsMeasure :
    0 < variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure := by
  rw [variance_snd_jointOmegaCardFactorsMeasure]
  refine Summable.tsum_pos
    ((summable_primeMoment2' two_pow_omegaExp_le).sub
      (summable_primeMoment1_sq' two_pow_omegaExp_le))
    (primeMomentVar_nonneg two_pow_omegaExp_le) ⟨7, by decide⟩ ?_
  have hΩ2 : ((omegaExp 2 : ℕ) : ℝ) = 1 := by
    rw [omegaExp_apply, ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
    norm_num
  have hlt := primeMoment1_omegaExp_lt_one (⟨7, by decide⟩ : {n : ℕ // n.Prime}) le_rfl
  have hδ2 : 0 < @scalarLocalMassReal 7 ⟨by decide⟩ 2 :=
    @zero_lt_toReal_δ_two 7 ⟨by decide⟩ (by norm_num)
  refine lt_of_lt_of_le ?_ (le_primeMomentVar two_pow_omegaExp_le ⟨7, by decide⟩)
  rw [hΩ2]
  exact mul_pos hδ2 (pow_pos (by linarith) 2)

/-! ### The covariance and the correlation -/

/-- Under the joint limiting law `P_joint` of `ω_Tam(E)` and `Ω(Tam(E))`, the covariance is given
by the absolutely convergent sum

  `Cov(ω_Tam(E), Ω(Tam(E))) = ∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)`. -/
@[bsd_tamagawa "T058"]
theorem covariance_omegaCardFactorsTamagawa :
    (Summable fun p : ℕ => |if h : p.Prime then
        (@δ p ⟨h⟩ 1).toReal
          * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
        else 0|) ∧
      covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
          jointOmegaCardFactorsMeasure
        = ∑' p : ℕ, if h : p.Prime then
            (@δ p ⟨h⟩ 1).toReal
              * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
            else 0 :=
  ⟨summable_abs_δ_one_mul_tsum_δ_mul_cardFactors, covariance_omegaCardFactors_eq_tsum⟩

/-- The linear correlation

  `Corr(ω_Tam(E), Ω(Tam(E)))
     = (∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)) / sqrt(Var(ω_Tam(E)) Var(Ω(Tam(E))))`

is well defined and finite: both variances under `P_joint` are positive, hence so is the square
root of their product, and the quotient has the stated numerator. -/
@[bsd_tamagawa "T058"]
theorem corr_omegaCardFactorsTamagawa :
    0 < variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure ∧
      0 < variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure ∧
      0 < Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
            * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure) ∧
      covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
            jointOmegaCardFactorsMeasure
          / Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
            * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure)
        = (∑' p : ℕ, if h : p.Prime then
              (@δ p ⟨h⟩ 1).toReal
                * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
              else 0)
            / Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
              * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure) := by
  have hX := zero_lt_variance_fst_jointOmegaCardFactorsMeasure
  have hY := zero_lt_variance_snd_jointOmegaCardFactorsMeasure
  refine ⟨hX, hY, Real.sqrt_pos.mpr (mul_pos hX hY), ?_⟩
  rw [covariance_omegaCardFactors_eq_tsum]
  simp only [covSeriesTerm]

end WeierstrassCurve
