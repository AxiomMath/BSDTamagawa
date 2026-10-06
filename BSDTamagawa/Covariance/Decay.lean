/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.DecayConditional
public import BSDTamagawa.Covariance.Formula

/-!
# Decay of the covariance of Tamagawa valuations

For distinct primes `ℓ ≠ ℓ'`, let `C_p(ℓ, ℓ')` be the local covariance at `p` of the valuations
`v_ℓ` and `v_{ℓ'}` under the local density `δ_p`. There is an absolute constant `C > 0` with

  `∑_p |C_p(ℓ, ℓ')| ≤ C/(ℓℓ')²`,

the series converging absolutely. Consequently the covariance of `v_ℓ(Tam(E))` and `v_{ℓ'}(Tam(E))`
in the limiting Tamagawa distribution is at most `C/(ℓℓ')²` in absolute value, and tends to `0` as
`ℓℓ' → ∞`. At the primes `p = 2, 3` the bound `|C_p(ℓ, ℓ')| ≤ (cross moment) + μ_{p,ℓ} μ_{p,ℓ'}`
together with the support of `v_ℓ v_{ℓ'}` on multiples of `ℓℓ'` suffices.

## Main definitions

* `WeierstrassCurve.bareMoment`: the moment `∑_t δ_p(t) t^k`.
* `WeierstrassCurve.smallCovBound`: the constant `∑_t δ_p(t) t⁴ + (∑_t δ_p(t) t³)²`.
* `WeierstrassCurve.covDecayConstU`: the absolute constant `C`.

## Main results

* `WeierstrassCurve.abs_localCov_le_smallCovBound`: `|C_p(ℓ, ℓ')| ≤ smallCovBound p / (ℓℓ')²` at
  every prime `p`.
* `WeierstrassCurve.tsum_abs_localCov_le`: `∑_p |C_p(ℓ, ℓ')|` converges and is at most
  `covDecayConstU / (ℓℓ')²`.
* `WeierstrassCurve.exists_covariance_decay`: the existential form of the bound above.
* `WeierstrassCurve.exists_covariance_decay_bound`: `|Cov(v_ℓ(Tam), v_{ℓ'}(Tam))| ≤ C/(ℓℓ')²`.
* `WeierstrassCurve.covariance_tamagawaValuation_tendsto_zero`: the covariance tends to `0` as
  `ℓℓ' → ∞`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BSDTamagawa BSDTamagawa.CovarianceFormula

/-! ### The bare moments of `δ_p`, finite at every prime -/

/-- The moment `∑_t δ_p(t) t^k` of the local density `δ_p`. -/
noncomputable def bareMoment (p : ℕ) [Fact p.Prime] (k : ℕ) : ℝ :=
  ∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ k

section Small

variable {p : ℕ} [Fact p.Prime]

/-- The bare moments are nonnegative. -/
theorem bareMoment_nonneg (k : ℕ) : 0 ≤ bareMoment p k :=
  tsum_nonneg fun t => by positivity

/-- **The marginal moment decays like `r^{-2}` at every prime `p`.**
`μ_{p,r} ≤ (∑_t δ_p(t) t³)/r²`. -/
theorem valuationMoment_le_bareMoment_div_sq {r : ℕ} (hr : r.Prime) :
    valuationMoment p r ≤ bareMoment p 3 / (r : ℝ) ^ 2 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hrsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have hterm : ∀ t : ℕ, valuationTerm p r t
      ≤ ((r : ℝ) ^ 2)⁻¹ * ((δ p t).toReal * (t : ℝ) ^ 3) := by
    intro t
    rcases eq_or_ne (padicValNat r t) 0 with h0 | h0
    · rw [valuationTerm, h0]
      have : (0 : ℝ) ≤ ((r : ℝ) ^ 2)⁻¹ * ((δ p t).toReal * (t : ℝ) ^ 3) := by positivity
      simpa using this
    · have hdvd : r ∣ t := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h0)
      have ht0 : t ≠ 0 := by
        intro h
        rw [h] at h0
        exact h0 (padicValNat_zero_right r)
      have hrt : (r : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hdvd
      have hvt : ((padicValNat r t : ℕ) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast (padicValNat_le_nat_log t).trans (Nat.log_le_self r t)
      have hδ : (0 : ℝ) ≤ (δ p t).toReal := ENNReal.toReal_nonneg
      have ht' : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      rw [valuationTerm, inv_mul_eq_div, le_div_iff₀ hrsq]
      have hstep : (δ p t).toReal * ((padicValNat r t : ℕ) : ℝ) * (r : ℝ) ^ 2
          ≤ (δ p t).toReal * (t : ℝ) * (t : ℝ) ^ 2 := by
        have h1 : (δ p t).toReal * ((padicValNat r t : ℕ) : ℝ) ≤ (δ p t).toReal * (t : ℝ) :=
          mul_le_mul_of_nonneg_left hvt hδ
        have h2 : (r : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
      calc (δ p t).toReal * ((padicValNat r t : ℕ) : ℝ) * (r : ℝ) ^ 2
          ≤ (δ p t).toReal * (t : ℝ) * (t : ℝ) ^ 2 := hstep
        _ = (δ p t).toReal * (t : ℝ) ^ 3 := by ring
  have hmaj : Summable fun t : ℕ => ((r : ℝ) ^ 2)⁻¹ * ((δ p t).toReal * (t : ℝ) ^ 3) :=
    (summable_δ_toReal_mul_pow 3).mul_left _
  refine ((summable_valuationTerm' hr).tsum_le_tsum hterm hmaj).trans ?_
  rw [tsum_mul_left, bareMoment, div_eq_inv_mul]

/-- **The cross moment decays like `(ℓℓ')^{-2}` at every prime `p`.**
`∑_t δ_p(t) v_ℓ(t) v_{ℓ'}(t) ≤ (∑_t δ_p(t) t⁴)/(ℓℓ')²` for distinct primes `ℓ ≠ ℓ'`. -/
theorem crossValuationMoment_le_bareMoment_div_sq {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') :
    crossValuationMoment p ℓ ℓ' ≤ bareMoment p 4 / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
  have hℓ0' : (0 : ℝ) < (ℓ' : ℝ) := by exact_mod_cast hℓ'.pos
  have hsq : (0 : ℝ) < ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by positivity
  have hterm : ∀ t : ℕ, crossValuationTerm p ℓ ℓ' t
      ≤ (((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2)⁻¹ * ((δ p t).toReal * (t : ℝ) ^ 4) := by
    intro t
    have hnn : (0 : ℝ) ≤ (((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2)⁻¹ * ((δ p t).toReal * (t : ℝ) ^ 4) := by
      positivity
    rcases eq_or_ne (padicValNat ℓ t) 0 with h0 | h0
    · rw [crossValuationTerm, h0]
      simpa using hnn
    rcases eq_or_ne (padicValNat ℓ' t) 0 with h0' | h0'
    · rw [crossValuationTerm, h0']
      simpa using hnn
    have hd : ℓ ∣ t := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h0)
    have hd' : ℓ' ∣ t := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h0')
    have hcop : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
    have hdd : ℓ * ℓ' ∣ t := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hd hd'
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at h0
      exact h0 (padicValNat_zero_right ℓ)
    have hle : (ℓ : ℝ) * (ℓ' : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hdd
    have hδ : (0 : ℝ) ≤ (δ p t).toReal := ENNReal.toReal_nonneg
    have hv : ((padicValNat ℓ t : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (padicValNat_le_nat_log t).trans (Nat.log_le_self ℓ t)
    have hv' : ((padicValNat ℓ' t : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (padicValNat_le_nat_log t).trans (Nat.log_le_self ℓ' t)
    rw [crossValuationTerm, inv_mul_eq_div, le_div_iff₀ hsq]
    have hstep : (δ p t).toReal * ((padicValNat ℓ t : ℕ) : ℝ) * ((padicValNat ℓ' t : ℕ) : ℝ)
        ≤ (δ p t).toReal * (t : ℝ) * (t : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv hδ) hv' (by positivity) (by positivity)
    have hsq2 : ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 ≤ (t : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    calc (δ p t).toReal * ((padicValNat ℓ t : ℕ) : ℝ) * ((padicValNat ℓ' t : ℕ) : ℝ)
          * ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2
        ≤ ((δ p t).toReal * (t : ℝ) * (t : ℝ)) * ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ ≤ ((δ p t).toReal * (t : ℝ) * (t : ℝ)) * (t : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq2 (by positivity)
      _ = (δ p t).toReal * (t : ℝ) ^ 4 := by ring
  have hmaj : Summable fun t : ℕ => (((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2)⁻¹ * ((δ p t).toReal * (t : ℝ) ^ 4) :=
    (summable_δ_toReal_mul_pow 4).mul_left _
  refine ((summable_crossValuationTerm' hℓ hℓ' hne).tsum_le_tsum hterm hmaj).trans ?_
  rw [tsum_mul_left, bareMoment, div_eq_inv_mul]

/-- The constant of the small-prime bound: `∑_t δ_p(t) t⁴ + (∑_t δ_p(t) t³)²`. -/
noncomputable def smallCovBound (p : ℕ) [Fact p.Prime] : ℝ :=
  bareMoment p 4 + (bareMoment p 3) ^ 2

/-- `0 ≤ smallCovBound p`. -/
theorem smallCovBound_nonneg : 0 ≤ smallCovBound p := by
  have := bareMoment_nonneg (p := p) 4
  have := bareMoment_nonneg (p := p) 3
  rw [smallCovBound]
  positivity

/-- **`|C_p(ℓ, ℓ')| ≤ smallCovBound p / (ℓℓ')²` at every prime `p`**, for distinct primes `ℓ ≠ ℓ'`.
-/
theorem abs_localCov_le_smallCovBound {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    |localCov p ℓ ℓ'| ≤ smallCovBound p / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
  have hℓ0' : (0 : ℝ) < (ℓ' : ℝ) := by exact_mod_cast hℓ'.pos
  have hc : 0 ≤ crossValuationMoment p ℓ ℓ' := crossValuationMoment_nonneg ℓ ℓ'
  have hm1 : 0 ≤ valuationMoment p ℓ := valuationMoment_nonneg ℓ
  have hm2 : 0 ≤ valuationMoment p ℓ' := valuationMoment_nonneg ℓ'
  have hbn : 0 ≤ bareMoment p 3 := bareMoment_nonneg 3
  have hmul : valuationMoment p ℓ * valuationMoment p ℓ'
      ≤ (bareMoment p 3 / (ℓ : ℝ) ^ 2) * (bareMoment p 3 / (ℓ' : ℝ) ^ 2) :=
    mul_le_mul (valuationMoment_le_bareMoment_div_sq hℓ) (valuationMoment_le_bareMoment_div_sq hℓ')
      hm2 (by positivity)
  have hsplit : |localCov p ℓ ℓ'|
      ≤ crossValuationMoment p ℓ ℓ' + valuationMoment p ℓ * valuationMoment p ℓ' := by
    rw [localCov]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hc, abs_of_nonneg (mul_nonneg hm1 hm2)]
  refine hsplit.trans ?_
  rw [show bareMoment p 3 / (ℓ : ℝ) ^ 2 * (bareMoment p 3 / (ℓ' : ℝ) ^ 2)
      = (bareMoment p 3) ^ 2 / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 by field_simp] at hmul
  rw [smallCovBound, add_div]
  linarith [crossValuationMoment_le_bareMoment_div_sq (p := p) hℓ hℓ' hne]

/-- `smallCovBound p ≤ smallCovBound 2 + smallCovBound 3` for the two primes below `5`. -/
theorem smallCovBound_le_add_of_lt_five (hp : p < 5) :
    smallCovBound p ≤ smallCovBound 2 + smallCovBound 3 := by
  rcases prime_eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with rfl | rfl | h
  · linarith [smallCovBound_nonneg (p := 3)]
  · linarith [smallCovBound_nonneg (p := 2)]
  · omega

end Small

/-! ### The absolute constant and the decay bound -/

/-- `9 (smallCovBound 2 + smallCovBound 3)`, the contribution of the primes `2` and `3` to the
decay constant; the `9` covers the factor `1/q² ≥ 1/9` at `q ∈ {2, 3}`. -/
noncomputable def smallCovConst : ℝ := 9 * (smallCovBound 2 + smallCovBound 3)

/-- `0 ≤ smallCovConst`. -/
theorem smallCovConst_nonneg : 0 ≤ smallCovConst := by
  have h2 := smallCovBound_nonneg (p := 2)
  have h3 := smallCovBound_nonneg (p := 3)
  rw [smallCovConst]
  linarith

/-- **The absolute constant of the covariance decay bound**,
`(63504 + smallCovConst) · ∑_p p⁻² + 1`. -/
noncomputable def covDecayConstU : ℝ := (63504 + smallCovConst) * primeInvSqSum + 1

/-- `0 < covDecayConstU`. -/
theorem covDecayConstU_pos : 0 < covDecayConstU := by
  have hS := primeInvSqSum_nonneg
  have hc := smallCovConst_nonneg
  have : 0 ≤ (63504 + smallCovConst) * primeInvSqSum := by positivity
  rw [covDecayConstU]
  linarith

section Main

variable {ℓ ℓ' : ℕ}

/-- **The per-prime bound at `p ≥ 5`.**
`|C_p| ≤ μ_{p,ℓ} μ_{p,ℓ'} ≤ B(ℓ) B(ℓ') p^{-4} ≤ B(ℓ) B(ℓ')/4 · p^{-2}`, where `B = momentDecay`. -/
theorem abs_localCov_le_momentDecay_of_five_le {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    |localCov p ℓ ℓ'| ≤ momentDecay ℓ * momentDecay ℓ' / 4 * (1 / (p : ℝ) ^ 2) := by
  have hlaw := hasTailGeometricLaw_of_five_le (p := p) hp
  have hd1 := momentDecay_nonneg ℓ
  have hd2 := momentDecay_nonneg ℓ'
  have hx : (p : ℝ)⁻¹ ≤ 1 / 2 := inv_cast_prime_le_half
  have hx0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hxs : ((p : ℝ)⁻¹) ^ 2 ≤ 1 / 4 := by nlinarith
  rw [one_div, ← inv_pow]
  calc |localCov p ℓ ℓ'|
      ≤ valuationMoment p ℓ * valuationMoment p ℓ' :=
        abs_localCov_le_valuationMoment_mul (hasLocalCovInputs_of_five_le hp) hℓ hℓ' hne
    _ ≤ (momentDecay ℓ * ((p : ℝ)⁻¹) ^ 2) * (momentDecay ℓ' * ((p : ℝ)⁻¹) ^ 2) :=
        mul_le_mul (valuationMoment_le_momentDecay hlaw hℓ)
          (valuationMoment_le_momentDecay hlaw hℓ') (valuationMoment_nonneg ℓ') (by positivity)
    _ = (momentDecay ℓ * momentDecay ℓ') * (((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ 2) := by ring
    _ ≤ (momentDecay ℓ * momentDecay ℓ') * (((p : ℝ)⁻¹) ^ 2 * (1 / 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxs (by positivity)) (by positivity)
    _ = momentDecay ℓ * momentDecay ℓ' / 4 * ((p : ℝ)⁻¹) ^ 2 := by ring

/-- **The per-prime bound at `p < 5`.** For a prime `p < 5` and distinct primes `ℓ ≠ ℓ'`,
`|localCov p ℓ ℓ'| ≤ smallCovConst / (ℓ ℓ')² · (1 / p²)`. -/
theorem abs_localCov_le_smallCovConst_of_lt_five {p : ℕ} [Fact p.Prime] (hp : p < 5)
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    |localCov p ℓ ℓ'| ≤ smallCovConst / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 * (1 / (p : ℝ) ^ 2) := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
  have hℓ0' : (0 : ℝ) < (ℓ' : ℝ) := by exact_mod_cast hℓ'.pos
  have hpos : (0 : ℝ) < ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by positivity
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp9 : (p : ℝ) ^ 2 ≤ 9 := by
    rcases prime_eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with rfl | rfl | h
    · norm_num
    · norm_num
    · omega
  have h2 := smallCovBound_nonneg (p := 2)
  have h3 := smallCovBound_nonneg (p := 3)
  calc |localCov p ℓ ℓ'| ≤ smallCovBound p / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 :=
        abs_localCov_le_smallCovBound hℓ hℓ' hne
    _ ≤ (smallCovBound 2 + smallCovBound 3) / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 * 1 := by
        rw [mul_one]
        exact div_le_div_of_nonneg_right (smallCovBound_le_add_of_lt_five hp) hpos.le
    _ ≤ (smallCovBound 2 + smallCovBound 3) / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 * (9 * (1 / (p : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (by rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith)
          (by positivity)
    _ = smallCovConst / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 * (1 / (p : ℝ) ^ 2) := by
        rw [smallCovConst]
        ring

/-- `(B(ℓ) B(ℓ')/4 + smallCovConst/(ℓℓ')²) (ℓℓ')² ≤ 504²/4 + smallCovConst`, where
`B = momentDecay`. -/
theorem momentDecay_add_smallCovConst_mul_sq_le (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) :
    (momentDecay ℓ * momentDecay ℓ' / 4 + smallCovConst / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2)
      * ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 ≤ 63504 + smallCovConst := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
  have hℓ0' : (0 : ℝ) < (ℓ' : ℝ) := by exact_mod_cast hℓ'.pos
  have hpos : (0 : ℝ) < ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by positivity
  have hd2 := momentDecay_nonneg ℓ'
  have hmul : (momentDecay ℓ * (ℓ : ℝ) ^ 2) * (momentDecay ℓ' * (ℓ' : ℝ) ^ 2) ≤ 504 * 504 :=
    mul_le_mul (momentDecay_mul_sq_le hℓ) (momentDecay_mul_sq_le hℓ') (by positivity) (by norm_num)
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  linarith

/-- **The covariance decay bound.** For every pair of distinct primes `ℓ ≠ ℓ'` the series
`∑_p C_p(ℓ, ℓ')` converges absolutely and

  `∑_p |C_p(ℓ, ℓ')| ≤ covDecayConstU / (ℓℓ')²`. -/
theorem tsum_abs_localCov_le (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
      (∑' q : {n : ℕ // n.Prime}, |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|)
        ≤ covDecayConstU / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by
  have habs := summable_abs_localCov hℓ hℓ' hne
  refine ⟨habs, ?_⟩
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
  have hℓ0' : (0 : ℝ) < (ℓ' : ℝ) := by exact_mod_cast hℓ'.pos
  have hpos : (0 : ℝ) < ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by positivity
  have hd1 := momentDecay_nonneg ℓ
  have hd2 := momentDecay_nonneg ℓ'
  have hcn := smallCovConst_nonneg
  have hM0 : 0 ≤ momentDecay ℓ * momentDecay ℓ' / 4 := by positivity
  have hE0 : 0 ≤ smallCovConst / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by positivity
  have hterm : ∀ q : {n : ℕ // n.Prime}, |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|
      ≤ (momentDecay ℓ * momentDecay ℓ' / 4 + smallCovConst / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2)
        * (1 / ((q : ℕ) : ℝ) ^ 2) := by
    intro q
    have hq : Fact (q : ℕ).Prime := ⟨q.2⟩
    rcases Nat.lt_or_ge (q : ℕ) 5 with hq5 | hq5
    · exact (abs_localCov_le_smallCovConst_of_lt_five hq5 hℓ hℓ' hne).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · exact (abs_localCov_le_momentDecay_of_five_le hq5 hℓ hℓ' hne).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hcmp := habs.tsum_le_tsum hterm (summable_primeInvSq.mul_left _)
  rw [tsum_mul_left, show (∑' q : {n : ℕ // n.Prime}, 1 / ((q : ℕ) : ℝ) ^ 2) = primeInvSqSum from
    rfl] at hcmp
  refine hcmp.trans ?_
  rw [le_div_iff₀ hpos, covDecayConstU]
  nlinarith [mul_le_mul_of_nonneg_right (momentDecay_add_smallCovConst_mul_sq_le hℓ hℓ')
    primeInvSqSum_nonneg]

/-- There is an absolute constant `C > 0` such that, for every pair of distinct primes `ℓ ≠ ℓ'`,

  `∑_p |C_p(ℓ, ℓ')| ≤ C/(ℓℓ')²`,

the series converging absolutely. -/
@[bsd_tamagawa "T056"]
theorem exists_covariance_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
        (∑' q : {n : ℕ // n.Prime}, |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|)
          ≤ C / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 :=
  ⟨covDecayConstU, covDecayConstU_pos, fun _ _ hℓ hℓ' hne => tsum_abs_localCov_le hℓ hℓ' hne⟩

/-! ### The covariance of the limiting Tamagawa distribution -/

/-- **`|∑_q C_q(ℓ, ℓ')| ≤ covDecayConstU/(ℓℓ')²`** for distinct primes `ℓ ≠ ℓ'`. -/
theorem abs_tsum_localCov_le (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    |∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|
      ≤ covDecayConstU / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by
  obtain ⟨habs, hbd⟩ := tsum_abs_localCov_le hℓ hℓ' hne
  refine le_trans ?_ hbd
  simpa using norm_tsum_le_tsum_norm
    (f := fun q : {n : ℕ // n.Prime} => @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ') (by simpa using habs)

/-- **`|Cov(v_ℓ(Tam), v_{ℓ'}(Tam))| ≤ covDecayConstU/(ℓℓ')²`.** The measure is the joint valuation
law `P_{{ℓ,ℓ'}}` and the two random variables are the `ℓ`- and `ℓ'`-coordinates of
`ℤ_{≥0}^{{ℓ,ℓ'}}`. -/
theorem abs_covariance_tamagawaValuation_le (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
        (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
        (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
      ≤ covDecayConstU / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by
  rw [(covariance_tamagawaValuation hℓ hℓ' hne).right]
  exact abs_tsum_localCov_le hℓ hℓ' hne

/-- There is an absolute constant `C > 0` such that, for every pair of distinct primes `ℓ ≠ ℓ'`,

  `|Cov(v_ℓ(Tam(E)), v_{ℓ'}(Tam(E)))| ≤ C/(ℓℓ')²`

in the limiting Tamagawa distribution. -/
@[bsd_tamagawa "T057c"]
theorem exists_covariance_decay_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
        ≤ C / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 :=
  ⟨covDecayConstU, covDecayConstU_pos, fun _ _ hℓ hℓ' hne =>
    abs_covariance_tamagawaValuation_le hℓ hℓ' hne⟩

/-- The covariance tends to `0` as `ℓℓ' → ∞`: for every `ε > 0` there is an `N` such that every
pair of distinct primes with `ℓℓ' ≥ N` has `|Cov(v_ℓ(Tam), v_{ℓ'}(Tam))| < ε`. -/
@[bsd_tamagawa "T057c"]
theorem covariance_tamagawaValuation_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' → N ≤ ℓ * ℓ' →
      |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
        < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (covDecayConstU / ε)
  refine ⟨n + 1, fun ℓ ℓ' hℓ hℓ' hne hN => ?_⟩
  have hbd := abs_covariance_tamagawaValuation_le hℓ hℓ' hne
  have hL1 : ((n : ℝ) + 1) ≤ (ℓ : ℝ) * (ℓ' : ℝ) := by exact_mod_cast hN
  have hL0 : (1 : ℝ) ≤ (ℓ : ℝ) * (ℓ' : ℝ) := by linarith
  have hsq : ((n : ℝ) + 1) ≤ ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := by nlinarith
  have hlt : covDecayConstU / ε < ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2 := lt_of_lt_of_le hn (by linarith)
  exact hbd.trans_lt ((div_lt_iff₀ hpos).2 (by linarith [(div_lt_iff₀ hε).1 hlt]))

end Main

end WeierstrassCurve
