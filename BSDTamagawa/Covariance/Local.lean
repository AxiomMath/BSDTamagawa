/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.DegreeBound

/-!
# The local covariance `C_p(ℓ, ℓ')`

For a prime `p` and naturals `ℓ, ℓ'`, with `δ_p` the local distribution of `v_p(Δ)` and
`v_ℓ = padicValNat ℓ`, the local covariance is

  `C_p(ℓ, ℓ') = ∑_{t ≥ 1} δ_p(t) v_ℓ(t) v_{ℓ'}(t)
                   - (∑_{t ≥ 1} δ_p(t) v_ℓ(t)) (∑_{t ≥ 1} δ_p(t) v_{ℓ'}(t))`.

For distinct primes `ℓ ≠ ℓ'` no `t < 5` is divisible by both, so the cross-moment is supported on
`t ≥ 5`:

  `∑_{t ≥ 1} δ_p(t) v_ℓ(t) v_{ℓ'}(t) = ∑_{t ≥ 5} δ_p(t) v_ℓ(t) v_{ℓ'}(t)`.

## Main definitions

* `WeierstrassCurve.valuationMoment`: the marginal moment `μ_{p,r} = ∑_{t ≥ 1} δ_p(t) v_r(t)`.
* `WeierstrassCurve.crossValuationMoment`: the cross-moment `∑_{t ≥ 1} δ_p(t) v_ℓ(t) v_{ℓ'}(t)`.
* `WeierstrassCurve.localCov`: the local covariance `C_p(ℓ, ℓ')`.

## Main results

* `WeierstrassCurve.crossValuationMoment_eq_tsum_five_le`: for distinct primes `ℓ ≠ ℓ'` the
  cross-moment equals its restriction to `t ≥ 5`.
* `WeierstrassCurve.localCov_comm`: `C_p(ℓ, ℓ') = C_p(ℓ', ℓ)`.

## Implementation notes

`δ_p(t)` is `ℝ≥0∞`-valued, where subtraction truncates at `0`, while `C_p(ℓ, ℓ')` may be negative.
All quantities are therefore real: `ENNReal.toReal` is applied to `δ_p(t)` inside each summand,
which loses nothing since `δ_p(t) ≤ 1`, and the subtraction in `localCov` takes place in `ℝ`.

The sums are `tsum`s, not `finsum`s, since the support of `δ_p` is infinite. Each real `tsum` is
`0` when its family is not summable; summability follows from finiteness of the corresponding
`ℝ≥0∞` sum (`summable_valuationTerm`, `summable_crossValuationTerm`).

`valuationTerm`, `crossValuationTerm`, `valuationMoment`, `crossValuationMoment` and `localCov` are
defined in `BSDTamagawa.Defs`.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped ENNReal

/-! ### Nonnegativity of the terms -/

/-- Every term of the marginal moment is nonnegative. -/
theorem valuationTerm_nonneg (p : ℕ) [Fact p.Prime] (r t : ℕ) : 0 ≤ valuationTerm p r t :=
  mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- Every term of the cross-moment is nonnegative. -/
theorem crossValuationTerm_nonneg (p : ℕ) [Fact p.Prime] (ℓ ℓ' t : ℕ) :
    0 ≤ crossValuationTerm p ℓ ℓ' t :=
  mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-! ### Comparison with the `ℝ≥0∞`-valued sums -/

/-- For every natural number `n`, `δ_p(t) · n` is finite in `ℝ≥0∞`. -/
theorem δ_mul_natCast_ne_top (p : ℕ) [Fact p.Prime] (t n : ℕ) : δ p t * (n : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (δ_le_one t))
    (ENNReal.natCast_ne_top n)

/-- The real marginal summand is the `toReal` of the `ℝ≥0∞` summand `δ_p(t) v_r(t)`. -/
theorem valuationTerm_eq_toReal (p : ℕ) [Fact p.Prime] (r t : ℕ) :
    valuationTerm p r t = (δ p t * (padicValNat r t : ℝ≥0∞)).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, valuationTerm]

/-- The real cross summand is the `toReal` of the `ℝ≥0∞` summand `δ_p(t) v_ℓ(t) v_{ℓ'}(t)`. -/
theorem crossValuationTerm_eq_toReal (p : ℕ) [Fact p.Prime] (ℓ ℓ' t : ℕ) :
    crossValuationTerm p ℓ ℓ' t
      = (δ p t * (padicValNat ℓ t : ℝ≥0∞) * (padicValNat ℓ' t : ℝ≥0∞)).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    crossValuationTerm]

/-! ### Summability -/

/-- The marginal family is summable as soon as its `ℝ≥0∞` counterpart is finite. -/
theorem summable_valuationTerm (p : ℕ) [Fact p.Prime] (r : ℕ)
    (h : (∑' t : ℕ, δ p t * (padicValNat r t : ℝ≥0∞)) ≠ ⊤) : Summable (valuationTerm p r) :=
  (ENNReal.summable_toReal h).congr fun t => (valuationTerm_eq_toReal p r t).symm

/-- The cross family is summable as soon as its `ℝ≥0∞` counterpart is finite. -/
theorem summable_crossValuationTerm (p : ℕ) [Fact p.Prime] (ℓ ℓ' : ℕ)
    (h : (∑' t : ℕ, δ p t * (padicValNat ℓ t : ℝ≥0∞) * (padicValNat ℓ' t : ℝ≥0∞)) ≠ ⊤) :
    Summable (crossValuationTerm p ℓ ℓ') :=
  (ENNReal.summable_toReal h).congr fun t => (crossValuationTerm_eq_toReal p ℓ ℓ' t).symm

/-! ### The support reduction -/

/-- Two distinct primes have product at least `6`. -/
private lemma six_le_mul_of_ne {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    6 ≤ ℓ * ℓ' := by
  have h2' : 2 ≤ ℓ' := hℓ'.two_le
  rcases eq_or_ne ℓ 2 with rfl | h
  · have := Ne.symm hne
    omega
  · have h2 : 2 ≤ ℓ := hℓ.two_le
    calc 6 = 3 * 2 := by norm_num
      _ ≤ ℓ * ℓ' := Nat.mul_le_mul (by omega) h2'

/-- For distinct primes `ℓ ≠ ℓ'` and `t < 5`, `v_ℓ(t) v_{ℓ'}(t) = 0`. -/
theorem mul_padicValNat_eq_zero_of_lt_five {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') {t : ℕ} (ht : t < 5) : padicValNat ℓ t * padicValNat ℓ' t = 0 := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := Nat.mul_ne_zero_iff.1 hcon
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact h1 (padicValNat_zero_right ℓ)
  have hdvd : ℓ * ℓ' ∣ t :=
    ((Nat.coprime_primes hℓ hℓ').2 hne).mul_dvd_of_dvd_of_dvd
      (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h1))
      (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h2))
  have hle : ℓ * ℓ' ≤ t := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hdvd
  have h6 : 6 ≤ ℓ * ℓ' := six_le_mul_of_ne hℓ hℓ' hne
  omega

/-- Every cross summand below `t = 5` vanishes, for distinct primes `ℓ ≠ ℓ'`. -/
theorem crossValuationTerm_eq_zero_of_lt_five (p : ℕ) [Fact p.Prime] {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') {t : ℕ} (ht : t < 5) : crossValuationTerm p ℓ ℓ' t = 0 := by
  have h : (padicValNat ℓ t : ℝ) * (padicValNat ℓ' t : ℝ) = 0 := by
    exact_mod_cast mul_padicValNat_eq_zero_of_lt_five hℓ hℓ' hne ht
  rw [crossValuationTerm, mul_assoc, h, mul_zero]

/-- For distinct primes `ℓ ≠ ℓ'`,

  `∑_{t ≥ 1} δ_p(t) v_ℓ(t) v_{ℓ'}(t) = ∑_{t ≥ 5} δ_p(t) v_ℓ(t) v_{ℓ'}(t)`,

the restricted range being encoded by zeroing the summand below `t = 5`. -/
@[bsd_tamagawa "T051"]
theorem crossValuationMoment_eq_tsum_five_le (p : ℕ) [Fact p.Prime] {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    crossValuationMoment p ℓ ℓ' = ∑' t : ℕ, if 5 ≤ t then crossValuationTerm p ℓ ℓ' t else 0 := by
  refine tsum_congr fun t => ?_
  rcases le_or_gt 5 t with h | h
  · rw [ite_eq_left h]
  · rw [ite_eq_right (Nat.not_le.2 h), crossValuationTerm_eq_zero_of_lt_five p hℓ hℓ' hne h]

/-! ### Symmetry in `ℓ` and `ℓ'` -/

/-- The cross-moment is symmetric in `ℓ` and `ℓ'`. -/
theorem crossValuationMoment_comm (p : ℕ) [Fact p.Prime] (ℓ ℓ' : ℕ) :
    crossValuationMoment p ℓ ℓ' = crossValuationMoment p ℓ' ℓ :=
  tsum_congr fun t => by rw [crossValuationTerm, crossValuationTerm, mul_right_comm]

/-- `C_p(ℓ, ℓ') = C_p(ℓ', ℓ)`. -/
theorem localCov_comm (p : ℕ) [Fact p.Prime] (ℓ ℓ' : ℕ) : localCov p ℓ ℓ' = localCov p ℓ' ℓ := by
  rw [localCov, localCov, crossValuationMoment_comm, mul_comm (valuationMoment p ℓ)]

end WeierstrassCurve
