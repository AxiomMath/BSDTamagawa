/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.BivariateValuationSum
public import BSDTamagawa.Covariance.FormulaConditional
public import BSDTamagawa.LocalDensity.HeadDensityTwoBound

/-!
# Negativity of the local covariance at `(ℓ, ℓ') = (2, 3)`

For a prime `p`, the local covariance `C_p(2, 3)` is negative under two hypotheses: the tail law
`HasTailConstantLaw p`, that `δ_p(t) = α_p p^{-t}` for `t ≥ 5` with `1/88572 ≤ α_p < 1/2`,
`α_2 ≤ 1/2046` and `α_3 ≤ 1/88572`; and the head-sum lower bounds `1/(2p²) ≤ A_{p,2}` and
`1/(3p³) ≤ A_{p,3}`, where `A_{p,r} = ∑_{1 ≤ t ≤ 4} δ_p(t) v_r(t)`. The cross-moment is at most
`α_p p^{-6}/(1 - p^{-6})²`, the product of the marginal moments is at least `1/(6p⁵)`, and
`6 α_p p^{11} < (p⁶ - 1)²`.

The file also proves the estimates shared by the other pairs: for distinct primes `ℓ, ℓ'` the
cross-moment is at most `α_p p^{ℓℓ'}/(p^{ℓℓ'} - 1)²`, and for a prime `r ≥ 5` the marginal moment
satisfies `μ_{p,r} ≥ α_p p^{-r}`.

## Main definitions

* `WeierstrassCurve.HasTailConstantLaw`: the geometric tail law for `δ_p` with the bounds on its
  constant.
* `WeierstrassCurve.HasLocalCovInputs`: `HasTailConstantLaw p` together with the two head-sum lower
  bounds.

## Main results

* `WeierstrassCurve.crossValuationMoment_le_crossBound`: the upper bound on the cross-moment.
* `WeierstrassCurve.tsum_le_valuationMoment_of_geom`: `μ_{p,r} ≥ α_p p^{-r}` for a prime `r ≥ 5`.
* `WeierstrassCurve.localCov_two_three_neg_of_inputs`: `C_p(2, 3) < 0` under the hypotheses above.

## Implementation notes

`localCov` is real-valued, being possibly negative. The real `tsum` of a non-summable family is
`0`, so the lower bounds on the marginal moments are proved from the summability of the
corresponding families.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped ENNReal
open BSDTamagawa

variable {p : ℕ} [Fact p.Prime]

/-! ### The hypotheses -/

/-- There is a constant `α_p` with `δ_p(t) = α_p p^{-t}` for every `t ≥ 5`, subject to
`1/88572 ≤ α_p < 1/2`, `α_2 ≤ 1/2046` and `α_3 ≤ 1/88572`. -/
def HasTailConstantLaw (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ a : ℝ≥0∞, (∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) ∧
    a < 1 / 2 ∧ 1 / 88572 ≤ a ∧ (p = 2 → a ≤ 1 / 2046) ∧ (p = 3 → a ≤ 1 / 88572)

/-- `HasTailConstantLaw p` together with the head-sum lower bounds `1/(2p²) ≤ A_{p,2}` and
`1/(3p³) ≤ A_{p,3}`. -/
def HasLocalCovInputs (p : ℕ) [Fact p.Prime] : Prop :=
  HasTailConstantLaw p ∧ 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2 ∧
    1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3

/-- `HasTailConstantLaw p` implies `HasTailGeometricLaw p`. -/
theorem hasTailGeometricLaw_of_hasTailConstantLaw (h : HasTailConstantLaw p) :
    HasTailGeometricLaw p := by
  obtain ⟨a, hgeom, hlt, -, -, -⟩ := h
  exact ⟨a, hlt.le.trans (by norm_num), hgeom⟩

/-! ### Elementary facts about the modulus and the constant -/

/-- `2 ≤ (p : ℝ)` for a prime `p`. -/
theorem two_le_cast_prime : (2 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast (Fact.out : p.Prime).two_le

/-- A prime is `2`, is `3`, or is at least `5`. -/
theorem prime_eq_two_or_eq_three_or_five_le {q : ℕ} (hq : q.Prime) : q = 2 ∨ q = 3 ∨ 5 ≤ q := by
  rcases lt_or_ge q 5 with h | h
  · have h2 := hq.two_le
    interval_cases q
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hq (by decide)
  · exact Or.inr (Or.inr h)

/-- `2 ≤ P ^ n` for `2 ≤ P` and `n ≥ 1`. -/
theorem two_le_pow_of_two_le {P : ℝ} (hP : 2 ≤ P) {n : ℕ} (hn : 1 ≤ n) : 2 ≤ P ^ n := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    _ ≤ P ^ n := pow_le_pow_left₀ (by norm_num) hP n

/-- `2 ^ n ≤ P ^ n` for `2 ≤ P`. -/
theorem two_pow_le_pow_of_two_le {P : ℝ} (hP : 2 ≤ P) (n : ℕ) : (2 : ℝ) ^ n ≤ P ^ n :=
  pow_le_pow_left₀ (by norm_num) hP n

/-- If `1/88572 ≤ a < 1/2` in `ℝ≥0∞`, then `0 < a.toReal`. -/
theorem toReal_tailConstant_pos {a : ℝ≥0∞} (hlt : a < 1 / 2) (hge : 1 / 88572 ≤ a) :
    0 < a.toReal := by
  refine ENNReal.toReal_pos (fun h => ?_) hlt.ne_top
  rw [h] at hge
  exact absurd hge (by norm_num)

/-- If `a < 1/2` in `ℝ≥0∞`, then `a.toReal < 1/2`. -/
theorem toReal_tailConstant_lt_half {a : ℝ≥0∞} (hlt : a < 1 / 2) : a.toReal < 1 / 2 := by
  simpa using (ENNReal.toReal_lt_toReal hlt.ne_top (by norm_num)).2 hlt

/-- If `1/88572 ≤ a < 1/2` in `ℝ≥0∞`, then `1/88572 ≤ a.toReal`. -/
theorem inv_le_toReal_tailConstant {a : ℝ≥0∞} (hlt : a < 1 / 2) (hge : 1 / 88572 ≤ a) :
    1 / 88572 ≤ a.toReal := by
  simpa using (ENNReal.toReal_le_toReal (by norm_num) hlt.ne_top).2 hge

/-! ### The cross-moment -/

/-- Under the geometric tail law with constant `a`, for distinct primes `ℓ, ℓ'` the cross summand
`δ_p(t) v_ℓ(t) v_{ℓ'}(t)` equals `a · BivariateValuationSum.summand ℓ ℓ' p t`. -/
theorem crossValuationTerm_eq_toReal_mul_summand {a : ℝ≥0∞}
    (hgeom : ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (t : ℕ) :
    crossValuationTerm p ℓ ℓ' t = a.toReal * BivariateValuationSum.summand ℓ ℓ' (p : ℝ) t := by
  rcases lt_or_ge t 5 with ht | ht
  · rw [crossValuationTerm_eq_zero_of_lt_five p hℓ hℓ' hne ht, BivariateValuationSum.summand,
      ite_eq_right (by omega), mul_zero]
  · have hz : (p : ℝ) ^ (-(t : ℤ)) = ((p : ℝ)⁻¹) ^ t := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [crossValuationTerm, hgeom t ht, BivariateValuationSum.summand, ite_eq_left ht, hz,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring

/-- For `2 ≤ P` and `n ≥ 1`, `P^{-n}/(1 - P^{-n})² = P^n/(P^n - 1)²`. -/
theorem zpow_neg_div_one_sub_sq {P : ℝ} (hP : 2 ≤ P) {n : ℕ} (hn : 1 ≤ n) :
    P ^ (-(n : ℤ)) / (1 - P ^ (-(n : ℤ))) ^ 2 = P ^ n / (P ^ n - 1) ^ 2 := by
  have h2 : (2 : ℝ) ≤ P ^ n := two_le_pow_of_two_le hP hn
  have hne : P ^ n ≠ 0 := by positivity
  have hne' : P ^ n - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [zpow_neg, zpow_natCast]
  field_simp

/-- Under the geometric tail law with constant `a`, for distinct primes `ℓ, ℓ'` the cross-moment is
at most `a · p^{ℓℓ'}/(p^{ℓℓ'} - 1)²`. -/
theorem crossValuationMoment_le_crossBound {a : ℝ≥0∞}
    (hgeom : ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    crossValuationMoment p ℓ ℓ'
      ≤ a.toReal * ((p : ℝ) ^ (ℓ * ℓ') / ((p : ℝ) ^ (ℓ * ℓ') - 1) ^ 2) := by
  have hone : 1 ≤ ℓ * ℓ' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hℓ.ne_zero hℓ'.ne_zero)
  have hbound :=
    BSDTamagawa.BivariateValuationSum.main_theorem ℓ ℓ' hℓ hℓ' hne (p : ℝ) two_le_cast_prime
  rw [← Nat.cast_mul, zpow_neg_div_one_sub_sq (P := (p : ℝ)) two_le_cast_prime hone] at hbound
  calc crossValuationMoment p ℓ ℓ'
      = ∑' t : ℕ, a.toReal * BivariateValuationSum.summand ℓ ℓ' (p : ℝ) t :=
        tsum_congr fun t => crossValuationTerm_eq_toReal_mul_summand hgeom hℓ hℓ' hne t
    _ = a.toReal * ∑' t : ℕ, BivariateValuationSum.summand ℓ ℓ' (p : ℝ) t := tsum_mul_left
    _ ≤ a.toReal * ((p : ℝ) ^ (ℓ * ℓ') / ((p : ℝ) ^ (ℓ * ℓ') - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg

/-! ### Lower bounds on the marginal moments -/

/-- The head sum `A_{p,r}` is finite: each of its four terms is `δ_p(t) ≤ 1` times a natural. -/
theorem headSum_ne_top (r : ℕ) : headSum p r ≠ ⊤ := by
  rw [headSum]
  exact (ENNReal.sum_lt_top.2 fun t _ => lt_top_iff_ne_top.2 (δ_mul_natCast_ne_top p t _)).ne

/-- Under the geometric tail law, `A_{p,r} ≤ μ_{p,r}` for a prime `r`. -/
theorem toReal_headSum_le_valuationMoment (h : HasTailGeometricLaw p) {r : ℕ} (hr : r.Prime) :
    (headSum p r).toReal ≤ valuationMoment p r := by
  have hs := summable_valuationTerm_of_tailLaw h hr
  rw [headSum, ENNReal.toReal_sum fun t _ => δ_mul_natCast_ne_top p t _]
  calc ∑ t ∈ Finset.Icc 1 4, (δ p t * (padicValNat r t : ℝ≥0∞)).toReal
      = ∑ t ∈ Finset.Icc 1 4, valuationTerm p r t :=
        Finset.sum_congr rfl fun t _ => (valuationTerm_eq_toReal p r t).symm
    _ ≤ ∑' t : ℕ, valuationTerm p r t :=
        hs.sum_le_tsum _ fun t _ => valuationTerm_nonneg p r t

/-- Under the geometric tail law with constant `a`, for a prime `r ≥ 5` the marginal moment
satisfies `a p^{-r} ≤ μ_{p,r}`. -/
theorem tsum_le_valuationMoment_of_geom (h : HasTailGeometricLaw p) {a : ℝ≥0∞}
    (hgeom : ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) : a.toReal / (p : ℝ) ^ r ≤ valuationMoment p r := by
  have hs := summable_valuationTerm_of_tailLaw h hr
  have hval : valuationTerm p r r = a.toReal / (p : ℝ) ^ r := by
    rw [valuationTerm, hgeom r hr5, padicValNat.self hr.one_lt, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [inv_pow, Nat.cast_one, mul_one, div_eq_mul_inv]
  exact hval ▸ hs.le_tsum r fun j _ => valuationTerm_nonneg p r j

/-- Under the geometric tail law, `1/(2p²) ≤ A_{p,2}` implies `1/(2p²) ≤ μ_{p,2}`. -/
theorem inv_two_mul_sq_le_valuationMoment_two (h : HasTailGeometricLaw p)
    (hA : 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2) :
    1 / (2 * (p : ℝ) ^ 2) ≤ valuationMoment p 2 := by
  have hfin : (1 : ℝ≥0∞) / (2 * (p : ℝ≥0∞) ^ 2) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ENNReal.one_ne_top ?_).ne
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
  have h1 := (ENNReal.toReal_le_toReal hfin (headSum_ne_top 2)).2 hA
  have h2 : ((1 : ℝ≥0∞) / (2 * (p : ℝ≥0∞) ^ 2)).toReal = 1 / (2 * (p : ℝ) ^ 2) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    norm_num
  rw [h2] at h1
  exact h1.trans (toReal_headSum_le_valuationMoment h Nat.prime_two)

/-- Under the geometric tail law, `1/(3p³) ≤ A_{p,3}` implies `1/(3p³) ≤ μ_{p,3}`. -/
theorem inv_three_mul_cube_le_valuationMoment_three (h : HasTailGeometricLaw p)
    (hA : 1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3) :
    1 / (3 * (p : ℝ) ^ 3) ≤ valuationMoment p 3 := by
  have hfin : (1 : ℝ≥0∞) / (3 * (p : ℝ≥0∞) ^ 3) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ENNReal.one_ne_top ?_).ne
    exact mul_ne_zero three_ne_zero
      (pow_ne_zero 3 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
  have h1 := (ENNReal.toReal_le_toReal hfin (headSum_ne_top 3)).2 hA
  have h2 : ((1 : ℝ≥0∞) / (3 * (p : ℝ≥0∞) ^ 3)).toReal = 1 / (3 * (p : ℝ) ^ 3) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    norm_num
  rw [h2] at h1
  exact h1.trans (toReal_headSum_le_valuationMoment h Nat.prime_three)

/-- `0 ≤ μ_{p,r}`: a `tsum` of nonnegative terms. -/
theorem valuationMoment_nonneg (r : ℕ) : 0 ≤ valuationMoment p r :=
  tsum_nonneg fun t => valuationTerm_nonneg p r t

/-- For `Z ≥ 2` and `D > 0`, `D·c·Z < N·(Z-1)²` implies `c·Z/(Z-1)² < N/D`. -/
theorem mul_div_sq_lt_div {Z c N D : ℝ} (hZ : 2 ≤ Z) (hD : 0 < D)
    (h : D * (c * Z) < N * (Z - 1) ^ 2) : c * (Z / (Z - 1) ^ 2) < N / D := by
  have h1 : (0 : ℝ) < Z - 1 := by linarith
  have hd : (0 : ℝ) < (Z - 1) ^ 2 := by positivity
  have hid : N / D - c * (Z / (Z - 1) ^ 2)
      = (N * (Z - 1) ^ 2 - D * (c * Z)) / (D * (Z - 1) ^ 2) := by
    field_simp
  have hpos : 0 < (N * (Z - 1) ^ 2 - D * (c * Z)) / (D * (Z - 1) ^ 2) :=
    div_pos (by linarith) (by positivity)
  rw [← hid] at hpos
  linarith

/-! ### The negativity criterion -/

/-- `C_p(ℓ, ℓ') < 0` if and only if the cross-moment is strictly below `μ_{p,ℓ} μ_{p,ℓ'}`. -/
theorem localCov_neg_iff (ℓ ℓ' : ℕ) :
    localCov p ℓ ℓ' < 0 ↔
      crossValuationMoment p ℓ ℓ' < valuationMoment p ℓ * valuationMoment p ℓ' := by
  rw [localCov, sub_neg]

/-! ### The case `(ℓ, ℓ') = (2, 3)` -/

/-- `6 c P^{11} < (P⁶ - 1)²` for `c > 0` in each of the cases `P = 2, c ≤ 1/2046`;
`P = 3, c ≤ 1/88572`; and `P ≥ 5, c < 1/2`. -/
theorem six_mul_pow_eleven_lt {P c : ℝ} (hc : 0 < c)
    (hcase : P = 2 ∧ c ≤ 1 / 2046 ∨ P = 3 ∧ c ≤ 1 / 88572 ∨ 5 ≤ P ∧ c < 1 / 2) :
    6 * c * P ^ 11 < (P ^ 6 - 1) ^ 2 := by
  rcases hcase with ⟨rfl, hc2⟩ | ⟨rfl, hc3⟩ | ⟨hP, hch⟩
  · nlinarith
  · nlinarith
  · have hP0 : (0 : ℝ) < P := by linarith
    have h5 : (3125 : ℝ) ≤ P ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hP 5]
    have h6 : (0 : ℝ) < P ^ 6 := by positivity
    have hA : (0 : ℝ) < P ^ 5 * (P - 3) - 2 := by nlinarith
    nlinarith [mul_pos h6 hA]

/-- Under `HasTailConstantLaw p` and the head-sum bounds `1/(2p²) ≤ A_{p,2}` and
`1/(3p³) ≤ A_{p,3}`, `C_p(2, 3) < 0`. -/
theorem localCov_two_three_neg_of_inputs (h : HasTailConstantLaw p)
    (hA2 : 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2)
    (hA3 : 1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3) : localCov p 2 3 < 0 := by
  have hlaw := hasTailGeometricLaw_of_hasTailConstantLaw h
  obtain ⟨a, hgeom, hlt, hge, h2, h3⟩ := h
  set P : ℝ := (p : ℝ) with hPdef
  set c : ℝ := a.toReal
  have hP : (2 : ℝ) ≤ P := two_le_cast_prime
  have hc0 : 0 < c := toReal_tailConstant_pos hlt hge
  have hcross : crossValuationMoment p 2 3 ≤ c * (P ^ 6 / (P ^ 6 - 1) ^ 2) := by
    simpa using crossValuationMoment_le_crossBound hgeom Nat.prime_two Nat.prime_three
      (by norm_num)
  have hμ2 : 1 / (2 * P ^ 2) ≤ valuationMoment p 2 := inv_two_mul_sq_le_valuationMoment_two hlaw hA2
  have hμ3 : 1 / (3 * P ^ 3) ≤ valuationMoment p 3 :=
    inv_three_mul_cube_le_valuationMoment_three hlaw hA3
  have hprod : 1 / (6 * P ^ 5) ≤ valuationMoment p 2 * valuationMoment p 3 := by
    calc 1 / (6 * P ^ 5) = 1 / (2 * P ^ 2) * (1 / (3 * P ^ 3)) := by
          field_simp
          ring
      _ ≤ valuationMoment p 2 * valuationMoment p 3 :=
          mul_le_mul hμ2 hμ3 (by positivity) (le_trans (by positivity) hμ2)
  have hcase : P = 2 ∧ c ≤ 1 / 2046 ∨ P = 3 ∧ c ≤ 1 / 88572 ∨ 5 ≤ P ∧ c < 1 / 2 := by
    rcases prime_eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with hq | hq | hq
    · exact Or.inl ⟨by rw [hPdef, hq]; norm_num,
        by simpa using ENNReal.toReal_mono (by norm_num) (h2 hq)⟩
    · exact Or.inr (Or.inl ⟨by rw [hPdef, hq]; norm_num,
        by simpa using ENNReal.toReal_mono (by norm_num) (h3 hq)⟩)
    · exact Or.inr (Or.inr ⟨by rw [hPdef]; exact_mod_cast hq, toReal_tailConstant_lt_half hlt⟩)
  have hnum : c * (P ^ 6 / (P ^ 6 - 1) ^ 2) < 1 / (6 * P ^ 5) := by
    refine mul_div_sq_lt_div (two_le_pow_of_two_le hP (by norm_num)) (by positivity) ?_
    calc 6 * P ^ 5 * (c * P ^ 6) = 6 * c * P ^ 11 := by ring
      _ < (P ^ 6 - 1) ^ 2 := six_mul_pow_eleven_lt hc0 hcase
      _ = 1 * (P ^ 6 - 1) ^ 2 := (one_mul _).symm
  rw [localCov_neg_iff]
  exact hcross.trans_lt (hnum.trans_le hprod)

/-- Under `HasLocalCovInputs p`, `C_p(2, 3) < 0`. -/
theorem localCov_two_three_neg (h : HasLocalCovInputs p) : localCov p 2 3 < 0 :=
  localCov_two_three_neg_of_inputs h.1 h.2.1 h.2.2

end WeierstrassCurve
