/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.LocalDensity.PrimeSquareTail
public import BSDTamagawa.Equidistribution.ExceptionalTail

/-!
# The limsup of the tail of exceptional reduction types

For the family of nonsingular integral short Weierstrass curves `E(a₄,a₆) : y² = x³ + a₄x + a₆`,
the contribution, among curves of height `≤ X`, of the primes `p > Y` at which the local reduction
datum `τ_p(E)` is not one of the trivial types in `𝒦₀ = {(I₀,1), (I₁,1)}` satisfies

  `limsup_{X→∞} (1/N(X)) ∑_{Ht(E)≤X} ∑_{p>Y} 𝟙_{τ_p(E)∉𝒦₀} ≪ ∑_{p>Y} 1/p²`,

and the right-hand side tends to `0` as `Y → ∞`.

For a prime `p ≥ 5`, `τ_p(E) ∉ 𝒦₀` forces `p² ∣ 4a₄³ + 27a₆²`, a nonzero integer of absolute value
at most `2X`, so only the primes `Y < p ≤ √(2X)` contribute. Summing the per-prime bound
`C (1/p² + 1/(p X^{1/3}) + 1/X^{1/2})` over these primes gives the main term `∑_{p>Y} 1/p²` and two
error terms, `X^{-1/3} ∑_{p ≤ √(2X)} 1/p` and `X^{-1/2} π(√(2X))`, which tend to `0`.

## Main definitions

* `ShortWeierstrassReductionStatistics.excPrimeSum`: the double sum `∑_{p > Y} N^exc_p(X)`.

## Main results

* `ShortWeierstrassReductionStatistics.exc_implies_p2_dvd`: for `p ≥ 5`, `τ_p(E) ∉ 𝒦₀` implies
  `p² ∣ 4a₄³ + 27a₆²`.
* `ShortWeierstrassReductionStatistics.limsup_excPrimeSum_le`: the limsup bound.
* `ShortWeierstrassReductionStatistics.main_statement`: the limsup bound together with
  `∑_{p>Y} 1/p² → 0`.

## References

* J. E. Cremona, M. Sadek, *Local and global densities for Weierstrass models of elliptic curves*,
  Math. Res. Lett. 30 (2023).
-/

@[expose] public section

open WeierstrassCurve
open BSDTamagawa.PrimeSqTail

namespace ShortWeierstrassReductionStatistics

/-! ## The double sum over the primes `p > Y` -/

/-- `exceptionalCount p X` for a prime `p`, and `0` otherwise. -/
noncomputable def exceptionalCountNat (p : ℕ) (X : ℝ) : ℕ :=
  if h : p.Prime then @exceptionalCount p ⟨h⟩ X else 0

/-- The double sum `∑_{Ht(E)≤X} ∑_{p>Y} 𝟙_{τ_p(E)∉𝒦₀}`, written as `∑_{p > Y} N^exc_p(X)`. -/
noncomputable def excPrimeSum (Y X : ℝ) : ℝ :=
  ∑' p : ℕ, if (Y < (p : ℝ)) then (exceptionalCountNat p X : ℝ) else 0

/-! ## The uniform per-prime tail estimate -/

/-- For a prime `p ≥ 5`, if the local reduction datum of `(a₄, a₆)` at `p` lies outside `𝒦₀`, then
`p² ∣ 4a₄³ + 27a₆²`. -/
lemma exc_implies_p2_dvd (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) (a4 a6 : ℤ)
    (hnk : ((tauZ p a4 a6).kodairaSymbol, (tauZ p a4 a6).tamagawaNumber) ∉ K0) :
    (p : ℤ) ^ 2 ∣ (4 * a4 ^ 3 + 27 * a6 ^ 2) := by
  have hdvdΔ : (p : ℤ) ^ 2 ∣ (ofShortNF a4 a6).Δ := by
    by_contra h
    exact hnk (tauZ_mem_K0_of_not_sq_dvd p a4 a6 h)
  rw [ofShortNF_Δ_eq] at hdvdΔ
  have hcop : IsCoprime ((p : ℤ) ^ 2) (-16) := by
    have hpprime : Nat.Prime p := Fact.out
    have hpnd16 : ¬ (p : ℤ) ∣ (16 : ℤ) := by
      intro hd
      have hd' : p ∣ 16 := by exact_mod_cast hd
      have hle : p ≤ 16 := Nat.le_of_dvd (by norm_num) hd'
      interval_cases p <;> revert hd' hpprime <;> decide
    exact ((Nat.prime_iff_prime_int.mp hpprime).coprime_iff_not_dvd.mpr
      (by simpa using hpnd16)).pow_left
  exact hcop.dvd_of_dvd_mul_left hdvdΔ

/-- A pair of height `≤ X` has `|4a₄³ + 27a₆²| ≤ 2X`. -/
lemma disc_abs_le_two_mul (a4 a6 : ℤ) (X : ℝ)
    (hX : (integralShortNFHeight a4 a6 : ℝ) ≤ X) :
    |(4 * a4 ^ 3 + 27 * a6 ^ 2 : ℤ)| ≤ 2 * X := by
  rw [integralShortNFHeight_eq, Int.cast_max] at hX
  have h4 : ((4 * (a4.natAbs : ℤ) ^ 3 : ℤ) : ℝ) ≤ X := (le_max_left _ _).trans hX
  have h27 : ((27 * a6 ^ 2 : ℤ) : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hbound : (|(4 * a4 ^ 3 + 27 * a6 ^ 2 : ℤ)| : ℤ)
      ≤ (4 * (a4.natAbs : ℤ) ^ 3) + (27 * a6 ^ 2) := by
    rw [← Int.abs_eq_natAbs]
    calc |(4 * a4 ^ 3 + 27 * a6 ^ 2 : ℤ)|
        ≤ |(4 * a4 ^ 3 : ℤ)| + |(27 * a6 ^ 2 : ℤ)| := abs_add_le _ _
      _ = 4 * |a4| ^ 3 + 27 * a6 ^ 2 := by
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (sq_nonneg a6),
            show |(4:ℤ)| = 4 from rfl, show |(27:ℤ)| = 27 from rfl]
  have hbound' : (|(4 * a4 ^ 3 + 27 * a6 ^ 2 : ℤ)| : ℝ)
      ≤ ((4 * (a4.natAbs : ℤ) ^ 3 : ℤ) : ℝ) + ((27 * a6 ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast hbound
  push_cast at h4 h27 hbound' ⊢
  linarith

/-- For a prime `p ≥ 5` with `2X < p²`, `exceptionalCount p X = 0`. -/
lemma Ncount_eq_zero_of_lt (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) (X : ℝ)
    (hX : 2 * X < (p : ℝ) ^ 2) : exceptionalCount p X = 0 := by
  unfold exceptionalCount
  have hempty : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily ∧
      ((tauZ p q.1 q.2).kodairaSymbol, (tauZ p q.1 q.2).tamagawaNumber) ∉ K0} = ∅ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hHt, hfam, hnk⟩
    have hne : (4 * q.1 ^ 3 + 27 * q.2 ^ 2 : ℤ) ≠ 0 := (ofShortNF_Δ_ne_zero_iff q.1 q.2).mp hfam
    have hdvd : (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2) :=
      exc_implies_p2_dvd p hp q.1 q.2 hnk
    have hple : (p : ℤ) ^ 2 ≤ |(4 * q.1 ^ 3 + 27 * q.2 ^ 2 : ℤ)| :=
      Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    have hdiscle := disc_abs_le_two_mul q.1 q.2 X hHt
    have hpler : (p : ℝ) ^ 2 ≤ ((|(4 * q.1 ^ 3 + 27 * q.2 ^ 2 : ℤ)| : ℤ) : ℝ) := by
      exact_mod_cast hple
    linarith
  rw [hempty]
  exact Set.ncard_empty _

/-- `N(X) → ∞` as `X → ∞`. -/
lemma Ncount_tendsto_atTop :
    Filter.Tendsto (fun X : ℝ => (integralShortNFCount X : ℝ)) Filter.atTop Filter.atTop := by
  have hlow : Filter.Tendsto
      (fun X : ℝ => ((2 * (WeierstrassCurve.a₄Bound X : ℝ) + 1) *
        (2 * (WeierstrassCurve.a₆Bound X : ℝ) + 1)) / 3)
      Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 3)
    apply Filter.Tendsto.atTop_mul_atTop₀
    · exact Filter.tendsto_atTop_add_const_right _ 1
        (WeierstrassCurve.a₄Bound_real_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))
    · exact Filter.tendsto_atTop_add_const_right _ 1
        (WeierstrassCurve.a₆Bound_real_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  apply Filter.tendsto_atTop_mono' _ _ hlow
  filter_upwards [Filter.eventually_ge_atTop (27:ℝ)] with X hX
  linarith [ShortWeierstrassReductionStatistics.Ncount_ge X hX]

/-! ## Finite support and the `limsup` -/

/-- The primes `p` with `Y < p ≤ √(2X)`. -/
noncomputable def excSupport (Y X : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.sqrt (2 * X)⌋₊ + 1)).filter (fun p => p.Prime ∧ Y < (p : ℝ))

/-- For `Y ≥ 5` and `1 ≤ X`, `excPrimeSum Y X` is the finite sum of `exceptionalCountNat p X` over
`excSupport Y X`. -/
lemma excPrimeSum_eq_finset_sum (Y X : ℝ) (hY : 5 ≤ Y) (hX : 1 ≤ X) :
    excPrimeSum Y X = ∑ p ∈ excSupport Y X, (exceptionalCountNat p X : ℝ) := by
  unfold excPrimeSum
  rw [tsum_eq_sum (s := excSupport Y X) ?_]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp only [excSupport, Finset.mem_filter, Finset.mem_range] at hp
    rw [ite_eq_left hp.2.2]
  · intro p hp
    by_cases hYp : Y < (p : ℝ)
    · rw [ite_eq_left hYp]
      by_cases hpr : p.Prime
      · have : Fact (Nat.Prime p) := ⟨hpr⟩
        have hp5 : 5 ≤ p := by exact_mod_cast (hY.trans_lt hYp).le
        have hge : ⌊Real.sqrt (2 * X)⌋₊ + 1 ≤ p := by
          by_contra hlt
          exact hp (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (not_le.mp hlt), hpr, hYp⟩)
        have hsqlt : Real.sqrt (2 * X) < (p : ℝ) := by
          have h2 : ((⌊Real.sqrt (2 * X)⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast hge
          push_cast at h2
          linarith [Nat.lt_floor_add_one (Real.sqrt (2 * X))]
        have hlt2X : 2 * X < (p : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (2 * X), Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * X)]
        simp [exceptionalCountNat, hpr, Ncount_eq_zero_of_lt p hp5 X hlt2X]
      · simp [exceptionalCountNat, hpr]
    · rw [ite_eq_right hYp]

/-- The sum of `1/p²` over `excSupport Y X` is at most `primeTail Y`. -/
lemma excSupport_sum_inv_sq_le (Y X : ℝ) :
    ∑ p ∈ excSupport Y X, (1 / (p : ℝ) ^ 2) ≤ primeTail Y :=
  sum_inv_sq_le_primeTail _ fun p hp => by
    simpa only [excSupport, Finset.mem_filter, Finset.mem_range] using
      (Finset.mem_filter.mp hp).2

/-- For `1 ≤ X`, the sum of `1/p` over `excSupport Y X` is at most `1 + log (2X)`. -/
lemma excSupport_sum_inv_le (Y X : ℝ) (hX : 1 ≤ X) :
    ∑ p ∈ excSupport Y X, (1 / (p : ℝ)) ≤ 1 + Real.log (2*X) := by
  set M : ℕ := ⌊Real.sqrt (2 * X)⌋₊ with hM
  have hsub : excSupport Y X ⊆ Finset.Icc 1 M := by
    intro p hp
    simp only [excSupport, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.1.one_lt.le, by omega⟩
  have hstep1 :
      ∑ p ∈ excSupport Y X, (1 / (p : ℝ)) ≤ ∑ n ∈ Finset.Icc 1 M, (1 / (n : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
  rw [show ∑ n ∈ Finset.Icc 1 M, (1 / (n : ℝ)) = harmonic M by
    rw [harmonic_eq_sum_Icc]; push_cast [one_div]; rfl] at hstep1
  have hharm : (harmonic M : ℝ) ≤ 1 + Real.log (M : ℝ) := harmonic_le_one_add_log M
  have hMle : (M : ℝ) ≤ 2 * X := by
    calc (M : ℝ) ≤ Real.sqrt (2*X) := Nat.floor_le (Real.sqrt_nonneg _)
      _ ≤ 2 * X := by
        rw [Real.sqrt_le_iff]
        exact ⟨by linarith, by nlinarith⟩
  have hlogle : Real.log (M : ℝ) ≤ Real.log (2*X) := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · rw [hM0]; simpa using Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast hMpos) hMle
  linarith

/-- `X^{-1/3} ∑_{p ∈ excSupport Y X} 1/p → 0` as `X → ∞`. -/
lemma errB_tendsto (Y : ℝ) :
    Filter.Tendsto
      (fun X : ℝ => (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ)))
      Filter.atTop (nhds 0) := by
  set g : ℝ → ℝ := fun X => (1 + Real.log (2*X)) * (1 / X ^ (1 / 3 : ℝ)) with hgdef
  have hinv : Filter.Tendsto (fun X : ℝ => (1 / X ^ (1 / 3 : ℝ))) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (y := (1 / 3 : ℝ)) (by norm_num))
  have hlog : Filter.Tendsto (fun X : ℝ => Real.log X * (1 / X ^ (1 / 3 : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 3)).tendsto_div_nhds_zero
  have hsum : Filter.Tendsto
      (fun X : ℝ => (1 + Real.log 2) * (1 / X ^ (1 / 3 : ℝ))
        + Real.log X * (1 / X ^ (1 / 3 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using (hinv.const_mul (1 + Real.log 2)).add hlog
  have hg0 : Filter.Tendsto g Filter.atTop (nhds 0) := by
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with X hX
    simp only [hgdef, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hX)]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with X hX
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
    rw [hgdef]
    calc (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
        ≤ (1 / X ^ (1 / 3 : ℝ)) * (1 + Real.log (2*X)) :=
          mul_le_mul_of_nonneg_left (excSupport_sum_inv_le Y X hX) (by positivity)
      _ = (1 + Real.log (2*X)) * (1 / X ^ (1 / 3 : ℝ)) := by ring

/-- `X^{-1/2} · #(excSupport Y X) → 0` as `X → ∞`. -/
lemma errE_tendsto (Y : ℝ) :
    Filter.Tendsto
      (fun X : ℝ => (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ))
      Filter.atTop (nhds 0) := by
  set C : ℝ := Real.log 4 + 1 with hC
  set g : ℝ → ℝ := fun X => C * Real.sqrt 2 / Real.log (Real.sqrt (2 * X)) with hgdef
  have hsqrt : Filter.Tendsto (fun X : ℝ => Real.sqrt (2 * X)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  have hloginf : Filter.Tendsto (fun X : ℝ => Real.log (Real.sqrt (2 * X)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hsqrt
  have hg0 : Filter.Tendsto g Filter.atTop (nhds 0) := by
    simpa [hgdef] using hloginf.const_div_atTop (C * Real.sqrt 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with X hX
    positivity
  · have hcheby' : ∀ᶠ X : ℝ in Filter.atTop,
        (↑(⌊Real.sqrt (2 * X)⌋₊.primeCounting) : ℝ)
          ≤ (Real.log 4 + 1) * Real.sqrt (2 * X) / Real.log (Real.sqrt (2 * X)) :=
      hsqrt.eventually (Chebyshev.eventually_primeCounting_le (ε := (1:ℝ)) (by norm_num))
    filter_upwards [hcheby', Filter.eventually_gt_atTop (1 : ℝ)] with X hcx hX1
    have hXpos : 0 < X := by linarith
    have hsub : excSupport Y X ⊆ Nat.primesBelow (⌊Real.sqrt (2 * X)⌋₊ + 1) := by
      intro p hp
      simp only [excSupport, Finset.mem_filter, Finset.mem_range] at hp
      rw [Nat.mem_primesBelow]
      exact ⟨hp.1, hp.2.1⟩
    have hcard : ((excSupport Y X).card : ℝ)
        ≤ (↑(⌊Real.sqrt (2 * X)⌋₊.primeCounting) : ℝ) := by
      have h₁ := Finset.card_le_card hsub
      rw [Nat.primesBelow_card_eq_primeCounting'] at h₁
      exact_mod_cast h₁
    have hrpow : X ^ (1 / 2 : ℝ) = Real.sqrt X := by rw [Real.sqrt_eq_rpow]
    have hsplit : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X :=
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) X
    have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
    have hLpos : 0 < Real.log (Real.sqrt (2 * X)) := by
      apply Real.log_pos
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    calc (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)
        ≤ (1 / X ^ (1 / 2 : ℝ))
            * ((Real.log 4 + 1) * Real.sqrt (2 * X) / Real.log (Real.sqrt (2 * X))) :=
          mul_le_mul_of_nonneg_left (hcard.trans hcx) (by positivity)
      _ = g X := by
          simp only [hgdef, hC, hrpow]
          have hLne := hLpos.ne'
          rw [hsplit]
          field_simp

/-- Given the per-prime bound with constant `C₁`, for `Y ≥ 5`, eventually in `X`,
`(1/N(X)) · excPrimeSum Y X ≤ C₁ (S(X) + B(X) + E(X))`, where `S(X)`, `B(X)`, `E(X)` are the sums
of `1/p²`, `X^{-1/3}/p` and `X^{-1/2}` over `excSupport Y X`. -/
lemma excPrimeSum_div_count_eventually_le (C₁ : ℝ)
    (hbound : ∀ (p : ℕ) [Fact (Nat.Prime p)], 5 ≤ p → ∀ X : ℝ, 4 ≤ X →
      (exceptionalCount p X : ℝ) / (integralShortNFCount X : ℝ) ≤
        C₁ * (1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) + 1 / X ^ (1 / 2 : ℝ)))
    (Y : ℝ) (hY : 5 ≤ Y) :
    ∀ᶠ X in Filter.atTop, (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X ≤
      C₁ * ((∑ p ∈ excSupport Y X, (1 / (p : ℝ) ^ 2))
        + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
        + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ),
    Ncount_tendsto_atTop.eventually_gt_atTop 0] with X hX4 hNX0
  have hX1 : (1 : ℝ) ≤ X := by linarith
  rw [excPrimeSum_eq_finset_sum Y X hY hX1, Finset.mul_sum]
  have hRHS : C₁ * ((∑ p ∈ excSupport Y X, (1 / (p : ℝ) ^ 2))
        + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
        + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ))
      = ∑ p ∈ excSupport Y X,
          C₁ * (1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ))
            + 1 / X ^ (1 / 2 : ℝ)) := by
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      one_div, mul_inv]
    ring_nf
  rw [hRHS]
  refine Finset.sum_le_sum fun p hp => ?_
  simp only [excSupport, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨_, hpr, hpY⟩ := hp
  have : Fact (Nat.Prime p) := ⟨hpr⟩
  have hp5 : 5 ≤ p := by exact_mod_cast (hY.trans_lt hpY).le
  have hNexcN : (exceptionalCountNat p X : ℝ) = (exceptionalCount p X : ℝ) := by
    simp only [exceptionalCountNat, dite_eq_left hpr]
  rw [hNexcN, one_div_mul_eq_div, div_le_iff₀ hNX0]
  have h := hbound p hp5 X hX4
  rw [div_le_iff₀ hNX0] at h
  linarith

/-- There is a constant `C > 0` such that for every `Y ≥ 5`,
`limsup_{X→∞} (1/N(X)) · excPrimeSum Y X ≤ C · primeTail Y`. -/
lemma limsup_excPrimeSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 5 ≤ Y →
      Filter.limsup (fun X : ℝ => (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X)
          Filter.atTop
        ≤ C * primeTail Y := by
  obtain ⟨C₁, hC₁, hbound⟩ := exceptional_ratio_bound
  refine ⟨C₁, hC₁, ?_⟩
  intro Y hY
  set S : ℝ → ℝ := fun X => ∑ p ∈ excSupport Y X, (1 / (p : ℝ) ^ 2)
  set B : ℝ → ℝ := fun X => (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
  set E : ℝ → ℝ := fun X => (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)
  set g : ℝ → ℝ := fun X => C₁ * (S X + B X + E X) with hg
  have hle : ∀ᶠ X in Filter.atTop,
      (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X ≤ g X :=
    excPrimeSum_div_count_eventually_le C₁ hbound Y hY
  have hBE : Filter.Tendsto (fun X => B X + E X) Filter.atTop (nhds 0) := by
    have h1 := (errB_tendsto Y).add (errE_tendsto Y)
    rwa [add_zero] at h1
  set h : ℝ → ℝ := fun X => C₁ * primeTail Y + C₁ * (B X + E X) with hh
  have hgh : ∀ X, g X ≤ h X := by
    intro X
    have hSle : S X ≤ primeTail Y := excSupport_sum_inv_sq_le Y X
    have hgX : g X = C₁ * S X + C₁ * (B X + E X) := by rw [hg]; ring
    rw [hgX, hh]
    have := mul_le_mul_of_nonneg_left hSle hC₁.le
    linarith
  have hconv : Filter.Tendsto h Filter.atTop (nhds (C₁ * primeTail Y)) := by
    simpa [hh] using (tendsto_const_nhds (x := C₁ * primeTail Y)
      (f := Filter.atTop (α := ℝ))).add (hBE.const_mul C₁)
  calc Filter.limsup (fun X : ℝ => (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X)
          Filter.atTop
      ≤ Filter.limsup h Filter.atTop := by
        apply Filter.limsup_le_limsup
        · filter_upwards [hle] with X hX using hX.trans (hgh X)
        · refine Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0) fun X => ?_
          have h1 : (0:ℝ) ≤ 1 / (integralShortNFCount X : ℝ) := by positivity
          have h2 : (0:ℝ) ≤ excPrimeSum Y X := by
            unfold excPrimeSum
            refine tsum_nonneg fun p => ?_
            split
            · positivity
            · exact le_rfl
          positivity
        · exact hconv.isBoundedUnder_le
    _ = C₁ * primeTail Y := hconv.limsup_eq

/-! ## The main statement -/

/-- There is a constant `C > 0` such that for every real `Y ≥ 5`,
`limsup_{X→∞} (1 / N(X)) ∑_{p > Y} N^exc_p(X) ≤ C ∑_{p > Y} 1/p²`, and moreover
`∑_{p > Y} 1/p² → 0` as `Y → ∞`. -/
@[bsd_tamagawa "T030b"]
theorem main_statement :
    (∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 5 ≤ Y →
        Filter.limsup (fun X : ℝ => (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X)
            Filter.atTop
          ≤ C * primeTail Y) ∧
      Filter.Tendsto (fun Y : ℝ => primeTail Y) Filter.atTop (nhds 0) :=
  ⟨limsup_excPrimeSum_le, prime_tail_tendsto_zero⟩

end ShortWeierstrassReductionStatistics
