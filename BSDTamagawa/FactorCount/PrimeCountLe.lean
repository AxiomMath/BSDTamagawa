/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.MomentsFinite

/-!
# `ω(Tam(E)) ≤ Ω(Tam(E))` in mean under the limiting Tamagawa law

Under the limiting law `P_Tam` of the Tamagawa product,

  `𝔼_{P_Tam}[ω(Tam(E))] := ∑_m P_Tam(m) ω(m) ≤ ∑_m P_Tam(m) Ω(m) =: 𝔼_{P_Tam}[Ω(Tam(E))] < ∞`,

where `ω(m)` is the number of distinct prime divisors of `m` and `Ω(m)` the number counted with
multiplicity. This statistic `ω(Tam(E))` differs from `ω_Tam(E) = #{p : c_p(E) > 1}`: the two are
incomparable in general (`c_2 = c_3 = 2` gives `ω(Tam) = 1 < 2 = ω_Tam`, while `c_2 = 6` gives
`ω(Tam) = 2 > 1 = ω_Tam`).

## Main definitions

* `WeierstrassCurve.cardFactorsTamagawaDensityMean`: the mean `∑_m P_Tam(m) Ω(m)`.
* `WeierstrassCurve.cardDistinctFactorsTamagawaDensityMean`: the mean `∑_m P_Tam(m) ω(m)`.

## Main results

* `WeierstrassCurve.cardFactors_le_self`: `Ω(n) ≤ n`.
* `WeierstrassCurve.cardDistinctFactors_le_cardFactors`: `ω(n) ≤ Ω(n)`.
* `WeierstrassCurve.summable_tamagawaDensity_mul_cardFactors`: `∑_m P_Tam(m) Ω(m) < ∞`.
* `WeierstrassCurve.cardDistinctFactorsTamagawaDensityMean_le`: the inequality of the two means
  together with the finiteness clause.
-/

@[expose] public section

namespace WeierstrassCurve

/-- `Ω(n) ≤ n` for every natural number `n`: for `n ≥ 1` every prime factor is at least `2`, so
`2 ^ Ω(n) ≤ n`, while `Ω(n) < 2 ^ Ω(n)`. -/
theorem cardFactors_le_self (n : ℕ) : (ArithmeticFunction.cardFactors n : ℕ) ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ArithmeticFunction.cardFactors_zero.le
  · rw [ArithmeticFunction.cardFactors_apply]
    refine le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self ?_)
    calc 2 ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
          List.pow_length_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn.ne'

/-- `ω(n) ≤ Ω(n)`: the list of prime factors with multiplicity is at least as long as its
deduplication. -/
theorem cardDistinctFactors_le_cardFactors (n : ℕ) :
    (ArithmeticFunction.cardDistinctFactors n : ℕ) ≤ ArithmeticFunction.cardFactors n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ArithmeticFunction.cardFactors_apply]
  exact (List.dedup_sublist _).length_le

/-- The first moment `∑_m P_Tam(m) m` of the limiting Tamagawa law converges. -/
theorem summable_tamagawaDensity_mul_natCast :
    Summable fun m : ℕ => tamagawaDensity m * (m : ℝ) :=
  (summable_tamagawaDensity_mul_pow 1).congr fun m => by rw [pow_one]

/-- `∑_m P_Tam(m) Ω(m)` converges, by comparison with the first moment, since `Ω(m) ≤ m`. -/
theorem summable_tamagawaDensity_mul_cardFactors :
    Summable fun m : ℕ => tamagawaDensity m * ((ArithmeticFunction.cardFactors m : ℕ) : ℝ) :=
  Summable.of_nonneg_of_le
    (fun m => mul_nonneg (tamagawaDensity_nonneg m) (Nat.cast_nonneg _))
    (fun m => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cardFactors_le_self m))
      (tamagawaDensity_nonneg m))
    summable_tamagawaDensity_mul_natCast

/-- `∑_m P_Tam(m) ω(m)` converges, by comparison with `∑_m P_Tam(m) Ω(m)`. -/
theorem summable_tamagawaDensity_mul_cardDistinctFactors :
    Summable fun m : ℕ =>
      tamagawaDensity m * ((ArithmeticFunction.cardDistinctFactors m : ℕ) : ℝ) :=
  Summable.of_nonneg_of_le
    (fun m => mul_nonneg (tamagawaDensity_nonneg m) (Nat.cast_nonneg _))
    (fun m => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cardDistinctFactors_le_cardFactors m))
      (tamagawaDensity_nonneg m))
    summable_tamagawaDensity_mul_cardFactors

/-- The mean `∑_m P_Tam(m) Ω(m)` of `Ω(Tam(E))` under the limiting Tamagawa law. -/
noncomputable def cardFactorsTamagawaDensityMean : ℝ :=
  ∑' m : ℕ, tamagawaDensity m * ((ArithmeticFunction.cardFactors m : ℕ) : ℝ)

/-- The mean `∑_m P_Tam(m) ω(m)` of `ω(Tam(E))` under the limiting Tamagawa law. -/
noncomputable def cardDistinctFactorsTamagawaDensityMean : ℝ :=
  ∑' m : ℕ, tamagawaDensity m * ((ArithmeticFunction.cardDistinctFactors m : ℕ) : ℝ)

/-- Under the limiting Tamagawa law `P_Tam`,

  `𝔼[ω(Tam(E))] ≤ 𝔼[Ω(Tam(E))] < ∞`:

the inequality of the two means, and the finiteness clause in the form that the series
`∑_m P_Tam(m) Ω(m)` defining the right-hand side converges (its terms are nonnegative, so this is
absolute convergence). -/
@[bsd_tamagawa "T046i"]
theorem cardDistinctFactorsTamagawaDensityMean_le :
    cardDistinctFactorsTamagawaDensityMean ≤ cardFactorsTamagawaDensityMean ∧
      Summable fun m : ℕ => tamagawaDensity m * ((ArithmeticFunction.cardFactors m : ℕ) : ℝ) :=
  ⟨Summable.tsum_le_tsum
      (fun m =>
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cardDistinctFactors_le_cardFactors m))
          (tamagawaDensity_nonneg m))
      summable_tamagawaDensity_mul_cardDistinctFactors summable_tamagawaDensity_mul_cardFactors,
    summable_tamagawaDensity_mul_cardFactors⟩

end WeierstrassCurve
