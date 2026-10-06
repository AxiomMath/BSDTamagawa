/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.DegreeBound

/-!
# Weighted sums of `Ω` and `v_ℓ` against `δ_p`

This file proves the arithmetic inequalities `v_ℓ(t) ≤ Ω(t) ≤ t` and, from the first, the
comparison

`∑_{t ≥ 1} δ_p(t) v_ℓ(t) ≤ ∑_{t ≥ 1} δ_p(t) Ω(t)`

of the two weighted sums against the scalar local density, uniformly in `ℓ`.

## Main results

* `BSDTamagawa.FirstMoment.cardFactors_le_self`: `Ω(n) ≤ n`.
* `BSDTamagawa.FirstMoment.factorization_le_cardFactors`: `v_ℓ(n) ≤ Ω(n)`.
* `WeierstrassCurve.tsum_δ_mul_factorization_le_tsum_δ_mul_cardFactors`:
  `∑_t δ_p(t) v_ℓ(t) ≤ ∑_t δ_p(t) Ω(t)`, uniformly in `ℓ`.

## Implementation notes

All sums are `tsum`s over `ℕ` of `ℝ≥0∞`-valued families, so no summability hypothesis is needed;
the `t = 0` term vanishes since `δ_p(0) = 0`.
-/

@[expose] public section

open scoped ENNReal

namespace BSDTamagawa.FirstMoment

/-! ### The two arithmetic inequalities -/

/-- `2 ^ Ω n ≤ n` for `n ≠ 0`. -/
theorem two_pow_cardFactors_le {n : ℕ} (hn : n ≠ 0) :
    2 ^ ArithmeticFunction.cardFactors n ≤ n := by
  have h := Multiset.pow_card_le_prod (s := (n.primeFactorsList : Multiset ℕ)) (a := 2)
    (fun x hx => (Nat.prime_of_mem_primeFactorsList (by simpa using hx)).two_le)
  simpa [ArithmeticFunction.cardFactors_apply, Nat.prod_primeFactorsList hn] using h

/-- `Ω n ≤ n`. -/
theorem cardFactors_le_self (n : ℕ) : ArithmeticFunction.cardFactors n ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (two_pow_cardFactors_le hn))

/-- `v_ℓ(n) ≤ Ω(n)`, for every `ℓ : ℕ`. -/
theorem factorization_le_cardFactors (n ℓ : ℕ) :
    n.factorization ℓ ≤ ArithmeticFunction.cardFactors n := by
  rw [ArithmeticFunction.cardFactors_apply, ← Nat.primeFactorsList_count_eq]
  exact List.count_le_length

end BSDTamagawa.FirstMoment

namespace WeierstrassCurve

open BSDTamagawa.FirstMoment

variable {p : ℕ} [Fact p.Prime]

/-! ### Comparing the two weighted sums -/

/-- `∑_t δ_p(t) v_ℓ(t) ≤ ∑_t δ_p(t) Ω(t)`, for every `ℓ`. -/
theorem tsum_δ_mul_factorization_le_tsum_δ_mul_cardFactors (ℓ : ℕ) :
    (∑' t : ℕ, δ p t * (t.factorization ℓ : ℝ≥0∞))
      ≤ ∑' t : ℕ, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) :=
  ENNReal.tsum_le_tsum fun t => by
    gcongr
    exact_mod_cast factorization_le_cardFactors t ℓ

end WeierstrassCurve
