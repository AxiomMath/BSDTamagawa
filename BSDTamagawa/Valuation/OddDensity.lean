/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.NoDivisorDensity

/-!
# The density of odd Tamagawa products

Let `P = P_{\{2\}}` be the limiting law of the `2`-adic valuation of the Tamagawa product `Tam(E)`
of short Weierstrass curves ordered by height, a probability measure on `ℤ_{≥0}^{\{2\}}`. Then

`P(Tam(E) is odd) = ∏_{p ∈ 𝒫} (∑_{t odd} δ_p(t))`,

where `δ_p(t)` is the local density of Tamagawa number `t` at `p`, and the Euler product converges.
This is the case `A = {2}` of the density of Tamagawa products prime to a finite set `A` of primes,
since `Tam(E)` is odd iff `2 ∤ Tam(E)`.

## Main results

* `WeierstrassCurve.setOf_coprime_two_eq_odd`: `(t, ∏_{m ∈ \{2\}} m) = 1` iff `t` is odd.
* `WeierstrassCurve.multipliable_oddDensity_primes`: the family `(∑_{t odd} δ_p(t))_{p ∈ 𝒫}` is
  multipliable.
* `WeierstrassCurve.tamagawaValuationMeasure_odd_toReal`: the odd density formula.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-! ### The singleton `Π = {2}` -/

/-- Every element of `({2} : Finset ℕ)` is prime. -/
private lemma forall_mem_singleton_two_prime : ∀ m ∈ ({2} : Finset ℕ), Nat.Prime m :=
  fun m hm => by rw [Finset.mem_singleton.1 hm]; exact Nat.prime_two

/-- `(t, ∏_{m ∈ \{2\}} m) = 1` iff `t` is odd. -/
theorem setOf_coprime_two_eq_odd :
    {t : ℕ | Nat.Coprime t (∏ x ∈ ({2} : Finset ℕ), x)} = {t : ℕ | Odd t} := by
  ext t
  simp only [Finset.prod_singleton, Set.mem_ofPred_eq]
  exact Nat.coprime_two_right

/-! ### The odd density -/

/-- The family `(∑_{t odd} δ_p(t))_{p ∈ 𝒫}` is `Multipliable`: the net of partial products over the
finite sets of primes converges. -/
@[bsd_tamagawa "T044d"]
theorem multipliable_oddDensity_primes :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ↥{t : ℕ | Odd t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal := by
  rw [← setOf_coprime_two_eq_odd]
  exact multipliable_coprimeDensity_primes {2} forall_mem_singleton_two_prime

/-- With `P` the limiting joint valuation law on `ℤ_{≥0}^{\{2\}}`,

`P(Tam(E) is odd) = ∏_{p ∈ 𝒫} (∑_{t odd} δ_p(t))`,

with `δ_p(t)` the local Tamagawa density at `p`. The event on the left is the set of multi-indices
whose coordinate at `2` vanishes, which is the event that `Tam(E)` is odd. -/
@[bsd_tamagawa "T044d"]
theorem tamagawaValuationMeasure_odd_toReal :
    (tamagawaValuationMeasure {2}
        {j : ↥({2} : Finset ℕ) → ℕ | ∀ ℓ : ↥({2} : Finset ℕ), j ℓ = 0}).toReal
      = ∏' p : {q : ℕ // q.Prime}, ∑' t : ↥{t : ℕ | Odd t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal := by
  rw [tamagawaValuationMeasure_notDvd_toReal {2} forall_mem_singleton_two_prime,
    setOf_coprime_two_eq_odd]

end WeierstrassCurve
