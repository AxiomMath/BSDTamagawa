/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.TamagawaProduct

/-!
# The Tamagawa prime count `ω_Tam`

`ω_Tam(E) := #{p prime : c_p(E) > 1}` counts the primes that contribute a nontrivial factor to the
Tamagawa product `Tam(E)`. It is `WeierstrassCurve.tamagawaOmega`, defined in `BSDTamagawa.Defs` as
a `Set.ncard` over `p : ℕ`; since `c_p = 1` at every non-prime index, the set automatically
consists of primes.

## Main results

* `WeierstrassCurve.finite_setOf_one_lt_localTamagawaNumber`: the set `{p : 1 < c_p(E)}` is finite.
-/

@[expose] public section

namespace WeierstrassCurve

/-- The primes contributing nontrivially to `Tam(E)` form a subset of the multiplicative support of
`p ↦ c_p(E)`: if `1 < c_p(E)` then in particular `c_p(E) ≠ 1`. -/
lemma setOf_one_lt_localTamagawaNumber_subset (a₄ a₆ : ℤ) :
    {p : ℕ | 1 < localTamagawaNumber p a₄ a₆} ⊆
      Function.mulSupport fun p : ℕ => localTamagawaNumber p a₄ a₆ :=
  fun _ hp => hp.ne'

/-- Only finitely many primes contribute nontrivially: the set `{p : 1 < c_p(E)}` is finite. -/
@[bsd_tamagawa "T005"]
lemma finite_setOf_one_lt_localTamagawaNumber (a₄ a₆ : ℤ) :
    {p : ℕ | 1 < localTamagawaNumber p a₄ a₆}.Finite :=
  (mulSupport_localTamagawaNumber_finite a₄ a₆).subset
    (setOf_one_lt_localTamagawaNumber_subset a₄ a₆)

/-- Every index counted by `ω_Tam(E)` is prime: at a non-prime index `c_p(E) = 1`. -/
lemma prime_of_one_lt_localTamagawaNumber {p : ℕ} {a₄ a₆ : ℤ}
    (hp : 1 < localTamagawaNumber p a₄ a₆) : p.Prime :=
  not_not.mp fun h => hp.ne' (localTamagawaNumber_of_not_prime h a₄ a₆)

end WeierstrassCurve
