/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.TamagawaProduct

/-!
# The truncated Tamagawa product `Tam_S(E)`

For a finite set of primes `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`Tam_S(E) := ∏_{p ∈ S} c_p(E)` is the finite truncation of the Tamagawa product `Tam(E)`. Once `S`
contains every prime with `c_p(E) > 1`, `Tam_S(E) = Tam(E)`. Non-prime members of `S` have
`c_p(E) = 1` and contribute the neutral factor.

## Main definitions

* `WeierstrassCurve.truncatedTamagawaProduct`: the product `Tam_S(E)`.

## Main results

* `WeierstrassCurve.truncatedTamagawaProduct_eq`: `Tam_S(E) = Tam(E)` once `S` contains every prime
  with `c_p(E) > 1`.
-/

@[expose] public section

namespace WeierstrassCurve

/-- For a finite set of primes `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`Tam_S(E) := ∏_{p ∈ S} c_p(E)`, where `c_p` is the local Tamagawa number. -/
@[bsd_tamagawa "T034e"]
noncomputable def truncatedTamagawaProduct (S : Finset ℕ) (a₄ a₆ : ℤ) : ℕ :=
  ∏ p ∈ S, localTamagawaNumber p a₄ a₆

/-- Once `S` contains every prime with `c_p(E) > 1`, the truncated product agrees with the global
one: `Tam_S(E) = Tam(E)`. -/
@[bsd_tamagawa "T034e"]
lemma truncatedTamagawaProduct_eq {S : Finset ℕ} {a₄ a₆ : ℤ}
    (hS : ∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ → p ∈ S) :
    truncatedTamagawaProduct S a₄ a₆ = tamagawaProduct a₄ a₆ :=
  (tamagawaProduct_eq_prod_of_mulSupport_subset
    fun p hp => hS p ((one_lt_localTamagawaNumber_iff p a₄ a₆).mpr hp)).symm

end WeierstrassCurve
