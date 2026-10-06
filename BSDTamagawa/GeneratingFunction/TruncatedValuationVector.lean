/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.TamagawaProduct

/-!
# The truncated valuation vector `v_{Π,S}(E)`

For finite sets of primes `S` and `Π` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`v_{Π,S}(E) := (∑_{p ∈ S} v_ℓ(c_p(E)))_{ℓ ∈ Π} ∈ ℕ^Π`, where `v_ℓ` is the `ℓ`-adic valuation and
`c_p` is the local Tamagawa number. Once `S` contains every prime with `c_p(E) > 1`,
`v_{Π,S}(E) = v_Π(Tam(E))`; this uses that every `c_p(E)` is nonzero, since valuations are additive
on products only away from `0`.

## Main definitions

* `WeierstrassCurve.truncatedTamagawaValuationVector`: the vector `v_{Π,S}(E)`.

## Main results

* `padicValNat.prod`: the `ℓ`-adic valuation of a finite product of nonzero naturals is the sum of
  the valuations.
* `WeierstrassCurve.truncatedTamagawaValuationVector_eq`: `v_{Π,S}(E) = v_Π(Tam(E))` once `S`
  contains every prime with `c_p(E) > 1`.
-/

@[expose] public section

namespace padicValNat

/-- The `ℓ`-adic valuation of a finite product of nonzero naturals is the sum of the valuations. -/
protected theorem prod {ι : Type*} {S : Finset ι} {f : ι → ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ∀ i ∈ S, f i ≠ 0) :
    padicValNat ℓ (∏ i ∈ S, f i) = ∑ i ∈ S, padicValNat ℓ (f i) := by
  rw [← Nat.factorization_def _ hℓ, Nat.factorization_prod_apply h]
  exact Finset.sum_congr rfl fun i _ => Nat.factorization_def (f i) hℓ

end padicValNat

namespace WeierstrassCurve

/-- For finite sets of primes `Π` and `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`v_{Π,S}(E) := (∑_{p ∈ S} v_ℓ(c_p(E)))_{ℓ ∈ Π} ∈ ℕ^Π`, where `v_ℓ = padicValNat ℓ` is the `ℓ`-adic
valuation and `c_p` is the local Tamagawa number. -/
@[bsd_tamagawa "T034d"]
noncomputable def truncatedTamagawaValuationVector (P S : Finset ℕ) (a₄ a₆ : ℤ) (ℓ : P) : ℕ :=
  ∑ p ∈ S, padicValNat ℓ (localTamagawaNumber p a₄ a₆)

/-- The `ℓ`-component of `v_{Π,S}(E)` is `∑_{p ∈ S} v_ℓ(c_p(E))`. -/
@[simp]
theorem truncatedTamagawaValuationVector_apply (P S : Finset ℕ) (a₄ a₆ : ℤ) (ℓ : P) :
    truncatedTamagawaValuationVector P S a₄ a₆ ℓ =
      ∑ p ∈ S, padicValNat ℓ (localTamagawaNumber p a₄ a₆) :=
  rfl

/-- If `Π` consists of primes and `S` contains every prime with `c_p(E) > 1`, the truncated vector
agrees with the global one: `v_{Π,S}(E) = (v_ℓ(Tam(E)))_{ℓ ∈ Π}`. -/
@[bsd_tamagawa "T034d"]
lemma truncatedTamagawaValuationVector_eq {P S : Finset ℕ} {a₄ a₆ : ℤ}
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ)
    (hS : ∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ → p ∈ S) :
    truncatedTamagawaValuationVector P S a₄ a₆ =
      fun ℓ : P => padicValNat ℓ (tamagawaProduct a₄ a₆) := by
  funext ℓ
  rw [truncatedTamagawaValuationVector_apply, tamagawaProduct_eq_prod_of_mulSupport_subset
      fun p hp => hS p ((one_lt_localTamagawaNumber_iff p a₄ a₆).mpr hp),
    padicValNat.prod (hP ℓ ℓ.2) fun p _ => localTamagawaNumber_ne_zero p a₄ a₆]

end WeierstrassCurve
