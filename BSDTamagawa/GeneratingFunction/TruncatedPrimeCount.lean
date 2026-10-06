/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.TamagawaPrimeCount

/-!
# The truncated Tamagawa prime count `ω_{Tam,S}(E)`

For a finite set of primes `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`ω_{Tam,S}(E) := ∑_{p ∈ S} 1[c_p(E) > 1]`, the number of primes of `S` contributing a nontrivial
factor to the Tamagawa product. It is the finite truncation of the global count `ω_Tam(E)`, and
agrees with it once `S` contains every prime with `c_p(E) > 1`. Non-prime members of `S` have
`c_p(E) = 1` and contribute `0`.

## Main definitions

* `WeierstrassCurve.truncatedTamagawaOmega`: the count `ω_{Tam,S}(E)`.

## Main results

* `WeierstrassCurve.truncatedTamagawaOmega_eq`: `ω_{Tam,S}(E) = ω_Tam(E)` once `S` contains every
  prime with `c_p(E) > 1`.
* `WeierstrassCurve.exists_finset_truncatedTamagawaOmega_eq`: such an `S` exists.
-/

@[expose] public section

namespace WeierstrassCurve

/-- For a finite set of primes `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`ω_{Tam,S}(E) := ∑_{p ∈ S} 1[c_p(E) > 1]`, where `c_p` is the local Tamagawa number. -/
@[bsd_tamagawa "T034b"]
noncomputable def truncatedTamagawaOmega (S : Finset ℕ) (a₄ a₆ : ℤ) : ℕ :=
  ∑ p ∈ S, if 1 < localTamagawaNumber p a₄ a₆ then 1 else 0

/-- Once `S` contains every prime with `c_p(E) > 1`, the truncated count agrees with the global
one: `ω_{Tam,S}(E) = ω_Tam(E)`. -/
@[bsd_tamagawa "T034b"]
lemma truncatedTamagawaOmega_eq {S : Finset ℕ} {a₄ a₆ : ℤ}
    (hS : ∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ → p ∈ S) :
    truncatedTamagawaOmega S a₄ a₆ = tamagawaOmega a₄ a₆ := by
  rw [truncatedTamagawaOmega, ← Finset.card_filter, ← Set.ncard_coe_finset, tamagawaOmega]
  congr 1
  ext p
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, and_iff_right_iff_imp]
  exact hS p

/-- There is a finite set `S` containing every prime with `c_p(E) > 1`, and for it
`ω_{Tam,S}(E) = ω_Tam(E)`. -/
lemma exists_finset_truncatedTamagawaOmega_eq (a₄ a₆ : ℤ) :
    ∃ S : Finset ℕ, (∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ → p ∈ S) ∧
      truncatedTamagawaOmega S a₄ a₆ = tamagawaOmega a₄ a₆ :=
  have hmem : ∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ →
      p ∈ (finite_setOf_one_lt_localTamagawaNumber a₄ a₆).toFinset :=
    fun _ hp => (Set.Finite.mem_toFinset _).mpr hp
  ⟨_, hmem, truncatedTamagawaOmega_eq hmem⟩

end WeierstrassCurve
