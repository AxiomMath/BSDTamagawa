/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.TamagawaProduct

/-!
# The truncated `Ω`-statistic `Ω_S(E)`

For a finite set of primes `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`Ω_S(E) := ∑_{p ∈ S} Ω(c_p(E))`, where `Ω` counts prime factors with multiplicity and `c_p` is the
local Tamagawa number. Once `S` contains every prime with `c_p(E) > 1`, `Ω_S(E) = Ω(Tam(E))`; this
uses that every `c_p(E)` is nonzero, since `Ω` is additive on products only away from `0`.

## Main definitions

* `WeierstrassCurve.truncatedTamagawaCardFactors`: the statistic `Ω_S(E)`.

## Main results

* `ArithmeticFunction.cardFactors_prod`: `Ω (∏ i ∈ S, f i) = ∑ i ∈ S, Ω (f i)` for nonzero `f i`.
* `WeierstrassCurve.truncatedTamagawaCardFactors_eq`: `Ω_S(E) = Ω(Tam(E))` once `S` contains every
  prime with `c_p(E) > 1`.
-/

@[expose] public section

namespace ArithmeticFunction

/-- `Ω` turns a finite product of nonzero naturals into a sum:
`Ω (∏ i ∈ S, f i) = ∑ i ∈ S, Ω (f i)`. -/
theorem cardFactors_prod {ι : Type*} {S : Finset ι} {f : ι → ℕ} (h : ∀ i ∈ S, f i ≠ 0) :
    cardFactors (∏ i ∈ S, f i) = ∑ i ∈ S, cardFactors (f i) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => h i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.sum_cons,
      cardFactors_mul (h a (Finset.mem_cons_self a s)) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

end ArithmeticFunction

namespace WeierstrassCurve

/-- For a finite set of primes `S` and the integral short Weierstrass model `E = E(a₄, a₆)`,
`Ω_S(E) := ∑_{p ∈ S} Ω(c_p(E))`, where `Ω = ArithmeticFunction.cardFactors` counts prime factors
with multiplicity and `c_p` is the local Tamagawa number. -/
@[bsd_tamagawa "T034c"]
noncomputable def truncatedTamagawaCardFactors (S : Finset ℕ) (a₄ a₆ : ℤ) : ℕ :=
  ∑ p ∈ S, ArithmeticFunction.cardFactors (localTamagawaNumber p a₄ a₆)

/-- Once `S` contains every prime with `c_p(E) > 1`, the truncated statistic agrees with the global
one: `Ω_S(E) = Ω(Tam(E))`. -/
@[bsd_tamagawa "T034c"]
lemma truncatedTamagawaCardFactors_eq {a₄ a₆ : ℤ} {S : Finset ℕ}
    (hS : ∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ → p ∈ S) :
    truncatedTamagawaCardFactors S a₄ a₆ =
      ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆) := by
  rw [tamagawaProduct_eq_prod_of_mulSupport_subset
      fun p hp => hS p ((one_lt_localTamagawaNumber_iff p a₄ a₆).mpr hp),
    ArithmeticFunction.cardFactors_prod fun p _ => localTamagawaNumber_ne_zero p a₄ a₆]
  rfl

end WeierstrassCurve
