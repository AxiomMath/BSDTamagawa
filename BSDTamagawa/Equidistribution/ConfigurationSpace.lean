/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.Measure

/-!
# The finite-prime configuration space `K_S`

For a finite set of primes `S`, the configuration space `K_S = ∏_{p ∈ S} ℤ_p²` is the product over
`p ∈ S` of the spaces of short Weierstrass coefficient pairs `(a₄, a₆)` over `ℤ_p`, with the
product topology. Being a finite product of compact metrizable spaces, `K_S` is compact and
metrizable.

## Main definitions

* `WeierstrassCurve.configSpace`: the configuration space `K_S`.

## Main results

* `WeierstrassCurve.compactSpace_configSpace`: `K_S` is compact.
* `WeierstrassCurve.metrizableSpace_configSpace`: `K_S` is metrizable.

## Implementation notes

The product is indexed by `↥(S.filter Nat.Prime)`, whose elements carry a proof of primality,
supplying the instance `Fact p.Prime` that the type `ℤ_[p]` requires. Non-prime members of `S`
contribute no factor.
-/

@[expose] public section

namespace WeierstrassCurve

/-- Membership in `S.filter Nat.Prime` supplies the instance `Fact p.Prime`. -/
instance factPrimeOfMemFilter (S : Finset ℕ) (p : ↥(S.filter Nat.Prime)) :
    Fact (p : ℕ).Prime :=
  ⟨(Finset.mem_filter.mp p.2).2⟩

/-- For a finite set of primes `S`, the configuration space `K_S = ∏_{p ∈ S} ℤ_p²`, the product
over the primes of `S` of the spaces `ℤ_[p] × ℤ_[p]` of short Weierstrass coefficient pairs
`(a₄, a₆)`, with the product topology. Non-prime members of `S` contribute no factor. -/
@[bsd_tamagawa "T033d"]
abbrev configSpace (S : Finset ℕ) : Type :=
  ∀ p : ↥(S.filter Nat.Prime), ℤ_[(p : ℕ)] × ℤ_[(p : ℕ)]

/-- `K_S` is compact. -/
@[bsd_tamagawa "T033d"]
lemma compactSpace_configSpace (S : Finset ℕ) : CompactSpace (configSpace S) :=
  inferInstance

/-- `K_S` is metrizable. -/
@[bsd_tamagawa "T033d"]
lemma metrizableSpace_configSpace (S : Finset ℕ) :
    TopologicalSpace.MetrizableSpace (configSpace S) :=
  inferInstance

end WeierstrassCurve
