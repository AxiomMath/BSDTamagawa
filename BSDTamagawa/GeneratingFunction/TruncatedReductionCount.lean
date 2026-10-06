/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.ReductionDatumPrimeCount

/-!
# The truncated reduction-datum count `ω_{K,S}(E)`

For a finite set of primes `S`, a reduction datum `K` and the integral short Weierstrass model
`E = E(a₄, a₆)`, `ω_{K,S}(E) := ∑_{p ∈ S} 1[τ_p(E) = K]` is the number of primes of `S` at which
`E` has local reduction datum exactly `K`. It is the finite truncation of the global count
`ω_K(E)`, and agrees with it for every `K ≠ (I₀, 1)` once `S` contains every prime with
`τ_p(E) ≠ (I₀, 1)`. A reduction datum is a pair `(Kodaira symbol, local Tamagawa number)`, and
non-prime indices carry the neutral datum `(I₀, 1)`.

## Main definitions

* `WeierstrassCurve.truncatedReductionOmega`: the count `ω_{K,S}(E)`.

## Main results

* `WeierstrassCurve.truncatedReductionOmega_eq`: `ω_{K,S}(E) = ω_K(E)` for `K ≠ (I₀, 1)` once `S`
  contains every prime with `τ_p(E) ≠ (I₀, 1)`.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped Classical in
/-- For a finite set of primes `S`, a reduction datum `K = (Kodaira symbol, local Tamagawa number)`
and the integral short Weierstrass model `E = E(a₄, a₆)`, `ω_{K,S}(E) := ∑_{p ∈ S} 1[τ_p(E) = K]`,
where `τ_p` is the local reduction datum. -/
@[bsd_tamagawa "T034a"]
noncomputable def truncatedReductionOmega (K : KodairaSymbol × ℕ) (S : Finset ℕ)
    (a₄ a₆ : ℤ) : ℕ :=
  ∑ p ∈ S, if localReductionDatum p a₄ a₆ = K then 1 else 0

/-- Once `S` contains every prime whose reduction datum is not the neutral `(I₀, 1)`, the truncated
count agrees with the global one: `ω_{K,S}(E) = ω_K(E)` for every `K ≠ (I₀, 1)`. -/
@[bsd_tamagawa "T034a"]
lemma truncatedReductionOmega_eq {K : KodairaSymbol × ℕ} {S : Finset ℕ} {a₄ a₆ : ℤ}
    (hK : K ≠ (KodairaSymbol.I 0, 1))
    (hS : ∀ p : ℕ, localReductionDatum p a₄ a₆ ≠ (KodairaSymbol.I 0, 1) → p ∈ S) :
    truncatedReductionOmega K S a₄ a₆ = reductionOmega K a₄ a₆ := by
  rw [truncatedReductionOmega, ← Finset.card_filter, ← Set.ncard_coe_finset, reductionOmega]
  congr 1
  ext p
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, and_iff_right_iff_imp]
  exact fun h => hS p fun h' => hK (h.symm.trans h')

end WeierstrassCurve
