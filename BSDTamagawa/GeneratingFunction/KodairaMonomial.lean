/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The Kodaira monomial `𝐮^ω`

For a finite set `Λ` of local reduction data, a Kodaira-parameter vector
`𝐮 = (u_K)_{K ∈ Λ} ∈ ℂ^Λ` and the integral short Weierstrass model `E = E(a₄, a₆)`, the Kodaira
monomial is `𝐮^ω := ∏_{K ∈ Λ} u_K^{ω_K(E)}`, where `ω_K(E)` is the number of primes at which `E`
has reduction datum `K`. The definition `WeierstrassCurve.kodairaMonomial` is in
`BSDTamagawa.Defs`, as the multi-monomial at the exponent `K ↦ ω_K(E)`.

## Main results

* `WeierstrassCurve.kodairaMonomial_empty`: for `Λ = ∅` the Kodaira monomial is `1`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- On the empty stratum set the Kodaira monomial is the empty product `1`. -/
@[simp]
lemma kodairaMonomial_empty (u : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ) (a₄ a₆ : ℤ) :
    kodairaMonomial ∅ u a₄ a₆ = 1 := by
  simp [kodairaMonomial, multiMonomial]

end WeierstrassCurve
