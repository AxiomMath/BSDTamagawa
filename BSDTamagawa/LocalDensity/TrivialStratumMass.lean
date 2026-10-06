/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The trivial-stratum mass `β_p`

For each prime `p`, `β_p := δ_p(I₀) + δ_p(I₁^sp) + δ_p(I₁^ns) = ∑_{K ∈ 𝒦₀} δ_p(K)` is the total
`δ_p`-mass of `𝒦₀ = {(I₀, 1), (I₁, 1)}`. The reduction datum
`(Kodaira symbol, component-group order)` does not record the split/non-split decoration of `I₁`,
so `I₁^sp` and `I₁^ns` both name `(I₁, 1)`, and `δ_p((I₁, 1)) = δ_p(I₁^sp) + δ_p(I₁^ns)`. Every
member of `𝒦₀` has Tamagawa number `1`, so `β_p ≤ δ_p(1)`, but the inequality is strict in general:
additive types such as `II` also have Tamagawa number `1`.

## Main results

* `WeierstrassCurve.β_add`: `β_p = δ_p((I₀, 1)) + δ_p((I₁, 1))`.
-/

@[expose] public section

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-- `β_p` evaluated on the two members of `𝒦₀`: `β_p = δ_p((I₀, 1)) + δ_p((I₁, 1))`. -/
lemma β_add : β p = deltaP p (KodairaSymbol.I 0, 1) + deltaP p (KodairaSymbol.I 1, 1) :=
  finsum_mem_pair (by simp)

end WeierstrassCurve
