/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Defs

/-!
# The set `𝒦` of local reduction data

`𝒦` is the index set of local reduction data: one element per stratum that the local behaviour of
an elliptic curve over `ℚ_p` can fall into. It is encoded as `ReductionData := KodairaSymbol × ℕ`
(defined in `BSDTamagawa.Defs`), the Kodaira symbol paired with the order of the component group,
as a reducible `abbrev`.

## Main definitions

* `BSDTamagawa.LocalReduction.ReductionData.kodaira`: the Kodaira symbol of a stratum.
* `BSDTamagawa.LocalReduction.ReductionData.tamagawa`: the local Tamagawa number of a stratum.

## Implementation notes

An element of `𝒦` is often described as recording the Kodaira symbol, the split/non-split data in
the multiplicative case, and the component group in the additive case. This encoding keeps the
symbol and the order of the component group and drops the split/non-split decoration. The
decoration does not change the component-group order (`I_n^{sp}` and `I_n^{ns}` both have `c = n`),
so every statistic of the Tamagawa number — `c_p`, `Tam`, `ω_Tam`, `Ω(Tam)`, `v_ℓ(Tam)` — is
unaffected; computing `δ_p(I_n^{sp})` separately would require refining the type.
-/

@[expose] public section

open WeierstrassCurve

namespace BSDTamagawa.LocalReduction

/-- The Kodaira-symbol map `κ : 𝒦 → {Kodaira symbols}`, sending a stratum to its Kodaira symbol and
forgetting the component-group order. -/
@[bsd_tamagawa "T006b"]
abbrev ReductionData.kodaira (K : ReductionData) : KodairaSymbol := K.1

/-- The local Tamagawa-number map `c : 𝒦 → ℕ`, sending a stratum to the order of the component
group it records. Positivity on the strata that arise is
`WeierstrassCurve.tauZ_tamagawaNumber_pos`. -/
@[bsd_tamagawa "T006c"]
abbrev ReductionData.tamagawa (K : ReductionData) : ℕ := K.2

end BSDTamagawa.LocalReduction
