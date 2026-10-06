/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Defs

/-!
# The Kodaira-parameter vector `𝐮 ∈ ℂ^Λ`

For a finite set `Λ ⊆ 𝒦 ∖ 𝒦₀` of local reduction data, the *Kodaira-parameter vector* is
`𝐮 = (u_K)_{K ∈ Λ} ∈ ℂ^Λ`: one formal variable per stratum in `Λ`. In the master generating
function each `u_K` marks the frequency `ω_K(E)` of the stratum `K`.

## Main definitions

* `BSDTamagawa.KodairaParam.KodairaParamSpace`: the space `ℂ^Λ` of Kodaira-parameter vectors.

## Main results

* `BSDTamagawa.KodairaParam.Admissible.notMem_K0`: every stratum of an admissible `Λ` lies
  outside `𝒦₀`.

## Implementation notes

`KodairaParamSpace Λ` is `BSDTamagawa.PrimeParam.ParamSpace` at the index type `↥Λ`. The
condition `Λ ⊆ 𝒦 ∖ 𝒦₀` is not part of the type; it is the separate predicate
`BSDTamagawa.KodairaParam.Admissible`, defined in `BSDTamagawa.Defs`.
-/

@[expose] public section

open BSDTamagawa.LocalReduction BSDTamagawa.PrimeParam

namespace BSDTamagawa.KodairaParam

/-- The Kodaira-parameter space `ℂ^Λ = ∏_{K ∈ Λ} ℂ`, with one coordinate per stratum of `Λ` and its
componentwise `ℂ`-vector space structure. -/
@[bsd_tamagawa "T014a"]
abbrev KodairaParamSpace (Λ : Finset ReductionData) : Type := ParamSpace (↥Λ)

/-- Every stratum of an admissible `Λ` lies outside `𝒦₀`. -/
lemma Admissible.notMem_K0 {Λ : Finset ReductionData} (h : Admissible Λ) {K : ReductionData}
    (hK : K ∈ Λ) : K ∉ WeierstrassCurve.K0 := h K hK

end BSDTamagawa.KodairaParam
