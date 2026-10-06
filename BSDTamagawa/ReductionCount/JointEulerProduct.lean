/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.Reduction

/-!
# The joint Euler product `F_Λ(𝐮)`

For a finite set `Λ` of local reduction data and `𝐮 = (u_K)_{K ∈ Λ} ∈ ℂ^Λ`,
`F_Λ(𝐮) := ∏_p (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`, the product over all primes of the
affine local factors built from the local reduction densities `δ_p(K) = μ_p(τ_p⁻¹(K))`
(`WeierstrassCurve.deltaP`), where `K` is a pair (Kodaira symbol, local Tamagawa number).

## Main definitions

* `WeierstrassCurve.jointReductionOmegaEulerFactor`: the local factor
  `1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K` at a prime `p`, and `1` at a non-prime index.
* `WeierstrassCurve.jointReductionOmegaEulerProduct`: the product `F_Λ(𝐮)` of the local factors.

## Implementation notes

The product is the topological infinite product `tprod` (`∏'`), which is `1` when the family is not
multipliable; it is not a `finprod`, since the multiplicative support of `p ↦ F_{Λ,p}(𝐮)` is
infinite for generic `𝐮`. The densities are coerced from `ℝ≥0∞` to `ℂ` before the subtraction
`1 - ∑_K δ_p(K)` is formed, since subtraction in `ℝ≥0∞` is truncated.
-/

@[expose] public section

namespace WeierstrassCurve

/-- The affine factor `1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K` of the joint Euler product
`F_Λ` at a prime `p`, built from the local reduction densities `δ_p(K)` (`deltaP`) read in `ℂ`
through `ENNReal.toReal`; at a non-prime index its value is `1`. -/
@[bsd_tamagawa "T040e"]
noncomputable def jointReductionOmegaEulerFactor (Λ : Finset (KodairaSymbol × ℕ))
    (p : ℕ) (u : Λ → ℂ) : ℂ :=
  if h : p.Prime then
    1 - ∑ K : Λ, ((@deltaP p ⟨h⟩ (K : KodairaSymbol × ℕ)).toReal : ℂ)
      + ∑ K : Λ, ((@deltaP p ⟨h⟩ (K : KodairaSymbol × ℕ)).toReal : ℂ) * u K
  else 1

/-- At a prime index the joint local factor is
`1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K`. -/
lemma jointReductionOmegaEulerFactor_of_prime {Λ : Finset (KodairaSymbol × ℕ)}
    (p : ℕ) [Fact p.Prime] (u : Λ → ℂ) :
    jointReductionOmegaEulerFactor Λ p u =
      1 - ∑ K : Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
        + ∑ K : Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * u K :=
  dite_eq_left Fact.out

/-- At a non-prime index the joint local factor is the neutral value `1`. -/
lemma jointReductionOmegaEulerFactor_of_not_prime {Λ : Finset (KodairaSymbol × ℕ)}
    {p : ℕ} (hp : ¬ p.Prime) (u : Λ → ℂ) :
    jointReductionOmegaEulerFactor Λ p u = 1 :=
  dite_eq_right hp

/-- For a finite set `Λ` of local reduction data `K = (Kodaira symbol, local Tamagawa number)` and
`𝐮 = (u_K)_{K ∈ Λ}` in `ℂ^Λ`, the joint Euler product
`F_Λ(𝐮) := ∏_p (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`, the product over all primes of the
affine local factors built from the local reduction densities `δ_p(K)`. The product is the
topological infinite product `tprod`, which is `1` when the family is not multipliable. -/
@[bsd_tamagawa "T040e"]
noncomputable def jointReductionOmegaEulerProduct (Λ : Finset (KodairaSymbol × ℕ))
    (u : Λ → ℂ) : ℂ :=
  ∏' p : ℕ, jointReductionOmegaEulerFactor Λ p u

end WeierstrassCurve
