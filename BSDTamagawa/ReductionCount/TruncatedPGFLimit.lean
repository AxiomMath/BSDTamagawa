/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.MasterEulerProduct
public import BSDTamagawa.ReductionCount.LocalFactorCollapse
public import BSDTamagawa.ReductionCount.EulerProductConvergence
public import BSDTamagawa.GeneratingFunction.KodairaParam

/-!
# Pointwise limit of the truncated joint pgf on the closed unit polydisc

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every `𝐮 = (u_K)_{K ∈ Λ} ∈ ℂ^Λ`
with `‖u_K‖ ≤ 1` for all `K ∈ Λ`,
`lim_{X → ∞} 𝒵_{Λ, ∅, X}(0; 1, 1, ∅, 𝐮) = F_Λ(𝐮)`,
with `𝒵_{Λ, Π, X}` the multivariable generating function `tamagawaGeneratingFunction` and `F_Λ`
the joint Euler product `jointReductionOmegaEulerProduct`
`∏'_p (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`. The master Euler product at the point
`(s, u, w, 𝐳) = (0, 1, 1, ∅)` has local factors equal to those of `F_Λ`.

## Main results

* `WeierstrassCurve.tendsto_tamagawaGeneratingFunction_jointReductionOmegaEulerProduct`: the
  displayed limit.
* `WeierstrassCurve.tprod_jointReductionOmegaEulerFactor_primes`: the joint Euler product over
  the primes equals the one over `ℕ`.
* `WeierstrassCurve.localFactor_kodairaFace_eq_jointReductionOmegaEulerFactor`: at a prime, the
  master local factor on the Kodaira face is the joint local factor.
* `WeierstrassCurve.tprod_localFactor_kodairaFace_eq_jointReductionOmegaEulerProduct`: the master
  Euler product on the Kodaira face is `F_Λ(𝐮)`.

## Implementation notes

Since `Π = ∅`, the index type `↥(∅ : Finset ℕ)` is empty and `z : ↥(∅ : Finset ℕ) → ℂ` is unique;
it is carried as a variable.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam

/-! ### The joint Euler product over the primes is the one over `ℕ` -/

/-- For finite `Λ ⊆ 𝒦 ∖ 𝒦₀`, `∏'_{p ∈ 𝒫} F_{Λ,p}(𝐮) = ∏'_{p : ℕ} F_{Λ,p}(𝐮)`: the joint Euler
product may be taken over the primes. -/
lemma tprod_jointReductionOmegaEulerFactor_primes {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) (u : Λ → ℂ) :
    ∏' p : {q : ℕ // q.Prime}, jointReductionOmegaEulerFactor Λ (p : ℕ) u
      = ∏' p : ℕ, jointReductionOmegaEulerFactor Λ p u := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      jointReductionOmegaEulerFactor Λ x u = 1 := fun x hx =>
    jointReductionOmegaEulerFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) u
  exact ((Subtype.coe_injective.hasProd_iff hone).2
    (multipliable_jointReductionOmegaEulerFactor hΛ u).hasProd).tprod_eq

/-! ### The master local factor on the Kodaira face is the joint local factor -/

/-- At a prime `p`, for a finite `Λ ⊆ 𝒦 ∖ 𝒦₀`,
`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, 1, 1, ∅, 𝐮) = F_{Λ,p}(𝐮)`: the master local factor on
the Kodaira face is the joint local factor `jointReductionOmegaEulerFactor`. -/
lemma localFactor_kodairaFace_eq_jointReductionOmegaEulerFactor {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) (p : {q : ℕ // q.Prime}) :
    ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
        ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          * localWeight Λ ∅ (K : ReductionData) 0 1 1 z uΛ
      = jointReductionOmegaEulerFactor Λ (p : ℕ) uΛ := by
  rw [@jointReductionOmegaEulerFactor_of_prime Λ (p : ℕ) ⟨p.2⟩ uΛ]
  exact @localFactor_collapse_kodaira (p : ℕ) ⟨p.2⟩ Λ hΛ z uΛ

/-- For finite `Λ ⊆ 𝒦 ∖ 𝒦₀`,
`∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, 1, 1, ∅, 𝐮)) = F_Λ(𝐮)`. -/
lemma tprod_localFactor_kodairaFace_eq_jointReductionOmegaEulerProduct
    {Λ : Finset ReductionData} (hΛ : Admissible Λ) (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) :
    ∏' p : {q : ℕ // q.Prime},
        (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight Λ ∅ (K : ReductionData) 0 1 1 z uΛ)
      = jointReductionOmegaEulerProduct Λ uΛ := by
  rw [tprod_congr (localFactor_kodairaFace_eq_jointReductionOmegaEulerFactor hΛ z uΛ),
    tprod_jointReductionOmegaEulerFactor_primes hΛ uΛ]
  rfl

/-! ### The limit of the truncated joint pgf -/

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every `𝐮 = (u_K)_{K ∈ Λ}` in
`ℂ^Λ` with `‖u_K‖ ≤ 1` for all `K ∈ Λ`, `lim_{X → ∞} 𝒵_{Λ, ∅, X}(0; 1, 1, ∅, 𝐮) = F_Λ(𝐮)`, with
`𝒵_{Λ, Π, X}` the multivariable generating function and `F_Λ` the joint Euler product
`∏'_p (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`. -/
@[bsd_tamagawa "T040m"]
theorem tendsto_tamagawaGeneratingFunction_jointReductionOmegaEulerProduct
    {Λ : Finset ReductionData} (hΛ : Admissible Λ) (z : (∅ : Finset ℕ) → ℂ) {uΛ : Λ → ℂ}
    (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Tendsto (tamagawaGeneratingFunction Λ ∅ 0 1 1 z uΛ) atTop
      (𝓝 (jointReductionOmegaEulerProduct Λ uΛ)) := by
  have hs : (0 : ℝ) ≤ (0 : ℂ).re := by simp
  have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hz : ∀ ℓ : (∅ : Finset ℕ), ‖z ℓ‖ ≤ 1 := fun ℓ =>
    absurd ℓ.2 (Finset.notMem_empty (ℓ : ℕ))
  have hP : ∀ ℓ ∈ (∅ : Finset ℕ), Nat.Prime ℓ := by simp
  rw [← tprod_localFactor_kodairaFace_eq_jointReductionOmegaEulerProduct hΛ z uΛ]
  exact tendsto_tamagawaGeneratingFunction_tprod_localFactor Λ ∅
    (fun K hK => hΛ.notMem_K0 hK) hP hs h1 h1 hz huΛ

end WeierstrassCurve
