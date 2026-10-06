/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.MasterEulerProduct
public import BSDTamagawa.PrimeCount.EulerProductConvergence

/-!
# Pointwise limit of the truncated generating function on the closed unit disc

For every `u : ℂ` with `‖u‖ ≤ 1`,

`lim_{X → ∞} 𝒵_{∅, ∅, X}(0; u, 1, ∅, ∅) = F(u)`,

with `𝒵_{Λ, Π, X}` the multivariable generating function (`tamagawaGeneratingFunction`) and `F` the
Euler product (`tamagawaOmegaEulerProduct`), `F(u) = ∏'_p (δ_p(1) + (1 - δ_p(1)) u)`. This is the
limit of the master Euler product at the face `Λ = Π = ∅`, `w = 1`, `s = 0`, where each master
local factor collapses to `δ_p(1) + (1 - δ_p(1)) u`.

## Main results

* `WeierstrassCurve.tprod_tamagawaOmegaEulerFactor_primes`:
  `∏'_{p ∈ 𝒫} F_p(u) = ∏'_{p : ℕ} F_p(u)`.
* `WeierstrassCurve.localFactor_scalarFace_eq_tamagawaOmegaEulerFactor`: at a prime, the master
  local factor on the face `Λ = Π = ∅`, `w = 1`, `s = 0` is `F_p(u)`.
* `WeierstrassCurve.tprod_localFactor_scalarFace_eq_tamagawaOmegaEulerProduct`: the master Euler
  product on that face is `F(u)`.
* `WeierstrassCurve.tendsto_tamagawaGeneratingFunction_tamagawaOmegaEulerProduct`: the displayed
  limit.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction

/-! ### The Euler product `F` over the primes is the one over `ℕ` -/

/-- **The Euler product, indexed by the primes.** `∏'_{p ∈ 𝒫} F_p(u) = ∏'_{p : ℕ} F_p(u)`. -/
lemma tprod_tamagawaOmegaEulerFactor_primes (u : ℂ) :
    ∏' p : {q : ℕ // q.Prime}, tamagawaOmegaEulerFactor (p : ℕ) u
      = ∏' p : ℕ, tamagawaOmegaEulerFactor p u := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      tamagawaOmegaEulerFactor x u = 1 := fun x hx =>
    tamagawaOmegaEulerFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) u
  exact ((Subtype.coe_injective.hasProd_iff hone).2
    (multipliable_tamagawaOmegaEulerFactor u).hasProd).tprod_eq

/-! ### The master local factor on the scalar face -/

/-- **The master local factor at the face `Λ = Π = ∅`, `w = 1`, `s = 0`.** At a prime `p` and for
every `u : ℂ`,

`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, u, 1, ∅, ∅) = F_p(u)`. -/
lemma localFactor_scalarFace_eq_tamagawaOmegaEulerFactor (u : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset ReductionData) → ℂ) (p : {q : ℕ // q.Prime}) :
    ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
        ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          * localWeight ∅ ∅ (K : ReductionData) 0 u 1 z uΛ
      = tamagawaOmegaEulerFactor (p : ℕ) u := by
  rw [@tamagawaOmegaEulerFactor_of_prime (p : ℕ) ⟨p.2⟩ u]
  exact @localFactor_collapse (p : ℕ) ⟨p.2⟩ u z uΛ

/-- **The master Euler product at the scalar face is `F(u)`:**

`∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, u, 1, ∅, ∅)) = F(u)`. -/
lemma tprod_localFactor_scalarFace_eq_tamagawaOmegaEulerProduct (u : ℂ)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    ∏' p : {q : ℕ // q.Prime},
        (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight ∅ ∅ (K : ReductionData) 0 u 1 z uΛ)
      = tamagawaOmegaEulerProduct u := by
  rw [tprod_congr (localFactor_scalarFace_eq_tamagawaOmegaEulerFactor u z uΛ),
    tprod_tamagawaOmegaEulerFactor_primes u]
  rfl

/-! ### The limit -/

/-- For every `u : ℂ` with `‖u‖ ≤ 1`,

`lim_{X → ∞} 𝒵_{∅, ∅, X}(0; u, 1, ∅, ∅) = F(u)`,

with `𝒵_{Λ, Π, X}` the multivariable generating function and `F` the Euler product
`∏'_p (δ_p(1) + (1 - δ_p(1)) u)`: the limit exists and equals `F(u)`. -/
@[bsd_tamagawa "T041j"]
theorem tendsto_tamagawaGeneratingFunction_tamagawaOmegaEulerProduct {u : ℂ} (hu : ‖u‖ ≤ 1)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    Tendsto (tamagawaGeneratingFunction ∅ ∅ 0 u 1 z uΛ) atTop
      (𝓝 (tamagawaOmegaEulerProduct u)) := by
  have hs : (0 : ℝ) ≤ (0 : ℂ).re := by simp
  have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hz : ∀ ℓ : (∅ : Finset ℕ), ‖z ℓ‖ ≤ 1 := fun ℓ => (Finset.notMem_empty _ ℓ.2).elim
  have huΛ : ∀ K : (∅ : Finset ReductionData), ‖uΛ K‖ ≤ 1 :=
    fun K => (Finset.notMem_empty _ K.2).elim
  have hP : ∀ ℓ ∈ (∅ : Finset ℕ), Nat.Prime ℓ := by simp
  rw [← tprod_localFactor_scalarFace_eq_tamagawaOmegaEulerProduct u z uΛ]
  exact tendsto_tamagawaGeneratingFunction_tprod_localFactor ∅ ∅ (by simp) hP hs hu h1 hz huΛ

end WeierstrassCurve
