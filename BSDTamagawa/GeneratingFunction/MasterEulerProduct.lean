/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.TruncationLimit

/-!
# The master Euler product

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data, let `Π` be a finite set of primes, and
let `𝒵_{Λ, Π, X}` be the multivariable generating function. Then for every choice of parameters in
the closed polydisc `𝒟 = {Re(s) ≥ 0, |u| ≤ 1, |w| ≤ 1, |z_ℓ| ≤ 1 ∀ ℓ ∈ Π, |u_K| ≤ 1 ∀ K ∈ Λ}`:

1. the limit `𝒵_{Λ, Π}(s; u, w, 𝐳, 𝐮) := lim_{X → ∞} 𝒵_{Λ, Π, X}(s; u, w, 𝐳, 𝐮)` exists;
2. the Euler product `∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))` converges
   absolutely, and uniformly on every compact subset of `𝒟`;
3. `𝒵_{Λ, Π}(s; u, w, 𝐳, 𝐮) = ∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))`.

Here `β_p` is the trivial-stratum mass, `δ_p(K)` the local reduction density, `Φ` the local weight
and `𝒦₀ = {(I₀, 1), (I₁, 1)}`.

## Main results

* `WeierstrassCurve.tendsto_tamagawaGeneratingFunction_tprod_localFactor`: assertions 1 and 3, as
  convergence of `𝒵_{Λ, Π, X}` to the Euler product.
* `WeierstrassCurve.multipliable_localFactor`: assertion 2, absolute convergence.
* `WeierstrassCurve.hasProdUniformlyOn_localFactor`: assertion 2, uniform convergence on a compact
  subset of `𝒟`.
* `WeierstrassCurve.tprod_localFactor_eq_tprod_masterLocalFactor`: the Euler product written out
  equals `∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ`.

## Implementation notes

The uniform convergence holds on every subset of `𝒟`, not only on compact ones, because the
majorant of the Weierstrass `M`-test does not depend on the parameters; the compactness hypothesis
of `hasProdUniformlyOn_localFactor` is therefore unused.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction

/-! ### The Euler product over the primes -/

/-- The product over the primes of `β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮)` equals
`∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ`. -/
lemma tprod_localFactor_eq_tprod_masterLocalFactor (Λ : Finset ReductionData) (P : Finset ℕ)
    {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    ∏' p : {q : ℕ // q.Prime},
        (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight Λ P (K : ReductionData) s u w z uΛ)
      = ∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ := by
  rw [← tprod_masterLocalFactor_primes Λ P hs hu hw hz huΛ]
  exact tprod_congr fun p =>
    (@masterLocalFactor_of_prime Λ P (p : ℕ) ⟨p.property⟩ s u w z uΛ).symm

/-! ### Existence of the limit and its value -/

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data and `Π` a finite set of primes, and
let the parameters satisfy `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π` and
`‖u_K‖ ≤ 1` for every `K ∈ Λ`. Then the limit of the generating function exists and equals the
master Euler product:

`lim_{X → ∞} 𝒵_{Λ, Π, X}(s; u, w, 𝐳, 𝐮)
  = ∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))`. -/
@[bsd_tamagawa "T036"]
theorem tendsto_tamagawaGeneratingFunction_tprod_localFactor (Λ : Finset ReductionData)
    (P : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Tendsto (tamagawaGeneratingFunction Λ P s u w z uΛ) atTop
      (𝓝 (∏' p : {q : ℕ // q.Prime},
        (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight Λ P (K : ReductionData) s u w z uΛ))) := by
  rw [tprod_localFactor_eq_tprod_masterLocalFactor Λ P hs hu hw hz huΛ]
  exact tendsto_tamagawaGeneratingFunction Λ P hΛ hP hs hu hw hz huΛ

/-! ### Absolute convergence -/

/-- At every point of the polydisc `𝒟` the family
`p ↦ β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮)`, indexed by the primes, is multipliable. -/
@[bsd_tamagawa "T036"]
theorem multipliable_localFactor (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
        ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          * localWeight Λ P (K : ReductionData) s u w z uΛ :=
  (multipliable_masterLocalFactor_primes Λ P hs hu hw hz huΛ).congr fun p =>
    @masterLocalFactor_of_prime Λ P (p : ℕ) ⟨p.property⟩ s u w z uΛ

/-! ### Uniform convergence -/

/-- For a finite set `S` of natural numbers and a finite set `T` of primes with
`S.subtype Nat.Prime ⊆ T`, `∏_{q ∈ T.image val ∪ S} L_q = ∏_{p ∈ T} L_p`, where `L_q` is
`masterLocalFactor` (which equals `1` at a non-prime index). -/
lemma prod_masterLocalFactor_union_eq (Λ : Finset ReductionData) (P : Finset ℕ) (S : Finset ℕ)
    (T : Finset {q : ℕ // q.Prime}) (hT : S.subtype Nat.Prime ⊆ T) (s u w : ℂ) (z : P → ℂ)
    (uΛ : Λ → ℂ) :
    ∏ q ∈ T.image (Subtype.val : {q : ℕ // q.Prime} → ℕ) ∪ S,
        masterLocalFactor Λ P q s u w z uΛ
      = ∏ p ∈ T, masterLocalFactor Λ P (p : ℕ) s u w z uΛ := by
  have hneutral : ∀ q ∈ T.image (Subtype.val : {q : ℕ // q.Prime} → ℕ) ∪ S,
      q ∉ T.image (Subtype.val : {q : ℕ // q.Prime} → ℕ) →
      masterLocalFactor Λ P q s u w z uΛ = 1 := fun q hq hq' =>
    masterLocalFactor_of_not_prime (fun hprime => hq' (Finset.mem_image.mpr
      ⟨⟨q, hprime⟩, hT (Finset.mem_subtype.mpr ((Finset.mem_union.mp hq).resolve_left hq')),
        rfl⟩)) s u w z uΛ
  calc ∏ q ∈ T.image (Subtype.val : {q : ℕ // q.Prime} → ℕ) ∪ S,
        masterLocalFactor Λ P q s u w z uΛ
      = ∏ q ∈ T.image (Subtype.val : {q : ℕ // q.Prime} → ℕ),
          masterLocalFactor Λ P q s u w z uΛ :=
        (Finset.prod_subset Finset.subset_union_left hneutral).symm
    _ = ∏ p ∈ T, masterLocalFactor Λ P (p : ℕ) s u w z uΛ :=
        Finset.prod_image fun a _ b _ h => Subtype.coe_injective h

/-- For every set `D` of parameter tuples contained in `𝒟`, the partial products of
`masterLocalFactor` over the finite sets of primes converge to `∏' p : ℕ, L_p` uniformly on `D`. -/
lemma hasProdUniformlyOn_masterLocalFactor_primes (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))}
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) :
    HasProdUniformlyOn
      (fun (p : {q : ℕ // q.Prime}) (x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)) =>
        masterLocalFactor Λ P (p : ℕ) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ) =>
        ∏' p : ℕ, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      D := by
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := (hasProdUniformlyOn_masterLocalFactor Λ P hD).tendstoUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff] at h
  obtain ⟨S, hS⟩ := eventually_atTop.mp (h ε hε)
  refine eventually_atTop.mpr ⟨S.subtype Nat.Prime, fun T hT x hx => ?_⟩
  obtain ⟨a, u, w, z, uΛ⟩ := x
  rw [← prod_masterLocalFactor_union_eq Λ P S T hT a u w z uΛ]
  exact hS _ Finset.subset_union_right _ hx

-- `hDcompact` is a hypothesis of the statement that the proof does not need.
set_option linter.unusedVariables false in
/-- Let `D` be a compact set of parameter tuples contained in the closed polydisc
`𝒟 = {Re(s) ≥ 0, ‖u‖ ≤ 1, ‖w‖ ≤ 1, ‖z_ℓ‖ ≤ 1 ∀ ℓ ∈ Π, ‖u_K‖ ≤ 1 ∀ K ∈ Λ}`. Then the partial
products of `β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮)` over the finite sets of primes
converge to `∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))` uniformly on `D`. -/
@[bsd_tamagawa "T036"]
theorem hasProdUniformlyOn_localFactor (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))} (hDcompact : IsCompact D)
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) :
    HasProdUniformlyOn
      (fun (p : {q : ℕ // q.Prime}) (x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)) =>
        ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight Λ P (K : ReductionData) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ) =>
        ∏' p : {q : ℕ // q.Prime},
          (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
            ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
              * localWeight Λ P (K : ReductionData) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
      D :=
  ((hasProdUniformlyOn_masterLocalFactor_primes Λ P hD).congr
      (Eventually.of_forall fun T ⟨a, u, w, z, uΛ⟩ _ => Finset.prod_congr rfl fun p _ =>
        @masterLocalFactor_of_prime Λ P (p : ℕ) ⟨p.property⟩ a u w z uΛ)).congr_right
    fun x hx => by
    obtain ⟨hs, hu, hw, hz, huΛ⟩ := hD x hx
    exact (tprod_localFactor_eq_tprod_masterLocalFactor Λ P hs hu hw hz huΛ).symm

end WeierstrassCurve
