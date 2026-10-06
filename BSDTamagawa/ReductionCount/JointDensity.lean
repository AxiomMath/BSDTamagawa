/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.ReductionCount.GeneratingFunctionIdentity

/-!
# Existence and the joint generating function of `π_Λ`

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data (`Admissible Λ`). For each
multi-index `𝐫 = (r_K)_{K ∈ Λ} ∈ ℤ_{≥0}^Λ` the density

`π_Λ(𝐫) := lim_{X → ∞} #{E : Ht(E) ≤ X, ω_K(E) = r_K for all K ∈ Λ} / N(X)`

exists, its joint generating function is

`∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫) 𝐮^𝐫 = ∏_{p ∈ 𝒫} (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`,

and that Euler product converges absolutely and locally uniformly for **all** `𝐮 ∈ ℂ^Λ`.

## Main results

* `WeierstrassCurve.tendsto_jointReductionOmegaCount_div_integralShortNFCount`: the proportion of
  integral short Weierstrass models of height at most `X` with `ω_K(E) = r_K` for all `K ∈ Λ`
  tends to `π_Λ(𝐫)` as `X → ∞`.
* `WeierstrassCurve.tsum_jointReductionOmegaDensity_multiMonomial_eq_tprod`: the joint generating
  function `∑_𝐫 π_Λ(𝐫) 𝐮^𝐫` equals the Euler product over the primes, for every `𝐮 ∈ ℂ^Λ`.
* `WeierstrassCurve.multipliable_jointLocalFactor_primes`: the family of local factors is
  multipliable at every `𝐮 ∈ ℂ^Λ`.
* `WeierstrassCurve.hasProdLocallyUniformly_jointLocalFactor_primes`: the Euler product converges
  locally uniformly on `ℂ^Λ`.
* `WeierstrassCurve.hasProdUniformlyOn_subtype_of_eq_one`: a uniformly convergent `ℕ`-indexed
  product whose factors are `1` off a subtype converges uniformly when restricted to that subtype.
* `WeierstrassCurve.tprod_jointLocalFactor_primes`: the Euler product over the primes equals
  `jointReductionOmegaEulerProduct Λ 𝐮`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

/-! ### Reindexing a uniformly convergent product to a subtype -/

/-- **A uniformly convergent product restricted to a subtype of its index set.** If every index
outside `{n // P n}` contributes the neutral factor `1`, then the net of partial products over the
finite subsets of `{n // P n}` converges to the same limit, uniformly on the same set. -/
lemma hasProdUniformlyOn_subtype_of_eq_one {M β : Type*} [CommMonoid M] [UniformSpace M]
    {f : ℕ → β → M} {g : β → M} {E : Set β} {P : ℕ → Prop}
    (hone : ∀ n, ¬ P n → f n = 1) (h : HasProdUniformlyOn f g E) :
    HasProdUniformlyOn (fun q : {n : ℕ // P n} => f (q : ℕ)) g E := by
  classical
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at h ⊢
  intro v hv
  obtain ⟨S, hS⟩ := eventually_atTop.1 (h v hv)
  refine eventually_atTop.2 ⟨S.subtype P, fun T hT x hx => ?_⟩
  have hneutral : ∀ n ∈ T.image (Subtype.val : {n : ℕ // P n} → ℕ) ∪ S,
      n ∉ T.image (Subtype.val : {n : ℕ // P n} → ℕ) → f n x = 1 := fun n hn hn' =>
    congrFun (hone n fun hP => hn' (Finset.mem_image.2
      ⟨⟨n, hP⟩, hT (Finset.mem_subtype.2 ((Finset.mem_union.1 hn).resolve_left hn')), rfl⟩)) x
  have hprod : ∏ q ∈ T, f (q : ℕ) x
      = ∏ n ∈ T.image (Subtype.val : {n : ℕ // P n} → ℕ) ∪ S, f n x :=
    (Finset.prod_image fun a _ b _ hab => Subtype.coe_injective hab).symm.trans
      (Finset.prod_subset Finset.subset_union_left hneutral)
  change (g x, ∏ q ∈ T, f (q : ℕ) x) ∈ v
  rw [hprod]
  exact hS _ Finset.subset_union_right x hx

/-! ### The Euler product over the primes -/

variable {Λ : Finset ReductionData}

/-- The product over the primes

`∏_{p ∈ 𝒫} (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`

equals `F_Λ(𝐮) = ∏' p : ℕ, F_{Λ,p}(𝐮)`, the joint Euler product `jointReductionOmegaEulerProduct`.
-/
lemma tprod_jointLocalFactor_primes (hΛ : Admissible Λ) (u : Λ → ℂ) :
    ∏' p : {q : ℕ // q.Prime},
        (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K)
      = jointReductionOmegaEulerProduct Λ u :=
  (tprod_congr fun p : {q : ℕ // q.Prime} =>
      (@jointReductionOmegaEulerFactor_of_prime Λ (p : ℕ) ⟨p.2⟩ u).symm).trans
    (tprod_jointReductionOmegaEulerFactor_primes hΛ u)

/-! ### Existence of the joint density -/

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data and `𝐫 = (r_K)_{K ∈ Λ} ∈ ℤ_{≥0}^Λ` a
multi-index. Then

`lim_{X → ∞} #{E : Ht(E) ≤ X, ω_K(E) = r_K for all K ∈ Λ} / N(X) = π_Λ(𝐫)`,

with `π_Λ(𝐫)` the joint density `jointReductionOmegaDensity Λ 𝐫`. The numerator counts the pairs
`(a₄, a₆) ∈ ℤ²` whose short Weierstrass model is nonsingular, has naive height at most `X`, and
satisfies `ω_K = r_K` for every `K ∈ Λ`; the denominator is `N(X)`. -/
@[bsd_tamagawa "T040a"]
theorem tendsto_jointReductionOmegaCount_div_integralShortNFCount (hΛ : Admissible Λ)
    (r : Λ → ℕ) :
    Tendsto (fun X : ℝ =>
        ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
            ∧ ∀ K : Λ, reductionOmega (K : ReductionData) q.1 q.2 = r K }.ncard : ℝ)
          / integralShortNFCount X)
      atTop (𝓝 (jointReductionOmegaDensity Λ r)) :=
  tendsto_jointReductionOmegaProportion_jointReductionOmegaDensity hΛ r

/-! ### The joint generating function -/

/-- The family `(π_Λ(𝐫) 𝐮^𝐫)_{𝐫 ∈ ℤ_{≥0}^Λ}` is summable with sum the Euler product
`∏_{p ∈ 𝒫} (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`, at every `𝐮 ∈ ℂ^Λ`. -/
theorem hasSum_jointReductionOmegaDensity_multiMonomial_tprod (hΛ : Admissible Λ) (u : Λ → ℂ) :
    HasSum (fun r : Λ → ℕ => ((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u)
      (∏' p : {q : ℕ // q.Prime},
        (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K)) := by
  rw [tprod_jointLocalFactor_primes hΛ u]
  exact hasSum_jointReductionOmegaDensity_multiMonomial hΛ u

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every `𝐮 ∈ ℂ^Λ`,

`∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫) 𝐮^𝐫
  = ∏_{p ∈ 𝒫} (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`,

with `π_Λ(𝐫)` the joint density, `𝐮^𝐫` the multi-monomial and `δ_p(K)` the local reduction density,
entering `ℂ` as `((δ_p(K)).toReal : ℂ)`. -/
@[bsd_tamagawa "T040a"]
theorem tsum_jointReductionOmegaDensity_multiMonomial_eq_tprod (hΛ : Admissible Λ) (u : Λ → ℂ) :
    ∑' r : Λ → ℕ, ((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u
      = ∏' p : {q : ℕ // q.Prime},
        (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K) :=
  (hasSum_jointReductionOmegaDensity_multiMonomial_tprod hΛ u).tsum_eq

/-! ### Absolute and locally uniform convergence on `ℂ^Λ` -/

/-- At every `𝐮 ∈ ℂ^Λ` the family of local factors
`(1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)_{p ∈ 𝒫}` is `Multipliable`: the net of partial
products over the finite sets of primes converges. -/
@[bsd_tamagawa "T040a"]
theorem multipliable_jointLocalFactor_primes (hΛ : Admissible Λ) (u : Λ → ℂ) :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
        + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K :=
  (multipliable_jointReductionOmegaEulerFactor_primes hΛ u).congr fun p =>
    @jointReductionOmegaEulerFactor_of_prime Λ (p : ℕ) ⟨p.2⟩ u

/-- The partial products `∏_{p ∈ S} (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)` over the finite
sets `S` of primes, directed by inclusion, converge to the Euler product locally uniformly on
`ℂ^Λ`. -/
@[bsd_tamagawa "T040a"]
theorem hasProdLocallyUniformly_jointLocalFactor_primes (hΛ : Admissible Λ) :
    HasProdLocallyUniformly
      (fun (p : {q : ℕ // q.Prime}) (v : Λ → ℂ) =>
        1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * v K)
      (fun v : Λ → ℂ => ∏' p : {q : ℕ // q.Prime},
        (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * v K)) := by
  refine hasProdLocallyUniformly_of_forall_compact fun E hE => ?_
  have h := hasProdUniformlyOn_subtype_of_eq_one (P := Nat.Prime)
    (fun n hn => funext fun v => jointReductionOmegaEulerFactor_of_not_prime hn v)
    (hasProdUniformlyOn_jointReductionOmegaEulerFactor hΛ hE)
  refine (h.congr (Eventually.of_forall fun T v _ => Finset.prod_congr rfl fun p _ =>
    @jointReductionOmegaEulerFactor_of_prime Λ (p : ℕ) ⟨p.2⟩ v)).congr_right fun v _ =>
      (tprod_jointLocalFactor_primes hΛ v).symm

end WeierstrassCurve
