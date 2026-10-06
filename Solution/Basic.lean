/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono, Ashvin A. Swaminathan, David Kurniadi Angdinata, Sidharth Hariharan
-/
module

public import BSDTamagawa

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace BSDTamagawa.Challenge

open Filter Topology MeasureTheory ProbabilityTheory WeierstrassCurve

open BSDTamagawa.LocalReduction in
/-- **`T036` — the master Euler product.** For a finite `Λ ⊆ 𝒦 ∖ 𝒦₀`, a finite set of primes `Π`
and parameters with `Re(s) ≥ 0` and `‖u‖, ‖w‖, ‖z_ℓ‖, ‖u_K‖ ≤ 1`, `𝒵_{Λ,Π,X}` tends to
`∏_p (β_p + ∑_{K ∉ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))`; the product converges absolutely, and
uniformly on every compact set of such parameters. -/
theorem T036 :
    (∀ (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ},
      (∀ K ∈ Λ, K ∉ K0) → (∀ ℓ ∈ P, Nat.Prime ℓ) → 0 ≤ s.re → ‖u‖ ≤ 1 → ‖w‖ ≤ 1 →
      (∀ ℓ : P, ‖z ℓ‖ ≤ 1) → (∀ K : Λ, ‖uΛ K‖ ≤ 1) →
      Tendsto (tamagawaGeneratingFunction Λ P s u w z uΛ) atTop
        (𝓝 (∏' p : {q : ℕ // q.Prime},
          (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
            ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
              * localWeight Λ P (K : ReductionData) s u w z uΛ)))) ∧
    (∀ (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ},
      0 ≤ s.re → ‖u‖ ≤ 1 → ‖w‖ ≤ 1 → (∀ ℓ : P, ‖z ℓ‖ ≤ 1) → (∀ K : Λ, ‖uΛ K‖ ≤ 1) →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight Λ P (K : ReductionData) s u w z uΛ) ∧
    (∀ (Λ : Finset ReductionData) (P : Finset ℕ) {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))},
      IsCompact D →
      (∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
        (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) →
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
        D) :=
  ⟨tendsto_tamagawaGeneratingFunction_tprod_localFactor, multipliable_localFactor,
    hasProdUniformlyOn_localFactor⟩

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex in
/-- **`T040a` — the joint law of the reduction counts.** For an admissible finite `Λ`, the joint
density `π_Λ(𝐫)` exists for every `𝐫`,
`∑_𝐫 π_Λ(𝐫) 𝐮^𝐫 = ∏_p (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`, and the product converges
absolutely and locally uniformly on `ℂ^Λ`. -/
theorem T040a :
    (∀ {Λ : Finset ReductionData}, Admissible Λ → ∀ (r : Λ → ℕ),
      Tendsto (fun X : ℝ =>
          ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
              ∧ ∀ K : Λ, reductionOmega (K : ReductionData) q.1 q.2 = r K }.ncard : ℝ)
            / integralShortNFCount X)
        atTop (𝓝 (jointReductionOmegaDensity Λ r))) ∧
    (∀ {Λ : Finset ReductionData}, Admissible Λ → ∀ (u : Λ → ℂ),
      ∑' r : Λ → ℕ, ((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u
        = ∏' p : {q : ℕ // q.Prime},
          (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K)) ∧
    (∀ {Λ : Finset ReductionData}, Admissible Λ → ∀ (u : Λ → ℂ),
      Multipliable fun p : {q : ℕ // q.Prime} =>
        1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K) ∧
    (∀ {Λ : Finset ReductionData}, Admissible Λ →
      HasProdLocallyUniformly
        (fun (p : {q : ℕ // q.Prime}) (v : Λ → ℂ) =>
          1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * v K)
        (fun v : Λ → ℂ => ∏' p : {q : ℕ // q.Prime},
          (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * v K))) :=
  ⟨tendsto_jointReductionOmegaCount_div_integralShortNFCount,
    tsum_jointReductionOmegaDensity_multiMonomial_eq_tprod, multipliable_jointLocalFactor_primes,
    hasProdLocallyUniformly_jointLocalFactor_primes⟩

open BSDTamagawa.LocalReduction in
/-- **`T040b` — mean and variance of `ω_K`.** For `K ∉ 𝒦₀`, under the law of `ω_K(E)`,
`𝔼[ω_K] = ∑_p δ_p(K)` and `Var(ω_K) = ∑_p δ_p(K)(1 - δ_p(K))`, both series convergent. -/
theorem T040b :
    (∀ {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)),
      Summable (stratumLocalMass K) ∧
        ∫ n, (n : ℝ) ∂ (marginalReductionOmegaPMF hK).toMeasure
          = ∑' p : ℕ, stratumLocalMass K p) ∧
    (∀ {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)),
      Summable (fun p : ℕ => stratumLocalMass K p * (1 - stratumLocalMass K p)) ∧
        variance (fun n : ℕ => (n : ℝ)) (marginalReductionOmegaPMF hK).toMeasure
          = ∑' p : ℕ, stratumLocalMass K p * (1 - stratumLocalMass K p)) :=
  ⟨integral_marginalReductionOmega, variance_marginalReductionOmega⟩

open BSDTamagawa.LocalReduction in
/-- **`T040c` — the covariance of `ω_K` and `ω_{K'}`.** For distinct `K, K' ∉ 𝒦₀`, under the joint
law, `Cov(ω_K, ω_{K'}) = -∑_p δ_p(K) δ_p(K')`, the series convergent; on `ℤ_{≥0}^{K, K'}` and on
`ℤ_{≥0}²`. -/
theorem T040c :
    (∀ {K K' : ReductionData}, K ∉ (K0 : Set ReductionData) → K' ∉ (K0 : Set ReductionData) →
      ∀ (hne : K ≠ K'),
      Summable (fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p) ∧
        covariance (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexFst K K' hne) : ℝ))
            (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexSnd K K' hne) : ℝ))
            (jointReductionOmegaMeasure (pairFinset K K' hne))
          = -∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p) ∧
    (∀ {K K' : ReductionData}, K ∉ (K0 : Set ReductionData) → K' ∉ (K0 : Set ReductionData) →
      ∀ (hne : K ≠ K'),
      Summable (fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p) ∧
        covariance (fun q : ℕ × ℕ => (q.1 : ℝ)) (fun q : ℕ × ℕ => (q.2 : ℝ))
            (pairReductionOmegaMeasure K K' hne)
          = -∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p) :=
  ⟨covariance_pairReductionOmega, covariance_pairReductionOmega_prod⟩

/-- **`T041` — the law of `ω_Tam`.** The density `π_r` exists for every `r`;
`∑_r π_r u^r = ∏_p (δ_p(1) + (1 - δ_p(1)) u)` for every `u ∈ ℂ`, the product converging absolutely
and locally uniformly; and `𝔼[ω_Tam] = ∑_p (1 - δ_p(1))`, `Var(ω_Tam) = ∑_p δ_p(1)(1 - δ_p(1))`,
both series convergent. -/
theorem T041 :
    (∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure
      = ∑' p : ℕ, if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) ∧
    (Summable fun p : ℕ => if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal)
      else 0) ∧
    (variance (fun n : ℕ => (n : ℝ)) tamagawaOmegaMeasure
      = ∑' p : ℕ, if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal) else 0) ∧
    (∀ r : ℕ,
      Filter.Tendsto (fun X : ℝ =>
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
            tamagawaOmega q.1 q.2 = r}.ncard : ℝ) / integralShortNFCount X)
        Filter.atTop (nhds (tamagawaOmegaDensity r))) ∧
    (∀ u : ℂ,
      (∑' r : ℕ, ((tamagawaOmegaDensity r : ℝ) : ℂ) * u ^ r)
        = ∏' p : ℕ, (if h : p.Prime then
            ((@δ p ⟨h⟩ 1).toReal : ℂ) + (1 - ((@δ p ⟨h⟩ 1).toReal : ℂ)) * u else 1)) ∧
    (Summable fun p : ℕ => if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) ∧
    ((∀ u : ℂ, Multipliable fun p : ℕ => tamagawaOmegaEulerFactor p u) ∧
      HasProdLocallyUniformly tamagawaOmegaEulerFactor
        (fun u => ∏' p : ℕ, tamagawaOmegaEulerFactor p u)) :=
  ⟨integral_natCast_tamagawaOmegaMeasure, summable_δ_one_mul_one_sub_δ_one,
    variance_natCast_tamagawaOmegaMeasure, tendsto_tamagawaOmegaCount_div_integralShortNFCount,
    tsum_tamagawaOmegaDensity_mul_pow_eq_tprod_primes, summable_one_sub_δ_one,
    multipliable_and_hasProdLocallyUniformly_tamagawaOmegaEulerFactor⟩

/-- **`T042` — the densities `π_r` in closed form.**
`π_r = ∑_{S ⊆ 𝒫, |S| = r} ∏_{p ∈ S} (1 - δ_p(1)) ∏_{q ∉ S} δ_q(1)`, written out for `r = 0, 1, 2`,
with every series and product in it convergent. -/
theorem T042 :
    (∀ r : ℕ,
      tamagawaOmegaDensity r
        = ∑' S : {S : Finset ℕ // S.card = r},
            (∏ p ∈ (S : Finset ℕ), (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0)) *
              ∏' q : {x : ℕ // x ∉ (S : Finset ℕ)},
                (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (tamagawaOmegaDensity 0 = ∏' q : ℕ, (if h : q.Prime then (@δ q ⟨h⟩ 1).toReal else 1)) ∧
    (tamagawaOmegaDensity 1
      = ∑' p : ℕ, (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) *
          ∏' q : {x : ℕ // x ≠ p},
            (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (tamagawaOmegaDensity 2
      = ∑' pq : {pq : ℕ × ℕ // pq.1 < pq.2},
          (if h : (pq : ℕ × ℕ).1.Prime then 1 - (@δ (pq : ℕ × ℕ).1 ⟨h⟩ 1).toReal else 0) *
            (if h : (pq : ℕ × ℕ).2.Prime then 1 - (@δ (pq : ℕ × ℕ).2 ⟨h⟩ 1).toReal else 0) *
            ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
              (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (∀ S : Finset ℕ,
      Multipliable fun q : {x : ℕ // x ∉ S} =>
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (Multipliable fun q : ℕ => (if h : q.Prime then (@δ q ⟨h⟩ 1).toReal else 1)) ∧
    (∀ p : ℕ,
      Multipliable fun q : {x : ℕ // x ≠ p} =>
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (∀ p q : ℕ,
      Multipliable fun r : {x : ℕ // x ≠ p ∧ x ≠ q} =>
        (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (∀ r : ℕ,
      Summable fun S : {S : Finset ℕ // S.card = r} =>
        (∏ p ∈ (S : Finset ℕ), (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0)) *
          ∏' q : {x : ℕ // x ∉ (S : Finset ℕ)},
            (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (Summable fun p : ℕ => (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) *
      ∏' q : {x : ℕ // x ≠ p},
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (Summable fun pq : {pq : ℕ × ℕ // pq.1 < pq.2} =>
      (if h : (pq : ℕ × ℕ).1.Prime then 1 - (@δ (pq : ℕ × ℕ).1 ⟨h⟩ 1).toReal else 0) *
        (if h : (pq : ℕ × ℕ).2.Prime then 1 - (@δ (pq : ℕ × ℕ).2 ⟨h⟩ 1).toReal else 0) *
        ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
          (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1)) :=
  ⟨tamagawaOmegaDensity_eq_tsum_card_eq, tamagawaOmegaDensity_zero_eq_tprod,
    tamagawaOmegaDensity_one_eq_tsum, tamagawaOmegaDensity_two_eq_tsum, multipliable_δ_one_notMem,
    multipliable_δ_one, multipliable_δ_one_ne, multipliable_δ_one_ne_pair,
    summable_subsetTerm_card_eq, summable_one_sub_δ_one_mul_tprod,
    summable_one_sub_δ_one_mul_tprod_pair⟩

open BSDTamagawa.ValuationMean in
/-- **`T043` — the mean of `v_ℓ(Tam)`.** For a prime `ℓ`, under the law of `v_ℓ(Tam(E))`,
`𝔼[v_ℓ(Tam)] = ∑_p ∑_{t ≥ 1} δ_p(t) v_ℓ(t)`, the double series convergent. -/
theorem T043 :
    ∀ {ℓ : ℕ}, ℓ.Prime →
      (Summable fun p : ℕ => if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0) ∧
        ∫ j, ((j (singletonIdx ℓ) : ℕ) : ℝ) ∂(tamagawaValuationMeasure {ℓ})
          = ∑' p : ℕ, if h : p.Prime then
              ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0 :=
  valuation_mean

open BSDTamagawa.MultiIndex in
/-- **`T044a` — the joint law of the valuations of `Tam`.** For a finite set of primes `Π`, the
density `Q_Π(𝐣)` exists for every `𝐣`, and for `‖z_ℓ‖ ≤ 1`,
`∑_𝐣 Q_Π(𝐣) 𝐳^𝐣 = ∏_p ∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}`, the product converging absolutely
and uniformly on the closed polydisc. -/
theorem T044a :
    (∀ (P : Finset ℕ), (∀ ℓ ∈ P, Nat.Prime ℓ) → ∀ (j : P → ℕ),
      Tendsto (fun X : ℝ =>
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
            ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ}.ncard : ℝ) /
            integralShortNFCount X)
        atTop (𝓝 (tamagawaValuationDensity P j))) ∧
    (∀ (P : Finset ℕ), (∀ ℓ ∈ P, Nat.Prime ℓ) → ∀ {z : P → ℂ}, (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
      ∑' j : P → ℕ, ((tamagawaValuationDensity P j : ℝ) : ℂ) * multiMonomial j z
        = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) ∧
    (∀ (P : Finset ℕ) {z : P → ℂ}, (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) ∧
    (∀ (P : Finset ℕ) {z : P → ℂ}, (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
      Summable fun p : {q : ℕ // q.Prime} =>
        ‖(∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) - 1‖) ∧
    (∀ (P : Finset ℕ),
      HasProdUniformlyOn
        (fun (p : {q : ℕ // q.Prime}) (z : P → ℂ) =>
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
        (fun z : P → ℂ => ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
        {z : P → ℂ | ∀ ℓ : P, ‖z ℓ‖ ≤ 1}) :=
  ⟨tendsto_tamagawaValuationCount_div_integralShortNFCount,
    tsum_tamagawaValuationDensity_mul_multiMonomial_eq_tprod_primes,
    multipliable_tamagawaValuationEulerFactor_primes,
    summable_norm_tamagawaValuationEulerFactor_sub_one_primes,
    hasProdUniformlyOn_tamagawaValuationEulerFactor_primes⟩

/-- **`T044b` — no prime of `A` divides `Tam`.** For a finite set `A` of primes,
`P(ℓ ∤ Tam(E) for all ℓ ∈ A) = ∏_p ∑_{(t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t)`, the product convergent. -/
theorem T044b :
    (∀ (A : Finset ℕ), (∀ ℓ ∈ A, Nat.Prime ℓ) →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) ∧
    (∀ (A : Finset ℕ), (∀ ℓ ∈ A, Nat.Prime ℓ) →
      (tamagawaValuationMeasure A {j : A → ℕ | ∀ ℓ : A, j ℓ = 0}).toReal
        = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) :=
  ⟨multipliable_coprimeDensity_primes, tamagawaValuationMeasure_notDvd_toReal⟩

/-- **`T044c` — `ℓ` divides `Tam`.** For a prime `ℓ`, `P(ℓ ∣ Tam(E)) = 1 - ∏_p ∑_{ℓ ∤ t} δ_p(t)`,
the product convergent. -/
theorem T044c :
    (∀ {l : ℕ}, l.Prime →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) ∧
    (∀ {l : ℕ}, l.Prime →
      (tamagawaValuationMeasure {l}
          {j : ↥({l} : Finset ℕ) → ℕ | j ⟨l, Finset.mem_singleton_self l⟩ ≠ 0}).toReal
        = 1 - ∏' p : {q : ℕ // q.Prime},
          ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) :=
  ⟨multipliable_notDvdDensity_primes, tamagawaValuationMeasure_dvd_toReal⟩

/-- **`T044d` — `Tam` is odd.** `P(Tam(E) odd) = ∏_p ∑_{t odd} δ_p(t)`, the product convergent. -/
theorem T044d :
    (Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ↥{t : ℕ | Odd t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) ∧
    ((tamagawaValuationMeasure {2}
        {j : ↥({2} : Finset ℕ) → ℕ | ∀ ℓ : ↥({2} : Finset ℕ), j ℓ = 0}).toReal
      = ∏' p : {q : ℕ // q.Prime}, ∑' t : ↥{t : ℕ | Odd t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) :=
  ⟨multipliable_oddDensity_primes, tamagawaValuationMeasure_odd_toReal⟩

open scoped Classical in
/-- **`T045` — the joint generating function of `(ω_Tam, Tam)`.** For `Re(s) ≥ 0` and `‖u‖ ≤ 1`,
`N(X)⁻¹ ∑_{H(E) ≤ X} u^{ω_Tam(E)} Tam(E)^{-s}` tends to
`∏_p (δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s})`. -/
theorem T045 :
    ∀ {s u : ℂ}, 0 ≤ s.re → ‖u‖ ≤ 1 →
      Tendsto (fun X : ℝ =>
          (∑' q : ℤ × ℤ,
              if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
                u ^ tamagawaOmega q.1 q.2 * (tamagawaProduct q.1 q.2 : ℂ) ^ (-s)
              else 0) / (integralShortNFCount X : ℂ)) atTop
        (𝓝 (∏' p : {q : ℕ // q.Prime},
          (((@δ (p : ℕ) ⟨p.2⟩ 1).toReal : ℂ)
            + u * ∑' t : ℕ,
                if 2 ≤ t then ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0))) :=
  tendsto_tamagawaOmegaDirichletAverage_tprod_omegaTamLocalFactor

/-- **`T046a` — the law of `Ω(Tam)`.** The density `ρ_b` exists for every `b`, and for `‖w‖ ≤ 1`,
`∑_b ρ_b w^b = ∏_p ∑_{t ≥ 1} δ_p(t) w^{Ω(t)}`, the product converging absolutely. -/
theorem T046a :
    (∀ b : ℕ,
      Tendsto (fun X : ℝ =>
          ({p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
            ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b}.ncard : ℝ) /
            integralShortNFCount X)
        atTop (𝓝 (cardFactorsTamagawaDensity b))) ∧
    (∀ {w : ℂ}, ‖w‖ ≤ 1 →
      ∑' b : ℕ, ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b
        = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t) ∧
    (∀ {w : ℂ}, ‖w‖ ≤ 1 →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t) ∧
    (∀ {w : ℂ}, ‖w‖ ≤ 1 →
      Summable fun p : {q : ℕ // q.Prime} =>
        ‖(∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t)
          - 1‖) :=
  ⟨tendsto_cardFactorsTamagawaCount_div_integralShortNFCount,
    tsum_cardFactorsTamagawaDensity_mul_pow_eq_tprod_primes,
    multipliable_cardFactorsEulerFactor_primes,
    summable_norm_cardFactorsEulerFactor_sub_one_primes⟩

/-- **`T046b` — the mean of `Ω(Tam)`.** `𝔼[Ω(Tam)] = ∑_p ∑_{t ≥ 1} δ_p(t) Ω(t)`, the double series
convergent. -/
theorem T046b :
    (Summable fun p : ℕ => if h : p.Prime then
        ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0) ∧
      ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
        = ∑' p : ℕ, if h : p.Prime then
            ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  cardFactors_mean

/-- **`T046c` — `𝔼[ω_Tam] ≤ 𝔼[Ω(Tam)] < ∞`.** The second mean is the convergent double series
`∑_p ∑_{t ≥ 1} δ_p(t) Ω(t)`. -/
theorem T046c :
    (∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure ≤ ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure) ∧
      (Summable fun p : ℕ => if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0) ∧
        ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
          = ∑' p : ℕ, if h : p.Prime then
              ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  omegaTamMean_le_cardFactors_mean

/-- **`T057a` — the covariance of two valuations.** For distinct primes `ℓ, ℓ'`,
`Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) = ∑_p C_p(ℓ, ℓ')`, the series absolutely convergent; on
`ℤ_{≥0}^{ℓ, ℓ'}` and on `ℤ_{≥0}²`. -/
theorem T057a :
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
        covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
            (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
            (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))
          = ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ') ∧
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ∀ (hne : ℓ ≠ ℓ'),
      (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
        covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
            (tamagawaValuationProdMeasure ℓ ℓ' hne)
          = ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ') :=
  ⟨covariance_tamagawaValuation, covariance_tamagawaValuation_prod⟩

/-- **`T057b` — the covariance is negative.** For distinct primes `ℓ, ℓ'`,
`Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0`; on `ℤ_{≥0}^{ℓ, ℓ'}` and on `ℤ_{≥0}²`. -/
theorem T057b :
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)) < 0) ∧
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ∀ (hne : ℓ ≠ ℓ'),
      covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
          (tamagawaValuationProdMeasure ℓ ℓ' hne) < 0) :=
  ⟨covariance_tamagawaValuation_neg, covariance_tamagawaValuation_prod_neg⟩

/-- **`T057c` — the covariance decays.** There is an absolute `C > 0` with
`|Cov(v_ℓ(Tam), v_{ℓ'}(Tam))| ≤ C / (ℓℓ')²` for all distinct primes `ℓ, ℓ'`; in particular the
covariance tends to `0` as `ℓℓ' → ∞`. -/
theorem T057c :
    (∃ C : ℝ, 0 < C ∧ ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
        ≤ C / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2) ∧
    (∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' → N ≤ ℓ * ℓ' →
        |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
            (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
            (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
          < ε) :=
  ⟨exists_covariance_decay_bound, covariance_tamagawaValuation_tendsto_zero⟩

/-- **`T058` — the correlation of `ω_Tam` and `Ω(Tam)`.** Under their joint law,
`Cov(ω_Tam, Ω(Tam)) = ∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)`, the series absolutely convergent, and both
variances are positive, so the correlation is a well-defined real number. -/
theorem T058 :
    ((Summable fun p : ℕ => |if h : p.Prime then
        (@δ p ⟨h⟩ 1).toReal
          * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
        else 0|) ∧
      covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
          jointOmegaCardFactorsMeasure
        = ∑' p : ℕ, if h : p.Prime then
            (@δ p ⟨h⟩ 1).toReal
              * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
            else 0) ∧
    (0 < variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure ∧
      0 < variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure ∧
      0 < Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
            * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure) ∧
      covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
            jointOmegaCardFactorsMeasure
          / Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
            * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure)
        = (∑' p : ℕ, if h : p.Prime then
              (@δ p ⟨h⟩ 1).toReal
                * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
              else 0)
            / Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
              * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure)) :=
  ⟨covariance_omegaCardFactorsTamagawa, corr_omegaCardFactorsTamagawa⟩

/-- **`T059a` — the moments of `Tam`.** For every `k`, `M_k = ∑_{m ≥ 1} P_Tam(m) m^k` converges
absolutely and `M_k = ∏_p ∑_{t ≥ 1} δ_p(t) t^k`. -/
theorem T059a :
    (∀ k : ℕ, Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k) ∧
    (∀ k : ℕ,
      ((tamagawaMoment k : ℝ) : ℂ)
        = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)) :=
  ⟨summable_tamagawaDensity_succ_mul_pow, ofReal_tamagawaMoment_eq_tprod_momentLocalFactor⟩

/-- **`T059b` — the tail of `Tam`.** For every `k` and `M ≥ 1`, `∑_{m ≥ M} P_Tam(m) ≤ M_k / M^k`;
so the tail decays faster than every power of `M`. -/
theorem T059b :
    (∀ (k : ℕ) {M : ℕ}, 1 ≤ M →
      (∑' n : ℕ, tamagawaDensity (n + M)) ≤ tamagawaMoment k / (M : ℝ) ^ k) ∧
    (∀ k : ℕ,
      ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M → (∑' n : ℕ, tamagawaDensity (n + M)) ≤ C / (M : ℝ) ^ k) :=
  ⟨tsum_tamagawaDensity_tail_le, exists_tsum_tamagawaDensity_tail_le⟩

end BSDTamagawa.Challenge

end
