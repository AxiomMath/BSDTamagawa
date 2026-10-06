/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.MasterEulerProduct
public import BSDTamagawa.GeneratingFunction.ScalarLocalFactorDeviation
public import BSDTamagawa.PrimeCount.DegeneratePoint
public import BSDTamagawa.GeneratingFunction.LocalFactorCollapse

/-!
# The joint generating function of `(ω_Tam, Tam)`

For `Re(s) ≥ 0` and `‖u‖ ≤ 1`,

`lim_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} Tam(E)^{-s}
  = ∏_{p ∈ 𝒫} (δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s})`,

where `E` runs over the integral short Weierstrass models `E(a₄, a₆)` with `Δ ≠ 0`, `N(X)` counts
those of naive height `Ht(E) ≤ X`, `ω_Tam(E)` is the number of primes dividing the Tamagawa product
`Tam(E)`, and `δ_p(t)` is the local density of Tamagawa number `t` at `p`. The identity is the
specialisation of the master Euler product for the generating function `𝒵` to the face `Λ = Π = ∅`,
`w = 1`, on which the local weight is `Φ_p(K) = u^{𝟙[c(K) > 1]} c(K)^{-s}`.

## Main results

* `WeierstrassCurve.localWeight_omegaTamFace`: on the face `Λ = Π = ∅`, `w = 1`, the local weight
  is `(if 1 < c(K) then u else 1) · c(K)^{-s}`.
* `WeierstrassCurve.hasSum_δ_toReal_mul_omegaTamFaceWeight`:
  `∑_t δ_p(t) u^{𝟙[t > 1]} t^{-s} = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s}`.
* `WeierstrassCurve.localFactor_omegaTamFace`: at a prime `p`,
  `β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, u, 1, ∅, ∅) = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s}`.
* `WeierstrassCurve.tamagawaGeneratingFunction_omegaTamFace`: `𝒵_{∅, ∅, X}(s; u, 1, ∅, ∅)` is the
  average `(1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} Tam(E)^{-s}`.
* `WeierstrassCurve.tendsto_tamagawaOmegaDirichletAverage_tprod_omegaTamLocalFactor`: the limit
  formula.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex BSDTamagawa.DegeneratePoint

/-! ### The local weight on the face `Λ = Π = ∅`, `w = 1` -/

/-- On the face `Λ = Π = ∅`, `w = 1`, the local weight `Φ_p(K)` is
`u^{𝟙[c(K) > 1]} c(K)^{-s}`, written as `(if 1 < c(K) then u else 1) · c(K)^{-s}`. -/
lemma localWeight_omegaTamFace (K : ReductionData) (s u : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset ReductionData) → ℂ) :
    localWeight ∅ ∅ K s u 1 z uΛ = (if 1 < K.2 then u else 1) * ((K.2 : ℕ) : ℂ) ^ (-s) := by
  rw [localWeight]
  simp [multiMonomial]

/-- For `Re(s) ≥ 0` and `‖u‖ ≤ 1`, `‖u^{𝟙[t > 1]} t^{-s}‖ ≤ 1` for every `t : ℕ`. -/
lemma norm_omegaTamFaceWeight_le_one {s u : ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (t : ℕ) :
    ‖(if 1 < t then u else 1) * (t : ℂ) ^ (-s)‖ ≤ 1 := by
  have hfst : ‖(if 1 < t then u else 1 : ℂ)‖ ≤ 1 := by
    split
    · exact hu
    · simp
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hfst).trans (norm_natCast_cpow_neg_le_one hs t)

/-! ### The `t`-series, split at `t = 1` -/

variable (p : ℕ)

/-- For `Re(s) ≥ 0` the tail series `∑_{t ≥ 2} δ_p(t) t^{-s}` converges absolutely. -/
lemma summable_δ_toReal_mul_natCast_cpow [Fact p.Prime] {s : ℂ} (hs : 0 ≤ s.re) :
    Summable fun t : ℕ => if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0 := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
    (hasSum_δ_toReal p).summable)
  by_cases ht : 2 ≤ t
  · rw [ite_eq_left ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (norm_natCast_cpow_neg_le_one hs t)
  · rw [ite_eq_right ht]
    simp [ENNReal.toReal_nonneg]

/-- For `Re(s) ≥ 0`,

`∑_{t} δ_p(t) u^{𝟙[t > 1]} t^{-s} = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s}`,

as a `HasSum`. -/
lemma hasSum_δ_toReal_mul_omegaTamFaceWeight [Fact p.Prime] {s u : ℂ} (hs : 0 ≤ s.re) :
    HasSum (fun t : ℕ => ((δ p t).toReal : ℂ) * ((if 1 < t then u else 1) * (t : ℂ) ^ (-s)))
      (((δ p 1).toReal : ℂ)
        + u * ∑' t : ℕ, if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0) := by
  have hG := (summable_δ_toReal_mul_natCast_cpow p hs).hasSum
  have h1 : HasSum (fun t : ℕ => if t = 1 then ((δ p 1).toReal : ℂ) else 0)
      ((δ p 1).toReal : ℂ) := hasSum_ite_eq 1 _
  have hfun : (fun t : ℕ => (if t = 1 then ((δ p 1).toReal : ℂ) else 0)
        + u * (if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0))
      = fun t : ℕ => ((δ p t).toReal : ℂ) * ((if 1 < t then u else 1) * (t : ℂ) ^ (-s)) := by
    funext t
    rcases eq_or_ne t 1 with rfl | ht1
    · simp
    · rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp [δ_zero]
      · rw [ite_eq_right ht1, ite_eq_left (show 2 ≤ t by omega), ite_eq_left (show 1 < t by omega),
          zero_add]
        ring
  rw [← hfun]
  exact h1.add (hG.mul_left u)

/-! ### Absolute summability over `𝒦`, and the fibrewise sum -/

/-- For `Re(s) ≥ 0` and `‖u‖ ≤ 1`, the term `δ_p(K) u^{𝟙[c(K) > 1]} c(K)^{-s}` has norm at most
`δ_p(K)`, for every `K ∈ 𝒦`. -/
lemma norm_deltaP_toReal_mul_omegaTamFaceWeight_le [Fact p.Prime] {s u : ℂ} (hs : 0 ≤ s.re)
    (hu : ‖u‖ ≤ 1) (K : ReductionData) :
    ‖((deltaP p K).toReal : ℂ) * ((if 1 < K.2 then u else 1) * ((K.2 : ℕ) : ℂ) ^ (-s))‖
      ≤ (deltaP p K).toReal := by
  have hnorm : ‖((deltaP p K).toReal : ℂ)‖ = (deltaP p K).toReal := by
    rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  rw [norm_mul, hnorm]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg
    (norm_omegaTamFaceWeight_le_one hs hu K.2)

/-- For `Re(s) ≥ 0` and `‖u‖ ≤ 1`, the series `∑_{K ∈ 𝒦} δ_p(K) u^{𝟙[c(K) > 1]} c(K)^{-s}`
converges absolutely. -/
lemma summable_deltaP_toReal_mul_omegaTamFaceWeight [Fact p.Prime] {s u : ℂ} (hs : 0 ≤ s.re)
    (hu : ‖u‖ ≤ 1) :
    Summable fun K : ReductionData =>
      ((deltaP p K).toReal : ℂ) * ((if 1 < K.2 then u else 1) * ((K.2 : ℕ) : ℂ) ^ (-s)) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_deltaP_toReal_mul_omegaTamFaceWeight_le p hs hu) (hasSum_deltaP_toReal p).summable)

/-- For `Re(s) ≥ 0` and `‖u‖ ≤ 1`,

`∑_{K ∈ 𝒦} δ_p(K) u^{𝟙[c(K) > 1]} c(K)^{-s} = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s}`,

as a `HasSum`. -/
lemma hasSum_deltaP_toReal_mul_omegaTamFaceWeight [Fact p.Prime] {s u : ℂ} (hs : 0 ≤ s.re)
    (hu : ‖u‖ ≤ 1) :
    HasSum (fun K : ReductionData =>
        ((deltaP p K).toReal : ℂ) * ((if 1 < K.2 then u else 1) * ((K.2 : ℕ) : ℂ) ^ (-s)))
      (((δ p 1).toReal : ℂ)
        + u * ∑' t : ℕ, if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0) := by
  have hsum := summable_deltaP_toReal_mul_omegaTamFaceWeight p hs hu
  have hfib := (((Equiv.prodComm ℕ KodairaSymbol).hasSum_iff).2 hsum.hasSum).prod_fiberwise
    fun t => (hasSum_deltaP_toReal_kodaira p t).mul_right
      ((if 1 < t then u else 1) * (t : ℂ) ^ (-s))
  have heq : ∑' K : ReductionData,
        ((deltaP p K).toReal : ℂ) * ((if 1 < K.2 then u else 1) * ((K.2 : ℕ) : ℂ) ^ (-s))
      = ((δ p 1).toReal : ℂ)
        + u * ∑' t : ℕ, if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0 :=
    hfib.unique (hasSum_δ_toReal_mul_omegaTamFaceWeight p hs)
  rw [← heq]
  exact hsum.hasSum

/-! ### The local factor on this face -/

/-- For a prime `p`, `Re(s) ≥ 0` and `‖u‖ ≤ 1`,

`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, u, 1, ∅, ∅) = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s}`,

with `β_p` the trivial-stratum mass, `δ_p(K)` the local reduction density, `δ_p(t)` the local
Tamagawa density and `Φ_p` the local weight. -/
theorem localFactor_omegaTamFace [Fact p.Prime] {s u : ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    ((β p).toReal : ℂ)
        + ∑' K : ↥(K0ᶜ : Set ReductionData),
            ((deltaP p (K : ReductionData)).toReal : ℂ)
              * localWeight ∅ ∅ (K : ReductionData) s u 1 z uΛ
      = ((δ p 1).toReal : ℂ)
          + u * ∑' t : ℕ, if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0 := by
  have hface : (fun K : ReductionData =>
        ((deltaP p K).toReal : ℂ) * localWeight ∅ ∅ K s u 1 z uΛ)
      = fun K : ReductionData => ((deltaP p K).toReal : ℂ)
          * ((if 1 < K.2 then u else 1) * ((K.2 : ℕ) : ℂ) ^ (-s)) :=
    funext fun K => by rw [localWeight_omegaTamFace]
  have htot : HasSum (fun K : ReductionData =>
      ((deltaP p K).toReal : ℂ) * localWeight ∅ ∅ K s u 1 z uΛ)
      (((δ p 1).toReal : ℂ)
        + u * ∑' t : ℕ, if 2 ≤ t then ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0) := by
    rw [hface]
    exact hasSum_deltaP_toReal_mul_omegaTamFaceWeight p hs hu
  have hone : ∀ K ∈ K0, localWeight ∅ ∅ K s u 1 z uΛ = 1 :=
    fun K hK => localWeight_eq_one ∅ ∅ hK (by simp) s u 1 z uΛ
  have hK0 : ∑' K : ↥K0, (((deltaP p (K : ReductionData)).toReal : ℂ)
      * localWeight ∅ ∅ (K : ReductionData) s u 1 z uΛ) = ((β p).toReal : ℂ) := by
    rw [tsum_subtype_K0 (M := ℂ) fun K => ((deltaP p K).toReal : ℂ)
      * localWeight ∅ ∅ K s u 1 z uΛ,
      hone (KodairaSymbol.I 0, 1) (by simp [K0]), hone (KodairaSymbol.I 1, 1) (by simp [K0]),
      β_add, ENNReal.toReal_add (deltaP_ne_top p _) (deltaP_ne_top p _)]
    push_cast
    ring
  rw [← hK0, htot.summable.tsum_subtype_add_tsum_subtype_compl K0, htot.tsum_eq]

/-! ### The Euler product on this face -/

/-- For `Re(s) ≥ 0` and `‖u‖ ≤ 1`,

`∏_{p ∈ 𝒫} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, u, 1, ∅, ∅))
  = ∏_{p ∈ 𝒫} (δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s})`. -/
lemma tprod_localFactor_omegaTamFace {s u : ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    ∏' p : {q : ℕ // q.Prime},
        (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight ∅ ∅ (K : ReductionData) s u 1 z uΛ)
      = ∏' p : {q : ℕ // q.Prime},
          (((@δ (p : ℕ) ⟨p.2⟩ 1).toReal : ℂ)
            + u * ∑' t : ℕ,
                if 2 ≤ t then ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0) :=
  tprod_congr fun p => @localFactor_omegaTamFace (p : ℕ) ⟨p.2⟩ s u hs hu z uΛ

/-! ### The generating function on this face is the average of the statement -/

open scoped Classical in
/-- On the face `Λ = Π = ∅`, `w = 1`, for every `s`, `u` and `X`,

`𝒵_{∅, ∅, X}(s; u, 1, ∅, ∅) = (1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} Tam(E)^{-s}`. -/
lemma tamagawaGeneratingFunction_omegaTamFace (s u : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset ReductionData) → ℂ) (X : ℝ) :
    tamagawaGeneratingFunction ∅ ∅ s u 1 z uΛ X
      = (∑' q : ℤ × ℤ,
          if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
            u ^ tamagawaOmega q.1 q.2 * (tamagawaProduct q.1 q.2 : ℂ) ^ (-s)
          else 0) / (integralShortNFCount X : ℂ) := by
  rw [tamagawaGeneratingFunction]
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
  · rw [ite_eq_left hq, ite_eq_left hq]
    simp [multiMonomial, kodairaMonomial_empty]
  · rw [ite_eq_right hq, ite_eq_right hq]

/-! ### The limit formula -/

open scoped Classical in
/-- For `Re(s) ≥ 0` and `‖u‖ ≤ 1`,

`lim_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} Tam(E)^{-s}
  = ∏_{p ∈ 𝒫} (δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s})`,

with `N(X)` the number of integral short Weierstrass models of naive height at most `X`, `ω_Tam`
the number of primes dividing the Tamagawa product `Tam`, and `δ_p(t)` the local Tamagawa density
at `p`. -/
@[bsd_tamagawa "T045"]
theorem tendsto_tamagawaOmegaDirichletAverage_tprod_omegaTamLocalFactor {s u : ℂ}
    (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ,
            if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
              u ^ tamagawaOmega q.1 q.2 * (tamagawaProduct q.1 q.2 : ℂ) ^ (-s)
            else 0) / (integralShortNFCount X : ℂ)) atTop
      (𝓝 (∏' p : {q : ℕ // q.Prime},
        (((@δ (p : ℕ) ⟨p.2⟩ 1).toReal : ℂ)
          + u * ∑' t : ℕ,
              if 2 ≤ t then ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0))) := by
  have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hz : ∀ ℓ : (∅ : Finset ℕ), ‖(fun _ => (0 : ℂ)) ℓ‖ ≤ 1 :=
    fun ℓ => (Finset.notMem_empty _ ℓ.2).elim
  have huΛ : ∀ K : (∅ : Finset ReductionData), ‖(fun _ => (0 : ℂ)) K‖ ≤ 1 :=
    fun K => (Finset.notMem_empty _ K.2).elim
  have hP : ∀ ℓ ∈ (∅ : Finset ℕ), Nat.Prime ℓ := by simp
  have hface : (fun X : ℝ =>
      (∑' q : ℤ × ℤ,
          if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
            u ^ tamagawaOmega q.1 q.2 * (tamagawaProduct q.1 q.2 : ℂ) ^ (-s)
          else 0) / (integralShortNFCount X : ℂ))
      = tamagawaGeneratingFunction ∅ ∅ s u 1 (fun _ => 0) (fun _ => 0) :=
    funext fun X =>
      (tamagawaGeneratingFunction_omegaTamFace s u (fun _ => 0) (fun _ => 0) X).symm
  rw [hface, ← tprod_localFactor_omegaTamFace hs hu (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))]
  exact tendsto_tamagawaGeneratingFunction_tprod_localFactor ∅ ∅ (by simp) hP hs hu h1 hz huΛ

end WeierstrassCurve
