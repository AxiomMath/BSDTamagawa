/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.FactorCount.LimitingDensityExists

/-!
# The joint limiting law of `(ω_Tam, Ω(Tam))`

The pair `(ω_Tam(E), Ω(Tam(E)))` has a joint limiting density `π(r, b)` over the family of short
Weierstrass curves ordered by height, and its bivariate generating function is the Euler product
`∏_{p ∈ 𝒫} g_p(u, w)` with `g_p(u, w) = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`.

## Main definitions

* `WeierstrassCurve.omegaCardFactorsEulerFactor`: the local factor `g_p(u, w)`.
* `WeierstrassCurve.omegaCardFactorsEulerProduct`: the Euler product `G(u, w) = ∏_p g_p(u, w)`.
* `WeierstrassCurve.omegaCardFactorsIndex`: the pair statistic as a `Bool`-multi-index.

## Main results

* `WeierstrassCurve.tendsto_jointOmegaCardFactorsAverage_omegaCardFactorsEulerProduct`: the
  bivariate empirical generating function converges on the closed bidisc:

    `(1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} w^{Ω(Tam(E))} ⟶ ∏_{p ∈ 𝒫} g_p(u, w)`

  for `‖u‖ ≤ 1` and `‖w‖ ≤ 1`.
* `WeierstrassCurve.tendsto_jointOmegaCardFactorsProportion_jointOmegaCardFactorsDensity`: the
  joint density exists:

    `lim_{X → ∞} #{E : Ht(E) ≤ X, Δ ≠ 0, ω_Tam(E) = r, Ω(Tam(E)) = b} / N(X) = π(r, b)`.

* `WeierstrassCurve.hasPolydiscExpansion_jointOmegaCardFactorsDensity`: `π` is a sub-probability
  vector whose generating function is `G` on the open bidisc.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex BSDTamagawa.DegeneratePoint
open BSDTamagawa.FiberCount BSDTamagawa.PrimeCountDensity

/-! ### §1. The local weight on the face `Λ = Π = ∅`, `s = 0` -/

/-- **`Φ_p` on the face `Λ = Π = ∅`, `s = 0`.** The local weight is `u^{𝟙[c(K) > 1]} w^{Ω(c(K))}`,
i.e. `u^{ω_{Tam,t}} w^{Ω(t)}` at `t = c(K)`, with `ω_{Tam,t} = 0` for `t ≤ 1` and `1` for `t ≥ 2`.
-/
lemma localWeight_omegaCardFactorsFace (K : ReductionData) (u w : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset ReductionData) → ℂ) :
    localWeight ∅ ∅ K 0 u w z uΛ
      = (if 1 < K.2 then u else 1) * w ^ ArithmeticFunction.cardFactors K.2 := by
  rw [localWeight]
  by_cases h : 1 < K.2 <;> simp [h, multiMonomial]

/-- **The face weight is bounded by `1` on the closed bidisc.** For `‖u‖ ≤ 1` and `‖w‖ ≤ 1`,
`‖u^{𝟙[t > 1]} w^{Ω(t)}‖ ≤ 1` at every `t : ℕ`. -/
lemma norm_omegaCardFactorsFaceWeight_le_one {u w : ℂ} (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (t : ℕ) :
    ‖(if 1 < t then u else 1) * w ^ ArithmeticFunction.cardFactors t‖ ≤ 1 := by
  have hfst : ‖(if 1 < t then u else 1 : ℂ)‖ ≤ 1 := by
    split
    · exact hu
    · simp
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) hfst).trans (pow_le_one₀ (norm_nonneg _) hw)

/-! ### §2. The `t`-series, split at `t = 1` -/

variable (p : ℕ)

/-- **The tail series `∑_{t ≥ 2} δ_p(t) w^{Ω(t)}` converges absolutely** for `‖w‖ ≤ 1`. -/
lemma summable_δ_toReal_mul_pow_cardFactors [Fact p.Prime] {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable fun t : ℕ =>
      if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0 := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
    (hasSum_δ_toReal p).summable)
  by_cases ht : 2 ≤ t
  · rw [ite_eq_left ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      norm_pow]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ (norm_nonneg _) hw)
  · rw [ite_eq_right ht]
    simp [ENNReal.toReal_nonneg]

/-- **The splitting of the local series at `t = 1`.** For `‖w‖ ≤ 1`,

`∑_{t} δ_p(t) u^{ω_{Tam,t}} w^{Ω(t)} = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`,

as a `HasSum`. -/
lemma hasSum_δ_toReal_mul_omegaCardFactorsFaceWeight [Fact p.Prime] {u w : ℂ} (hw : ‖w‖ ≤ 1) :
    HasSum (fun t : ℕ => ((δ p t).toReal : ℂ)
        * ((if 1 < t then u else 1) * w ^ ArithmeticFunction.cardFactors t))
      (((δ p 1).toReal : ℂ) + u * ∑' t : ℕ,
        if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0) := by
  have hG := (summable_δ_toReal_mul_pow_cardFactors p hw).hasSum
  have h1 : HasSum (fun t : ℕ => if t = 1 then ((δ p 1).toReal : ℂ) else 0)
      ((δ p 1).toReal : ℂ) := hasSum_ite_eq 1 _
  have hfun : (fun t : ℕ => (if t = 1 then ((δ p 1).toReal : ℂ) else 0)
        + u * (if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0))
      = fun t : ℕ => ((δ p t).toReal : ℂ)
          * ((if 1 < t then u else 1) * w ^ ArithmeticFunction.cardFactors t) := by
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

/-! ### §3. The local factor of the master Euler product on this face -/

/-- **Termwise domination over `𝒦`.** On the closed bidisc the `K`-th term has norm at most
`δ_p(K)`. -/
lemma norm_deltaP_toReal_mul_omegaCardFactorsFaceWeight_le [Fact p.Prime] {u w : ℂ}
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (K : ReductionData) :
    ‖((deltaP p K).toReal : ℂ)
        * ((if 1 < K.2 then u else 1) * w ^ ArithmeticFunction.cardFactors K.2)‖
      ≤ (deltaP p K).toReal := by
  have hnorm : ‖((deltaP p K).toReal : ℂ)‖ = (deltaP p K).toReal := by
    rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  rw [norm_mul, hnorm]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg
    (norm_omegaCardFactorsFaceWeight_le_one hu hw K.2)

/-- **The `𝒦`-indexed series converges absolutely on the closed bidisc.** -/
lemma summable_deltaP_toReal_mul_omegaCardFactorsFaceWeight [Fact p.Prime] {u w : ℂ}
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    Summable fun K : ReductionData => ((deltaP p K).toReal : ℂ)
      * ((if 1 < K.2 then u else 1) * w ^ ArithmeticFunction.cardFactors K.2) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_deltaP_toReal_mul_omegaCardFactorsFaceWeight_le p hu hw)
    (hasSum_deltaP_toReal p).summable)

/-- **The `𝒦`-indexed series sums to `δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`** on the closed bidisc.
-/
lemma hasSum_deltaP_toReal_mul_omegaCardFactorsFaceWeight [Fact p.Prime] {u w : ℂ}
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    HasSum (fun K : ReductionData => ((deltaP p K).toReal : ℂ)
        * ((if 1 < K.2 then u else 1) * w ^ ArithmeticFunction.cardFactors K.2))
      (((δ p 1).toReal : ℂ) + u * ∑' t : ℕ,
        if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0) := by
  have hsum := summable_deltaP_toReal_mul_omegaCardFactorsFaceWeight p hu hw
  have hfib := (((Equiv.prodComm ℕ KodairaSymbol).hasSum_iff).2 hsum.hasSum).prod_fiberwise
    fun t => (hasSum_deltaP_toReal_kodaira p t).mul_right
      ((if 1 < t then u else 1) * w ^ ArithmeticFunction.cardFactors t)
  have heq : ∑' K : ReductionData, ((deltaP p K).toReal : ℂ)
        * ((if 1 < K.2 then u else 1) * w ^ ArithmeticFunction.cardFactors K.2)
      = ((δ p 1).toReal : ℂ) + u * ∑' t : ℕ,
        if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0 :=
    hfib.unique (hasSum_δ_toReal_mul_omegaCardFactorsFaceWeight p hw)
  rw [← heq]
  exact hsum.hasSum

/-- **The local factor `g_p(u, w)`**, `δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`, extended by `1` at a
non-prime index, so that a `∏' p : ℕ` is the product over the primes. -/
noncomputable def omegaCardFactorsEulerFactor (p : ℕ) (u w : ℂ) : ℂ :=
  if h : p.Prime then
    ((@δ p ⟨h⟩ 1).toReal : ℂ) + u * ∑' t : ℕ,
      if 2 ≤ t then ((@δ p ⟨h⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0
  else 1

/-- At a prime index `g_p` is the displayed sum. -/
lemma omegaCardFactorsEulerFactor_of_prime [Fact p.Prime] (u w : ℂ) :
    omegaCardFactorsEulerFactor p u w = ((δ p 1).toReal : ℂ) + u * ∑' t : ℕ,
      if 2 ≤ t then ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t else 0 :=
  dite_eq_left Fact.out

/-- **The Euler product `G(u, w) = ∏_{p ∈ 𝒫} g_p(u, w)`**, a `tprod` over the primes as an index
type. -/
noncomputable def omegaCardFactorsEulerProduct (u w : ℂ) : ℂ :=
  ∏' p : {q : ℕ // q.Prime}, omegaCardFactorsEulerFactor (p : ℕ) u w

/-- **The local-factor identification.** For a prime `p`, `‖u‖ ≤ 1` and `‖w‖ ≤ 1`,

`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, u, w, ∅, ∅) = g_p(u, w)`,

with `β_p` the trivial-stratum mass and `Φ_p` the local weight. The left side is the local factor
of the master Euler product. -/
theorem localFactor_collapse_omegaCardFactors [Fact p.Prime] {u w : ℂ} (hu : ‖u‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    ((β p).toReal : ℂ)
        + ∑' K : ↥(K0ᶜ : Set ReductionData),
            ((deltaP p (K : ReductionData)).toReal : ℂ)
              * localWeight ∅ ∅ (K : ReductionData) 0 u w z uΛ
      = omegaCardFactorsEulerFactor p u w := by
  have hface : (fun K : ReductionData =>
        ((deltaP p K).toReal : ℂ) * localWeight ∅ ∅ K 0 u w z uΛ)
      = fun K : ReductionData => ((deltaP p K).toReal : ℂ)
          * ((if 1 < K.2 then u else 1) * w ^ ArithmeticFunction.cardFactors K.2) :=
    funext fun K => by rw [localWeight_omegaCardFactorsFace]
  have htot : HasSum (fun K : ReductionData =>
      ((deltaP p K).toReal : ℂ) * localWeight ∅ ∅ K 0 u w z uΛ)
      (omegaCardFactorsEulerFactor p u w) := by
    rw [hface, omegaCardFactorsEulerFactor_of_prime]
    exact hasSum_deltaP_toReal_mul_omegaCardFactorsFaceWeight p hu hw
  have hone : ∀ K ∈ K0, localWeight ∅ ∅ K 0 u w z uΛ = 1 :=
    fun K hK => localWeight_eq_one ∅ ∅ hK (by simp) 0 u w z uΛ
  have hK0 : ∑' K : ↥K0, (((deltaP p (K : ReductionData)).toReal : ℂ)
      * localWeight ∅ ∅ (K : ReductionData) 0 u w z uΛ) = ((β p).toReal : ℂ) := by
    rw [tsum_subtype_K0 (M := ℂ) fun K => ((deltaP p K).toReal : ℂ)
      * localWeight ∅ ∅ K 0 u w z uΛ,
      hone (KodairaSymbol.I 0, 1) (by simp [K0]), hone (KodairaSymbol.I 1, 1) (by simp [K0]),
      β_add, ENNReal.toReal_add (deltaP_ne_top p _) (deltaP_ne_top p _)]
    push_cast
    ring
  rw [← hK0, htot.summable.tsum_subtype_add_tsum_subtype_compl K0, htot.tsum_eq]

/-- **The master Euler product at the face `Λ = Π = ∅`, `s = 0` is `G(u, w)`** on the closed
bidisc.
-/
lemma tprod_localFactor_omegaCardFactorsFace {u w : ℂ} (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    ∏' p : {q : ℕ // q.Prime},
        (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight ∅ ∅ (K : ReductionData) 0 u w z uΛ)
      = omegaCardFactorsEulerProduct u w :=
  tprod_congr fun p =>
    @localFactor_collapse_omegaCardFactors (p : ℕ) ⟨p.2⟩ u w hu hw z uΛ

/-! ### §4. The bivariate empirical generating function and its limit -/

open scoped Classical in
/-- **`𝒵` on the face `Λ = Π = ∅`, `s = 0` is the bivariate empirical average.**

`𝒵_{∅, ∅, X}(0; u, w, ∅, ∅) = (1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} w^{Ω(Tam(E))}`. -/
lemma tamagawaGeneratingFunction_omegaCardFactorsFace (u w : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset ReductionData) → ℂ) (X : ℝ) :
    tamagawaGeneratingFunction ∅ ∅ 0 u w z uΛ X
      = (∑' q : ℤ × ℤ,
          if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
            u ^ tamagawaOmega q.1 q.2
              * w ^ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)
          else 0) / (integralShortNFCount X : ℂ) := by
  rw [tamagawaGeneratingFunction]
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
  · rw [ite_eq_left hq, ite_eq_left hq]
    simp [multiMonomial, kodairaMonomial_empty]
  · rw [ite_eq_right hq, ite_eq_right hq]

open scoped Classical in
/-- **The bivariate limit of the empirical generating function.** For `‖u‖ ≤ 1` and `‖w‖ ≤ 1`,

`lim_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} u^{ω_Tam(E)} w^{Ω(Tam(E))} = ∏_{p ∈ 𝒫} g_p(u, w)`,
`g_p(u, w) = δ_p(1) + u ∑_{t ≥ 2} δ_p(t) w^{Ω(t)}`,

with `N(X)` the counting function, `Ht` the naive height, `ω_Tam` the Tamagawa prime count, `Tam`
the global Tamagawa product, `Ω` the number of prime factors with multiplicity and `δ_p(t)` the
scalar local density. -/
theorem tendsto_jointOmegaCardFactorsAverage_omegaCardFactorsEulerProduct {u w : ℂ}
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ,
            if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
              u ^ tamagawaOmega q.1 q.2
                * w ^ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)
            else 0) / (integralShortNFCount X : ℂ))
      atTop (𝓝 (omegaCardFactorsEulerProduct u w)) := by
  have h0 : (0 : ℝ) ≤ (0 : ℂ).re := by simp
  have hz : ∀ ℓ : (∅ : Finset ℕ), ‖(fun _ => (0 : ℂ)) ℓ‖ ≤ 1 :=
    fun ℓ => (Finset.notMem_empty _ ℓ.2).elim
  have huΛ : ∀ K : (∅ : Finset ReductionData), ‖(fun _ => (0 : ℂ)) K‖ ≤ 1 :=
    fun K => (Finset.notMem_empty _ K.2).elim
  have hP : ∀ ℓ ∈ (∅ : Finset ℕ), Nat.Prime ℓ := by simp
  have hface : (fun X : ℝ =>
      (∑' q : ℤ × ℤ,
          if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
            u ^ tamagawaOmega q.1 q.2
              * w ^ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)
          else 0) / (integralShortNFCount X : ℂ))
      = tamagawaGeneratingFunction ∅ ∅ 0 u w (fun _ => 0) (fun _ => 0) :=
    funext fun X =>
      (tamagawaGeneratingFunction_omegaCardFactorsFace u w (fun _ => 0) (fun _ => 0) X).symm
  rw [hface, ← tprod_localFactor_omegaCardFactorsFace hu hw (fun _ => (0 : ℂ))
    (fun _ => (0 : ℂ))]
  exact tendsto_tamagawaGeneratingFunction_tprod_localFactor ∅ ∅ (by simp) hP h0 hu hw hz huΛ

/-! ### §5. The joint density

The statistic `q ↦ (ω_Tam(q), Ω(Tam(q)))` is read as a `Bool`-multi-index, `false` carrying `ω_Tam`
and `true` carrying `Ω(Tam)`. -/

/-- **The pair statistic as a `Bool`-multi-index**: `false ↦ ω_Tam(E)`, `true ↦ Ω(Tam(E))`. -/
noncomputable def omegaCardFactorsIndex (q : ℤ × ℤ) : Bool →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Bool =>
    if i then ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) else tamagawaOmega q.1 q.2

/-- The `false` coordinate of `omegaCardFactorsIndex q` is `ω_Tam(q)`. -/
@[simp]
lemma omegaCardFactorsIndex_false (q : ℤ × ℤ) :
    omegaCardFactorsIndex q false = tamagawaOmega q.1 q.2 := rfl

/-- The `true` coordinate of `omegaCardFactorsIndex q` is `Ω(Tam(q))`. -/
@[simp]
lemma omegaCardFactorsIndex_true (q : ℤ × ℤ) :
    omegaCardFactorsIndex q true
      = ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) := rfl

/-- **The multi-index attached to a pair `(r, b)`.** -/
noncomputable def omegaCardFactorsMulti (r b : ℕ) : Bool →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Bool => if i then b else r

/-- The `false` coordinate of `omegaCardFactorsMulti r b` is `r`. -/
@[simp]
lemma omegaCardFactorsMulti_false (r b : ℕ) : omegaCardFactorsMulti r b false = r := rfl

/-- The `true` coordinate of `omegaCardFactorsMulti r b` is `b`. -/
@[simp]
lemma omegaCardFactorsMulti_true (r b : ℕ) : omegaCardFactorsMulti r b true = b := rfl

/-- The `Bool`-monomial is the bivariate monomial `u^{ω_Tam(E)} w^{Ω(Tam(E))}`, with `u = z false`
and `w = z true`. -/
lemma multiMonomial_omegaCardFactorsIndex (z : Bool → ℂ) (q : ℤ × ℤ) :
    multiMonomial (⇑(omegaCardFactorsIndex q)) z
      = z false ^ tamagawaOmega q.1 q.2
        * z true ^ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) := by
  rw [multiMonomial, Fintype.prod_bool, omegaCardFactorsIndex_false, omegaCardFactorsIndex_true,
    mul_comm]

/-- **The joint fibre.** The fibre of the pair statistic over a multi-index `𝐣` is the set counted
by the numerator of the joint proportion at `(j false, j true)`. -/
lemma setOf_mem_and_omegaCardFactorsIndex_eq (j : Bool →₀ ℕ) (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧ omegaCardFactorsIndex q = j} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
        tamagawaOmega q.1 q.2 = j false ∧
          ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = j true} := by
  refine Set.ext fun q => ?_
  simp only [Set.mem_ofPred_eq, and_assoc, Finsupp.ext_iff, Bool.forall_bool,
    omegaCardFactorsIndex_false, omegaCardFactorsIndex_true]

/-- The fibre quotient of the pair statistic over `𝐣` is the joint proportion at
`(j false, j true)`. -/
lemma ncard_fiber_div_eq_jointOmegaCardFactorsProportion (j : Bool →₀ ℕ) (X : ℝ) :
    ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily} ∧
        omegaCardFactorsIndex q = j}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ)
      = jointOmegaCardFactorsProportion (j false) (j true) X := by
  rw [setOf_mem_and_omegaCardFactorsIndex_eq j X, ncard_setOf_height_le_and_mem_family,
    jointOmegaCardFactorsProportion]

/-- **The bivariate empirical average as a multi-index series.** For `z` in the *open* bidisc,

`(1/N(X)) ∑_{Ht(E) ≤ X} 𝐳^{(ω_Tam(E), Ω(Tam(E)))} ⟶ G(z_false, z_true)`,

with the cut-off written as a `Set.indicator`. -/
lemma tendsto_tsum_indicator_omegaCardFactorsMonomial_div (z : Bool → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.indicator
          (fun q => multiMonomial (⇑(omegaCardFactorsIndex q)) z) q) /
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.ncard : ℂ))
      atTop (𝓝 (omegaCardFactorsEulerProduct (z false) (z true))) := by
  refine (tendsto_jointOmegaCardFactorsAverage_omegaCardFactorsEulerProduct
    (hz false).le (hz true).le).congr fun X => ?_
  rw [ncard_setOf_height_le_and_mem_family]
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
  · rw [ite_eq_left (show _ ∧ _ from hq), Set.indicator_of_mem hq,
      multiMonomial_omegaCardFactorsIndex]
  · rw [ite_eq_right (show ¬(_ ∧ _) from hq), Set.indicator_of_notMem hq]

/-- **Existence of the joint limiting density.** For all `r, b : ℕ`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Δ ≠ 0, ω_Tam(E) = r, Ω(Tam(E)) = b} / N(X) = π(r, b)`,

with `π(r, b) = jointOmegaCardFactorsDensity r b`. -/
theorem tendsto_jointOmegaCardFactorsProportion_jointOmegaCardFactorsDensity (r b : ℕ) :
    Tendsto (fun X : ℝ => jointOmegaCardFactorsProportion r b X) atTop
      (𝓝 (jointOmegaCardFactorsDensity r b)) := by
  have h := tendsto_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    omegaCardFactorsIndex
    (fun z : Bool → ℂ => omegaCardFactorsEulerProduct (z false) (z true)) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_omegaCardFactorsMonomial_div z hz)
    (omegaCardFactorsMulti r b)
  rw [jointOmegaCardFactorsDensity]
  simpa only [ncard_fiber_div_eq_jointOmegaCardFactorsProportion, omegaCardFactorsMulti_false,
    omegaCardFactorsMulti_true] using h

/-- **The joint density is a sub-probability vector expanding `G` on the open bidisc.** Values in
`[0, 1]`, summable over `Bool →₀ ℕ` with total mass at most `1`, and
`∑_{(r,b)} π(r, b) u^r w^b = G(u, w)` for `‖u‖, ‖w‖ < 1`. -/
theorem hasPolydiscExpansion_jointOmegaCardFactorsDensity :
    (∀ j : Bool →₀ ℕ,
        jointOmegaCardFactorsDensity (j false) (j true) ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun j : Bool →₀ ℕ => jointOmegaCardFactorsDensity (j false) (j true)) ∧
      (∑' j : Bool →₀ ℕ, jointOmegaCardFactorsDensity (j false) (j true)) ≤ 1 ∧
      HasPolydiscExpansion
        (fun j : Bool →₀ ℕ =>
          ((jointOmegaCardFactorsDensity (j false) (j true) : ℝ) : ℂ))
        (fun z : Bool → ℂ => omegaCardFactorsEulerProduct (z false) (z true)) := by
  have h := hasPolydiscExpansion_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    omegaCardFactorsIndex
    (fun z : Bool → ℂ => omegaCardFactorsEulerProduct (z false) (z true)) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_omegaCardFactorsMonomial_div z hz)
  simp only [ncard_fiber_div_eq_jointOmegaCardFactorsProportion] at h
  exact h

end WeierstrassCurve
