/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.GeneratingFunction.LocalWeightTrivial
public import BSDTamagawa.Equidistribution.FinitePrimeFactorization
public import BSDTamagawa.GeneratingFunction.TruncatedReductionCount
public import BSDTamagawa.GeneratingFunction.TruncatedPrimeCount
public import BSDTamagawa.GeneratingFunction.TruncatedFactorCount
public import BSDTamagawa.GeneratingFunction.TruncatedValuationVector
public import BSDTamagawa.GeneratingFunction.TruncatedTamagawaProduct

/-!
# The truncated generating-function identity

Let `S` be a finite set of primes, `Λ ⊆ 𝒦 ∖ 𝒦₀` finite and `Π` a finite set of primes, and let
`Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for `ℓ ∈ Π` and `‖u_K‖ ≤ 1` for `K ∈ Λ`. Then
`lim_{X → ∞} (1 / N(X)) ∑_{Ht(E) ≤ X} u^{ω_{Tam,S}(E)} w^{Ω_S(E)} 𝐳^{𝐯_{Π,S}(E)}
  (∏_{K ∈ Λ} u_K^{ω_{K,S}(E)}) Tam_S(E)^{-s}`
exists and equals `∏_{p ∈ S} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))`.

The summand factors as `∏_{p ∈ S} Φ(τ_p(E); s, u, w, 𝐳, 𝐮)`, the local weight `Φ` is bounded by `1`
on the parameter region, and the equidistribution of the local reduction data at the primes of `S`
then gives the limit `∏_{p ∈ S} ∑_{K ∈ 𝒦} δ_p(K) Φ(K)`. Splitting the inner sum at `𝒦₀`, where
`Φ = 1` and the densities add up to `β_p`, gives the stated form.

## Main results

* `WeierstrassCurve.norm_localWeight_le_one`: `‖Φ(K; s, u, w, 𝐳, 𝐮)‖ ≤ 1` on the parameter region,
  for every `K`.
* `WeierstrassCurve.natCast_prod_cpow`: `(∏ c_q)^s = ∏ c_q^s` for natural numbers `c_q`.
* `WeierstrassCurve.prod_localWeight_localReductionDatum`: the factorisation of the summand.
* `WeierstrassCurve.tsum_deltaP_toReal_mul_localWeight`: the split of the inner sum at `𝒦₀`.
* `WeierstrassCurve.tendsto_average_truncatedWeight`: the limit formula above.
-/

@[expose] public section

open Filter Topology BSDTamagawa.MultiIndex

namespace WeierstrassCurve

/-! ### The local weight is bounded by `1` on `𝒟` -/

/-- `‖t^{-s}‖ ≤ 1` for every natural number `t` (including `t = 0`) and `Re(s) ≥ 0`. -/
lemma norm_natCast_cpow_neg_le_one {s : ℂ} (hs : 0 ≤ s.re) (t : ℕ) :
    ‖(t : ℂ) ^ (-s)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0), norm_zero]
      exact zero_le_one
  · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by rw [Complex.neg_re]; linarith)

/-- A multi-monomial whose parameters all have modulus at most `1` has modulus at most `1`. -/
lemma norm_multiMonomial_le_one {ι : Type*} [Fintype ι] (j : ι → ℕ) {v : ι → ℂ}
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖multiMonomial j v‖ ≤ 1 := by
  rw [multiMonomial, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    fun i _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hv i)

/-- If `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π` and `‖u_{K'}‖ ≤ 1` for
every `K' ∈ Λ`, then `‖Φ(K; s, u, w, 𝐳, 𝐮)‖ ≤ 1` for every `K ∈ 𝒦`. -/
lemma norm_localWeight_le_one (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) (K : KodairaSymbol × ℕ) :
    ‖localWeight Λ P K s u w z uΛ‖ ≤ 1 := by
  rw [localWeight]
  simp only [norm_mul]
  have h₁ : ‖u ^ (if 1 < K.2 then 1 else 0)‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
  have h₂ : ‖w ^ ArithmeticFunction.cardFactors K.2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_multiMonomial_le_one _ huΛ)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_natCast_cpow_neg_le_one hs K.2)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_multiMonomial_le_one _ hz)
  exact (mul_le_of_le_one_left (norm_nonneg _) h₁).trans h₂

/-! ### The weight factors prime by prime -/

/-- A finite product of multi-monomials is the multi-monomial at the summed exponent vector:
`∏_i v^{j_i} = v^{∑_i j_i}`. -/
lemma prod_multiMonomial {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (j : ι → κ → ℕ)
    (v : κ → ℂ) : ∏ i, multiMonomial (j i) v = multiMonomial (fun k => ∑ i, j i k) v := by
  simp only [multiMonomial]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum _ _ _

/-- For natural numbers `c_q`, `(∏_{q ∈ T} c_q)^s = ∏_{q ∈ T} c_q^s` in `ℂ`. (For general complex
bases this fails, because of the branch cut of `Complex.cpow`.) -/
lemma natCast_prod_cpow {ι : Type*} (T : Finset ι) (c : ι → ℕ) (s : ℂ) :
    ((∏ q ∈ T, c q : ℕ) : ℂ) ^ s = ∏ q ∈ T, ((c q : ℕ) : ℂ) ^ s := by
  induction T using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, ← ih, Nat.cast_mul,
      ← Complex.ofReal_natCast (c a), ← Complex.ofReal_natCast (∏ q ∈ t, c q),
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

open scoped Classical in
/-- For the integral short Weierstrass model `E = E(a₄, a₆)` and `Λ ⊆ 𝒦 ∖ 𝒦₀`,
`∏_{p ∈ S} Φ(τ_p(E); s, u, w, 𝐳, 𝐮)
  = u^{ω_{Tam,S}(E)} w^{Ω_S(E)} 𝐳^{𝐯_{Π,S}(E)} Tam_S(E)^{-s} ∏_{K ∈ Λ} u_K^{ω_{K,S}(E)}`,
the product running over the primes of `S`. -/
lemma prod_localWeight_localReductionDatum (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ)
    (hΛ : ∀ K ∈ Λ, K ∉ K0) (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) (a₄ a₆ : ℤ) :
    ∏ q : ↥(S.filter Nat.Prime),
        localWeight Λ P (localReductionDatum (q : ℕ) a₄ a₆) s u w z uΛ
      = u ^ truncatedTamagawaOmega S a₄ a₆ * w ^ truncatedTamagawaCardFactors S a₄ a₆ *
          multiMonomial (truncatedTamagawaValuationVector P S a₄ a₆) z *
          (truncatedTamagawaProduct S a₄ a₆ : ℂ) ^ (-s) *
          multiMonomial
            (fun K : Λ => truncatedReductionOmega (K : KodairaSymbol × ℕ) S a₄ a₆) uΛ := by
  have hone : ∀ p ∈ S, ¬ p.Prime → localTamagawaNumber p a₄ a₆ = 1 :=
    fun p _ hp => localTamagawaNumber_of_not_prime hp a₄ a₆
  have h₁ : ∑ p ∈ S.filter Nat.Prime, (if 1 < localTamagawaNumber p a₄ a₆ then 1 else 0)
      = truncatedTamagawaOmega S a₄ a₆ :=
    Finset.sum_filter_of_ne fun p hp hv => by
      by_contra hnp; rw [hone p hp hnp] at hv; simp at hv
  have h₂ : ∑ p ∈ S.filter Nat.Prime,
        ArithmeticFunction.cardFactors (localTamagawaNumber p a₄ a₆)
      = truncatedTamagawaCardFactors S a₄ a₆ :=
    Finset.sum_filter_of_ne fun p hp hv => by
      by_contra hnp; rw [hone p hp hnp] at hv; simp at hv
  have h₃ : ∀ ℓ : P, ∑ p ∈ S.filter Nat.Prime, padicValNat ℓ (localTamagawaNumber p a₄ a₆)
      = truncatedTamagawaValuationVector P S a₄ a₆ ℓ := fun ℓ =>
    Finset.sum_filter_of_ne fun p hp hv => by
      by_contra hnp; rw [hone p hp hnp] at hv; simp at hv
  have h₄ : ∀ K' : Λ, ∑ p ∈ S.filter Nat.Prime,
        (if localReductionDatum p a₄ a₆ = (K' : KodairaSymbol × ℕ) then 1 else 0)
      = truncatedReductionOmega (K' : KodairaSymbol × ℕ) S a₄ a₆ := fun K' =>
    Finset.sum_filter_of_ne fun p hp hv => by
      by_contra hnp
      rw [localReductionDatum_of_not_prime hnp] at hv
      refine hv (ite_eq_right fun h => hΛ _ K'.2 ?_)
      rw [← h]; exact Set.mem_insert _ _
  have h₅ : ∏ p ∈ S.filter Nat.Prime, localTamagawaNumber p a₄ a₆
      = truncatedTamagawaProduct S a₄ a₆ :=
    Finset.prod_filter_of_ne fun p hp hv => by
      by_contra hnp; exact hv (hone p hp hnp)
  have e₁ : ∏ x : ↥(S.filter Nat.Prime),
      u ^ (if 1 < localTamagawaNumber (x : ℕ) a₄ a₆ then 1 else 0)
      = u ^ truncatedTamagawaOmega S a₄ a₆ := by
    rw [Finset.prod_pow_eq_pow_sum, ← h₁,
      Finset.sum_coe_sort (S.filter Nat.Prime)
        fun p => if 1 < localTamagawaNumber p a₄ a₆ then 1 else 0]
  have e₂ : ∏ x : ↥(S.filter Nat.Prime),
      w ^ ArithmeticFunction.cardFactors (localTamagawaNumber (x : ℕ) a₄ a₆)
      = w ^ truncatedTamagawaCardFactors S a₄ a₆ := by
    rw [Finset.prod_pow_eq_pow_sum, ← h₂,
      Finset.sum_coe_sort (S.filter Nat.Prime)
        fun p => ArithmeticFunction.cardFactors (localTamagawaNumber p a₄ a₆)]
  have e₃ : ∏ x : ↥(S.filter Nat.Prime),
        multiMonomial (fun ℓ : P => padicValNat ℓ (localTamagawaNumber (x : ℕ) a₄ a₆)) z
      = multiMonomial (truncatedTamagawaValuationVector P S a₄ a₆) z := by
    have hv : (fun ℓ : P => ∑ x : ↥(S.filter Nat.Prime),
          padicValNat ℓ (localTamagawaNumber (x : ℕ) a₄ a₆))
        = truncatedTamagawaValuationVector P S a₄ a₆ :=
      funext fun ℓ => by
        rw [Finset.sum_coe_sort (S.filter Nat.Prime)
          fun p => padicValNat (ℓ : ℕ) (localTamagawaNumber p a₄ a₆), h₃ ℓ]
    rw [prod_multiMonomial, hv]
  have e₄ : ∏ x : ↥(S.filter Nat.Prime), ((localTamagawaNumber (x : ℕ) a₄ a₆ : ℕ) : ℂ) ^ (-s)
      = (truncatedTamagawaProduct S a₄ a₆ : ℂ) ^ (-s) := by
    rw [← natCast_prod_cpow, ← h₅,
      Finset.prod_coe_sort (S.filter Nat.Prime) fun p => localTamagawaNumber p a₄ a₆]
  have e₅ : ∏ x : ↥(S.filter Nat.Prime), multiMonomial
        (fun K' : Λ => if localReductionDatum (x : ℕ) a₄ a₆ = (K' : KodairaSymbol × ℕ)
          then 1 else 0) uΛ
      = multiMonomial
        (fun K' : Λ => truncatedReductionOmega (K' : KodairaSymbol × ℕ) S a₄ a₆) uΛ := by
    have hv : (fun K' : Λ => ∑ x : ↥(S.filter Nat.Prime),
          if localReductionDatum (x : ℕ) a₄ a₆ = (K' : KodairaSymbol × ℕ) then 1 else 0)
        = fun K' : Λ => truncatedReductionOmega (K' : KodairaSymbol × ℕ) S a₄ a₆ :=
      funext fun K' => by
        rw [Finset.sum_coe_sort (S.filter Nat.Prime)
          fun p => if localReductionDatum p a₄ a₆ = (K' : KodairaSymbol × ℕ) then 1 else 0,
          h₄ K']
    rw [prod_multiMonomial, hv]
  simp only [localWeight, localReductionDatum_snd]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, e₁, e₂, e₃, e₄, e₅]

/-! ### The inner sum, split at `𝒦₀` -/

/-- For a prime `p` and parameters in `𝒟`, if `Λ ⊆ 𝒦 ∖ 𝒦₀`, then
`∑_{K ∈ 𝒦} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮) = β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮)`, with
`β_p` the trivial-stratum mass and `δ_p` the local reduction density. -/
lemma tsum_deltaP_toReal_mul_localWeight (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ)
    (p : ℕ) [Fact p.Prime] {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0)
    (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1)
    (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) :
    ∑' K : KodairaSymbol × ℕ, ((deltaP p K).toReal : ℂ) * localWeight Λ P K s u w z uΛ
      = ((β p).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
          ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) *
            localWeight Λ P (K : KodairaSymbol × ℕ) s u w z uΛ := by
  have hsum : Summable fun K : KodairaSymbol × ℕ =>
      ((deltaP p K).toReal : ℂ) * localWeight Λ P K s u w z uΛ :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun K => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg
          (norm_localWeight_le_one Λ P hs hu hw hz huΛ K))
      (hasSum_deltaP_toReal p).summable)
  have hK0 : ∑' K : ↥K0, (((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) *
      localWeight Λ P (K : KodairaSymbol × ℕ) s u w z uΛ) = ((β p).toReal : ℂ) := by
    have hone : ∀ K ∈ K0, localWeight Λ P K s u w z uΛ = 1 :=
      fun K hK => localWeight_eq_one Λ P hK hΛ s u w z uΛ
    rw [tsum_subtype_K0 (M := ℂ) fun K => ((deltaP p K).toReal : ℂ) *
        localWeight Λ P K s u w z uΛ,
      hone (KodairaSymbol.I 0, 1) (by simp [K0]), hone (KodairaSymbol.I 1, 1) (by simp [K0]),
      β_add, ENNReal.toReal_add (deltaP_ne_top p _) (deltaP_ne_top p _)]
    push_cast
    ring
  rw [← hsum.tsum_subtype_add_tsum_subtype_compl K0, hK0]

/-! ### The truncated identity -/

/-- Let `S` be a finite set of primes, `Λ ⊆ 𝒦 ∖ 𝒦₀` finite and `Π` a finite set of primes, and let
`Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π` and `‖u_K‖ ≤ 1` for every `K ∈ Λ`.
Then
`lim_{X → ∞} (1 / N(X)) ∑_{Ht(E) ≤ X} u^{ω_{Tam,S}(E)} w^{Ω_S(E)} 𝐳^{𝐯_{Π,S}(E)}
  Tam_S(E)^{-s} (∏_{K ∈ Λ} u_K^{ω_{K,S}(E)})`
exists and equals `∏_{p ∈ S} (β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))`, where `β_p` is the
trivial-stratum mass, `δ_p` the local reduction density and `Φ` the local weight. -/
@[bsd_tamagawa "T035"]
theorem tendsto_average_truncatedWeight (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ)
    {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hs : 0 ≤ s.re)
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) :
    Tendsto (fun X : ℝ => (integralShortNFCount X : ℂ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          u ^ truncatedTamagawaOmega S E.1.1 E.1.2 *
            w ^ truncatedTamagawaCardFactors S E.1.1 E.1.2 *
            multiMonomial (truncatedTamagawaValuationVector P S E.1.1 E.1.2) z *
            (truncatedTamagawaProduct S E.1.1 E.1.2 : ℂ) ^ (-s) *
            multiMonomial (fun K : Λ =>
              truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)
      atTop
      (𝓝 (∏ q : ↥(S.filter Nat.Prime), (((β (q : ℕ)).toReal : ℂ) +
        ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
          ((deltaP (q : ℕ) (K : KodairaSymbol × ℕ)).toReal : ℂ) *
            localWeight Λ P (K : KodairaSymbol × ℕ) s u w z uΛ))) := by
  have key := tendsto_average_prod_tauZ S (fun _ K => localWeight Λ P K s u w z uΛ)
    (B := fun _ => 1) fun q K => norm_localWeight_le_one Λ P hs hu hw hz huΛ K
  have hlim : (∏ q : ↥(S.filter Nat.Prime), ∑' K : KodairaSymbol × ℕ,
        ((deltaP (q : ℕ) K).toReal : ℂ) * localWeight Λ P K s u w z uΛ)
      = ∏ q : ↥(S.filter Nat.Prime), (((β (q : ℕ)).toReal : ℂ) +
        ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
          ((deltaP (q : ℕ) (K : KodairaSymbol × ℕ)).toReal : ℂ) *
            localWeight Λ P (K : KodairaSymbol × ℕ) s u w z uΛ) :=
    Finset.prod_congr rfl fun q _ =>
      tsum_deltaP_toReal_mul_localWeight Λ P (q : ℕ) hΛ hs hu hw hz huΛ
  rw [← hlim]
  refine key.congr fun X => congrArg _ (tsum_congr fun E => ?_)
  rw [← prod_localWeight_localReductionDatum Λ P S hΛ s u w z uΛ E.1.1 E.1.2]
  exact Finset.prod_congr rfl fun q _ => by rw [localReductionDatum_of_prime]

end WeierstrassCurve
