/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.EulerProductHolds
public import BSDTamagawa.Moments.LocalFinite

/-!
# Every moment of the limiting Tamagawa law is finite

Let `P_Tam` be the limiting distribution of the global Tamagawa number over short Weierstrass
curves ordered by height, and `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x` its local moment factors. This file
proves that every real moment of `P_Tam` is finite,

`∑_{m ≥ 1} P_Tam(m) m^x < ∞` for every `x : ℝ`,

and hence that `∑_m ‖P_Tam(m) m^{-s}‖ < ∞` for every `s : ℂ`.

## Main definitions

* `momentFactorReal`: The real local moment factor `G_p(x)`, equal to `1` at a non-prime `p`.
* `momentDefect`: The deviation `‖G_p(x) - 1‖` at a prime `p`, and `0` elsewhere.
* `tamagawaMomentBound`: The constant `C_x = exp(∑_p ‖G_p(x) - 1‖)`.
* `truncMomentWeight`: The bounded weight `w_{k,M}(t) = t^k · 1[t ≤ M]`.
* `truncMomentFactor`: The local factor `∑_{t ≥ 1} δ_p(t) w_{k,M}(t)` at a prime `p`, and `1`
  elsewhere.
* `truncatedTamagawaDensity`: The limiting law `P_Tam^S` of the Tamagawa product over a finite set
  `S` of primes.

## Main results

* `prod_momentFactorReal_le`: Every finite product of the factors `G_p(x)`, `x ≥ 0`, is at most
  `C_x`.
* `sum_truncatedTamagawaDensity_mul_pow_le`: `∑_{m = 1}^{M} P_Tam^S(m) m^k ≤ C_k` for every finite
  `S` and every `M`.
* `sum_tamagawaDensity_mul_pow_le`: `∑_{m = 1}^{M} P_Tam(m) m^k ≤ C_k` for every `M`.
* `summable_tamagawaDensity_mul_rpow`: `∑_m P_Tam(m) m^x` converges for every `x : ℝ`.
* `summable_norm_tamagawaDensity_mul_cpow_all`: `∑_m ‖P_Tam(m) m^{-s}‖` converges for every
  `s : ℂ`.
* `hasEulerProductOffHalfPlane_iff_tsum_eq`: `HasEulerProductOffHalfPlane` is equivalent to the
  identity `∑_m P_Tam(m) m^{-s} = ∏_p L_p(s)` for every `s : ℂ`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction

/-! ### The real moment local factor, total in `p` -/

/-- The real local moment factor `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x` at a prime `p`, and `1` at a
non-prime `p`. -/
noncomputable def momentFactorReal (p : ℕ) (x : ℝ) : ℝ :=
  if h : p.Prime then ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (t : ℝ) ^ x else 1

/-- At a prime `p`, `G_p(x) = ∑_t δ_p(t) t^x`. -/
lemma momentFactorReal_of_prime (p : ℕ) [Fact p.Prime] (x : ℝ) :
    momentFactorReal p x = ∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ x :=
  dite_eq_left Fact.out

/-- At a non-prime `p`, `momentFactorReal p x = 1`. -/
lemma momentFactorReal_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (x : ℝ) :
    momentFactorReal p x = 1 :=
  dite_eq_right hp

/-- The coercion of `momentFactorReal p x` to `ℂ` is `momentLocalFactor p x`. -/
lemma ofReal_momentFactorReal (p : ℕ) (x : ℝ) :
    ((momentFactorReal p x : ℝ) : ℂ) = momentLocalFactor p x := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [momentFactorReal_of_prime p x, momentLocalFactor_eq_ofReal p x]
  · rw [momentFactorReal_of_not_prime hp, momentLocalFactor_of_not_prime hp, Complex.ofReal_one]

/-- For `x ≥ 0`, the local moment factor satisfies `1 ≤ G_p(x)`. -/
lemma one_le_momentFactorReal (p : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ momentFactorReal p x := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [momentFactorReal_of_prime p x, ← tsum_δ_toReal p]
    refine Summable.tsum_le_tsum (fun t => ?_) (summable_δ_toReal p)
      (summable_δ_toReal_mul_rpow p x)
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [δ_zero]
    · exact le_mul_of_one_le_right ENNReal.toReal_nonneg (one_le_natCast_rpow ht hx)
  · rw [momentFactorReal_of_not_prime hp]

/-- For `x ≥ 0`, the local moment factor satisfies `0 ≤ G_p(x)`. -/
lemma momentFactorReal_nonneg (p : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ momentFactorReal p x :=
  le_trans zero_le_one (one_le_momentFactorReal p hx)

/-- The deviation `‖G_p(x) - 1‖` at a prime `p`, and `0` at a non-prime `p`. -/
noncomputable def momentDefect (x : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then ‖momentLocalFactor p x - 1‖ else 0

/-- The deviation `momentDefect x p` is nonnegative. -/
lemma momentDefect_nonneg (x : ℝ) (p : ℕ) : 0 ≤ momentDefect x p := by
  rw [momentDefect]
  split
  · exact norm_nonneg _
  · exact le_rfl

/-- For `x ≥ 0`, `G_p(x) = 1 + ‖G_p(x) - 1‖`. -/
lemma momentFactorReal_eq_one_add_momentDefect (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    momentFactorReal p x = 1 + momentDefect x p := by
  by_cases hp : p.Prime
  · have hone := one_le_momentFactorReal p hx
    have h : momentLocalFactor p x - 1 = ((momentFactorReal p x - 1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, ofReal_momentFactorReal, Complex.ofReal_one]
    rw [momentDefect, ite_eq_left hp, h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    ring
  · rw [momentFactorReal_of_not_prime hp, momentDefect, ite_eq_right hp, add_zero]

/-- For every `x : ℝ`, the family `p ↦ momentDefect x p` is summable over `ℕ`. -/
lemma summable_momentDefect (x : ℝ) : Summable (momentDefect x) := by
  have h : Summable fun p : {q : ℕ // q.Prime} => ‖momentLocalFactor (p : ℕ) x - 1‖ :=
    summable_norm_momentLocalFactor_sub_one x
  have hind : Summable ({q : ℕ | q.Prime}.indicator
      fun q : ℕ => ‖momentLocalFactor q x - 1‖) := summable_subtype_iff_indicator.mp h
  refine hind.congr fun p => ?_
  by_cases hp : p.Prime
  · rw [Set.indicator_of_mem (show p ∈ {q : ℕ | q.Prime} from hp), momentDefect, ite_eq_left hp]
  · rw [Set.indicator_of_notMem (show p ∉ {q : ℕ | q.Prime} from hp), momentDefect, ite_eq_right hp]

/-- The constant `C_x = exp(∑_p ‖G_p(x) - 1‖)`, the sum running over the primes. -/
noncomputable def tamagawaMomentBound (x : ℝ) : ℝ := Real.exp (∑' p : ℕ, momentDefect x p)

/-- For `x ≥ 0` and every finite set `S`, `∏_{p ∈ S prime} G_p(x) ≤ C_x`. -/
lemma prod_momentFactorReal_le {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    ∏ q ∈ S.filter Nat.Prime, momentFactorReal q x ≤ tamagawaMomentBound x := by
  have hstep : ∏ q ∈ S.filter Nat.Prime, momentFactorReal q x
      ≤ ∏ q ∈ S.filter Nat.Prime, Real.exp (momentDefect x q) := by
    refine Finset.prod_le_prod₀ (fun q _ => momentFactorReal_nonneg q hx) fun q _ => ?_
    rw [momentFactorReal_eq_one_add_momentDefect q hx]
    linarith [Real.add_one_le_exp (momentDefect x q)]
  refine hstep.trans ?_
  rw [← Real.exp_sum, tamagawaMomentBound]
  exact Real.exp_le_exp.2
    (Summable.sum_le_tsum _ (fun p _ => momentDefect_nonneg x p) (summable_momentDefect x))

/-! ### The bounded truncated moment weight -/

/-- The truncated moment weight `w_{k,M}(t) = t^k · 1[t ≤ M]`. -/
noncomputable def truncMomentWeight (k M t : ℕ) : ℝ := if t ≤ M then (t : ℝ) ^ k else 0

/-- The weight `w_{k,M}(t)` is nonnegative. -/
lemma truncMomentWeight_nonneg (k M t : ℕ) : 0 ≤ truncMomentWeight k M t := by
  rw [truncMomentWeight]
  split
  · positivity
  · exact le_rfl

/-- `w_{k,M}(t) ≤ t^k`. -/
lemma truncMomentWeight_le (k M t : ℕ) : truncMomentWeight k M t ≤ (t : ℝ) ^ k := by
  rw [truncMomentWeight]
  split
  · exact le_rfl
  · positivity

/-- For `t ≤ M`, `w_{k,M}(t) = t^k`. -/
lemma truncMomentWeight_of_le {k M t : ℕ} (h : t ≤ M) :
    truncMomentWeight k M t = (t : ℝ) ^ k := ite_eq_left h

/-- `w_{k,M}(t) ≤ M^k`. -/
lemma truncMomentWeight_le_bound (k M t : ℕ) : truncMomentWeight k M t ≤ (M : ℝ) ^ k := by
  rw [truncMomentWeight]
  split
  · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast ‹t ≤ M›) k
  · positivity

/-- The complex norm of `w_{k,M}(t)` is at most `M^k`. -/
lemma norm_ofReal_truncMomentWeight_le (k M t : ℕ) :
    ‖((truncMomentWeight k M t : ℝ) : ℂ)‖ ≤ (M : ℝ) ^ k := by
  rw [Complex.norm_real, Real.norm_of_nonneg (truncMomentWeight_nonneg k M t)]
  exact truncMomentWeight_le_bound k M t

/-! ### The local sum of the truncated weight -/

/-- For every prime `p` and all `k`, `M`,

`∑_{K ∈ 𝒦} δ_p(K) w_{k,M}(c(K)) = ∑_{t ≥ 1} δ_p(t) w_{k,M}(t)`,

where `c(K)` is the Tamagawa number of the reduction datum `K`. -/
lemma tsum_deltaP_toReal_mul_truncMomentWeight (p : ℕ) [Fact p.Prime] (k M : ℕ) :
    ∑' K : ReductionData, ((deltaP p K).toReal : ℂ) * ((truncMomentWeight k M K.2 : ℝ) : ℂ)
      = ((∑' t : ℕ, (δ p t).toReal * truncMomentWeight k M t : ℝ) : ℂ) := by
  have hK : Summable fun K : ReductionData =>
      ((deltaP p K).toReal : ℂ) * ((truncMomentWeight k M K.2 : ℝ) : ℂ) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun K => ?_)
      ((hasSum_deltaP_toReal p).summable.mul_right ((M : ℝ) ^ k)))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (norm_ofReal_truncMomentWeight_le k M K.2)
      ENNReal.toReal_nonneg
  have hfib : HasSum (fun t : ℕ => ((δ p t).toReal : ℂ) * ((truncMomentWeight k M t : ℝ) : ℂ))
      (∑' K : ReductionData,
        ((deltaP p K).toReal : ℂ) * ((truncMomentWeight k M K.2 : ℝ) : ℂ)) :=
    (((Equiv.prodComm ℕ KodairaSymbol).hasSum_iff).2 hK.hasSum).prod_fiberwise
      fun t => (hasSum_deltaP_toReal_kodaira p t).mul_right
        ((truncMomentWeight k M t : ℝ) : ℂ)
  have hreal : Summable fun t : ℕ => (δ p t).toReal * truncMomentWeight k M t :=
    Summable.of_nonneg_of_le
      (fun t => mul_nonneg ENNReal.toReal_nonneg (truncMomentWeight_nonneg k M t))
      (fun t => mul_le_mul_of_nonneg_left (truncMomentWeight_le k M t) ENNReal.toReal_nonneg)
      (summable_δ_toReal_mul_pow (p := p) k)
  refine hfib.unique ?_
  have h := hreal.hasSum.map Complex.ofRealHom Complex.continuous_ofReal
  refine h.congr_fun fun t => ?_
  simp [Complex.ofRealHom]

/-- The truncated local moment factor `∑_{t ≥ 1} δ_p(t) w_{k,M}(t)` at a prime `p`, and `1` at a
non-prime `p`. -/
noncomputable def truncMomentFactor (p k M : ℕ) : ℝ :=
  if h : p.Prime then ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * truncMomentWeight k M t else 1

/-- At a prime `p`, `truncMomentFactor p k M = ∑_t δ_p(t) w_{k,M}(t)`. -/
lemma truncMomentFactor_of_prime (p : ℕ) [Fact p.Prime] (k M : ℕ) :
    truncMomentFactor p k M = ∑' t : ℕ, (δ p t).toReal * truncMomentWeight k M t :=
  dite_eq_left Fact.out

/-- The truncated local moment factor is nonnegative. -/
lemma truncMomentFactor_nonneg (p k M : ℕ) : 0 ≤ truncMomentFactor p k M := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [truncMomentFactor_of_prime p k M]
    exact tsum_nonneg fun t =>
      mul_nonneg ENNReal.toReal_nonneg (truncMomentWeight_nonneg k M t)
  · rw [truncMomentFactor, dite_eq_right hp]
    exact zero_le_one

/-- The truncated local moment factor is at most `G_p(k)`. -/
lemma truncMomentFactor_le_momentFactorReal (p k M : ℕ) :
    truncMomentFactor p k M ≤ momentFactorReal p (k : ℝ) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hsub : Summable fun t : ℕ => (δ p t).toReal * truncMomentWeight k M t :=
      Summable.of_nonneg_of_le
        (fun t => mul_nonneg ENNReal.toReal_nonneg (truncMomentWeight_nonneg k M t))
        (fun t => mul_le_mul_of_nonneg_left (truncMomentWeight_le k M t) ENNReal.toReal_nonneg)
        (summable_δ_toReal_mul_pow (p := p) k)
    rw [truncMomentFactor_of_prime p k M, momentFactorReal_of_prime p (k : ℝ)]
    refine Summable.tsum_le_tsum (fun t => ?_) hsub (summable_δ_toReal_mul_rpow p (k : ℝ))
    rw [Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (truncMomentWeight_le k M t) ENNReal.toReal_nonneg
  · rw [truncMomentFactor, dite_eq_right hp, momentFactorReal_of_not_prime hp]

/-- For every finite set `S` and all `k`, `M`, `∏_{p ∈ S prime} (∑_t δ_p(t) w_{k,M}(t)) ≤ C_k`. -/
lemma prod_truncMomentFactor_le (S : Finset ℕ) (k M : ℕ) :
    ∏ q ∈ S.filter Nat.Prime, truncMomentFactor q k M ≤ tamagawaMomentBound (k : ℝ) :=
  le_trans (Finset.prod_le_prod₀ (fun q _ => truncMomentFactor_nonneg q k M)
      fun q _ => truncMomentFactor_le_momentFactorReal q k M)
    (prod_momentFactorReal_le (by positivity) S)

/-! ### The average of the truncated weight over the height-truncated family -/

/-- For every finite set `S` and all `k`, `M`,

`lim_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} ∏_{p ∈ S} w_{k,M}(c_p(E))
  = ∏_{p ∈ S} (∑_{t ≥ 1} δ_p(t) w_{k,M}(t))`,

the products running over the primes in `S`. -/
lemma tendsto_average_prod_truncMomentWeight (S : Finset ℕ) (k M : ℕ) :
    Tendsto (fun X : ℝ => (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ∏ q : ↥(S.filter Nat.Prime),
            truncMomentWeight k M (localTamagawaNumber (q : ℕ) E.1.1 E.1.2))
      atTop (𝓝 (∏ q ∈ S.filter Nat.Prime, truncMomentFactor q k M)) := by
  have key := tendsto_average_prod_tauZ S
    (fun _ K => ((truncMomentWeight k M K.2 : ℝ) : ℂ)) (B := fun _ => (M : ℝ) ^ k)
    fun _ K => norm_ofReal_truncMomentWeight_le k M K.2
  have hlim : (∏ q : ↥(S.filter Nat.Prime), ∑' K : ReductionData,
        ((deltaP (q : ℕ) K).toReal : ℂ) * ((truncMomentWeight k M K.2 : ℝ) : ℂ))
      = ((∏ q ∈ S.filter Nat.Prime, truncMomentFactor q k M : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod, ← Finset.prod_coe_sort (S.filter Nat.Prime)
      fun q => ((truncMomentFactor q k M : ℝ) : ℂ)]
    refine Finset.prod_congr rfl fun q _ => ?_
    have : Fact (q : ℕ).Prime := ⟨(Finset.mem_filter.1 q.2).2⟩
    rw [tsum_deltaP_toReal_mul_truncMomentWeight (q : ℕ) k M, truncMomentFactor_of_prime]
  rw [hlim] at key
  have hcast : ∀ X : ℝ, ((integralShortNFCount X : ℂ))⁻¹ *
      ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily},
        ∏ q : ↥(S.filter Nat.Prime),
          ((truncMomentWeight k M ((tauZ (q : ℕ) E.1.1 E.1.2).kodairaSymbol,
            (tauZ (q : ℕ) E.1.1 E.1.2).tamagawaNumber).2 : ℝ) : ℂ)
      = (((integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ∏ q : ↥(S.filter Nat.Prime),
            truncMomentWeight k M (localTamagawaNumber (q : ℕ) E.1.1 E.1.2) : ℝ) : ℂ) := by
    intro X
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_tsum]
    refine congrArg _ (tsum_congr fun E => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun q _ => ?_
    have : Fact (q : ℕ).Prime := ⟨(Finset.mem_filter.1 q.2).2⟩
    rw [localTamagawaNumber_of_prime]
  have hre := (Complex.continuous_re.tendsto _).comp key
  refine hre.congr fun X => ?_
  simp only [Function.comp_apply, hcast X, Complex.ofReal_re]

/-! ### The pointwise domination -/

/-- The truncated Tamagawa product `Tam_S(E)` is at least `1`. -/
lemma one_le_truncatedTamagawaProduct (S : Finset ℕ) (a₄ a₆ : ℤ) :
    1 ≤ truncatedTamagawaProduct S a₄ a₆ :=
  Finset.one_le_prod fun p _ => localTamagawaNumber_pos p a₄ a₆

/-- For every finite set `S` and every pair `(a₄, a₆)`,

`w_{k,M}(Tam_S(E)) ≤ ∏_{p ∈ S} w_{k,M}(c_p(E))`,

the product running over the primes in `S`. -/
lemma truncMomentWeight_truncatedTamagawaProduct_le (S : Finset ℕ) (k M : ℕ) (a₄ a₆ : ℤ) :
    truncMomentWeight k M (truncatedTamagawaProduct S a₄ a₆)
      ≤ ∏ q : ↥(S.filter Nat.Prime),
          truncMomentWeight k M (localTamagawaNumber (q : ℕ) a₄ a₆) := by
  have hprod : ∏ q : ↥(S.filter Nat.Prime), localTamagawaNumber (q : ℕ) a₄ a₆
      = truncatedTamagawaProduct S a₄ a₆ :=
    prod_localTamagawaNumber_eq_truncatedTamagawaProduct S a₄ a₆
  by_cases hM : truncatedTamagawaProduct S a₄ a₆ ≤ M
  · have hone : ∀ i ∈ (Finset.univ : Finset ↥(S.filter Nat.Prime)),
        1 ≤ localTamagawaNumber (i : ℕ) a₄ a₆ := by
      intro i _
      have := localTamagawaNumber_pos (i : ℕ) a₄ a₆
      omega
    have hle : ∀ q : ↥(S.filter Nat.Prime), localTamagawaNumber (q : ℕ) a₄ a₆ ≤ M := by
      intro q
      refine le_trans ?_ hM
      rw [← hprod]
      exact Finset.single_le_prod hone (Finset.mem_univ q)
    have hRHS : ∏ q : ↥(S.filter Nat.Prime),
        truncMomentWeight k M (localTamagawaNumber (q : ℕ) a₄ a₆)
        = ((truncatedTamagawaProduct S a₄ a₆ : ℕ) : ℝ) ^ k := by
      rw [Finset.prod_congr rfl fun q _ => truncMomentWeight_of_le (k := k) (hle q),
        Finset.prod_pow, ← Nat.cast_prod, hprod]
    rw [truncMomentWeight_of_le hM, hRHS]
  · rw [truncMomentWeight, ite_eq_right hM]
    exact Finset.prod_nonneg fun q _ => truncMomentWeight_nonneg k M _

/-! ### The `S`-truncated truncated moment -/

open scoped Classical in
/-- For every `X ≥ 0`,

`∑_{m = 1}^{M} P_Tam^S(m; X) m^k = (1/N(X)) ∑_{Ht(E) ≤ X} w_{k,M}(Tam_S(E))`. -/
lemma sum_truncatedTamagawaTupleProportion_mul_pow (S : Finset ℕ) (k M : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ m ∈ Finset.Icc 1 M, truncatedTamagawaTupleProportion S m X * (m : ℝ) ^ k
      = (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          truncMomentWeight k M (truncatedTamagawaProduct S E.1.1 E.1.2) := by
  have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} :=
    (finite_setOf_height_le_and_mem_family hX).to_subtype
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      truncatedTamagawaTupleProportion S m X * (m : ℝ) ^ k
        = (integralShortNFCount X : ℝ)⁻¹ *
          ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
              E ∈ integralShortNFFamily},
            (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then ((m : ℝ) ^ k) else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.1 hm).1
      omega
    rw [truncatedTamagawaTupleProportion_eq_average S hm0 hX, mul_assoc, ← tsum_mul_right]
    exact congrArg _ (tsum_congr fun E => by split_ifs <;> simp)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    ← Summable.tsum_finsetSum fun _ _ => Summable.of_finite]
  refine congrArg _ (tsum_congr fun E => ?_)
  rw [Finset.sum_ite_eq (Finset.Icc 1 M) (truncatedTamagawaProduct S E.1.1 E.1.2)
    fun m : ℕ => ((m : ℝ) ^ k)]
  by_cases h : truncatedTamagawaProduct S E.1.1 E.1.2 ≤ M
  · rw [ite_eq_left (Finset.mem_Icc.2 ⟨one_le_truncatedTamagawaProduct S E.1.1 E.1.2, h⟩),
      truncMomentWeight_of_le h]
  · rw [ite_eq_right fun hc => h (Finset.mem_Icc.1 hc).2, truncMomentWeight, ite_eq_right h]

/-- The limiting law `P_Tam^S(m)` of the Tamagawa product over a finite set `S` of primes: the sum,
over the tuples `(c_p)_{p ∈ S}` with product `m`, of the limiting proportion of curves with those
local Tamagawa numbers. -/
noncomputable def truncatedTamagawaDensity (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ t ∈ tamagawaTupleFactorizations S m,
    limUnder atTop (localTamagawaTupleProportion S (Finsupp.equivFunOnFinite.symm t))

/-- The proportion `P_Tam^S(m; X)` tends to `P_Tam^S(m)` as `X → ∞`. -/
lemma tendsto_truncatedTamagawaDensity (S : Finset ℕ) (m : ℕ) :
    Tendsto (truncatedTamagawaTupleProportion S m) atTop
      (𝓝 (truncatedTamagawaDensity S m)) :=
  tendsto_truncatedTamagawaTupleProportion S m

/-- For every finite set `S` and all `k`, `M`, `∑_{m = 1}^{M} P_Tam^S(m) m^k ≤ C_k`. -/
theorem sum_truncatedTamagawaDensity_mul_pow_le (S : Finset ℕ) (k M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, truncatedTamagawaDensity S m * (m : ℝ) ^ k
      ≤ tamagawaMomentBound (k : ℝ) := by
  have hL : Tendsto (fun X : ℝ => ∑ m ∈ Finset.Icc 1 M,
      truncatedTamagawaTupleProportion S m X * (m : ℝ) ^ k) atTop
      (𝓝 (∑ m ∈ Finset.Icc 1 M, truncatedTamagawaDensity S m * (m : ℝ) ^ k)) :=
    tendsto_finsetSum _ fun m _ => (tendsto_truncatedTamagawaDensity S m).mul_const _
  have hR := tendsto_average_prod_truncMomentWeight S k M
  have hle : ∀ᶠ X in atTop, (∑ m ∈ Finset.Icc 1 M,
      truncatedTamagawaTupleProportion S m X * (m : ℝ) ^ k)
      ≤ (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ∏ q : ↥(S.filter Nat.Prime),
            truncMomentWeight k M (localTamagawaNumber (q : ℕ) E.1.1 E.1.2) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
        E ∈ integralShortNFFamily} :=
      (finite_setOf_height_le_and_mem_family hX).to_subtype
    rw [sum_truncatedTamagawaTupleProportion_mul_pow S k M hX]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Summable.tsum_le_tsum
      (fun E => truncMomentWeight_truncatedTamagawaProduct_le S k M E.1.1 E.1.2)
      Summable.of_finite Summable.of_finite
  exact le_trans (le_of_tendsto_of_tendsto hL hR hle) (prod_truncMomentFactor_le S k M)

/-! ### The tail: `P_Tam` is uniformly close to `P_Tam^S` -/

/-- For a finite set `S ⊇ {2, 3}` and `m ≠ 0`,

`|P_Tam(m) - P_Tam^S(m)| ≤ ∑_{p ∉ S} (1 - β_p)`. -/
lemma abs_tamagawaDensity_sub_truncatedTamagawaDensity_le (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) :
    |tamagawaDensity m - truncatedTamagawaDensity S m|
      ≤ ∑' p : ℕ, if p ∈ S then 0 else betaDefect p := by
  have h : Tendsto (fun X : ℝ =>
      |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X|) atTop
      (𝓝 |tamagawaDensity m - truncatedTamagawaDensity S m|) :=
    ((tendsto_tamagawaProportion_tamagawaDensity m).sub
      (tendsto_truncatedTamagawaDensity S m)).abs
  rw [← h.limsup_eq]
  exact limsup_abs_sub_truncatedTamagawaTupleProportion_le S hm h2 h3

/-! ### The moment bound for `P_Tam`, and summability -/

/-- For all `k` and `M`,

`∑_{m = 1}^{M} P_Tam(m) m^k ≤ C_k`. -/
theorem sum_tamagawaDensity_mul_pow_le (k M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, tamagawaDensity m * (m : ℝ) ^ k ≤ tamagawaMomentBound (k : ℝ) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set A : ℝ := ∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ k with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun m _ => by positivity
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  have hη : 0 < ε / (A + 1) := by positivity
  obtain ⟨S, h23, hS⟩ : ∃ S : Finset ℕ, ({2, 3} : Finset ℕ) ≤ S ∧
      (∑' p : ℕ, if p ∈ S then 0 else betaDefect p) < ε / (A + 1) := by
    have h := (tendsto_tsum_betaDefect_compl.eventually (eventually_lt_nhds hη)).and
      (eventually_ge_atTop ({2, 3} : Finset ℕ))
    obtain ⟨S, hS1, hS2⟩ := h.exists
    exact ⟨S, hS2, hS1⟩
  have h2 : 2 ∈ S := h23 (by decide)
  have h3 : 3 ∈ S := h23 (by decide)
  set b : ℝ := ∑' p : ℕ, (if p ∈ S then (0 : ℝ) else betaDefect p) with hbdef
  have hb0 : 0 ≤ b := tsum_nonneg fun p => by
    split
    · exact le_rfl
    · exact betaDefect_nonneg p
  have hstep : ∑ m ∈ Finset.Icc 1 M, tamagawaDensity m * (m : ℝ) ^ k
      ≤ ∑ m ∈ Finset.Icc 1 M,
          (truncatedTamagawaDensity S m * (m : ℝ) ^ k + b * (m : ℝ) ^ k) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.1 hm).1
      omega
    have hle : tamagawaDensity m ≤ truncatedTamagawaDensity S m + b := by
      have := (abs_le.1 (abs_tamagawaDensity_sub_truncatedTamagawaDensity_le S hm0 h2 h3)).2
      linarith
    calc tamagawaDensity m * (m : ℝ) ^ k
        ≤ (truncatedTamagawaDensity S m + b) * (m : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = truncatedTamagawaDensity S m * (m : ℝ) ^ k + b * (m : ℝ) ^ k := by ring
  have hsplit : ∑ m ∈ Finset.Icc 1 M,
      (truncatedTamagawaDensity S m * (m : ℝ) ^ k + b * (m : ℝ) ^ k)
      = (∑ m ∈ Finset.Icc 1 M, truncatedTamagawaDensity S m * (m : ℝ) ^ k) + b * A := by
    rw [Finset.sum_add_distrib, hAdef, Finset.mul_sum]
  have hbA : b * A ≤ ε := by
    have h1 : b * A ≤ (ε / (A + 1)) * A := mul_le_mul_of_nonneg_right hS.le hA0
    have h2' : (ε / (A + 1)) * A ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hA1]
      nlinarith
    linarith
  have hfin := sum_truncatedTamagawaDensity_mul_pow_le S k M
  rw [hsplit] at hstep
  linarith

/-- For every `k : ℕ`, the family `m ↦ P_Tam(m) m^k` is summable. -/
theorem summable_tamagawaDensity_mul_pow (k : ℕ) :
    Summable fun m : ℕ => tamagawaDensity m * (m : ℝ) ^ k := by
  refine summable_of_sum_le
    (f := fun m : ℕ => tamagawaDensity m * (m : ℝ) ^ k) (c := tamagawaMomentBound (k : ℝ))
    (fun m => mul_nonneg (tamagawaDensity_nonneg m) (by positivity)) fun u => ?_
  have hsub : u ⊆ insert 0 (Finset.Icc 1 (u.sup id)) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_Icc.2 ⟨hpos, Finset.le_sup (f := id) hm⟩)
  have hzero : tamagawaDensity 0 * ((0 : ℕ) : ℝ) ^ k = 0 := by
    rw [tamagawaDensity_zero, zero_mul]
  calc ∑ m ∈ u, tamagawaDensity m * (m : ℝ) ^ k
      ≤ ∑ m ∈ insert 0 (Finset.Icc 1 (u.sup id)), tamagawaDensity m * (m : ℝ) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          mul_nonneg (tamagawaDensity_nonneg m) (by positivity)
    _ = ∑ m ∈ Finset.Icc 1 (u.sup id), tamagawaDensity m * (m : ℝ) ^ k := by
        rw [Finset.sum_insert (by simp), hzero, zero_add]
    _ ≤ tamagawaMomentBound (k : ℝ) := sum_tamagawaDensity_mul_pow_le k (u.sup id)

/-- For every `x : ℝ`, the family `m ↦ P_Tam(m) m^x` is summable. -/
theorem summable_tamagawaDensity_mul_rpow (x : ℝ) :
    Summable fun m : ℕ => tamagawaDensity m * (m : ℝ) ^ x := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (tamagawaDensity_nonneg m) (Real.rpow_nonneg (by positivity) x))
    (fun m => ?_) (summable_tamagawaDensity_mul_pow ⌈x⌉₊)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [tamagawaDensity_zero, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (tamagawaDensity_nonneg m)
    rw [← Real.rpow_natCast (m : ℝ) ⌈x⌉₊]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (Nat.le_ceil x)

/-- For every `s : ℂ`, the family `m ↦ ‖P_Tam(m) m^{-s}‖` is summable. -/
theorem summable_norm_tamagawaDensity_mul_cpow_all (s : ℂ) :
    Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖ :=
  (summable_norm_tamagawaDensity_mul_cpow_iff s).2 (summable_tamagawaDensity_mul_rpow (-s.re))

/-- `HasEulerProductOffHalfPlane` holds if and only if, for every `s : ℂ`,

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`. -/
theorem hasEulerProductOffHalfPlane_iff_tsum_eq :
    HasEulerProductOffHalfPlane ↔ ∀ s : ℂ,
      ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
        = ∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s := by
  rw [hasEulerProductOffHalfPlane_iff]
  exact forall_congr' fun s =>
    ⟨fun h => h.2, fun h => ⟨summable_norm_tamagawaDensity_mul_cpow_all s, h⟩⟩

end WeierstrassCurve
