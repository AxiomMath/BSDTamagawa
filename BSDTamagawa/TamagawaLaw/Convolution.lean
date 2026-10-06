/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.FubiniFiniteProduct
public import BSDTamagawa.TamagawaLaw.MomentsFinite

/-!
# The `S`-truncated Tamagawa law is the `S`-fold convolution of the local laws

For a finite set `S` of primes, the joint limiting density of the local Tamagawa numbers,
`lim_{X → ∞} #{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X)`, equals the product `∏_{p ∈ S} δ_p(𝐭_p)` of the local
densities. Consequently the `S`-truncated limiting law `P_Tam^S(m)` is the `S`-fold multiplicative
convolution of the local laws `(δ_p)_{p ∈ S}`: the local reductions at distinct primes are
asymptotically independent.

## Main definitions

* `WeierstrassCurve.localDensity`: `δ_p(t)` as a real number at a prime `p`, and `0` otherwise.

## Main results

* `WeierstrassCurve.limUnder_localTamagawaTupleProportion`:
  `lim_X #{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X) = ∏_{p ∈ S} δ_p(𝐭_p)`.
* `WeierstrassCurve.truncatedTamagawaDensity_eq`:
  `P_Tam^S(m) = ∑_{∏_p 𝐭_p = m} ∏_{p ∈ S} δ_p(𝐭_p)`.
* `WeierstrassCurve.hasPolydiscExpansion_prodLocalDensity`: the product family
  `𝐭 ↦ ∏_{p ∈ S} δ_p(𝐭_p)` is the coefficient family of `localTamagawaEuler S` on the open unit
  polydisc.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.Analysis.FinsuppFubini
open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex
open BSDTamagawa.CoeffExtraction BSDTamagawa.FiberCount BSDTamagawa.PrimeCountDensity

/-! ### `δ_p` as a total real-valued function -/

/-- `δ_p(t)` as a real number and as a total function of `p : ℕ`: the local density `δ p t` at a
prime and `0` at every non-prime. -/
noncomputable def localDensity (p t : ℕ) : ℝ :=
  if h : p.Prime then (@δ p ⟨h⟩ t).toReal else 0

/-- At a prime `p`, `localDensity p t` is the real number `δ_p(t)`. -/
lemma localDensity_of_prime (p : ℕ) [Fact p.Prime] (t : ℕ) :
    localDensity p t = (δ p t).toReal :=
  dite_eq_left Fact.out

/-- Off the primes, `localDensity p t` vanishes. -/
lemma localDensity_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (t : ℕ) : localDensity p t = 0 :=
  dite_eq_right hp

/-- The local densities are nonnegative. -/
lemma localDensity_nonneg (p t : ℕ) : 0 ≤ localDensity p t := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [localDensity_of_prime]
    exact ENNReal.toReal_nonneg
  · rw [localDensity_of_not_prime hp]

/-- `δ_p(0) = 0`, in the total form. -/
@[simp]
lemma localDensity_zero (p : ℕ) : localDensity p 0 = 0 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [localDensity_of_prime, δ_zero, ENNReal.toReal_zero]
  · rw [localDensity_of_not_prime hp]

/-- The local law `t ↦ localDensity p t` is summable. -/
lemma summable_localDensity (p : ℕ) : Summable (localDensity p) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    exact (summable_δ_toReal p).congr fun t => (localDensity_of_prime p t).symm
  · exact summable_zero.congr fun t => (localDensity_of_not_prime hp t).symm

/-- For every real exponent `x`, the family `t ↦ δ_p(t) t^x` is summable. -/
lemma summable_localDensity_mul_rpow (p : ℕ) (x : ℝ) :
    Summable fun t : ℕ => localDensity p t * (t : ℝ) ^ x := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    exact (summable_δ_toReal_mul_rpow p x).congr fun t => by rw [localDensity_of_prime]
  · exact summable_zero.congr fun t => by rw [localDensity_of_not_prime hp, zero_mul]

/-! ### The reduction-data collapse at a bounded weight -/

/-- For every prime `p` and every `w : ℕ → ℂ` with `‖w t‖ ≤ B` for all `t`,

`∑_{K ∈ 𝒦 × ℕ} δ_p(K) w(c(K)) = ∑_{t ≥ 0} δ_p(t) w(t)`,

where `c(K)` is the Tamagawa coordinate of the reduction datum `K`. -/
lemma tsum_deltaP_toReal_mul_of_bounded (p : ℕ) [Fact p.Prime] (w : ℕ → ℂ) {B : ℝ}
    (hw : ∀ t : ℕ, ‖w t‖ ≤ B) :
    ∑' K : ReductionData, ((deltaP p K).toReal : ℂ) * w K.2
      = ∑' t : ℕ, ((δ p t).toReal : ℂ) * w t := by
  have hK : Summable fun K : ReductionData => ((deltaP p K).toReal : ℂ) * w K.2 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun K => ?_)
      ((hasSum_deltaP_toReal p).summable.mul_right B))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hw K.2) ENNReal.toReal_nonneg
  have hfib : HasSum (fun t : ℕ => ((δ p t).toReal : ℂ) * w t)
      (∑' K : ReductionData, ((deltaP p K).toReal : ℂ) * w K.2) :=
    (((Equiv.prodComm ℕ KodairaSymbol).hasSum_iff).2 hK.hasSum).prod_fiberwise
      fun t => (hasSum_deltaP_toReal_kodaira p t).mul_right (w t)
  exact hfib.tsum_eq.symm

/-! ### The finite Euler product in terms of the local laws -/

/-- For every `𝐳` in the closed unit polydisc, `localTamagawaEuler S 𝐳` is the product of the local
generating functions:

`∏_{p ∈ S} (∑_{K} δ_p(K) z_p^{c(K)}) = ∏_{p ∈ S} (∑_{t ≥ 0} δ_p(t) z_p^t)`. -/
lemma localTamagawaEuler_eq_prod_tsum (S : Finset ℕ) (z : ↥(S.filter Nat.Prime) → ℂ)
    (hz : ∀ p, ‖z p‖ ≤ 1) :
    localTamagawaEuler S z
      = ∏ p : ↥(S.filter Nat.Prime), ∑' t : ℕ, ((localDensity (p : ℕ) t : ℝ) : ℂ) * z p ^ t := by
  rw [localTamagawaEuler]
  refine Finset.prod_congr rfl fun p _ => ?_
  have : Fact (p : ℕ).Prime := ⟨(Finset.mem_filter.1 p.2).2⟩
  rw [tsum_deltaP_toReal_mul_of_bounded (p : ℕ) (fun t : ℕ => z p ^ t) (B := 1) fun t => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hz p)]
  exact tsum_congr fun t => by rw [localDensity_of_prime]

/-! ### The convolution family expands the same generating function -/

/-- On the open unit polydisc,

`∏_{p ∈ S} (∑_{t ≥ 0} δ_p(t) z_p^t) = ∑_{𝐭 : S →₀ ℕ} (∏_{p ∈ S} δ_p(𝐭_p)) 𝐳^𝐭`,

so `𝐭 ↦ ∏_{p ∈ S} δ_p(𝐭_p)` is a polydisc expansion of `localTamagawaEuler S`. -/
theorem hasPolydiscExpansion_prodLocalDensity (S : Finset ℕ) :
    HasPolydiscExpansion
      (fun t : ↥(S.filter Nat.Prime) →₀ ℕ =>
        ((∏ p : ↥(S.filter Nat.Prime), localDensity (p : ℕ) (t p) : ℝ) : ℂ))
      (localTamagawaEuler S) := by
  intro z hz
  have hnorm : ∀ p : ↥(S.filter Nat.Prime),
      Summable fun t : ℕ => ‖((localDensity (p : ℕ) t : ℝ) : ℂ) * z p ^ t‖ := by
    intro p
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
      (summable_localDensity (p : ℕ))
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (localDensity_nonneg (p : ℕ) t), norm_pow]
    exact mul_le_of_le_one_right (localDensity_nonneg (p : ℕ) t)
      (pow_le_one₀ (norm_nonneg _) (hz p).le)
  have h := hasSum_finsuppProd
    (fun (p : ↥(S.filter Nat.Prime)) (t : ℕ) => ((localDensity (p : ℕ) t : ℝ) : ℂ) * z p ^ t)
    hnorm
  rw [localTamagawaEuler_eq_prod_tsum S z fun p => (hz p).le]
  refine h.congr_fun fun t => ?_
  simp only [smul_eq_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]

/-! ### The closed form of the fibre densities -/

/-- For every finite `S` and every multi-index `𝐭`,

`lim_{X → ∞} #{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X) = ∏_{p ∈ S} δ_p(𝐭_p)`,

that is, the joint limiting law of `(c_p(E))_{p ∈ S}` is the product of the local laws. -/
theorem limUnder_localTamagawaTupleProportion (S : Finset ℕ) (t : ↥(S.filter Nat.Prime) →₀ ℕ) :
    limUnder atTop (localTamagawaTupleProportion S t)
      = ∏ p : ↥(S.filter Nat.Prime), localDensity (p : ℕ) (t p) := by
  have hexp := (hasPolydiscExpansion_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (localTamagawaTuple S) (localTamagawaEuler S) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun X hX => by
      rw [ncard_setOf_height_le_and_mem_family]
      exact integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_localTamagawaMonomial_div S z fun p => (hz p).le)).2.2.2
  exact Complex.ofReal_injective
    (congrFun (coeff_eq_of_hasPolydiscExpansion hexp
      (hasPolydiscExpansion_prodLocalDensity S)) t)

/-! ### The `S`-truncated law as the `S`-fold multiplicative convolution -/

/-- For every finite `S` and every `m`, `P_Tam^S(m)` is the `S`-fold multiplicative convolution of
the local laws:

`P_Tam^S(m) = ∑_{𝐭 : ∏_{p ∈ S} 𝐭_p = m} ∏_{p ∈ S} δ_p(𝐭_p)`. -/
theorem truncatedTamagawaDensity_eq (S : Finset ℕ) (m : ℕ) :
    truncatedTamagawaDensity S m
      = ∑ t ∈ tamagawaTupleFactorizations S m,
          ∏ p : ↥(S.filter Nat.Prime), localDensity (p : ℕ) (t p) := by
  rw [truncatedTamagawaDensity]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [limUnder_localTamagawaTupleProportion]
  exact Finset.prod_congr rfl fun p _ => by simp

/-- The `S`-truncated Tamagawa law `P_Tam^S(m)` is nonnegative. -/
lemma truncatedTamagawaDensity_nonneg (S : Finset ℕ) (m : ℕ) :
    0 ≤ truncatedTamagawaDensity S m := by
  rw [truncatedTamagawaDensity_eq]
  exact Finset.sum_nonneg fun t _ =>
    Finset.prod_nonneg fun p _ => localDensity_nonneg (p : ℕ) (t p)

/-- There are no factorizations of `0` indexed by `S`: a tuple with product `0` has a zero entry,
and `Nat.divisors 0 = ∅`. -/
@[simp]
lemma tamagawaTupleFactorizations_zero (S : Finset ℕ) :
    tamagawaTupleFactorizations S 0 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun t ht => ?_
  rw [tamagawaTupleFactorizations, Finset.mem_filter, Fintype.mem_piFinset] at ht
  obtain ⟨p, -, -⟩ := Finset.prod_eq_zero_iff.1 ht.2
  exact absurd (Nat.mem_divisors.1 (ht.1 p)).2 (by simp)

/-- `P_Tam^S(0) = 0`: the `S`-truncated law is supported on `m ≥ 1`. -/
@[simp]
lemma truncatedTamagawaDensity_zero (S : Finset ℕ) : truncatedTamagawaDensity S 0 = 0 := by
  rw [truncatedTamagawaDensity_eq, tamagawaTupleFactorizations_zero, Finset.sum_empty]

end WeierstrassCurve
