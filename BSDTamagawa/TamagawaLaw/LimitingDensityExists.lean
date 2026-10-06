/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.LimitingDensity
public import BSDTamagawa.PrimeCount.LimitingDensityExists

/-!
# Existence of the limiting Tamagawa density

For every `m`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Tam(E) = m} / N(X) = P_Tam(m)`,

with `P_Tam(m)` the limiting density `tamagawaDensity m`. For a finite set `S` of primes write
`Tam_S(E) = ∏_{p ∈ S} c_p(E)`. The joint law of the local Tamagawa numbers `(c_p(E))_{p ∈ S}`
converges, hence so does the proportion of curves with `Tam_S(E) = m`; and
`limsup_{X → ∞} |P_Tam(m; X) - P_Tam^S(m; X)| ≤ ∑_{p ∉ S} (1 - β_p)`, which tends to `0` as `S`
exhausts the primes. Approximation by convergent families then gives convergence of `P_Tam(m; X)`.

## Main definitions

* `WeierstrassCurve.localTamagawaTuple`: the tuple `𝐜_S(E) = (c_p(E))_{p ∈ S}` of local Tamagawa
  numbers.
* `WeierstrassCurve.localTamagawaTupleProportion`: the proportion
  `#{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X)`.
* `WeierstrassCurve.tamagawaTupleFactorizations`: the tuples `𝐭` with `∏_{p ∈ S} t_p = m`.
* `WeierstrassCurve.truncatedTamagawaTupleProportion`: the `S`-truncated proportion
  `P_Tam^S(m; X)`.

## Main results

* `WeierstrassCurve.tendsto_localTamagawaTupleProportion`: the fibre proportions of `𝐜_S` converge.
* `WeierstrassCurve.limsup_abs_sub_truncatedTamagawaTupleProportion_le`: the bound on
  `limsup |P_Tam(m; X) - P_Tam^S(m; X)|`.
* `WeierstrassCurve.exists_tendsto_tamagawaProportion`: `P_Tam(m; X)` converges as `X → ∞`.
* `WeierstrassCurve.tendsto_tamagawaProportion_tamagawaDensity`: `P_Tam(m; X) → P_Tam(m)`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Theorem 1.1.
-/

@[expose] public section

open Filter Topology

namespace BSDTamagawa.TamagawaDensityExists

/-! ### Two generic lemmas -/

/-- For predicates `Q`, `P` on any type, `∑_{x : Q} 1[P x] = #{x : Q x ∧ P x}`, with `Set.ncard` on
the right (both sides are `0` when the intersection is infinite). -/
lemma tsum_ite_ncard_inter {α : Type*} (Q P : α → Prop) [DecidablePred P] :
    ∑' x : {x : α // Q x}, (if P (x : α) then (1 : ℝ) else 0)
      = ({x | Q x ∧ P x}.ncard : ℝ) := by
  have h : ∀ x : {x : α // Q x}, (if P (x : α) then (1 : ℝ) else 0)
      = {y | P y}.indicator (fun _ => (1 : ℝ)) (x : α) := by
    intro x
    by_cases hx : P (x : α)
    · rw [ite_eq_left hx]
      exact (Set.indicator_of_mem (show (x : α) ∈ {y | P y} from hx)
        (fun _ => (1 : ℝ))).symm
    · rw [ite_eq_right hx]
      exact (Set.indicator_of_notMem (show (x : α) ∉ {y | P y} from hx)
        (fun _ => (1 : ℝ))).symm
  rw [tsum_congr h, show (∑' x : {x : α // Q x}, {y | P y}.indicator (fun _ => (1 : ℝ)) (x : α))
      = ∑' x : ↥{y | Q y}, {y | P y}.indicator (fun _ => (1 : ℝ)) (x : α) from rfl,
    tsum_subtype, Set.indicator_indicator, ← tsum_subtype, tsum_const,
    Nat.card_coe_set_eq, nsmul_eq_mul, mul_one]
  rfl

/-- If for every `ε > 0` some real constant `c` satisfies `|f X - c| ≤ ε` for all large `X`, then
`f` converges as `X → ∞`. -/
lemma exists_tendsto_of_forall_eventually_abs_sub_le {f : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ᶠ X in atTop, |f X - c| ≤ ε) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hcauchy : Cauchy (map f atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨map_neBot, fun ε hε => ?_⟩
    obtain ⟨c, hc⟩ := h (ε / 3) (by linarith)
    refine ⟨{y : ℝ | |y - c| ≤ ε / 3}, hc, fun x hx y hy => ?_⟩
    simp only [Set.mem_ofPred_eq] at hx hy
    have htri : |x - y| ≤ |x - c| + |c - y| := abs_sub_le x c y
    rw [abs_sub_comm c y] at htri
    rw [Real.dist_eq]
    linarith
  obtain ⟨L, hL⟩ := CompleteSpace.complete hcauchy
  exact ⟨L, hL⟩

end BSDTamagawa.TamagawaDensityExists

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex BSDTamagawa.TamagawaDensityExists
open BSDTamagawa.PrimeSqTail BSDTamagawa.FiberCount BSDTamagawa.PrimeCountDensity
open ShortWeierstrassReductionStatistics

/-! ### The joint local Tamagawa tuple, and its fibre densities -/

/-- The tuple of local Tamagawa numbers at the primes of `S`,
`𝐜_S(q) := (c_p(q))_{p ∈ S, p prime}`, as a finitely supported function on `↥(S.filter Nat.Prime)`.
-/
noncomputable def localTamagawaTuple (S : Finset ℕ) (q : ℤ × ℤ) :
    ↥(S.filter Nat.Prime) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p : ↥(S.filter Nat.Prime) => localTamagawaNumber (p : ℕ) q.1 q.2

/-- The finite product `∏_{p ∈ S} (∑_K δ_p(K) z_p^{c(K)})` over the primes of `S`, where `K` ranges
over the reduction data and `c(K)` is the Tamagawa coordinate of `K`. -/
noncomputable def localTamagawaEuler (S : Finset ℕ) (z : ↥(S.filter Nat.Prime) → ℂ) : ℂ :=
  ∏ p : ↥(S.filter Nat.Prime), ∑' K : ReductionData, ((deltaP (p : ℕ) K).toReal : ℂ) * z p ^ K.2

/-- For `𝐳` in the closed unit polydisc,

`(1/N(X)) ∑_{Ht(E) ≤ X} ∏_{p ∈ S} z_p^{c_p(E)} ⟶ ∏_{p ∈ S} (∑_K δ_p(K) z_p^{c(K)})`

as `X → ∞`. -/
theorem tendsto_tsum_indicator_localTamagawaMonomial_div (S : Finset ℕ)
    (z : ↥(S.filter Nat.Prime) → ℂ) (hz : ∀ p, ‖z p‖ ≤ 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.indicator
          (fun q => multiMonomial (⇑(localTamagawaTuple S q)) z) q) /
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.ncard : ℂ))
      atTop (𝓝 (localTamagawaEuler S z)) := by
  refine (tendsto_average_prod_tauZ S (fun p K => z p ^ K.2) (B := fun _ => 1)
    (fun p K => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hz p))).congr fun X => ?_
  rw [ncard_setOf_height_le_and_mem_family, div_eq_inv_mul]
  congr 1
  rw [← tsum_subtype]
  refine tsum_congr fun E => ?_
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [show (localTamagawaTuple S E.1) p = localTamagawaNumber (p : ℕ) E.1.1 E.1.2 from rfl,
    localTamagawaNumber_of_prime]

/-- The height-truncated proportion `#{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X)` of a fibre of `𝐜_S`. -/
noncomputable def localTamagawaTupleProportion (S : Finset ℕ)
    (t : ↥(S.filter Nat.Prime) →₀ ℕ) (X : ℝ) : ℝ :=
  ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily} ∧ localTamagawaTuple S q = t}.ncard : ℝ) /
    ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.ncard : ℝ)

/-- For every finite `S` and every multi-index `𝐭`, the proportion
`#{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X)` converges as `X → ∞`. -/
theorem tendsto_localTamagawaTupleProportion (S : Finset ℕ) (t : ↥(S.filter Nat.Prime) →₀ ℕ) :
    Tendsto (localTamagawaTupleProportion S t) atTop
      (𝓝 (limUnder atTop (localTamagawaTupleProportion S t))) :=
  tendsto_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (localTamagawaTuple S) (localTamagawaEuler S) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun X hX => by
      rw [ncard_setOf_height_le_and_mem_family]
      exact integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_localTamagawaMonomial_div S z fun p => (hz p).le) t

/-! ### The truncated event `Tam_S(E) = m` as a finite union of fibres -/

/-- The tuples `𝐭`, indexed by the primes of `S`, with entries dividing `m` and
`∏_{p ∈ S} t_p = m`. -/
noncomputable def tamagawaTupleFactorizations (S : Finset ℕ) (m : ℕ) :
    Finset (↥(S.filter Nat.Prime) → ℕ) :=
  (Fintype.piFinset fun _ => m.divisors).filter fun t => ∏ p, t p = m

/-- For `m ≠ 0`, a tuple lies in `tamagawaTupleFactorizations S m` if and only if its product is
`m`. -/
lemma mem_tamagawaTupleFactorizations_iff (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0)
    (t : ↥(S.filter Nat.Prime) → ℕ) :
    t ∈ tamagawaTupleFactorizations S m ↔ ∏ p, t p = m := by
  rw [tamagawaTupleFactorizations, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun p => Nat.mem_divisors.2 ⟨?_, hm⟩, h⟩⟩
  exact h ▸ Finset.dvd_prod_of_mem t (Finset.mem_univ p)

/-- `∏_{p ∈ S, p prime} c_p(E) = Tam_S(E)`, the truncated Tamagawa product. -/
lemma prod_localTamagawaNumber_eq_truncatedTamagawaProduct (S : Finset ℕ) (a₄ a₆ : ℤ) :
    ∏ p : ↥(S.filter Nat.Prime), localTamagawaNumber (p : ℕ) a₄ a₆
      = truncatedTamagawaProduct S a₄ a₆ := by
  rw [truncatedTamagawaProduct,
    Finset.prod_coe_sort (S.filter Nat.Prime) fun p => localTamagawaNumber p a₄ a₆]
  refine Finset.prod_filter_of_ne fun p _ hne => ?_
  exact prime_of_one_lt_localTamagawaNumber ((one_lt_localTamagawaNumber_iff p a₄ a₆).mpr hne)

open scoped Classical in
/-- For `m ≠ 0`,

`∑_{𝐭 : ∏ 𝐭 = m} 1[𝐜_S(E) = 𝐭] = 1[Tam_S(E) = m]`. -/
lemma sum_ite_localTamagawaTuple_eq (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0) (q : ℤ × ℤ) :
    ∑ t ∈ tamagawaTupleFactorizations S m,
        (if localTamagawaTuple S q = Finsupp.equivFunOnFinite.symm t then (1 : ℝ) else 0)
      = if truncatedTamagawaProduct S q.1 q.2 = m then (1 : ℝ) else 0 := by
  have hcongr : ∀ t : ↥(S.filter Nat.Prime) → ℕ,
      (if localTamagawaTuple S q = Finsupp.equivFunOnFinite.symm t then (1 : ℝ) else 0)
        = if (fun p : ↥(S.filter Nat.Prime) => localTamagawaNumber (p : ℕ) q.1 q.2) = t then
            (1 : ℝ) else 0 := by
    intro t
    refine if_congr ?_ rfl rfl
    rw [localTamagawaTuple, EmbeddingLike.apply_eq_iff_eq]
  rw [Finset.sum_congr rfl fun t _ => hcongr t,
    Finset.sum_ite_eq (tamagawaTupleFactorizations S m)
      (fun p : ↥(S.filter Nat.Prime) => localTamagawaNumber (p : ℕ) q.1 q.2) (fun _ => (1 : ℝ))]
  refine if_congr ?_ rfl rfl
  rw [mem_tamagawaTupleFactorizations_iff S hm,
    prod_localTamagawaNumber_eq_truncatedTamagawaProduct]

/-! ### The two averages -/

/-- The `S`-truncated proportion
`P_Tam^S(m; X) := ∑_{𝐭 : ∏ 𝐭 = m} #{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X)`. For `m ≠ 0` it is
`#{E ∈ 𝓔(X) : Tam_S(E) = m} / N(X)`. -/
noncomputable def truncatedTamagawaTupleProportion (S : Finset ℕ) (m : ℕ) (X : ℝ) : ℝ :=
  ∑ t ∈ tamagawaTupleFactorizations S m,
    localTamagawaTupleProportion S (Finsupp.equivFunOnFinite.symm t) X

/-- The `S`-truncated proportion `P_Tam^S(m; X)` converges as `X → ∞`. -/
theorem tendsto_truncatedTamagawaTupleProportion (S : Finset ℕ) (m : ℕ) :
    Tendsto (truncatedTamagawaTupleProportion S m) atTop
      (𝓝 (∑ t ∈ tamagawaTupleFactorizations S m,
        limUnder atTop (localTamagawaTupleProportion S (Finsupp.equivFunOnFinite.symm t)))) :=
  tendsto_finsetSum _ fun _ _ => tendsto_localTamagawaTupleProportion S _

open scoped Classical in
/-- `P_Tam(m; X) = (1/N(X)) ∑_{E ∈ 𝓔(X)} 1[Tam(E) = m]`. -/
lemma tamagawaProportion_eq_average (m : ℕ) (X : ℝ) :
    tamagawaProportion m X = (integralShortNFCount X : ℝ)⁻¹ *
      ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily},
        (if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0) := by
  have hset : {x : ℤ × ℤ | ((integralShortNFHeight x.1 x.2 : ℝ) ≤ X ∧
        x ∈ integralShortNFFamily) ∧ tamagawaProduct x.1 x.2 = m}
      = {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
        tamagawaProduct p.1 p.2 = m} := Set.ext fun _ => and_assoc
  rw [tsum_ite_ncard_inter (fun q : ℤ × ℤ => (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily) (fun q : ℤ × ℤ => tamagawaProduct q.1 q.2 = m), hset,
    tamagawaProportion, div_eq_inv_mul]

open scoped Classical in
/-- For every multi-index `𝐭`,
`#{E ∈ 𝓔(X) : 𝐜_S(E) = 𝐭} / N(X) = (1/N(X)) ∑_{E ∈ 𝓔(X)} 1[𝐜_S(E) = 𝐭]`. -/
lemma localTamagawaTupleProportion_eq_average (S : Finset ℕ) (t : ↥(S.filter Nat.Prime) →₀ ℕ)
    (X : ℝ) :
    localTamagawaTupleProportion S t X = (integralShortNFCount X : ℝ)⁻¹ *
      ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily},
        (if localTamagawaTuple S E.1 = t then (1 : ℝ) else 0) := by
  rw [tsum_ite_ncard_inter (fun q : ℤ × ℤ => (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily) (fun q : ℤ × ℤ => localTamagawaTuple S q = t),
    localTamagawaTupleProportion, ncard_setOf_height_le_and_mem_family, div_eq_inv_mul]
  rfl

open scoped Classical in
/-- For `m ≠ 0` and `X ≥ 0`, `P_Tam^S(m; X) = (1/N(X)) ∑_{E ∈ 𝓔(X)} 1[Tam_S(E) = m]`. -/
lemma truncatedTamagawaTupleProportion_eq_average (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0) {X : ℝ}
    (hX : 0 ≤ X) :
    truncatedTamagawaTupleProportion S m X = (integralShortNFCount X : ℝ)⁻¹ *
      ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily},
        (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0) := by
  have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} := (finite_setOf_height_le_and_mem_family hX).to_subtype
  rw [truncatedTamagawaTupleProportion,
    Finset.sum_congr rfl fun t _ => localTamagawaTupleProportion_eq_average S _ X,
    ← Finset.mul_sum, ← Summable.tsum_finsetSum fun _ _ => Summable.of_finite]
  exact congrArg _ (tsum_congr fun E => sum_ite_localTamagawaTuple_eq S hm E.1)

/-! ### The tail: the two averages differ only at exceptional primes outside `S` -/

open scoped Classical in
/-- If `T` contains every prime `p ∉ S` with `τ_p(E) ∉ 𝒦₀`, then

`|1[Tam(E) = m] - 1[Tam_S(E) = m]| ≤ ∑_{p ∈ T ∖ S} 1[τ_p(E) ∉ 𝒦₀]`. -/
lemma abs_ite_sub_ite_le (S T : Finset ℕ) (m : ℕ) {a₄ a₆ : ℤ}
    (hT : ∀ p : ℕ, p ∉ S → localReductionDatum p a₄ a₆ ∉ K0 → p ∈ T) :
    |(if tamagawaProduct a₄ a₆ = m then (1 : ℝ) else 0)
        - (if truncatedTamagawaProduct S a₄ a₆ = m then (1 : ℝ) else 0)|
      ≤ ∑ p ∈ T \ S, (if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1) := by
  have hnn : ∀ p : ℕ, (0 : ℝ) ≤ if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1 :=
    fun p => by split <;> norm_num
  by_cases hall : ∀ p : ℕ, p ∉ S → localReductionDatum p a₄ a₆ ∈ K0
  · have heq : truncatedTamagawaProduct S a₄ a₆ = tamagawaProduct a₄ a₆ :=
      truncatedTamagawaProduct_eq fun p hlt => by
        by_contra hpS
        rw [localTamagawaNumber_eq_one_of_mem_K0 (hall p hpS)] at hlt
        exact absurd hlt (lt_irrefl 1)
    rw [heq, sub_self, abs_zero]
    exact Finset.sum_nonneg fun p _ => hnn p
  · obtain ⟨p₀, hp₀S, hp₀⟩ : ∃ p : ℕ, p ∉ S ∧ localReductionDatum p a₄ a₆ ∉ K0 := by
      by_contra h
      exact hall fun p hpS => not_not.1 fun hnk => h ⟨p, hpS, hnk⟩
    have h1 : (1 : ℝ) ≤ ∑ p ∈ T \ S,
        (if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1) := by
      have hmem : p₀ ∈ T \ S := Finset.mem_sdiff.2 ⟨hT p₀ hp₀S hp₀, hp₀S⟩
      have := Finset.single_le_sum (f := fun p : ℕ =>
        if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1) (fun p _ => hnn p) hmem
      rwa [ite_eq_right hp₀] at this
    have h2 : |(if tamagawaProduct a₄ a₆ = m then (1 : ℝ) else 0)
        - (if truncatedTamagawaProduct S a₄ a₆ = m then (1 : ℝ) else 0)| ≤ 1 := by
      rcases eq_or_ne (tamagawaProduct a₄ a₆) m with h | h <;>
        rcases eq_or_ne (truncatedTamagawaProduct S a₄ a₆) m with h' | h' <;>
        simp [h, h']
    linarith

open scoped Classical in
/-- For `S ⊇ {2, 3}`, `m ≠ 0`, `X ≥ 4` and a cutoff `Y ≥ 5`,

`|P_Tam(m; X) - P_Tam^S(m; X)| ≤ ∑_{p ≤ Y, p ∉ S} (1/N(X)) N^exc_p(X)
  + (1/N(X)) excPrimeSum Y X`. -/
lemma abs_sub_truncatedTamagawaTupleProportion_le (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) {X Y : ℝ} (hX : 4 ≤ X) (hY : 5 ≤ Y) :
    |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X| ≤
      ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
        ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
        + (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} := (finite_setOf_height_le_and_mem_family hX0).to_subtype
  have hNnn : (0 : ℝ) ≤ (integralShortNFCount X : ℝ)⁻¹ := by positivity
  have hdiff : tamagawaProportion m X - truncatedTamagawaTupleProportion S m X
      = (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ((if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0)
            - (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0)) := by
    rw [tamagawaProportion_eq_average, truncatedTamagawaTupleProportion_eq_average S hm hX0,
      ← mul_sub, Summable.tsum_sub Summable.of_finite Summable.of_finite]
  have hpt : ∀ E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      |(if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0)
          - (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0)|
        ≤ ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S,
          (if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1) := fun E =>
    abs_ite_sub_ite_le S _ m fun p hpS hnk =>
      mem_cover_of_notMem_K0 h2 h3 Y hX0 E.2.2 E.2.1 hpS hnk
  have hswap : ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      (∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S,
        (if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1))
      = ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S, (exceptionalCountNat p X : ℝ) := by
    rw [Summable.tsum_finsetSum fun p _ => Summable.of_finite]
    exact Finset.sum_congr rfl fun p _ => tsum_ite_notMem_K0_eq_exceptionalCountNat p X
  have habs : |∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      ((if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0)
        - (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0))|
      ≤ ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily},
        |(if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0)
          - (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (f := fun E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily} =>
        (if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0)
          - (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0))
      Summable.of_finite
  have hbox : |∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      ((if tamagawaProduct E.1.1 E.1.2 = m then (1 : ℝ) else 0)
        - (if truncatedTamagawaProduct S E.1.1 E.1.2 = m then (1 : ℝ) else 0))|
      ≤ ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S, (exceptionalCountNat p X : ℝ) :=
    habs.trans ((Summable.tsum_le_tsum hpt Summable.of_finite Summable.of_finite).trans_eq hswap)
  have hsplit : ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S, (exceptionalCountNat p X : ℝ)
      ≤ ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, (exceptionalCountNat p X : ℝ) + excPrimeSum Y X := by
    rw [Finset.union_sdiff_distrib, excPrimeSum_eq_finset_sum Y X hY (by linarith)]
    have hinter : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) \ S) ∩ (excSupport Y X \ S),
        (exceptionalCountNat p X : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    have hle : ∑ p ∈ excSupport Y X \ S, (exceptionalCountNat p X : ℝ)
        ≤ ∑ p ∈ excSupport Y X, (exceptionalCountNat p X : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p _ _ => by positivity
    have := Finset.sum_union_inter (s₁ := Finset.range (⌊Y⌋₊ + 1) \ S)
      (s₂ := excSupport Y X \ S) (f := fun p : ℕ => (exceptionalCountNat p X : ℝ))
    linarith
  rw [hdiff, abs_mul, abs_of_nonneg hNnn]
  calc (integralShortNFCount X : ℝ)⁻¹ * |_|
      ≤ (integralShortNFCount X : ℝ)⁻¹ *
          (∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, (exceptionalCountNat p X : ℝ) + excPrimeSum Y X) :=
        mul_le_mul_of_nonneg_left (hbox.trans hsplit) hNnn
    _ = ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
          ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
          + (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X := by
        rw [← Finset.mul_sum, one_div]
        ring

/-- The function `X ↦ |P_Tam(m; X) - P_Tam^S(m; X)|` is bounded above along `atTop`. -/
lemma isBoundedUnder_le_abs_sub_truncatedTamagawaTupleProportion (S : Finset ℕ) (m : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun X : ℝ => |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X|) := by
  refine isBoundedUnder_of ⟨1 + ((tamagawaTupleFactorizations S m).card : ℝ), fun X => ?_⟩
  have h1 : |tamagawaProportion m X| ≤ 1 :=
    abs_le.2 ⟨by linarith [tamagawaProportion_nonneg m X], tamagawaProportion_le_one m X⟩
  have hfib : ∀ t : ↥(S.filter Nat.Prime) →₀ ℕ, |localTamagawaTupleProportion S t X| ≤ 1 := by
    intro t
    rw [localTamagawaTupleProportion, abs_of_nonneg (by positivity)]
    by_cases hfin : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily}.Finite
    · rcases eq_or_ne ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard) 0 with h0 | h0
      · rw [h0]
        simp
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h0)]
        have hsub : {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
              q ∈ integralShortNFFamily} ∧ localTamagawaTuple S q = t} ⊆
            {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
              q ∈ integralShortNFFamily} := fun q hq => hq.1
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    · rw [Set.Infinite.ncard hfin]
      simp
  have h2 : |truncatedTamagawaTupleProportion S m X|
      ≤ ((tamagawaTupleFactorizations S m).card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ t ∈ tamagawaTupleFactorizations S m,
          |localTamagawaTupleProportion S (Finsupp.equivFunOnFinite.symm t) X|
        ≤ ∑ _t ∈ tamagawaTupleFactorizations S m, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => hfib _
      _ = ((tamagawaTupleFactorizations S m).card : ℝ) := by simp
  have h3 : |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X|
      ≤ |tamagawaProportion m X| + |truncatedTamagawaTupleProportion S m X| := by
    simpa only [Real.norm_eq_abs] using
      norm_sub_le (tamagawaProportion m X) (truncatedTamagawaTupleProportion S m X)
  linarith

open scoped Classical in
/-- For `S ⊇ {2, 3}` and `m ≠ 0`,

`limsup_{X → ∞} |P_Tam(m; X) - P_Tam^S(m; X)| ≤ ∑_{p ∉ S} (1 - β_p)`. -/
lemma limsup_abs_sub_truncatedTamagawaTupleProportion_le (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) :
    limsup (fun X : ℝ => |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X|)
        atTop
      ≤ ∑' p : ℕ, if p ∈ S then 0 else betaDefect p := by
  set f : ℝ → ℝ := fun X =>
    |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X| with hf
  have hcob : IsCoboundedUnder (· ≤ ·) atTop f :=
    Filter.isCoboundedUnder_le_of_le atTop (x := 0) fun X => abs_nonneg _
  obtain ⟨C₁, hC₁, hbound⟩ := exceptional_ratio_bound
  have key : ∀ Y : ℝ, 5 ≤ Y → limsup f atTop
      ≤ (∑' p : ℕ, if p ∈ S then 0 else betaDefect p) + C₁ * primeTail Y := by
    intro Y hY
    set g : ℝ → ℝ := fun X =>
      ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
        ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
        + C₁ * (primeTail Y + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
          + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)) with hg
    have hgt : Tendsto g atTop
        (𝓝 (∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p + C₁ * primeTail Y)) := by
      have hone : Tendsto (fun X : ℝ => ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
          ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))) atTop
          (𝓝 (∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p)) :=
        tendsto_finsetSum _ fun p _ => tendsto_ratio_exceptionalCountNat p
      have htwo : Tendsto (fun X : ℝ => primeTail Y
          + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
          + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)) atTop (𝓝 (primeTail Y)) := by
        have h := ((tendsto_const_nhds (x := primeTail Y) (f := (atTop : Filter ℝ))).add
          (errB_tendsto Y)).add (errE_tendsto Y)
        rwa [add_zero, add_zero] at h
      exact hone.add (htwo.const_mul C₁)
    have hfg : ∀ᶠ X in atTop, f X ≤ g X := by
      filter_upwards [eventually_ge_atTop (4 : ℝ),
        excPrimeSum_div_count_eventually_le C₁ hbound Y hY] with X hX4 hXb
      have hper := abs_sub_truncatedTamagawaTupleProportion_le S hm h2 h3 hX4 hY
      have htail : (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X
          ≤ C₁ * (primeTail Y + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
            + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)) := by
        refine hXb.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
        have := excSupport_sum_inv_sq_le Y X
        linarith
      simp only [hf, hg]
      linarith
    calc limsup f atTop ≤ limsup g atTop := limsup_le_limsup hfg hcob hgt.isBoundedUnder_le
      _ = ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p + C₁ * primeTail Y := hgt.limsup_eq
      _ ≤ (∑' p : ℕ, if p ∈ S then 0 else betaDefect p) + C₁ * primeTail Y := by
          have hsum : ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p
              ≤ ∑' p : ℕ, if p ∈ S then 0 else betaDefect p := by
            have heq : ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p
                = ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
                    (if p ∈ S then (0 : ℝ) else betaDefect p) :=
              Finset.sum_congr rfl fun p hp => by rw [ite_eq_right (Finset.mem_sdiff.1 hp).2]
            rw [heq]
            exact Summable.sum_le_tsum _
              (fun i _ => by split; exacts [le_rfl, betaDefect_nonneg i])
              (summable_betaDefect_compl S)
          linarith
  have hlim : Tendsto (fun Y : ℝ => (∑' p : ℕ, if p ∈ S then 0 else betaDefect p)
      + C₁ * primeTail Y) atTop (𝓝 (∑' p : ℕ, if p ∈ S then 0 else betaDefect p)) := by
    simpa using (tendsto_const_nhds
      (x := ∑' p : ℕ, if p ∈ S then 0 else betaDefect p)
      (f := (atTop : Filter ℝ))).add (prime_tail_tendsto_zero.const_mul C₁)
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (5 : ℝ)] with Y hY using key Y hY

/-! ### Convergence of the truncated proportions -/

open scoped Classical in
/-- For `m ≠ 0` and every `ε > 0` there is a real `c` with `|P_Tam(m; X) - c| ≤ ε` for all large
`X`. -/
lemma exists_eventually_abs_sub_tamagawaProportion_le {m : ℕ} (hm : m ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ᶠ X in atTop, |tamagawaProportion m X - c| ≤ ε := by
  obtain ⟨S, h23, hS⟩ : ∃ S : Finset ℕ, ({2, 3} : Finset ℕ) ≤ S ∧
      (∑' p : ℕ, if p ∈ S then 0 else betaDefect p) < ε / 2 := by
    have h := (tendsto_tsum_betaDefect_compl.eventually
      (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))).and
      (eventually_ge_atTop ({2, 3} : Finset ℕ))
    obtain ⟨S, hS1, hS2⟩ := h.exists
    exact ⟨S, hS2, hS1⟩
  have h2 : 2 ∈ S := h23 (by decide)
  have h3 : 3 ∈ S := h23 (by decide)
  set c : ℝ := ∑ t ∈ tamagawaTupleFactorizations S m,
    limUnder atTop (localTamagawaTupleProportion S (Finsupp.equivFunOnFinite.symm t)) with hc
  refine ⟨c, ?_⟩
  have hlt : limsup (fun X : ℝ =>
      |tamagawaProportion m X - truncatedTamagawaTupleProportion S m X|) atTop < ε / 2 :=
    lt_of_le_of_lt (limsup_abs_sub_truncatedTamagawaTupleProportion_le S hm h2 h3) hS
  have hev := eventually_lt_of_limsup_lt hlt
    (isBoundedUnder_le_abs_sub_truncatedTamagawaTupleProportion S m)
  have hcv : ∀ᶠ X in atTop, |truncatedTamagawaTupleProportion S m X - c| < ε / 2 := by
    have h := (tendsto_truncatedTamagawaTupleProportion S m).eventually
      (Metric.ball_mem_nhds c (show (0 : ℝ) < ε / 2 by linarith))
    filter_upwards [h] with X hX
    rw [← Real.dist_eq]
    exact Metric.mem_ball.1 hX
  filter_upwards [hev, hcv] with X hX1 hX2
  have htri := abs_sub_le (tamagawaProportion m X)
    (truncatedTamagawaTupleProportion S m X) c
  linarith

/-- `P_Tam(0; X) = 0` for every `X`, the Tamagawa product being positive. -/
lemma tamagawaProportion_zero (X : ℝ) : tamagawaProportion 0 X = 0 := by
  rw [tamagawaProportion, show {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧
      p ∈ integralShortNFFamily ∧ tamagawaProduct p.1 p.2 = 0} = ∅ from
    Set.eq_empty_iff_forall_notMem.2 fun q hq => tamagawaProduct_ne_zero q.1 q.2 hq.2.2]
  simp

/-- For every `m`, the truncated proportion `P_Tam(m; X)` converges as `X → ∞`. -/
theorem exists_tendsto_tamagawaProportion (m : ℕ) :
    ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L) := by
  rcases eq_or_ne m 0 with rfl | hm
  · refine ⟨0, ?_⟩
    rw [show tamagawaProportion 0 = fun _ : ℝ => (0 : ℝ) from funext tamagawaProportion_zero]
    exact tendsto_const_nhds
  · exact exists_tendsto_of_forall_eventually_abs_sub_le fun ε hε =>
      exists_eventually_abs_sub_tamagawaProportion_le hm hε

/-- For every `m`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Δ(E) ≠ 0, Tam(E) = m} / N(X) = P_Tam(m)`,

with `P_Tam(m)` the limiting density `tamagawaDensity m`. -/
@[bsd_tamagawa "T018b"]
theorem tendsto_tamagawaProportion_tamagawaDensity (m : ℕ) :
    Tendsto (tamagawaProportion m) atTop (𝓝 (tamagawaDensity m)) :=
  tendsto_tamagawaProportion (exists_tendsto_tamagawaProportion m)

end WeierstrassCurve
