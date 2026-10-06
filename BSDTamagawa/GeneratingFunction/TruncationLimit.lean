/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.AbsoluteConvergence
public import BSDTamagawa.GeneratingFunction.LargePrimeTail

/-!
# The truncated identity extends to the full product

For a finite set `Λ ⊆ 𝒦 ∖ 𝒦₀` of reduction data, a finite set `Π` of primes and parameters on the
closed polydisc `𝒟` (that is, `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for `ℓ ∈ Π` and
`‖u_K‖ ≤ 1` for `K ∈ Λ`), the generating function `𝒵_{Λ, Π, X}` converges as `X → ∞` to the master
Euler product:

`lim_{X → ∞} 𝒵_{Λ, Π, X}(s; u, w, 𝐳, 𝐮) = ∏_{p ∈ 𝒫} L_p(s; u, w, 𝐳, 𝐮)`.

Writing `W(E)` for the weight of `E` and `W_S(E)` for its truncation at a finite set of primes `S`,
the proof is an `ε/3` argument with the triangle inequality

```
|𝒵_{Λ,Π,X} - ∏_{p ∈ 𝒫} L_p|
  ≤ N(X)⁻¹ ∑_{Ht(E) ≤ X} |W(E) - W_S(E)|
  + |N(X)⁻¹ ∑_{Ht(E) ≤ X} W_S(E) - ∏_{p ∈ S} L_p|
  + |∏_{p ∈ S} L_p - ∏_{p ∈ 𝒫} L_p|.
```

The first term has `limsup` at most `2 ∑_{p ∉ S} (1 - β_p)`, the second tends to `0` as `X → ∞` by
the truncated identity, and the first bound and the third term tend to `0` as `S` exhausts the
primes; one `S` is fixed first, and then `X → ∞`.

## Main results

* `WeierstrassCurve.tamagawaGeneratingFunction_eq_inv_mul_tsum`: `𝒵_{Λ, Π, X}` as `N(X)⁻¹` times a
  sum over the height box.
* `WeierstrassCurve.average_norm_sub_truncatedWeight_le_two`:
  `N(X)⁻¹ ∑_{Ht(E) ≤ X} ‖W(E) - W_S(E)‖ ≤ 2`.
* `WeierstrassCurve.norm_tamagawaGeneratingFunction_sub_average_truncatedWeight_le`:
  `‖𝒵_{Λ, Π, X} - N(X)⁻¹ ∑_{Ht(E) ≤ X} W_S(E)‖ ≤ N(X)⁻¹ ∑_{Ht(E) ≤ X} ‖W(E) - W_S(E)‖`.
* `WeierstrassCurve.tprod_masterLocalFactor_primes`: `∏'_{p ∈ 𝒫} L_p = ∏'_{p : ℕ} L_p`.
* `WeierstrassCurve.tendsto_tamagawaGeneratingFunction`: the limit formula above.

## Implementation notes

A bound `Filter.limsup u atTop ≤ c` gives no eventual bound on `u`, since `Filter.limsup` takes a
junk value when `u` is not bounded above; the boundedness needed to pass from the `limsup` bound to
an eventual bound is therefore proved separately, from the pointwise bound `‖W - W_S‖ ≤ 2`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-! ### The generating function as an average over the height box -/

open scoped Classical in
/-- The generating function as an average over the height box:
`𝒵_{Λ, Π, X} = N(X)⁻¹ ∑_{Ht(E) ≤ X, E ∈ 𝓕} W(E)`, the sum running over the subtype of integral
pairs of height at most `X` in the family. -/
lemma tamagawaGeneratingFunction_eq_inv_mul_tsum (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ)
    (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) (X : ℝ) :
    tamagawaGeneratingFunction Λ P s u w z uΛ X =
      (integralShortNFCount X : ℂ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          u ^ tamagawaOmega E.1.1 E.1.2 *
            w ^ ArithmeticFunction.cardFactors (tamagawaProduct E.1.1 E.1.2) *
            multiMonomial (tamagawaValuationVector P E.1.1 E.1.2) z *
            (tamagawaProduct E.1.1 E.1.2 : ℂ) ^ (-s) * kodairaMonomial Λ uΛ E.1.1 E.1.2 := by
  have h := tsum_subtype {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
    fun q : ℤ × ℤ => u ^ tamagawaOmega q.1 q.2 *
      w ^ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) *
      multiMonomial (tamagawaValuationVector P q.1 q.2) z *
      (tamagawaProduct q.1 q.2 : ℂ) ^ (-s) * kodairaMonomial Λ uΛ q.1 q.2
  rw [tamagawaGeneratingFunction, div_eq_inv_mul]
  congr 1
  refine Eq.trans (tsum_congr fun q => ?_) h.symm
  by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
  · rw [ite_eq_left (show _ ∧ _ from hq), Set.indicator_of_mem hq]
  · rw [ite_eq_right (show ¬(_ ∧ _) from hq), Set.indicator_of_notMem hq]

/-! ### The averaged error is bounded by `2` -/

/-- On the polydisc `𝒟`, `‖W(E) - W_S(E)‖ ≤ 2` for every finite set of primes `S` and every model
`E = E(a₄, a₆)`, where `W` is the weight of the generating function and `W_S` its truncation. -/
lemma norm_sub_truncatedWeight_le_two (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ)
    {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hs : 0 ≤ s.re)
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1)
    (a₄ a₆ : ℤ) :
    ‖(u ^ tamagawaOmega a₄ a₆ * w ^ ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆) *
          multiMonomial (tamagawaValuationVector P a₄ a₆) z *
          (tamagawaProduct a₄ a₆ : ℂ) ^ (-s) * kodairaMonomial Λ uΛ a₄ a₆)
        - (u ^ truncatedTamagawaOmega S a₄ a₆ * w ^ truncatedTamagawaCardFactors S a₄ a₆ *
          multiMonomial (truncatedTamagawaValuationVector P S a₄ a₆) z *
          (truncatedTamagawaProduct S a₄ a₆ : ℂ) ^ (-s) *
          multiMonomial (fun K : Λ =>
            truncatedReductionOmega (K : KodairaSymbol × ℕ) S a₄ a₆) uΛ)‖ ≤ 2 := by
  have h₂ := norm_weight_le_one Λ P hs hu hw hz huΛ a₄ a₆
  have h₃ := norm_truncatedWeight_le_one Λ P S hΛ hs hu hw hz huΛ a₄ a₆
  exact (norm_sub_le _ _).trans (by linarith)

/-- For a finite index type of cardinality `n`, `n⁻¹ ∑' i, f i ≤ c` whenever `0 ≤ c` and `f ≤ c`
pointwise. -/
private lemma inv_mul_tsum_le_of_forall_le {ι : Type*} [Finite ι] {f : ι → ℝ} {c : ℝ} {n : ℕ}
    (hc : 0 ≤ c) (hn : Nat.card ι = n) (h : ∀ i, f i ≤ c) :
    (n : ℝ)⁻¹ * ∑' i, f i ≤ c := by
  have hsum : ∑' i, f i ≤ (n : ℝ) * c := by
    refine (Summable.tsum_le_tsum h Summable.of_finite Summable.of_finite).trans_eq ?_
    rw [tsum_const, hn, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simpa using hc
  · have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h0
    refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
    field_simp

/-- On the polydisc `𝒟`, for every `X ≥ 0`, `N(X)⁻¹ ∑_{Ht(E) ≤ X} ‖W(E) - W_S(E)‖ ≤ 2`. -/
lemma average_norm_sub_truncatedWeight_le_two (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ)
    {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hs : 0 ≤ s.re)
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1)
    {X : ℝ} (hX : 0 ≤ X) :
    (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ‖(u ^ tamagawaOmega E.1.1 E.1.2 *
              w ^ ArithmeticFunction.cardFactors (tamagawaProduct E.1.1 E.1.2) *
              multiMonomial (tamagawaValuationVector P E.1.1 E.1.2) z *
              (tamagawaProduct E.1.1 E.1.2 : ℂ) ^ (-s) * kodairaMonomial Λ uΛ E.1.1 E.1.2)
            - (u ^ truncatedTamagawaOmega S E.1.1 E.1.2 *
              w ^ truncatedTamagawaCardFactors S E.1.1 E.1.2 *
              multiMonomial (truncatedTamagawaValuationVector P S E.1.1 E.1.2) z *
              (truncatedTamagawaProduct S E.1.1 E.1.2 : ℂ) ^ (-s) *
              multiMonomial (fun K : Λ =>
                truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)‖ ≤ 2 := by
  have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} := (finite_setOf_height_le_and_mem_family hX).to_subtype
  have hcard : Nat.card {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} = integralShortNFCount X := by
    rw [integralShortNFCount, ← Nat.card_coe_set_eq]
    rfl
  exact inv_mul_tsum_le_of_forall_le zero_le_two hcard
    fun E => norm_sub_truncatedWeight_le_two Λ P S hΛ hs hu hw hz huΛ E.1.1 E.1.2

/-- On the polydisc `𝒟`, the averaged error `X ↦ N(X)⁻¹ ∑_{Ht(E) ≤ X} ‖W(E) - W_S(E)‖` is bounded
above along `atTop`. -/
lemma isBoundedUnder_average_norm_sub_truncatedWeight (Λ : Finset (KodairaSymbol × ℕ))
    (P S : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0)
    (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1)
    (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) :
    IsBoundedUnder (· ≤ ·) (atTop : Filter ℝ) fun X : ℝ =>
      (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ‖(u ^ tamagawaOmega E.1.1 E.1.2 *
              w ^ ArithmeticFunction.cardFactors (tamagawaProduct E.1.1 E.1.2) *
              multiMonomial (tamagawaValuationVector P E.1.1 E.1.2) z *
              (tamagawaProduct E.1.1 E.1.2 : ℂ) ^ (-s) * kodairaMonomial Λ uΛ E.1.1 E.1.2)
            - (u ^ truncatedTamagawaOmega S E.1.1 E.1.2 *
              w ^ truncatedTamagawaCardFactors S E.1.1 E.1.2 *
              multiMonomial (truncatedTamagawaValuationVector P S E.1.1 E.1.2) z *
              (truncatedTamagawaProduct S E.1.1 E.1.2 : ℂ) ^ (-s) *
              multiMonomial (fun K : Λ =>
                truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)‖ :=
  (isBoundedUnder_const (a := (2 : ℝ))).mono_le <| by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    exact average_norm_sub_truncatedWeight_le_two Λ P S hΛ hs hu hw hz huΛ hX

/-! ### Comparison with the truncated average at a fixed `X` -/

/-- For every `X ≥ 0`,
`‖𝒵_{Λ, Π, X} - N(X)⁻¹ ∑_{Ht(E) ≤ X} W_S(E)‖ ≤ N(X)⁻¹ ∑_{Ht(E) ≤ X} ‖W(E) - W_S(E)‖`. -/
lemma norm_tamagawaGeneratingFunction_sub_average_truncatedWeight_le
    (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ) (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ)
    {X : ℝ} (hX : 0 ≤ X) :
    ‖tamagawaGeneratingFunction Λ P s u w z uΛ X -
        (integralShortNFCount X : ℂ)⁻¹ *
          ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
              E ∈ integralShortNFFamily},
            u ^ truncatedTamagawaOmega S E.1.1 E.1.2 *
              w ^ truncatedTamagawaCardFactors S E.1.1 E.1.2 *
              multiMonomial (truncatedTamagawaValuationVector P S E.1.1 E.1.2) z *
              (truncatedTamagawaProduct S E.1.1 E.1.2 : ℂ) ^ (-s) *
              multiMonomial (fun K : Λ =>
                truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ‖
      ≤ (integralShortNFCount X : ℝ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ‖(u ^ tamagawaOmega E.1.1 E.1.2 *
              w ^ ArithmeticFunction.cardFactors (tamagawaProduct E.1.1 E.1.2) *
              multiMonomial (tamagawaValuationVector P E.1.1 E.1.2) z *
              (tamagawaProduct E.1.1 E.1.2 : ℂ) ^ (-s) * kodairaMonomial Λ uΛ E.1.1 E.1.2)
            - (u ^ truncatedTamagawaOmega S E.1.1 E.1.2 *
              w ^ truncatedTamagawaCardFactors S E.1.1 E.1.2 *
              multiMonomial (truncatedTamagawaValuationVector P S E.1.1 E.1.2) z *
              (truncatedTamagawaProduct S E.1.1 E.1.2 : ℂ) ^ (-s) *
              multiMonomial (fun K : Λ =>
                truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)‖ := by
  have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} := (finite_setOf_height_le_and_mem_family hX).to_subtype
  rw [tamagawaGeneratingFunction_eq_inv_mul_tsum, ← mul_sub,
    ← Summable.tsum_sub Summable.of_finite Summable.of_finite, norm_mul, norm_inv,
    Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm Summable.of_finite) (by positivity)

/-! ### The truncated limit is the partial Euler product `∏_{p ∈ S} L_p` -/

/-- `∏_{q ∈ S, q prime} (β_q + ∑_{K ∉ 𝒦₀} δ_q(K) Φ(K; s, u, w, 𝐳, 𝐮)) = ∏_{p ∈ S} L_p`, where `L_p`
is `masterLocalFactor` (equal to `1` at a non-prime index). -/
lemma prod_localFactor_filter_eq_prod_masterLocalFactor (Λ : Finset (KodairaSymbol × ℕ))
    (P S : Finset ℕ) (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) :
    (∏ q : ↥(S.filter Nat.Prime), (((β (q : ℕ)).toReal : ℂ) +
        ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
          ((deltaP (q : ℕ) (K : KodairaSymbol × ℕ)).toReal : ℂ) *
            localWeight Λ P (K : KodairaSymbol × ℕ) s u w z uΛ))
      = ∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ := by
  classical
  calc (∏ q : ↥(S.filter Nat.Prime), (((β (q : ℕ)).toReal : ℂ) +
          ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
            ((deltaP (q : ℕ) (K : KodairaSymbol × ℕ)).toReal : ℂ) *
              localWeight Λ P (K : KodairaSymbol × ℕ) s u w z uΛ))
      = ∏ q : ↥(S.filter Nat.Prime), masterLocalFactor Λ P (q : ℕ) s u w z uΛ :=
        Finset.prod_congr rfl fun q _ =>
          (masterLocalFactor_of_prime Λ P (q : ℕ) s u w z uΛ).symm
    _ = ∏ p ∈ S.filter Nat.Prime, masterLocalFactor Λ P p s u w z uΛ :=
        Finset.prod_coe_sort (S.filter Nat.Prime) fun p => masterLocalFactor Λ P p s u w z uΛ
    _ = ∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ :=
        Finset.prod_filter_of_ne fun p _ hne => by
          by_contra hp
          exact hne (masterLocalFactor_of_not_prime hp s u w z uΛ)

/-! ### The `ℕ`-indexed product is the product over the primes -/

/-- `∏'_{p ∈ 𝒫} L_p = ∏'_{p : ℕ} L_p` on the polydisc `𝒟`. -/
lemma tprod_masterLocalFactor_primes (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    ∏' p : {q : ℕ // q.Prime}, masterLocalFactor Λ P (p : ℕ) s u w z uΛ
      = ∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      masterLocalFactor Λ P x s u w z uΛ = 1 := fun x hx =>
    masterLocalFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) s u w z uΛ
  exact ((Subtype.coe_injective.hasProd_iff hone).2
    (multipliable_masterLocalFactor Λ P hs hu hw hz huΛ).hasProd).tprod_eq

/-! ### The limit of the generating function -/

/-- From `‖a - b‖ ≤ x`, `x < ε`, `‖b - c‖ < ε` and `‖c - d‖ < ε` follows `‖a - d‖ < 3ε`. -/
private lemma norm_sub_lt_of_triangle {a b c d : ℂ} {x ε : ℝ} (h₁ : ‖a - b‖ ≤ x) (h₂ : x < ε)
    (h₃ : ‖b - c‖ < ε) (h₄ : ‖c - d‖ < ε) : ‖a - d‖ < 3 * ε := by
  have ht : ‖a - d‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖ := by
    simpa only [dist_eq_norm] using dist_triangle4 a b c d
  linarith

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of reduction data and `Π` a finite set of primes, and let the
parameters lie on the closed polydisc `𝒟`: `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for
`ℓ ∈ Π` and `‖u_K‖ ≤ 1` for `K ∈ Λ`. Then

`lim_{X → ∞} 𝒵_{Λ, Π, X}(s; u, w, 𝐳, 𝐮) = ∏_{p ∈ 𝒫} L_p(s; u, w, 𝐳, 𝐮)`,

with `L_p` the master local factor. (The product is indexed by `ℕ`, and `L_p = 1` off the
primes.) -/
@[bsd_tamagawa "T036c"]
theorem tendsto_tamagawaGeneratingFunction (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ)
    {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hP : ∀ ℓ ∈ P, Nat.Prime ℓ)
    (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1)
    (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Tendsto (tamagawaGeneratingFunction Λ P s u w z uΛ) atTop
      (𝓝 (∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ)) := by
  have key : Tendsto (fun X : ℝ => tamagawaGeneratingFunction Λ P s u w z uΛ X
      - ∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ) atTop (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    have hε3 : (0 : ℝ) < ε / 3 := by positivity
    have hbetaN := tendsto_tsum_betaDefect_compl.const_mul (2 : ℝ)
    rw [mul_zero] at hbetaN
    have hprodT : Tendsto (fun T : Finset ℕ => ∏ p ∈ T, masterLocalFactor Λ P p s u w z uΛ)
        atTop (𝓝 (∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ)) :=
      (multipliable_masterLocalFactor Λ P hs hu hw hz huΛ).hasProd
    have hprodN := (hprodT.sub_const (∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ)).norm
    rw [sub_self, norm_zero] at hprodN
    obtain ⟨S, ⟨⟨h23, hbeta⟩, hprod⟩⟩ :=
      (((eventually_ge_atTop ({2, 3} : Finset ℕ)).and
        (hbetaN.eventually_lt_const hε3)).and (hprodN.eventually_lt_const hε3)).exists
    have hsub : ({2, 3} : Finset ℕ) ⊆ S := h23
    have h2 : 2 ∈ S := hsub (by simp)
    have h3 : 3 ∈ S := hsub (by simp)
    have hA := eventually_lt_of_limsup_lt
      ((limsup_average_norm_sub_truncatedWeight_le Λ P S hΛ hP h2 h3 hs hu hw hz huΛ).trans_lt
        hbeta)
      (isBoundedUnder_average_norm_sub_truncatedWeight Λ P S hΛ hs hu hw hz huΛ)
    have hB := tendsto_average_truncatedWeight Λ P S hΛ hs hu hw hz huΛ
    rw [prod_localFactor_filter_eq_prod_masterLocalFactor Λ P S s u w z uΛ] at hB
    have hBN := (hB.sub_const (∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ)).norm
    rw [sub_self, norm_zero] at hBN
    filter_upwards [eventually_ge_atTop (0 : ℝ), hA, hBN.eventually_lt_const hε3] with
      X hX hAX hBX
    have h := norm_sub_lt_of_triangle
      (norm_tamagawaGeneratingFunction_sub_average_truncatedWeight_le Λ P S s u w z uΛ hX)
      hAX hBX hprod
    linarith
  simpa using key.add_const (∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ)

end WeierstrassCurve
