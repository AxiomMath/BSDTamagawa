/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.K0Mass
public import BSDTamagawa.Equidistribution.ExceptionalTailLimsup
public import BSDTamagawa.GeneratingFunction.TruncatedIdentity

/-!
# Tail contribution from large primes

Let `S ⊇ {2, 3}` be a finite set of primes. On the parameter polydisc `𝒟` — `Re(s) ≥ 0`,
`‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for `ℓ ∈ Π` and `‖u_K‖ ≤ 1` for `K ∈ Λ` — the `S`-truncated
weight `W_S(E)` approximates the full weight `W(E)` of the generating function on average:

`limsup_{X → ∞} (1 / N(X)) ∑_{Ht(E) ≤ X} |W(E) - W_S(E)| ≤ 2 ∑_{p ∉ S} (1 - β_p)`,

and the majorant `∑_{p ∉ S} (1 - β_p)` tends to `0` as `S` exhausts the primes. The two weights
agree unless some prime `p ∉ S` has `τ_p(E) ∉ 𝒦₀`; the primes `p ≤ Y` are handled by the
equidistribution of `τ_p(E)` and the primes `p > Y` by the bound on the exceptional prime sum.

## Main definitions

* `WeierstrassCurve.betaDefect`: `1 - β_p` at a prime `p`, and `0` off the primes.

## Main results

* `WeierstrassCurve.tendsto_tsum_betaDefect_compl`: `∑_{p ∉ S} (1 - β_p) → 0` along the finite
  sets `S` directed by inclusion.
* `WeierstrassCurve.tendsto_ratio_exceptionalCountNat`:
  `(1/N(X)) · #{E : Ht(E) ≤ X, τ_p(E) ∉ 𝒦₀} → 1 - β_p`.
* `WeierstrassCurve.truncatedWeight_eq`: if every prime `p ∉ S` has `τ_p(E) ∈ 𝒦₀`, then
  `W_S(E) = W(E)`.
* `WeierstrassCurve.limsup_average_norm_sub_truncatedWeight_le`: the `limsup` bound above.

## Implementation notes

The weights `W(E)` and `W_S(E)` are not given definitions: they are written out as the summands
of `tamagawaGeneratingFunction` and of the truncated average. The outer sum runs over the
subtype of nonsingular pairs of height at most `X`, and `1/N(X)` is the real `(N(X))⁻¹`, which is
`0` when `N(X) = 0`.
-/

@[expose] public section

open Filter Topology BSDTamagawa.MultiIndex BSDTamagawa.PrimeSqTail
open ShortWeierstrassReductionStatistics

open scoped ENNReal

namespace WeierstrassCurve

/-! ### The series `∑_p (1 - β_p)` -/

/-- The mass `1 - β_p` outside the trivial stratum `𝒦₀` at a prime `p`, as a real number, and `0`
at a non-prime index. -/
noncomputable def betaDefect (p : ℕ) : ℝ :=
  if h : p.Prime then (1 - @β p ⟨h⟩).toReal else 0

/-- At a prime index, `betaDefect p = (1 - β_p).toReal`. -/
lemma betaDefect_of_prime (p : ℕ) [Fact p.Prime] : betaDefect p = (1 - β p).toReal :=
  dite_eq_left (Fact.out : p.Prime)

/-- At a non-prime index, `betaDefect p = 0`. -/
lemma betaDefect_of_not_prime {p : ℕ} (hp : ¬ p.Prime) : betaDefect p = 0 := dite_eq_right hp

/-- `betaDefect p` is nonnegative. -/
lemma betaDefect_nonneg (p : ℕ) : 0 ≤ betaDefect p := by
  rw [betaDefect]; split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- `betaDefect p ≤ 9 · primeSq p`, i.e. `1 - β_p ≤ 9/p²` at every prime. -/
lemma betaDefect_le_nine_mul_primeSq (p : ℕ) : betaDefect p ≤ 9 * primeSq p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hp.pos.ne'
    have htop : (9 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 ≠ ⊤ := by
      simp [ENNReal.div_eq_top, hp0]
    have h := ENNReal.toReal_mono htop (one_sub_β_le_nine_div_sq p)
    rw [betaDefect_of_prime]
    refine h.trans ?_
    rw [primeSq, ite_eq_left hp, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    norm_num [div_eq_mul_inv]
  · rw [betaDefect_of_not_prime hp]
    have := primeSq_nonneg p
    linarith

/-- The series `∑_p (1 - β_p)` converges. -/
lemma summable_betaDefect : Summable betaDefect :=
  Summable.of_nonneg_of_le betaDefect_nonneg betaDefect_le_nine_mul_primeSq
    (summable_primeSq.mul_left 9)

/-- The series `p ↦ 1[p ∉ S] (1 - β_p)` is summable. -/
lemma summable_betaDefect_compl (S : Finset ℕ) :
    Summable (fun p : ℕ => if p ∈ S then 0 else betaDefect p) :=
  summable_betaDefect.of_nonneg_of_le
    (fun p => by split; exacts [le_rfl, betaDefect_nonneg p])
    (fun p => by split; exacts [betaDefect_nonneg p, le_rfl])

/-- `∑_{p ∉ S} (1 - β_p) → 0` as `S` exhausts the primes, i.e. along the filter `atTop` on the
finite sets of natural numbers directed by inclusion. -/
@[bsd_tamagawa "T036b"]
theorem tendsto_tsum_betaDefect_compl :
    Tendsto (fun S : Finset ℕ => ∑' p : ℕ, if p ∈ S then 0 else betaDefect p)
      atTop (𝓝 0) := by
  refine (tendsto_tsum_compl_atTop_zero betaDefect).congr fun S => ?_
  rw [show (∑' p : {x : ℕ // x ∉ S}, betaDefect p)
      = ∑' p : ↑({x : ℕ | x ∉ S}), betaDefect p from rfl, tsum_subtype]
  refine tsum_congr fun p => ?_
  rw [Set.indicator_apply]
  by_cases hp : p ∈ S <;> simp [hp]

/-! ### The exceptional proportion at a single prime -/

open scoped Classical in
/-- For a set `A` in any type, `∑' i, 1[i ∈ A] = #A`; for an infinite `A` both sides are `0`. -/
lemma tsum_ite_ncard {ι : Type*} (A : Set ι) :
    ∑' i : ι, (if i ∈ A then (1 : ℝ) else 0) = (A.ncard : ℝ) := by
  have h : (fun i : ι => if i ∈ A then (1 : ℝ) else 0) = A.indicator (fun _ => (1 : ℝ)) := by
    funext i
    rw [Set.indicator_apply]
  rw [h, ← tsum_subtype, tsum_const, Nat.card_coe_set_eq, nsmul_eq_mul, mul_one]

open scoped Classical in
/-- For every index `p` and every `X`, `∑_{Ht(E) ≤ X} 1[τ_p(E) ∉ 𝒦₀] = N^exc_p(X)`, the sum running
over the nonsingular pairs of height at most `X`. -/
lemma tsum_ite_notMem_K0_eq_exceptionalCountNat (p : ℕ) (X : ℝ) :
    ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
        E ∈ integralShortNFFamily},
        (if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1)
      = (exceptionalCountNat p X : ℝ) := by
  set A : Set {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} := {E | localReductionDatum p E.1.1 E.1.2 ∉ K0} with hA
  have hstep : ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      (if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1) = (A.ncard : ℝ) := by
    rw [← tsum_ite_ncard A]
    refine tsum_congr fun E => ?_
    by_cases h : localReductionDatum p E.1.1 E.1.2 ∈ K0 <;> simp [hA, h]
  rw [hstep]
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have himg : Subtype.val '' A =
        {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          ((tauZ p q.1 q.2).kodairaSymbol, (tauZ p q.1 q.2).tamagawaNumber) ∉ K0} := by
      ext q
      simp only [hA, Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_left,
        exists_prop, exists_eq_right_right, ← localReductionDatum_of_prime p q.1 q.2]
      tauto
    rw [exceptionalCountNat, dite_eq_left hp, exceptionalCount, ← himg,
      Set.ncard_image_of_injective A Subtype.val_injective]
  · rw [exceptionalCountNat, dite_eq_right hp]
    have hempty : A = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun E hE => hE (by
        rw [localReductionDatum_of_not_prime hp]; exact Set.mem_insert _ _)
    rw [hempty, Set.ncard_empty]

/-- For a prime `p`, a product over the index type `↥({p}.filter Nat.Prime)` is its single factor
at `p`. -/
lemma prod_singleton_filter_prime {M : Type*} [CommMonoid M] {p : ℕ} (hp : p.Prime)
    (g : ↥(({p} : Finset ℕ).filter Nat.Prime) → M) :
    ∏ q, g q = g ⟨p, Finset.mem_filter.2 ⟨Finset.mem_singleton_self p, hp⟩⟩ :=
  Finset.prod_eq_single_of_mem _ (Finset.mem_univ _) fun b _ hb =>
    absurd (Subtype.ext (Finset.mem_singleton.1 (Finset.mem_filter.1 b.2).1)) hb

open scoped Classical in
/-- For every index `p`, `(1/N(X)) · #{E : Ht(E) ≤ X, τ_p(E) ∉ 𝒦₀} → 1 - β_p` as `X → ∞`. -/
lemma tendsto_ratio_exceptionalCountNat (p : ℕ) :
    Tendsto (fun X : ℝ => (integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
      atTop (𝓝 (betaDefect p)) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have key := tendsto_average_prod_tauZ ({p} : Finset ℕ)
      (fun _ K => if K ∈ K0 then (0 : ℂ) else 1) (B := fun _ => 1)
      (fun _ K => by by_cases h : K ∈ K0 <;> simp [h])
    have hval : (∏ q : ↥(({p} : Finset ℕ).filter Nat.Prime),
        ∑' K : KodairaSymbol × ℕ, ((deltaP (q : ℕ) K).toReal : ℂ) *
          (if K ∈ K0 then (0 : ℂ) else 1)) = ((betaDefect p : ℝ) : ℂ) := by
      rw [prod_singleton_filter_prime hp]
      change (∑' K : KodairaSymbol × ℕ, ((deltaP p K).toReal : ℂ) *
          (if K ∈ K0 then (0 : ℂ) else 1)) = ((betaDefect p : ℝ) : ℂ)
      have h1 : ∀ K : KodairaSymbol × ℕ, ((deltaP p K).toReal : ℂ) *
          (if K ∈ K0 then (0 : ℂ) else 1)
          = (((if K ∈ K0 then (0 : ℝ) else (deltaP p K).toReal) : ℝ) : ℂ) := by
        intro K; by_cases h : K ∈ K0 <;> simp [h]
      have h2 : ∑' K : KodairaSymbol × ℕ, (if K ∈ K0 then (0 : ℝ) else (deltaP p K).toReal)
          = ∑' K : ↥((K0 : Set (KodairaSymbol × ℕ))ᶜ),
              (deltaP p (K : KodairaSymbol × ℕ)).toReal := by
        rw [tsum_subtype ((K0 : Set (KodairaSymbol × ℕ))ᶜ)
          (fun K => (deltaP p K).toReal)]
        refine tsum_congr fun K => ?_
        rw [Set.indicator_apply]
        by_cases h : K ∈ K0 <;> simp [h]
      rw [tsum_congr h1, ← Complex.ofReal_tsum, h2,
        ← ENNReal.tsum_toReal_eq (fun K : ↥((K0 : Set (KodairaSymbol × ℕ))ᶜ) =>
          deltaP_ne_top p (K : KodairaSymbol × ℕ)),
        ← one_sub_β_eq_tsum_compl_K0, betaDefect_of_prime]
    have hfun : ∀ X : ℝ, (integralShortNFCount X : ℂ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ∏ q : ↥(({p} : Finset ℕ).filter Nat.Prime),
            (if ((tauZ (q : ℕ) E.1.1 E.1.2).kodairaSymbol,
              (tauZ (q : ℕ) E.1.1 E.1.2).tamagawaNumber) ∈ K0 then (0 : ℂ) else 1)
        = (((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ) : ℝ) : ℂ) := by
      intro X
      have hin : ∀ E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
          E ∈ integralShortNFFamily},
          (∏ q : ↥(({p} : Finset ℕ).filter Nat.Prime),
            (if ((tauZ (q : ℕ) E.1.1 E.1.2).kodairaSymbol,
              (tauZ (q : ℕ) E.1.1 E.1.2).tamagawaNumber) ∈ K0 then (0 : ℂ) else 1))
          = (((if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1) : ℝ) : ℂ) := by
        intro E
        have hstep : ∀ q : ↥(({p} : Finset ℕ).filter Nat.Prime),
            (if ((tauZ (q : ℕ) E.1.1 E.1.2).kodairaSymbol,
                (tauZ (q : ℕ) E.1.1 E.1.2).tamagawaNumber) ∈ K0 then (0 : ℂ) else 1)
              = if localReductionDatum (q : ℕ) E.1.1 E.1.2 ∈ K0 then (0 : ℂ) else 1 :=
          fun q => by rw [localReductionDatum_of_prime]
        simp only [hstep]
        rw [prod_singleton_filter_prime hp]
        by_cases h : localReductionDatum p E.1.1 E.1.2 ∈ K0 <;> simp [h]
      rw [tsum_congr hin, ← Complex.ofReal_tsum, tsum_ite_notMem_K0_eq_exceptionalCountNat]
      push_cast
      ring
    have h3 : Tendsto
        (fun X : ℝ => (((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ) : ℝ) : ℂ))
        atTop (𝓝 ((betaDefect p : ℝ) : ℂ)) := hval ▸ key.congr hfun
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h3
  · rw [betaDefect_of_not_prime hp]
    refine Tendsto.congr (fun X => ?_) tendsto_const_nhds
    rw [exceptionalCountNat, dite_eq_right hp]
    simp

/-! ### The truncated weight agrees with the full weight off the exceptional set -/

/-- If `τ_p(E) ∈ 𝒦₀`, then the local Tamagawa number `c_p(E)` is `1`. -/
lemma localTamagawaNumber_eq_one_of_mem_K0 {p : ℕ} {a₄ a₆ : ℤ}
    (h : localReductionDatum p a₄ a₆ ∈ K0) : localTamagawaNumber p a₄ a₆ = 1 := by
  rw [← localReductionDatum_snd]
  rcases h with h | h <;> rw [h]

/-- For `K ∉ 𝒦₀`, if every prime `p ∉ S` has `τ_p(E) ∈ 𝒦₀`, then `ω_{K,S}(E) = ω_K(E)`. -/
lemma truncatedReductionOmega_eq_of_forall_mem_K0 {K : KodairaSymbol × ℕ} {S : Finset ℕ}
    {a₄ a₆ : ℤ} (hK : K ∉ K0)
    (hS : ∀ p : ℕ, p ∉ S → localReductionDatum p a₄ a₆ ∈ K0) :
    truncatedReductionOmega K S a₄ a₆ = reductionOmega K a₄ a₆ := by
  rw [truncatedReductionOmega, ← Finset.card_filter, ← Set.ncard_coe_finset, reductionOmega]
  congr 1
  ext p
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, and_iff_right_iff_imp]
  intro h
  by_contra hpS
  exact hK (h ▸ hS p hpS)

/-- If `Λ ⊆ 𝒦 ∖ 𝒦₀`, `Π` consists of primes and every prime `p ∉ S` has `τ_p(E) ∈ 𝒦₀`, then
`W_S(E) = W(E)`. -/
lemma truncatedWeight_eq (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ) (s u w : ℂ)
    (z : P → ℂ) (uΛ : Λ → ℂ) (hΛ : ∀ K ∈ Λ, K ∉ K0) (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {a₄ a₆ : ℤ}
    (hS : ∀ p : ℕ, p ∉ S → localReductionDatum p a₄ a₆ ∈ K0) :
    u ^ truncatedTamagawaOmega S a₄ a₆ * w ^ truncatedTamagawaCardFactors S a₄ a₆ *
        multiMonomial (truncatedTamagawaValuationVector P S a₄ a₆) z *
        (truncatedTamagawaProduct S a₄ a₆ : ℂ) ^ (-s) *
        multiMonomial (fun K : Λ => truncatedReductionOmega (K : KodairaSymbol × ℕ) S a₄ a₆) uΛ
      = u ^ tamagawaOmega a₄ a₆ * w ^ ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆) *
        multiMonomial (tamagawaValuationVector P a₄ a₆) z *
        (tamagawaProduct a₄ a₆ : ℂ) ^ (-s) * kodairaMonomial Λ uΛ a₄ a₆ := by
  have hS' : ∀ p : ℕ, 1 < localTamagawaNumber p a₄ a₆ → p ∈ S := fun p hlt => by
    by_contra hpS
    rw [localTamagawaNumber_eq_one_of_mem_K0 (hS p hpS)] at hlt
    exact absurd hlt (lt_irrefl 1)
  have hu : (fun K : Λ => truncatedReductionOmega (K : KodairaSymbol × ℕ) S a₄ a₆)
      = fun K : Λ => reductionOmega (K : KodairaSymbol × ℕ) a₄ a₆ :=
    funext fun K => truncatedReductionOmega_eq_of_forall_mem_K0 (hΛ _ K.2) hS
  rw [truncatedTamagawaOmega_eq hS', truncatedTamagawaCardFactors_eq hS',
    truncatedTamagawaValuationVector_eq hP hS', truncatedTamagawaProduct_eq hS', hu,
    kodairaMonomial]
  rfl

/-- On the polydisc `𝒟`, the full weight `W(E)` has norm at most `1`. -/
lemma norm_weight_le_one (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) (a₄ a₆ : ℤ) :
    ‖u ^ tamagawaOmega a₄ a₆ * w ^ ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆) *
        multiMonomial (tamagawaValuationVector P a₄ a₆) z *
        (tamagawaProduct a₄ a₆ : ℂ) ^ (-s) * kodairaMonomial Λ uΛ a₄ a₆‖ ≤ 1 := by
  simp only [norm_mul]
  have h₁ : ‖u ^ tamagawaOmega a₄ a₆‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
  have h₂ : ‖w ^ ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆)‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_multiMonomial_le_one _ huΛ)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_natCast_cpow_neg_le_one hs _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_multiMonomial_le_one _ hz)
  exact (mul_le_of_le_one_left (norm_nonneg _) h₁).trans h₂

/-- On the polydisc `𝒟`, the truncated weight `W_S(E)` has norm at most `1`. -/
lemma norm_truncatedWeight_le_one (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) (a₄ a₆ : ℤ) :
    ‖u ^ truncatedTamagawaOmega S a₄ a₆ * w ^ truncatedTamagawaCardFactors S a₄ a₆ *
        multiMonomial (truncatedTamagawaValuationVector P S a₄ a₆) z *
        (truncatedTamagawaProduct S a₄ a₆ : ℂ) ^ (-s) *
        multiMonomial (fun K : Λ =>
          truncatedReductionOmega (K : KodairaSymbol × ℕ) S a₄ a₆) uΛ‖ ≤ 1 := by
  rw [← prod_localWeight_localReductionDatum Λ P S hΛ s u w z uΛ a₄ a₆, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    fun q _ => norm_localWeight_le_one Λ P hs hu hw hz huΛ _

open scoped Classical in
/-- On the polydisc `𝒟`, for any finite set `T` of indices containing every prime `p ∉ S` with
`τ_p(E) ∉ 𝒦₀`, `|W(E) - W_S(E)| ≤ 2 ∑_{p ∈ T ∖ S} 1[τ_p(E) ∉ 𝒦₀]`. -/
lemma norm_sub_le_two_mul_sum (Λ : Finset (KodairaSymbol × ℕ)) (P S T : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hP : ∀ ℓ ∈ P, Nat.Prime ℓ)
    (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1)
    (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) {a₄ a₆ : ℤ}
    (hT : ∀ p : ℕ, p ∉ S → localReductionDatum p a₄ a₆ ∉ K0 → p ∈ T) :
    ‖(u ^ tamagawaOmega a₄ a₆ * w ^ ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆) *
          multiMonomial (tamagawaValuationVector P a₄ a₆) z *
          (tamagawaProduct a₄ a₆ : ℂ) ^ (-s) * kodairaMonomial Λ uΛ a₄ a₆)
        - (u ^ truncatedTamagawaOmega S a₄ a₆ * w ^ truncatedTamagawaCardFactors S a₄ a₆ *
          multiMonomial (truncatedTamagawaValuationVector P S a₄ a₆) z *
          (truncatedTamagawaProduct S a₄ a₆ : ℂ) ^ (-s) *
          multiMonomial (fun K : Λ =>
            truncatedReductionOmega (K : KodairaSymbol × ℕ) S a₄ a₆) uΛ)‖
      ≤ 2 * ∑ p ∈ T \ S, (if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1) := by
  have hnn : ∀ p : ℕ, (0 : ℝ) ≤ if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1 :=
    fun p => by split <;> norm_num
  by_cases hall : ∀ p : ℕ, p ∉ S → localReductionDatum p a₄ a₆ ∈ K0
  · rw [truncatedWeight_eq Λ P S s u w z uΛ hΛ hP hall, sub_self, norm_zero]
    have := Finset.sum_nonneg (fun p (_ : p ∈ T \ S) => hnn p)
    linarith
  · push Not at hall
    obtain ⟨p₀, hp₀S, hp₀⟩ := hall
    have h1 : (1 : ℝ) ≤ ∑ p ∈ T \ S, (if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1) := by
      have hmem : p₀ ∈ T \ S := Finset.mem_sdiff.2 ⟨hT p₀ hp₀S hp₀, hp₀S⟩
      have := Finset.single_le_sum (f := fun p : ℕ =>
        if localReductionDatum p a₄ a₆ ∈ K0 then (0 : ℝ) else 1) (fun p _ => hnn p) hmem
      rwa [ite_eq_right hp₀] at this
    refine le_trans (norm_sub_le _ _) ?_
    have h₂ := norm_weight_le_one Λ P hs hu hw hz huΛ a₄ a₆
    have h₃ := norm_truncatedWeight_le_one Λ P S hΛ hs hu hw hz huΛ a₄ a₆
    linarith

/-! ### The covering finite set of exceptional primes -/

/-- For a nonsingular `(a₄, a₆)` of height at most `X` and `S ⊇ {2, 3}`, a prime `p ∉ S` with
`τ_p(E) ∉ 𝒦₀` lies in `Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X`, for every cutoff `Y`. -/
lemma mem_cover_of_notMem_K0 {S : Finset ℕ} (h2 : 2 ∈ S) (h3 : 3 ∈ S) (Y : ℝ) {X : ℝ}
    (hX : 0 ≤ X) {a₄ a₆ : ℤ} (hfam : (a₄, a₆) ∈ integralShortNFFamily)
    (hht : (integralShortNFHeight a₄ a₆ : ℝ) ≤ X) {p : ℕ} (hpS : p ∉ S)
    (hnk : localReductionDatum p a₄ a₆ ∉ K0) :
    p ∈ Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X := by
  have hp : p.Prime := by
    by_contra h
    exact hnk (by rw [localReductionDatum_of_not_prime h]; exact Set.mem_insert _ _)
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h2' : p ≠ 2 := fun h => hpS (h ▸ h2)
    have h3' : p ≠ 3 := fun h => hpS (h ▸ h3)
    have h4' : p ≠ 4 := fun h => absurd (h ▸ hp) (by decide)
    have := hp.two_le
    omega
  rcases le_or_gt (p : ℝ) Y with hle | hgt
  · exact Finset.mem_union_left _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hle)))
  · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hp, hgt⟩)
    have hdvd := exc_implies_p2_dvd p hp5 a₄ a₆ (by rwa [← localReductionDatum_of_prime])
    have hD : (4 * a₄ ^ 3 + 27 * a₆ ^ 2 : ℤ) ≠ 0 :=
      (ofShortNF_Δ_ne_zero_iff a₄ a₆).1 hfam
    have hint : ((p : ℤ)) ^ 2 ≤ |4 * a₄ ^ 3 + 27 * a₆ ^ 2| :=
      Int.le_of_dvd (abs_pos.2 hD) ((dvd_abs _ _).2 hdvd)
    have habs := disc_abs_le_two_mul a₄ a₆ X hht
    have hsq : (p : ℝ) ^ 2 ≤ 2 * X := by
      have hcast : (((p : ℤ)) ^ 2 : ℝ) ≤ ((|4 * a₄ ^ 3 + 27 * a₆ ^ 2| : ℤ) : ℝ) := by
        exact_mod_cast hint
      push_cast at hcast habs
      linarith
    refine Nat.lt_succ_of_le (Nat.le_floor ?_)
    rw [Real.le_sqrt (by positivity) (by linarith)]
    exact hsq

/-! ### The per-`X` inequality -/

open scoped Classical in
/-- For `X ≥ 4` and a cutoff `Y ≥ 5`, `(1/N(X)) ∑_{Ht(E) ≤ X} |W(E) - W_S(E)|` is at most
`2 ∑_{p ≤ Y, p ∉ S} (1/N(X)) N^exc_p(X) + 2 (1/N(X)) excPrimeSum Y X`. -/
lemma average_norm_sub_le (Λ : Finset (KodairaSymbol × ℕ)) (P S : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0) (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (h2 : 2 ∈ S)
    (h3 : 3 ∈ S) (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1)
    (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) {X Y : ℝ} (hX : 4 ≤ X) (hY : 5 ≤ Y) :
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
                truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)‖
      ≤ 2 * ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
            ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
          + 2 * ((1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X) := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hfin : Finite {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily} := (finite_setOf_height_le_and_mem_family hX0).to_subtype
  have hNnn : (0 : ℝ) ≤ (integralShortNFCount X : ℝ)⁻¹ := by positivity
  have hpt : ∀ E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      ‖_‖ ≤ 2 * ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S,
        (if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1) := fun E =>
    norm_sub_le_two_mul_sum Λ P S _ hΛ hP hs hu hw hz huΛ
      fun p hpS hnk => mem_cover_of_notMem_K0 h2 h3 Y hX0 E.2.2 E.2.1 hpS hnk
  have hswap : ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
      E ∈ integralShortNFFamily},
      (2 * ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S,
        (if localReductionDatum p E.1.1 E.1.2 ∈ K0 then (0 : ℝ) else 1))
      = 2 * ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S,
          (exceptionalCountNat p X : ℝ) := by
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun p _ => Summable.of_finite)]
    exact congrArg _ (Finset.sum_congr rfl fun p _ => tsum_ite_notMem_K0_eq_exceptionalCountNat p X)
  have hbox := (Summable.tsum_le_tsum hpt Summable.of_finite Summable.of_finite).trans_eq hswap
  have hsplit : ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S, (exceptionalCountNat p X : ℝ)
      ≤ ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, (exceptionalCountNat p X : ℝ)
        + ∑ p ∈ excSupport Y X, (exceptionalCountNat p X : ℝ) := by
    rw [Finset.union_sdiff_distrib]
    have hinter : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) \ S) ∩ (excSupport Y X \ S),
        (exceptionalCountNat p X : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    have hle : ∑ p ∈ excSupport Y X \ S, (exceptionalCountNat p X : ℝ)
        ≤ ∑ p ∈ excSupport Y X, (exceptionalCountNat p X : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p _ _ => by positivity
    have := Finset.sum_union_inter (s₁ := Finset.range (⌊Y⌋₊ + 1) \ S)
      (s₂ := excSupport Y X \ S) (f := fun p : ℕ => (exceptionalCountNat p X : ℝ))
    linarith
  calc (integralShortNFCount X : ℝ)⁻¹ * _
      ≤ (integralShortNFCount X : ℝ)⁻¹ *
          (2 * ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1) ∪ excSupport Y X) \ S,
            (exceptionalCountNat p X : ℝ)) :=
        mul_le_mul_of_nonneg_left hbox hNnn
    _ ≤ (integralShortNFCount X : ℝ)⁻¹ *
          (2 * (∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, (exceptionalCountNat p X : ℝ) +
            excPrimeSum Y X)) := by
        refine mul_le_mul_of_nonneg_left ?_ hNnn
        rw [excPrimeSum_eq_finset_sum Y X hY (by linarith)]
        linarith
    _ = 2 * ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
            ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
          + 2 * ((1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X) := by
        rw [← Finset.mul_sum, one_div]
        ring

/-! ### The averaged bound -/

open scoped Classical in
/-- Let `S ⊇ {2, 3}` be a finite set of primes, `Λ ⊆ 𝒦 ∖ 𝒦₀` finite, `Π` a finite set of primes,
and let the parameters lie on the polydisc `𝒟`: `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` for
`ℓ ∈ Π`, `‖u_K‖ ≤ 1` for `K ∈ Λ`. Then

`limsup_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} |W(E) - W_S(E)| ≤ 2 ∑_{p ∉ S} (1 - β_p)`,

with `W` the summand of `tamagawaGeneratingFunction` and `W_S` its `S`-truncation. -/
@[bsd_tamagawa "T036b"]
theorem limsup_average_norm_sub_truncatedWeight_le (Λ : Finset (KodairaSymbol × ℕ))
    (P S : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hΛ : ∀ K ∈ Λ, K ∉ K0)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K' : Λ, ‖uΛ K'‖ ≤ 1) :
    limsup (fun X : ℝ => (integralShortNFCount X : ℝ)⁻¹ *
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
                truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)‖)
        atTop
      ≤ 2 * ∑' p : ℕ, if p ∈ S then 0 else betaDefect p := by
  set f : ℝ → ℝ := fun X => (integralShortNFCount X : ℝ)⁻¹ *
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
              truncatedReductionOmega (K : KodairaSymbol × ℕ) S E.1.1 E.1.2) uΛ)‖ with hf
  have hcob : IsCoboundedUnder (· ≤ ·) atTop f :=
    Filter.isCoboundedUnder_le_of_le atTop (x := 0) fun X => by
      rw [hf]
      exact mul_nonneg (by positivity) (tsum_nonneg fun E => norm_nonneg _)
  obtain ⟨C₁, hC₁, hbound⟩ := exceptional_ratio_bound
  have key : ∀ Y : ℝ, 5 ≤ Y → limsup f atTop
      ≤ 2 * (∑' p : ℕ, if p ∈ S then 0 else betaDefect p) + 2 * (C₁ * primeTail Y) := by
    intro Y hY
    set g : ℝ → ℝ := fun X =>
      2 * ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S,
          ((integralShortNFCount X : ℝ)⁻¹ * (exceptionalCountNat p X : ℝ))
        + 2 * (C₁ * (primeTail Y + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
          + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ))) with hg
    have hgt : Tendsto g atTop
        (𝓝 (2 * ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p + 2 * (C₁ * primeTail Y))) := by
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
      exact (hone.const_mul 2).add ((htwo.const_mul C₁).const_mul 2)
    have hfg : ∀ᶠ X in atTop, f X ≤ g X := by
      filter_upwards [eventually_ge_atTop (4 : ℝ),
        excPrimeSum_div_count_eventually_le C₁ hbound Y hY] with X hX4 hXb
      have hbox := average_norm_sub_le Λ P S hΛ hP h2 h3 hs hu hw hz huΛ hX4 hY
      have htail : (1 / (integralShortNFCount X : ℝ)) * excPrimeSum Y X
          ≤ C₁ * (primeTail Y + (1 / X ^ (1 / 3 : ℝ)) * ∑ p ∈ excSupport Y X, (1 / (p : ℝ))
            + (1 / X ^ (1 / 2 : ℝ)) * ((excSupport Y X).card : ℝ)) := by
        refine hXb.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
        have := excSupport_sum_inv_sq_le Y X
        linarith
      simp only [hf, hg]
      linarith
    calc limsup f atTop ≤ limsup g atTop := limsup_le_limsup hfg hcob hgt.isBoundedUnder_le
      _ = 2 * ∑ p ∈ Finset.range (⌊Y⌋₊ + 1) \ S, betaDefect p + 2 * (C₁ * primeTail Y) :=
          hgt.limsup_eq
      _ ≤ 2 * (∑' p : ℕ, if p ∈ S then 0 else betaDefect p) + 2 * (C₁ * primeTail Y) := by
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
  have hlim : Tendsto (fun Y : ℝ => 2 * (∑' p : ℕ, if p ∈ S then 0 else betaDefect p)
      + 2 * (C₁ * primeTail Y)) atTop
      (𝓝 (2 * ∑' p : ℕ, if p ∈ S then 0 else betaDefect p)) := by
    have h := (prime_tail_tendsto_zero.const_mul C₁).const_mul 2
    simpa using (tendsto_const_nhds
      (x := 2 * ∑' p : ℕ, if p ∈ S then 0 else betaDefect p)
      (f := (atTop : Filter ℝ))).add h
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (5 : ℝ)] with Y hY using key Y hY

end WeierstrassCurve
