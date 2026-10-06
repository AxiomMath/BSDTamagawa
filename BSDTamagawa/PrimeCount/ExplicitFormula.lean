/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.PrimeCount.GeneratingFunctionIdentity

/-!
# The explicit formula for the limiting distribution of `ω(Tam)`

With `π_r` the limiting density of curves whose Tamagawa product has exactly `r` distinct prime
factors,

  `π_0 = ∏_{p ∈ 𝒫} δ_p(1)`,
  `π_1 = ∑_{p ∈ 𝒫} (1 - δ_p(1)) ∏_{q ≠ p} δ_q(1)`,
  `π_2 = ∑_{p < q} (1 - δ_p(1))(1 - δ_q(1)) ∏_{r ≠ p, q} δ_r(1)`,

and more generally, for every `r ≥ 0`,

  `π_r = ∑_{S ⊆ 𝒫, |S| = r} (∏_{p ∈ S} (1 - δ_p(1))) (∏_{q ∉ S} δ_q(1))`.

The formula is obtained by expanding the Euler product `∏_p ((1 - b_p)u + b_p)` by distributivity,
for an abstract family `b : ℕ → ℝ` with `b p ∈ [0, 1]` and `∑_p (1 - b p) < ∞`, collecting terms by
`|S|`, and comparing coefficients with the generating-function identity for `π_r`. No division by
`δ_p(1)` occurs, so no nonvanishing hypothesis is needed.

## Main definitions

* `BSDTamagawa.ExplicitFormula.tailProd`: the tail product `∏'_{q ∉ S} b_q`.
* `BSDTamagawa.ExplicitFormula.subsetTerm`: `t_S = (∏_{p ∈ S}(1 - b_p)) ∏'_{q ∉ S} b_q`.
* `BSDTamagawa.ExplicitFormula.cardCoeff`: the sum of `t_S` over the `r`-element sets `S`.
* `WeierstrassCurve.tamagawaLocalTrivialMass`: `δ_p(1)` as a real-valued family over `ℕ`, equal to
  `1` off the primes.

## Main results

* `BSDTamagawa.ExplicitFormula.hasSum_subsetTerm`: `∑_S t_S u^{|S|} = ∏'_p ((1 - b_p)u + b_p)`.
* `BSDTamagawa.ExplicitFormula.hasSum_cardCoeff`: the same identity collected by `|S|`.
* `WeierstrassCurve.tamagawaOmegaDensity_eq_tsum_card_eq`: the general formula.
* `WeierstrassCurve.tamagawaOmegaDensity_zero_eq_tprod`,
  `WeierstrassCurve.tamagawaOmegaDensity_one_eq_tsum`,
  `WeierstrassCurve.tamagawaOmegaDensity_two_eq_tsum`: the cases `r = 0, 1, 2`.
* `WeierstrassCurve.multipliable_δ_one_notMem`, `WeierstrassCurve.multipliable_δ_one`,
  `WeierstrassCurve.multipliable_δ_one_ne`, `WeierstrassCurve.multipliable_δ_one_ne_pair`,
  `WeierstrassCurve.summable_subsetTerm_card_eq`,
  `WeierstrassCurve.summable_one_sub_δ_one_mul_tprod`,
  `WeierstrassCurve.summable_one_sub_δ_one_mul_tprod_pair`: the products and series in these
  formulas converge.

## Implementation notes

Indices run over `ℕ`: at a non-prime index the factor `1 - δ_p(1)` is `0` and the factor `δ_q(1)`
is `1`, so the sums over finite subsets of `ℕ` agree with the sums over finite sets of primes.
-/

@[expose] public section

namespace BSDTamagawa.ExplicitFormula

open Filter Topology

variable {b : ℕ → ℝ}

/-- The tail product `∏_{q ∉ S} b_q`. -/
noncomputable def tailProd (b : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∏' q : {x : ℕ // x ∉ S}, b (q : ℕ)

/-- The term attached to a finite set `S`. -/
noncomputable def subsetTerm (b : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, (1 - b p)) * tailProd b S

/-- **The tail family is multipliable.** If `b ≤ 1` and `∑_p (1 - b p) < ∞`, then for any finite
`S` the family `(b_q)_{q ∉ S}` is multipliable. -/
theorem multipliable_compl (hb1 : ∀ p, b p ≤ 1) (hbs : Summable fun p => 1 - b p)
    (S : Finset ℕ) : Multipliable fun q : {x : ℕ // x ∉ S} => b (q : ℕ) := by
  have h1 : Summable fun q : {x : ℕ // x ∉ S} => ‖-(1 - b (q : ℕ))‖ := by
    refine ((Finset.summable_compl_iff S).mpr hbs).congr fun q => ?_
    rw [norm_neg, Real.norm_of_nonneg (by linarith [hb1 (q : ℕ)])]
  exact (multipliable_one_add_of_summable h1).congr fun q => by ring

/-- `tailProd b S` is the limit of the partial products `∏_{q ∈ V} b_q` over finite
`V ⊆ {q // q ∉ S}`. -/
theorem hasProd_compl (hb1 : ∀ p, b p ≤ 1) (hbs : Summable fun p => 1 - b p) (S : Finset ℕ) :
    HasProd (fun q : {x : ℕ // x ∉ S} => b (q : ℕ)) (tailProd b S) :=
  (multipliable_compl hb1 hbs S).hasProd

/-- Weierstrass' elementary inequality `1 - ∑ (1 - c i) ≤ ∏ c i` for `c i ∈ [0,1]`. -/
theorem one_sub_sum_le_prod {ι : Type*} (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (V : Finset ι) : 1 - ∑ i ∈ V, (1 - c i) ≤ ∏ i ∈ V, c i := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | insert i V hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hP1 : ∏ j ∈ V, c j ≤ 1 := Finset.prod_le_one₀ (fun j _ => hc0 j) (fun j _ => hc1 j)
    have hP0 : 0 ≤ ∏ j ∈ V, c j := Finset.prod_nonneg fun j _ => hc0 j
    have hs0 : 0 ≤ ∑ j ∈ V, (1 - c j) := Finset.sum_nonneg fun j _ => by linarith [hc1 j]
    nlinarith [hc0 i, hc1 i]

/-- `∏'_{q ∉ S} b_q ≤ 1`: every partial product is, each factor lying in `[0, 1]`. -/
theorem tailProd_le_one (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (S : Finset ℕ) : tailProd b S ≤ 1 :=
  le_of_tendsto' (hasProd_compl hb1 hbs S) fun _ =>
    Finset.prod_le_one₀ (fun i _ => hb0 i) (fun i _ => hb1 i)

/-- `0 ≤ ∏'_{q ∉ S} b_q`: every partial product is. -/
theorem tailProd_nonneg (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (S : Finset ℕ) : 0 ≤ tailProd b S :=
  ge_of_tendsto' (hasProd_compl hb1 hbs S) fun _ => Finset.prod_nonneg fun i _ => hb0 i

/-- **Weierstrass' lower bound for the tail product:**
`1 - ∑'_{q ∉ S}(1 - b_q) ≤ ∏'_{q ∉ S} b_q`. -/
theorem one_sub_tsum_le_tailProd (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (S : Finset ℕ) :
    1 - (∑' q : {x : ℕ // x ∉ S}, (1 - b (q : ℕ))) ≤ tailProd b S := by
  refine ge_of_tendsto' (hasProd_compl hb1 hbs S) fun V => ?_
  have hle := Summable.sum_le_tsum (f := fun q : {x : ℕ // x ∉ S} => 1 - b (q : ℕ)) V
    (fun i _ => by linarith [hb1 (i : ℕ)]) ((Finset.summable_compl_iff S).mpr hbs)
  have hW := one_sub_sum_le_prod (fun q : {x : ℕ // x ∉ S} => b (q : ℕ))
    (fun i => hb0 (i : ℕ)) (fun i => hb1 (i : ℕ)) V
  linarith

/-- **The tail products tend to `1`.** As `S` grows through the finite subsets of `ℕ`,
`∏'_{q ∉ S} b_q → 1`. -/
theorem tendsto_tailProd (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) : Tendsto (tailProd b) atTop (nhds 1) := by
  have hσ : Tendsto (fun S : Finset ℕ => ∑' q : {x : ℕ // x ∉ S}, (1 - b (q : ℕ))) atTop
      (nhds 0) := tendsto_tsum_compl_atTop_zero fun p => 1 - b p
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun S : Finset ℕ => 1 - ∑' q : {x : ℕ // x ∉ S}, (1 - b (q : ℕ)))
    (h := fun _ : Finset ℕ => (1 : ℝ)) ?_ tendsto_const_nhds
    (fun S => one_sub_tsum_le_tailProd hb0 hb1 hbs S) (fun S => tailProd_le_one hb0 hb1 hbs S)
  simpa using tendsto_const_nhds.sub hσ

/-- **Splitting a tail product.** For `S ⊆ T`,

  `∏'_{q ∉ S} b_q = (∏_{q ∈ T \ S} b_q) · ∏'_{q ∉ T} b_q`. -/
theorem tailProd_eq_prod_sdiff_mul (hb1 : ∀ p, b p ≤ 1) (hbs : Summable fun p => 1 - b p)
    {S T : Finset ℕ} (hST : S ⊆ T) :
    tailProd b S = (∏ q ∈ T \ S, b q) * tailProd b T := by
  classical
  have key : ∀ U : Finset ℕ,
      tailProd b U = ∏' q : ℕ, Set.mulIndicator {x : ℕ | x ∉ U} b q := fun U =>
    tprod_subtype {x : ℕ | x ∉ U} b
  have hm1 : Multipliable (Set.mulIndicator (↑(T \ S) : Set ℕ) b) :=
    multipliable_of_ne_finset_one (s := T \ S) fun q hq =>
      Set.mulIndicator_of_notMem (by simpa using hq) _
  have hm2 : Multipliable (Set.mulIndicator {x : ℕ | x ∉ T} b) :=
    multipliable_subtype_iff_mulIndicator.mp (multipliable_compl hb1 hbs T)
  have hfac : ∀ q : ℕ, Set.mulIndicator {x : ℕ | x ∉ S} b q
      = Set.mulIndicator (↑(T \ S) : Set ℕ) b q * Set.mulIndicator {x : ℕ | x ∉ T} b q := by
    intro q
    by_cases hqT : q ∈ T
    · by_cases hqS : q ∈ S
      · simp [Set.mulIndicator, hqS, hqT]
      · simp [Set.mulIndicator, hqS, hqT]
    · have hqS : q ∉ S := fun h => hqT (hST h)
      simp [Set.mulIndicator, hqS, hqT]
  rw [key S, key T, tprod_congr hfac, hm1.tprod_mul hm2,
    tprod_eq_prod (s := T \ S) (L := .unconditional ℕ)
      (f := Set.mulIndicator (↑(T \ S) : Set ℕ) b)
      (fun q hq => Set.mulIndicator_of_notMem (by simpa using hq) _)]
  congr 1
  exact Finset.prod_congr rfl fun q hq => Set.mulIndicator_of_mem (by simpa using hq) _

/-- **Powersets are cofinal.** `T ↦ T.powerset` tends to `atTop` in `Finset (Finset ℕ)`. -/
theorem tendsto_powerset : Tendsto (fun T : Finset ℕ => T.powerset) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun V => ⟨V.sup id, fun T hT S hS => ?_⟩
  rw [Finset.mem_powerset]
  exact fun x hx => hT (Finset.le_sup (f := id) hS hx)

/-- **The Euler product converges.** The affine family
`p ↦ (1 - b_p)u + b_p = 1 + (1 - b_p)(u - 1)` is multipliable at every `u ∈ ℂ`. -/
theorem multipliable_affine (hb1 : ∀ p, b p ≤ 1) (hbs : Summable fun p => 1 - b p) (u : ℂ) :
    Multipliable fun p : ℕ => ((1 - b p : ℝ) : ℂ) * u + ((b p : ℝ) : ℂ) := by
  have h1 : Summable fun p : ℕ => ‖((1 - b p : ℝ) : ℂ) * (u - 1)‖ := by
    refine (hbs.mul_right ‖u - 1‖).congr fun p => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hb1 p])]
  exact (multipliable_one_add_of_summable h1).congr fun p => by push_cast; ring

/-- **The finite expansion, with the tail folded in.** For every finite `T` and every `u ∈ ℂ`,

  `(∏'_{q ∉ T} b_q) · ∏_{p ∈ T} ((1 - b_p)u + b_p) = ∑_{S ⊆ T} t_S u^{|S|}`,

where `t_S = (∏_{p ∈ S}(1 - b_p)) ∏'_{q ∉ S} b_q` is `subsetTerm`. -/
theorem prod_powerset_eq (hb1 : ∀ p, b p ≤ 1) (hbs : Summable fun p => 1 - b p) (u : ℂ)
    (T : Finset ℕ) :
    ((tailProd b T : ℝ) : ℂ) * ∏ p ∈ T, (((1 - b p : ℝ) : ℂ) * u + ((b p : ℝ) : ℂ))
      = ∑ S ∈ T.powerset, ((subsetTerm b S : ℝ) : ℂ) * u ^ S.card := by
  classical
  rw [Finset.prod_add (fun p : ℕ => ((1 - b p : ℝ) : ℂ) * u) (fun p : ℕ => ((b p : ℝ) : ℂ)) T,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  rw [subsetTerm, tailProd_eq_prod_sdiff_mul hb1 hbs hS, Finset.prod_mul_distrib,
    Finset.prod_const]
  push_cast
  ring

/-- `0 ≤ t_S`, both factors being nonnegative. -/
theorem subsetTerm_nonneg (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (S : Finset ℕ) : 0 ≤ subsetTerm b S :=
  mul_nonneg (Finset.prod_nonneg fun p _ => by linarith [hb1 p]) (tailProd_nonneg hb0 hb1 hbs S)

/-- `t_S ≤ ∏_{p ∈ S}(1 - b_p)`, the tail product being at most `1`. -/
theorem subsetTerm_le (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (S : Finset ℕ) :
    subsetTerm b S ≤ ∏ p ∈ S, (1 - b p) := by
  rw [subsetTerm]
  exact mul_le_of_le_one_right (Finset.prod_nonneg fun p _ => by linarith [hb1 p])
    (tailProd_le_one hb0 hb1 hbs S)

/-- **The expansion converges absolutely.** `∑_{S : Finset ℕ} ‖t_S u^{|S|}‖ < ∞` at every
`u ∈ ℂ`. -/
theorem summable_subsetTerm_mul_pow (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (u : ℂ) :
    Summable fun S : Finset ℕ => ((subsetTerm b S : ℝ) : ℂ) * u ^ S.card := by
  have hmaj : Summable fun S : Finset ℕ => ∏ p ∈ S, ((1 - b p) * ‖u‖) :=
    summable_finsetProd_of_summable_nonneg
      (fun p => mul_nonneg (by linarith [hb1 p]) (norm_nonneg u)) (hbs.mul_right ‖u‖)
  refine Summable.of_norm_bounded hmaj fun S => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (subsetTerm_nonneg hb0 hb1 hbs S)]
  exact mul_le_mul_of_nonneg_right (subsetTerm_le hb0 hb1 hbs S) (by positivity)

/-- The family `(t_S)_S` is summable. -/
theorem summable_subsetTerm (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) : Summable (subsetTerm b) := by
  refine Summable.of_nonneg_of_le (subsetTerm_nonneg hb0 hb1 hbs) (subsetTerm_le hb0 hb1 hbs)
    (summable_finsetProd_of_summable_nonneg (fun p => by linarith [hb1 p]) hbs)

/-- **The infinite expansion.** At every `u ∈ ℂ`,

  `∑_{S : Finset ℕ} t_S u^{|S|} = ∏'_p ((1 - b_p)u + b_p)`. -/
theorem hasSum_subsetTerm (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (u : ℂ) :
    HasSum (fun S : Finset ℕ => ((subsetTerm b S : ℝ) : ℂ) * u ^ S.card)
      (∏' p : ℕ, (((1 - b p : ℝ) : ℂ) * u + ((b p : ℝ) : ℂ))) := by
  have hsum := summable_subsetTerm_mul_pow hb0 hb1 hbs u
  have h1 : Tendsto (fun T : Finset ℕ =>
      ∑ S ∈ T.powerset, ((subsetTerm b S : ℝ) : ℂ) * u ^ S.card) atTop
      (nhds (∑' S : Finset ℕ, ((subsetTerm b S : ℝ) : ℂ) * u ^ S.card)) :=
    hsum.hasSum.comp tendsto_powerset
  have hR : Tendsto (fun T : Finset ℕ => ((tailProd b T : ℝ) : ℂ)) atTop (nhds 1) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp (tendsto_tailProd hb0 hb1 hbs)
  have h2 : Tendsto (fun T : Finset ℕ =>
      ∑ S ∈ T.powerset, ((subsetTerm b S : ℝ) : ℂ) * u ^ S.card) atTop
      (nhds (∏' p : ℕ, (((1 - b p : ℝ) : ℂ) * u + ((b p : ℝ) : ℂ)))) := by
    simpa only [prod_powerset_eq hb1 hbs u, one_mul] using
      hR.mul (multipliable_affine hb1 hbs u).hasProd
  rw [← tendsto_nhds_unique h1 h2]
  exact hsum.hasSum

/-- The coefficient of `u^r`: the sum of the terms over the `r`-element subsets. -/
noncomputable def cardCoeff (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑' S : {S : Finset ℕ // S.card = r}, subsetTerm b (S : Finset ℕ)

/-- **The expansion, collected by cardinality.** At every `u ∈ ℂ`,

  `∑_{r ≥ 0} (cardCoeff b r) u^r = ∏'_p ((1 - b_p)u + b_p)`. -/
theorem hasSum_cardCoeff (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1)
    (hbs : Summable fun p => 1 - b p) (u : ℂ) :
    HasSum (fun r : ℕ => ((cardCoeff b r : ℝ) : ℂ) * u ^ r)
      (∏' p : ℕ, (((1 - b p : ℝ) : ℂ) * u + ((b p : ℝ) : ℂ))) := by
  have he := (Equiv.hasSum_iff (Equiv.sigmaFiberEquiv (fun S : Finset ℕ => S.card))).mpr
    (hasSum_subsetTerm hb0 hb1 hbs u)
  refine he.sigma fun r => ?_
  have hfib : Summable fun c : {S : Finset ℕ // S.card = r} => subsetTerm b (c : Finset ℕ) :=
    (summable_subsetTerm hb0 hb1 hbs).subtype _
  have hC : HasSum (fun c : {S : Finset ℕ // S.card = r} =>
      ((subsetTerm b (c : Finset ℕ) : ℝ) : ℂ) * u ^ r) (((cardCoeff b r : ℝ) : ℂ) * u ^ r) := by
    refine HasSum.mul_right _ ?_
    rw [cardCoeff]
    exact hfib.hasSum.map (Complex.ofRealHom : ℝ →+* ℂ) Complex.continuous_ofReal
  refine hC.congr_fun fun c => ?_
  rw [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, c.property]

end BSDTamagawa.ExplicitFormula

namespace WeierstrassCurve

open Filter Topology
open BSDTamagawa BSDTamagawa.ExplicitFormula

/-- The local *trivial* mass `δ_p(1)`, as a real-valued family over `ℕ`. -/
noncomputable def tamagawaLocalTrivialMass (p : ℕ) : ℝ :=
  if h : p.Prime then (@δ p ⟨h⟩ 1).toReal else 1

/-- At a prime index the local trivial mass is `(δ_p(1)).toReal`. -/
theorem tamagawaLocalTrivialMass_of_prime (p : ℕ) [Fact p.Prime] :
    tamagawaLocalTrivialMass p = (δ p 1).toReal := dite_eq_left Fact.out

/-- At a non-prime index the local trivial mass is `1`. -/
theorem tamagawaLocalTrivialMass_of_not_prime {p : ℕ} (hp : ¬ p.Prime) :
    tamagawaLocalTrivialMass p = 1 := dite_eq_right hp

/-- `1 - δ_p(1)` is the local tail mass `tamagawaLocalTailMass p`, at every index. -/
theorem one_sub_tamagawaLocalTrivialMass (p : ℕ) :
    1 - tamagawaLocalTrivialMass p = tamagawaLocalTailMass p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTrivialMass_of_prime, tamagawaLocalTailMass_of_prime]
  · rw [tamagawaLocalTrivialMass_of_not_prime hp, tamagawaLocalTailMass_of_not_prime hp, sub_self]

/-- `0 ≤ δ_p(1)`. -/
theorem tamagawaLocalTrivialMass_nonneg (p : ℕ) : 0 ≤ tamagawaLocalTrivialMass p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTrivialMass_of_prime]
    exact ENNReal.toReal_nonneg
  · rw [tamagawaLocalTrivialMass_of_not_prime hp]
    exact zero_le_one

/-- `δ_p(1) ≤ 1`. -/
theorem tamagawaLocalTrivialMass_le_one (p : ℕ) : tamagawaLocalTrivialMass p ≤ 1 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTrivialMass_of_prime]
    exact δ_one_toReal_le_one
  · rw [tamagawaLocalTrivialMass_of_not_prime hp]

/-- `∑_p (1 - δ_p(1)) < ∞`. -/
theorem summable_one_sub_tamagawaLocalTrivialMass :
    Summable fun p : ℕ => 1 - tamagawaLocalTrivialMass p :=
  summable_tamagawaLocalTailMass.congr fun p => (one_sub_tamagawaLocalTrivialMass p).symm

/-- **The affine factor is the local Euler factor:** `(1 - δ_p(1))u + δ_p(1)` is
`tamagawaOmegaEulerFactor p u`. -/
theorem affine_eq_tamagawaOmegaEulerFactor (p : ℕ) (u : ℂ) :
    ((1 - tamagawaLocalTrivialMass p : ℝ) : ℂ) * u + ((tamagawaLocalTrivialMass p : ℝ) : ℂ)
      = tamagawaOmegaEulerFactor p u := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaOmegaEulerFactor_of_prime, tamagawaLocalTrivialMass_of_prime]
    push_cast
    ring
  · rw [tamagawaOmegaEulerFactor_of_not_prime hp, tamagawaLocalTrivialMass_of_not_prime hp]
    push_cast
    ring

/-- `∏'_p ((1 - δ_p(1))u + δ_p(1))` is the Euler product `F(u)`. -/
theorem tprod_affine_eq_tamagawaOmegaEulerProduct (u : ℂ) :
    (∏' p : ℕ, (((1 - tamagawaLocalTrivialMass p : ℝ) : ℂ) * u
        + ((tamagawaLocalTrivialMass p : ℝ) : ℂ)))
      = tamagawaOmegaEulerProduct u := by
  rw [tamagawaOmegaEulerProduct]
  exact tprod_congr (affine_eq_tamagawaOmegaEulerFactor · u)

/-- **The expansion's generating function is `F`.** For every `u : ℂ`,

  `∑_{r ≥ 0} (cardCoeff r) u^r = F(u)`. -/
theorem hasSum_cardCoeff_tamagawaLocalTrivialMass (u : ℂ) :
    HasSum (fun r : ℕ => ((cardCoeff tamagawaLocalTrivialMass r : ℝ) : ℂ) * u ^ r)
      (tamagawaOmegaEulerProduct u) :=
  tprod_affine_eq_tamagawaOmegaEulerProduct u ▸
    hasSum_cardCoeff tamagawaLocalTrivialMass_nonneg tamagawaLocalTrivialMass_le_one
      summable_one_sub_tamagawaLocalTrivialMass u

/-- The coefficient family `cardCoeff` expands `F` on the open unit disc, in the `Unit`-indexed
polydisc form. -/
theorem hasPolydiscExpansion_cardCoeff :
    HasPolydiscExpansion
      (fun j : Unit →₀ ℕ => ((cardCoeff tamagawaLocalTrivialMass (j ()) : ℝ) : ℂ))
      (fun z : Unit → ℂ => tamagawaOmegaEulerProduct (z ())) := by
  intro z _
  refine (Equiv.hasSum_iff (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm).mp ?_
  refine (hasSum_cardCoeff_tamagawaLocalTrivialMass (z ())).congr_fun fun r => ?_
  simp [smul_eq_mul]

/-- **The expansion's coefficient is `π_r`.** For every `r`,

  `cardCoeff r = π_r`. -/
theorem cardCoeff_eq_tamagawaOmegaDensity (r : ℕ) :
    cardCoeff tamagawaLocalTrivialMass r = tamagawaOmegaDensity r :=
  Complex.ofReal_injective (congrFun
    (BSDTamagawa.CoeffExtraction.coeff_eq_of_hasPolydiscExpansion hasPolydiscExpansion_cardCoeff
      hasPolydiscExpansion_tamagawaOmegaDensity.right.right.right)
    (Finsupp.equivFunOnFinite.symm fun _ : Unit => r))

/-- The expansion's term at `S`, expanded:

  `t_S = (∏_{p ∈ S}(1 - δ_p(1))) ∏'_{q ∉ S} δ_q(1)`. -/
theorem subsetTerm_tamagawaLocalTrivialMass (S : Finset ℕ) :
    subsetTerm tamagawaLocalTrivialMass S
      = (∏ p ∈ S, tamagawaLocalTailMass p) *
          ∏' q : {x : ℕ // x ∉ S}, tamagawaLocalTrivialMass (q : ℕ) := by
  rw [subsetTerm, tailProd]
  exact congrArg (· * ∏' q : {x : ℕ // x ∉ S}, tamagawaLocalTrivialMass (q : ℕ))
    (Finset.prod_congr rfl fun p _ => one_sub_tamagawaLocalTrivialMass p)

/-! ### The three low-order cases -/

/-- The `1`-element subsets of `ℕ` are exactly the singletons. -/
noncomputable def cardOneEquiv : ℕ ≃ {S : Finset ℕ // S.card = 1} :=
  Equiv.ofBijective (fun p => ⟨{p}, Finset.card_singleton p⟩)
    ⟨fun _ _ h => by simpa using Subtype.mk_eq_mk.mp h, fun S => by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp S.property
      exact ⟨a, Subtype.ext ha.symm⟩⟩

/-- The `2`-element subsets of `ℕ` are exactly the pairs `{p, q}` with `p < q`. -/
noncomputable def cardTwoEquiv : {pq : ℕ × ℕ // pq.1 < pq.2} ≃ {S : Finset ℕ // S.card = 2} :=
  Equiv.ofBijective
    (fun pq => ⟨{(pq : ℕ × ℕ).1, (pq : ℕ × ℕ).2}, by
      rw [Finset.card_insert_of_notMem (by simpa using pq.property.ne), Finset.card_singleton]⟩)
    ⟨by
      intro x y hxy
      obtain ⟨⟨p, q⟩, hpq⟩ := x
      obtain ⟨⟨p', q'⟩, hpq'⟩ := y
      have key := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hxy : ({p, q} : Finset ℕ) = {p', q'})
      simp only [Finset.mem_insert, Finset.mem_singleton] at key
      obtain ⟨rfl, rfl⟩ : p = p' ∧ q = q' := by
        have h1 := (key p).mp (by simp)
        have h2 := (key q).mp (by simp)
        have h3 := (key p').mpr (by simp)
        have h4 := (key q').mpr (by simp)
        omega
      rfl, by
      intro S
      obtain ⟨a, c, hac, hS⟩ := Finset.card_eq_two.mp S.property
      rcases lt_or_gt_of_ne hac with h | h
      · exact ⟨⟨(a, c), h⟩, Subtype.ext hS.symm⟩
      · exact ⟨⟨(c, a), h⟩, Subtype.ext (show ({c, a} : Finset ℕ) = (S : Finset ℕ) by
          rw [Finset.pair_comm]; exact hS.symm)⟩⟩

/-- The term at `S = ∅` is the full product `∏'_q δ_q(1)`. -/
theorem subsetTerm_empty :
    subsetTerm tamagawaLocalTrivialMass ∅ = ∏' q : ℕ, tamagawaLocalTrivialMass q := by
  rw [subsetTerm_tamagawaLocalTrivialMass, Finset.prod_empty, one_mul]
  exact Equiv.tprod_eq (Equiv.subtypeUnivEquiv fun x : ℕ => Finset.notMem_empty x)
    tamagawaLocalTrivialMass

/-- The term at a singleton `S = {p}` is `(1 - δ_p(1)) ∏'_{q ≠ p} δ_q(1)`. -/
theorem subsetTerm_singleton (p : ℕ) :
    subsetTerm tamagawaLocalTrivialMass {p}
      = tamagawaLocalTailMass p *
          ∏' q : {x : ℕ // x ≠ p}, tamagawaLocalTrivialMass (q : ℕ) := by
  rw [subsetTerm_tamagawaLocalTrivialMass, Finset.prod_singleton]
  exact congrArg (tamagawaLocalTailMass p * ·)
    (Equiv.tprod_eq (Equiv.subtypeEquivRight fun x => by simp)
      fun q : {x : ℕ // x ≠ p} => tamagawaLocalTrivialMass (q : ℕ))

/-- The term at a pair `S = {p, q}` with `p ≠ q` is
`(1 - δ_p(1))(1 - δ_q(1)) ∏'_{r ≠ p, q} δ_r(1)`. -/
theorem subsetTerm_pair {p q : ℕ} (hpq : p ≠ q) :
    subsetTerm tamagawaLocalTrivialMass {p, q}
      = tamagawaLocalTailMass p * tamagawaLocalTailMass q *
          ∏' r : {x : ℕ // x ≠ p ∧ x ≠ q}, tamagawaLocalTrivialMass (r : ℕ) := by
  rw [subsetTerm_tamagawaLocalTrivialMass, Finset.prod_insert (by simpa using hpq),
    Finset.prod_singleton]
  exact congrArg (tamagawaLocalTailMass p * tamagawaLocalTailMass q * ·)
    (Equiv.tprod_eq (Equiv.subtypeEquivRight fun x => by simp [not_or])
      fun r : {x : ℕ // x ≠ p ∧ x ≠ q} => tamagawaLocalTrivialMass (r : ℕ))

/-- **The `r = 0` coefficient** is `∏'_q δ_q(1)`. -/
theorem cardCoeff_zero :
    cardCoeff tamagawaLocalTrivialMass 0 = ∏' q : ℕ, tamagawaLocalTrivialMass q := by
  rw [cardCoeff, tsum_eq_single ⟨∅, Finset.card_empty⟩
    (fun S hS => absurd (Subtype.ext (Finset.card_eq_zero.mp S.property)) hS)]
  exact subsetTerm_empty

/-- **The `r = 1` coefficient** is `∑'_p (1 - δ_p(1)) ∏'_{q ≠ p} δ_q(1)`. -/
theorem cardCoeff_one :
    cardCoeff tamagawaLocalTrivialMass 1
      = ∑' p : ℕ, tamagawaLocalTailMass p *
          ∏' q : {x : ℕ // x ≠ p}, tamagawaLocalTrivialMass (q : ℕ) := by
  rw [cardCoeff, ← Equiv.tsum_eq cardOneEquiv]
  exact tsum_congr subsetTerm_singleton

/-- **The `r = 2` coefficient** is `∑'_{p < q} (1 - δ_p(1))(1 - δ_q(1)) ∏'_{r ≠ p, q} δ_r(1)`. -/
theorem cardCoeff_two :
    cardCoeff tamagawaLocalTrivialMass 2
      = ∑' pq : {pq : ℕ × ℕ // pq.1 < pq.2},
          tamagawaLocalTailMass (pq : ℕ × ℕ).1 * tamagawaLocalTailMass (pq : ℕ × ℕ).2 *
            ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
              tamagawaLocalTrivialMass (r : ℕ) := by
  rw [cardCoeff, ← Equiv.tsum_eq cardTwoEquiv]
  exact tsum_congr fun ⟨_, h⟩ => subsetTerm_pair h.ne

/-- The terms `t_S` at `b = δ_·(1)` are summable over all of `Finset ℕ`. -/
theorem summable_subsetTerm_tamagawaLocalTrivialMass :
    Summable (subsetTerm tamagawaLocalTrivialMass) :=
  summable_subsetTerm tamagawaLocalTrivialMass_nonneg tamagawaLocalTrivialMass_le_one
    summable_one_sub_tamagawaLocalTrivialMass

/-! ### The explicit formula -/

/-- For every `r ≥ 0`,

  `π_r = ∑_{S ⊆ 𝒫, |S| = r} (∏_{p ∈ S} (1 - δ_p(1))) (∏_{q ∉ S} δ_q(1))`,

with `π_r` the limiting density and `δ_p(1)` the scalar local density. The index `S` runs over the
`r`-element subsets of `ℕ`; a subset containing a non-prime contributes `0`. -/
@[bsd_tamagawa "T042"]
theorem tamagawaOmegaDensity_eq_tsum_card_eq (r : ℕ) :
    tamagawaOmegaDensity r
      = ∑' S : {S : Finset ℕ // S.card = r},
          (∏ p ∈ (S : Finset ℕ), (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0)) *
            ∏' q : {x : ℕ // x ∉ (S : Finset ℕ)},
              (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1) := by
  rw [← cardCoeff_eq_tamagawaOmegaDensity r, cardCoeff]
  exact tsum_congr fun S => subsetTerm_tamagawaLocalTrivialMass (S : Finset ℕ)

/-- The case `r = 0`: `π_0 = ∏_{p ∈ 𝒫} δ_p(1)`. -/
@[bsd_tamagawa "T042"]
theorem tamagawaOmegaDensity_zero_eq_tprod :
    tamagawaOmegaDensity 0 = ∏' q : ℕ, (if h : q.Prime then (@δ q ⟨h⟩ 1).toReal else 1) := by
  rw [← cardCoeff_eq_tamagawaOmegaDensity 0]
  exact cardCoeff_zero

/-- The case `r = 1`: `π_1 = ∑_{p ∈ 𝒫} (1 - δ_p(1)) ∏_{q ≠ p} δ_q(1)`. -/
@[bsd_tamagawa "T042"]
theorem tamagawaOmegaDensity_one_eq_tsum :
    tamagawaOmegaDensity 1
      = ∑' p : ℕ, (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) *
          ∏' q : {x : ℕ // x ≠ p},
            (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1) := by
  rw [← cardCoeff_eq_tamagawaOmegaDensity 1]
  exact cardCoeff_one

/-- The case `r = 2`: `π_2 = ∑_{p < q} (1 - δ_p(1))(1 - δ_q(1)) ∏_{r ≠ p, q} δ_r(1)`. -/
@[bsd_tamagawa "T042"]
theorem tamagawaOmegaDensity_two_eq_tsum :
    tamagawaOmegaDensity 2
      = ∑' pq : {pq : ℕ × ℕ // pq.1 < pq.2},
          (if h : (pq : ℕ × ℕ).1.Prime then 1 - (@δ (pq : ℕ × ℕ).1 ⟨h⟩ 1).toReal else 0) *
            (if h : (pq : ℕ × ℕ).2.Prime then 1 - (@δ (pq : ℕ × ℕ).2 ⟨h⟩ 1).toReal else 0) *
            ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
              (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1) := by
  rw [← cardCoeff_eq_tamagawaOmegaDensity 2]
  exact cardCoeff_two

/-! ### Convergence of the products and series in the explicit formula -/

/-- For every finite `S`, the family `(δ_q(1))_{q ∉ S}` is multipliable. -/
@[bsd_tamagawa "T042"]
theorem multipliable_δ_one_notMem (S : Finset ℕ) :
    Multipliable fun q : {x : ℕ // x ∉ S} =>
      (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1) :=
  multipliable_compl tamagawaLocalTrivialMass_le_one summable_one_sub_tamagawaLocalTrivialMass S

/-- The family `(δ_q(1))_q` is multipliable. -/
@[bsd_tamagawa "T042"]
theorem multipliable_δ_one :
    Multipliable fun q : ℕ => (if h : q.Prime then (@δ q ⟨h⟩ 1).toReal else 1) := by
  refine (Equiv.multipliable_iff
    (Equiv.subtypeUnivEquiv fun x : ℕ => Finset.notMem_empty x)).mp ?_
  exact multipliable_δ_one_notMem ∅

/-- For every `p`, the family `(δ_q(1))_{q ≠ p}` is multipliable. -/
@[bsd_tamagawa "T042"]
theorem multipliable_δ_one_ne (p : ℕ) :
    Multipliable fun q : {x : ℕ // x ≠ p} =>
      (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1) := by
  refine (Equiv.multipliable_iff (Equiv.subtypeEquivRight fun x => (by simp : x ∉ ({p} : Finset ℕ)
    ↔ x ≠ p))).mp ?_
  exact multipliable_δ_one_notMem {p}

/-- For all `p`, `q`, the family `(δ_r(1))_{r ≠ p, q}` is multipliable. -/
@[bsd_tamagawa "T042"]
theorem multipliable_δ_one_ne_pair (p q : ℕ) :
    Multipliable fun r : {x : ℕ // x ≠ p ∧ x ≠ q} =>
      (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1) := by
  refine (Equiv.multipliable_iff (Equiv.subtypeEquivRight fun x =>
    (by simp [not_or] : x ∉ ({p, q} : Finset ℕ) ↔ (x ≠ p ∧ x ≠ q)))).mp ?_
  exact multipliable_δ_one_notMem {p, q}

/-- For every `r`, the terms `t_S` over the `r`-element subsets `S` are summable. -/
@[bsd_tamagawa "T042"]
theorem summable_subsetTerm_card_eq (r : ℕ) :
    Summable fun S : {S : Finset ℕ // S.card = r} =>
      (∏ p ∈ (S : Finset ℕ), (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0)) *
        ∏' q : {x : ℕ // x ∉ (S : Finset ℕ)},
          (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1) :=
  (summable_subsetTerm_tamagawaLocalTrivialMass.subtype {S : Finset ℕ | S.card = r}).congr
    fun ⟨S, _⟩ => subsetTerm_tamagawaLocalTrivialMass S

/-- The family `p ↦ (1 - δ_p(1)) ∏'_{q ≠ p} δ_q(1)` is summable. -/
@[bsd_tamagawa "T042"]
theorem summable_one_sub_δ_one_mul_tprod :
    Summable fun p : ℕ => (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) *
      ∏' q : {x : ℕ // x ≠ p},
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1) :=
  ((Equiv.summable_iff cardOneEquiv).mpr
    (summable_subsetTerm_tamagawaLocalTrivialMass.subtype
      {S : Finset ℕ | S.card = 1})).congr subsetTerm_singleton

/-- The family `(p, q) ↦ (1 - δ_p(1))(1 - δ_q(1)) ∏'_{r ≠ p, q} δ_r(1)` over pairs `p < q` is
summable. -/
@[bsd_tamagawa "T042"]
theorem summable_one_sub_δ_one_mul_tprod_pair :
    Summable fun pq : {pq : ℕ × ℕ // pq.1 < pq.2} =>
      (if h : (pq : ℕ × ℕ).1.Prime then 1 - (@δ (pq : ℕ × ℕ).1 ⟨h⟩ 1).toReal else 0) *
        (if h : (pq : ℕ × ℕ).2.Prime then 1 - (@δ (pq : ℕ × ℕ).2 ⟨h⟩ 1).toReal else 0) *
        ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
          (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1) :=
  ((Equiv.summable_iff cardTwoEquiv).mpr
    (summable_subsetTerm_tamagawaLocalTrivialMass.subtype
      {S : Finset ℕ | S.card = 2})).congr fun ⟨_, h⟩ => subsetTerm_pair h.ne

end WeierstrassCurve
