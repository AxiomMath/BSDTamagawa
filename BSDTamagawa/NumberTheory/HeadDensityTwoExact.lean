/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityTwo
public import BSDTamagawa.NumberTheory.SplitDecoratedDensity

/-!
# The non-split even `Iₙ` rows, and `δ_p(2)` reduced to the `Iₙ*` family

Let `p ≥ 5`, `N = |goodRes p|`, so that `2N = p - 1`, and `T = (1 - p⁻¹⁰)⁻¹ = p¹⁰/(p¹⁰ - 1)`. This
file evaluates the rows of the local density table (Griffin–Ono–Tsai, Table 5) for the non-split
even `Iₙ` strata with Tamagawa number `2`:

| row | value | closed form |
|---|---|---|
| `δ_p((Iₙ, 2))`, `n ≥ 4` even | `2N² p^{-(n+2)} T` | `(p-1)²p^{8-n}/(2(p¹⁰-1))` |
| `δ_p((I₀, 2))` | `0` | `0` |

At `n ≥ 3` the index `(Iₙ, n)` names only the split half of the level-`n` multiplicative locus; the
non-split half reports Tamagawa number `2` when `n` is even. Summed over the even levels, the whole
multiplicative contribution to `{c = 2}` is

  `∑_{n ≥ 0} δ_p((I_{2n}, 2)) = 4N²p⁻⁴T + 2N²p⁻⁶T(1 - p⁻²)⁻¹`,

where at `n = 2` both branches of Step 2 of Tate's algorithm report `2`.

Every stratum of `{c = 2}` occurs exactly once in the decomposition

  `δ_p(2) = ∑_{n} δ_p((I_{2n}, 2)) + δ_p((III, 2)) + ∑_{n} δ_p((Iₙ*, 2)) + δ_p((III*, 2))`,

and substituting the evaluated rows gives `δ_p(2) = gotHeadTwoEvaluated p + ∑_{n} δ_p((Iₙ*, 2))`.
Since `gotHeadTwoEvaluated p + gotIStarTwoTotal p = gotδ p 2`, the equality
`δ_p(2) = gotδ p 2` holds iff the `Iₙ*` strata with `c = 2` have total mass
`gotIStarTwoTotal p = ((p²-1)/(2p⁷)) T`.

## Main definitions

* `WeierstrassCurve.gotHeadTwoEvaluated`: the real closed form
  `((p-1)²/p⁴ + (p-1)/p⁴ + (p-1)/(2p⁴(p+1)) + (p-1)/p⁹) T` of the rows `(I₂, 2)`, `(III, 2)`, the
  non-split even `(Iₙ, 2)` for `n ≥ 4`, and `(III*, 2)`.
* `WeierstrassCurve.gotIStarTwoTotal`, `WeierstrassCurve.gotIZeroStarTwo`,
  `WeierstrassCurve.gotInStarTwo`: the table values `((p²-1)/(2p⁷)) T`, `(p(p-1)/2) p⁻⁷ T` and
  `((p-1)/2) p⁻⁷ T` of the whole `Iₙ*` contribution to `δ_p(2)`, of the row `(I₀*, 2)`, and of the
  non-split `Iₙ*` family with `n ≥ 1`.

## Main results

* `WeierstrassCurve.deltaP_I_zero_two_eq_zero`: `δ_p((I₀, 2)) = 0`.
* `WeierstrassCurve.stratFibre_diff_range_eq_iNonSplitLocus_even`: for even `n ≥ 4`, the minimal
  part of `τ_p⁻¹((Iₙ, 2))` is the non-split level-`n` locus.
* `WeierstrassCurve.deltaP_I_two_eq_of_even`: `δ_p((Iₙ, 2)) = 2N² p^{-(n+2)} T` for even `n ≥ 4`.
* `WeierstrassCurve.tsum_deltaP_I_even_two_eq`: the sum of the even multiplicative rows.
* `WeierstrassCurve.δ_two_eq_add_tsum`: `δ_p(2)` as a sum of rows.
* `WeierstrassCurve.δ_two_eq_ofReal_add_tsum_Istar`:
  `δ_p(2) = gotHeadTwoEvaluated p + ∑_{n} δ_p((Iₙ*, 2))`.
* `WeierstrassCurve.gotHeadTwoEvaluated_add_eq_gotδ_two`:
  `gotHeadTwoEvaluated p + gotIStarTwoTotal p = gotδ p 2`.
* `WeierstrassCurve.δ_two_eq_ofReal_gotδ_iff`: `δ_p(2) = gotδ p 2` iff
  `∑_{n} δ_p((Iₙ*, 2)) = gotIStarTwoTotal p`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Table 5.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Points of an `Iₙ` stratum with `p ∣ a₄` are dilates -/

/-- For `p ≥ 5`, a point of a stratum `τ_p⁻¹((Iₙ, c))` whose model has `p ∣ Δ` and `p ∣ a₄` is a
dilate. -/
private theorem mem_range_of_dvd_fst_of_dvd_Δ (hp : 5 ≤ p) {n c : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ stratFibre p (KodairaSymbol.I n, c))
    (hd : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ) (h4 : (p : ℤ_[p]) ∣ x.1) :
    x ∈ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
  have hstrat : strat p ⟨x, hUp⟩ = (KodairaSymbol.I n, c) := (mem_stratFibre_iff hUp).1 hx
  have hkod : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I n := by
    rw [strat] at hstrat
    exact congrArg Prod.fst hstrat
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
    rw [ofShortNF_c₄]
    exact h4.mul_left _
  obtain ⟨h4', h6'⟩ := TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I
    PadicInt.uniformizer_ne_zero hUp hd hc₄ hkod
  rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4'
  rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6'
  exact PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨h4', h6'⟩

/-! ### The degenerate member `(I₀, 2)` -/

/-- For every prime `p ≥ 5`, the stratum `τ_p⁻¹((I₀, 2))` has no minimal point:

  `τ_p⁻¹((I₀, 2)) ∖ σ_p(ℤ_p²) = ∅`. -/
theorem stratFibre_diff_range_I_zero_two_eq_empty (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.I 0, 2) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨hxF, hxR⟩
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  have hs := (mem_stratFibre_iff hUp).1 hxF
  rw [strat] at hs
  have hκ : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
      = KodairaSymbol.I 0 := congrArg Prod.fst hs
  have hc : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).tamagawaNumber
      = 2 := congrArg Prod.snd hs
  by_cases hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ
  · by_cases hc₄ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄
    · refine hxR (mem_range_of_dvd_fst_of_dvd_Δ hp hxF hpΔ ?_)
      rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hc₄
    · rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄] at hκ
      have h0 : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((0 : ℕ) : ℕ∞) :=
        (toNat_emultiplicity_Δ_eq_iff hUp 0).1 (KodairaSymbol.I.inj hκ)
      rw [Nat.cast_zero, emultiplicity_eq_zero] at h0
      exact h0 hpΔ
  · rw [run_eq_of_not_dvd_Δ hUp hpΔ] at hc
    exact absurd hc (by norm_num)

/-- For every prime `p ≥ 5`, `δ_p((I₀, 2)) = 0`. -/
theorem deltaP_I_zero_two_eq_zero (hp : 5 ≤ p) : deltaP p (KodairaSymbol.I 0, 2) = 0 := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_I_zero_two_eq_empty hp, measure_empty,
    zero_mul]

/-! ### The non-split even `Iₙ` rows -/

/-- For `p ≥ 5` and even `n ≥ 1`, the non-split level-`n` locus lies in the stratum
`τ_p⁻¹((Iₙ, 2))`. -/
theorem iNonSplitLocus_subset_stratFibre_two (hp : 5 ≤ p) {n : ℕ} (hn : 1 ≤ n) (heven : Even n) :
    iNonSplitLocus p n ⊆ stratFibre p (KodairaSymbol.I n, 2) := by
  have hoddp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  intro x hx
  obtain ⟨hxL, hns⟩ := hx
  have hUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_of_mem_iLocus hp hxL
  have hΔv := emultiplicity_Δ_of_mem_iLocus hp hxL
  have hc₄ := not_dvd_c₄_of_mem_iLocus hp hxL
  have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := dvd_Δ_of_emultiplicity_eq hn hΔv
  have htoNat : (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat = n :=
    (toNat_emultiplicity_Δ_eq_iff hUp n).2 hΔv
  have hnosplit : ¬ Step2.TangentSplits (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    intro hsplit
    have hsq := (Step2.tangentSplits_iff_isSquare_neg_c₆ hpΔ hc₄
      (not_dvd_two_of_odd hoddp)).1 hsplit
    rw [ofShortNF_c₆, show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 by ring,
      isSquare_mod_iff_isSquare_toZMod] at hsq
    exact hns hsq
  have hκ : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
      = KodairaSymbol.I n := by
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄, htoNat]
  have hc : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).tamagawaNumber
      = 2 := by
    rw [run_tamagawaNumber_of_nodal hUp hpΔ hc₄, htoNat, ite_eq_right hnosplit,
      ite_eq_right (Nat.not_odd_iff_even.2 heven)]
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-- For every prime `p ≥ 5` and every even `n ≥ 4`, the minimal part of the stratum
`τ_p⁻¹((Iₙ, 2))` is the non-split level-`n` locus:

  `τ_p⁻¹((Iₙ, 2)) ∖ σ_p(ℤ_p²) = {p ∤ a₄, v_p(4a₄³ + 27a₆²) = n, 864a₆ a non-square mod p}`.

The hypothesis `n ≥ 4` cannot be relaxed to `n ≥ 2`: at `n = 2` the split branch also reports `2`,
and the minimal part is the whole level-2 locus. -/
theorem stratFibre_diff_range_eq_iNonSplitLocus_even (hp : 5 ≤ p) {n : ℕ} (hn : 4 ≤ n)
    (heven : Even n) :
    stratFibre p (KodairaSymbol.I n, 2) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = iNonSplitLocus p n := by
  have hoddp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have hs := (mem_stratFibre_iff hUp).1 hxF
    rw [strat] at hs
    have hκ : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
        = KodairaSymbol.I n := congrArg Prod.fst hs
    have hc : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).tamagawaNumber
        = 2 := congrArg Prod.snd hs
    have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
      by_contra hnd
      rw [run_eq_of_not_dvd_Δ hUp hnd] at hκ
      exact absurd (KodairaSymbol.I.inj hκ) (by omega)
    have h4 : ¬ (p : ℤ_[p]) ∣ x.1 := fun hdvd =>
      hxR (mem_range_of_dvd_fst_of_dvd_Δ hp hxF hpΔ hdvd)
    have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
      rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
      exact h4
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄] at hκ
    have htoNat : (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat = n :=
      KodairaSymbol.I.inj hκ
    have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((n : ℕ) : ℕ∞) :=
      (toNat_emultiplicity_Δ_eq_iff hUp n).1 htoNat
    rw [run_tamagawaNumber_of_nodal hUp hpΔ hc₄, htoNat] at hc
    have hnosplit : ¬ Step2.TangentSplits (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
      intro hsplit
      rw [ite_eq_left hsplit] at hc
      omega
    have hns : ¬ IsSquare (PadicInt.toZMod (864 * x.2)) := by
      intro hsq
      refine hnosplit ((Step2.tangentSplits_iff_isSquare_neg_c₆ hpΔ hc₄
        (not_dvd_two_of_odd hoddp)).2 ?_)
      rw [ofShortNF_c₆, show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 by ring,
        isSquare_mod_iff_isSquare_toZMod]
      exact hsq
    rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add] at hΔv
    exact ⟨⟨h4, hΔv⟩, hns⟩
  · intro x hx
    refine ⟨iNonSplitLocus_subset_stratFibre_two hp (by omega) heven hx, fun hr => ?_⟩
    exact hx.1.1 (dvd_trans (dvd_pow_self _ (by norm_num : 4 ≠ 0))
      (PadicInt.mem_range_scaleProdByPPow_iff.1 hr).1)

/-- For every prime `p ≥ 5` and every even `n ≥ 4`,

  `δ_p((Iₙ, 2)) = 2N² p^{-(n+2)} (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)²p^{8-n}/(2(p¹⁰-1))`. -/
theorem deltaP_I_two_eq_of_even (hp : 5 ≤ p) {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    deltaP p (KodairaSymbol.I n, 2)
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (n + 2)
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_iNonSplitLocus_even hp hn heven,
    ← iFineLocus_false, volume_iFineLocus_eq hp (by omega)]

/-! ### The even multiplicative family, summed -/

/-- For every prime `p ≥ 5`,

  `∑_{n ≥ 0} δ_p((I_{2n}, 2)) = 4N² p⁻⁴ T + 2N² p⁻⁶ T (1 - p⁻²)⁻¹`,   `T = (1 - p⁻¹⁰)⁻¹`,

`2N = p - 1`. In closed form the total is `(p-1)²p⁶/(p¹⁰-1) + (p-1)²p⁴/(2(p²-1)(p¹⁰-1))`. -/
theorem tsum_deltaP_I_even_two_eq (hp : 5 ≤ p) :
    ∑' n : ℕ, deltaP p (KodairaSymbol.I (2 * n), 2)
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 4
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
        + 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 6
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ * (1 - ((p : ℝ≥0∞)⁻¹) ^ 2)⁻¹ := by
  have h0 : deltaP p (KodairaSymbol.I (2 * 0), 2) = 0 := by
    rw [show (2 * 0 : ℕ) = 0 from by norm_num]
    exact deltaP_I_zero_two_eq_zero hp
  have h1 : deltaP p (KodairaSymbol.I (2 * (0 + 1)), 2)
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 4
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
    rw [show (2 * (0 + 1) : ℕ) = 2 from by norm_num]
    exact deltaP_I_two_eq hp
  have hstep : ∀ k : ℕ, deltaP p (KodairaSymbol.I (2 * (k + 1 + 1)), 2)
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 6
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ * (((p : ℝ≥0∞)⁻¹) ^ 2) ^ k := by
    intro k
    rw [deltaP_I_two_eq_of_even hp (by omega) ⟨k + 2, by ring⟩,
      show 2 * (k + 1 + 1) + 2 = 6 + 2 * k from by ring, pow_add, pow_mul]
    ring
  rw [tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable, h0, zero_add, h1,
    tsum_congr hstep, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-! ### `δ_p(2)` as a sum of rows -/

/-- The `Iₙ*` part of the fibre `{c = 2}` is measurable. -/
theorem measurableSet_iUnion_stratFibre_Istar_two :
    MeasurableSet (⋃ n : ℕ, stratFibre p (KodairaSymbol.I! n, 2)) :=
  MeasurableSet.iUnion fun n =>
    (isOpen_stratFibre (p := p) (KodairaSymbol.I! n, 2)).measurableSet

/-- The even multiplicative part of `{c = 2}` has mass `∑_n δ_p((I_{2n}, 2))`. -/
theorem volume_iUnion_stratFibre_I_even_two :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (⋃ n : ℕ, stratFibre p (KodairaSymbol.I (2 * n), 2))
      = ∑' n : ℕ, deltaP p (KodairaSymbol.I (2 * n), 2) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => stratFibre p (KodairaSymbol.I (2 * n), 2))) := by
    intro i j hij
    refine disjoint_stratFibre_of_ne (fun h => hij ?_) 2 2
    have := KodairaSymbol.I.inj h
    omega
  rw [measure_iUnion hdisj fun n =>
    (isOpen_stratFibre (p := p) (KodairaSymbol.I (2 * n), 2)).measurableSet]
  exact tsum_congr fun n => volume_stratFibre _

/-- The `Iₙ*` part of `{c = 2}` has mass `∑_n δ_p((Iₙ*, 2))`. -/
theorem volume_iUnion_stratFibre_Istar_two :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (⋃ n : ℕ, stratFibre p (KodairaSymbol.I! n, 2))
      = ∑' n : ℕ, deltaP p (KodairaSymbol.I! n, 2) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => stratFibre p (KodairaSymbol.I! n, 2))) := by
    intro i j hij
    exact disjoint_stratFibre_of_ne (fun h => hij (KodairaSymbol.I!.inj h)) 2 2
  rw [measure_iUnion hdisj fun n =>
    (isOpen_stratFibre (p := p) (KodairaSymbol.I! n, 2)).measurableSet]
  exact tsum_congr fun n => volume_stratFibre _

/-- `δ_p(2)` is the sum of the rows of the fibre `{c = 2}`:

  `δ_p(2) = ∑_{n} δ_p((I_{2n}, 2)) + δ_p((III, 2)) + ∑_{n} δ_p((Iₙ*, 2)) + δ_p((III*, 2))`. -/
theorem δ_two_eq_add_tsum :
    δ p 2 = ∑' n : ℕ, deltaP p (KodairaSymbol.I (2 * n), 2) + deltaP p (KodairaSymbol.III, 2)
        + ∑' n : ℕ, deltaP p (KodairaSymbol.I! n, 2)
      + deltaP p (KodairaSymbol.III!, 2) := by
  have dAB : Disjoint (⋃ n : ℕ, stratFibre p (KodairaSymbol.I (2 * n), 2))
      (stratFibre p (KodairaSymbol.III, 2)) :=
    Set.disjoint_iUnion_left.2 fun n => disjoint_stratFibre_of_ne (by simp) 2 2
  have dAC : Disjoint (⋃ n : ℕ, stratFibre p (KodairaSymbol.I (2 * n), 2))
      (⋃ n : ℕ, stratFibre p (KodairaSymbol.I! n, 2)) :=
    Set.disjoint_iUnion_left.2 fun n =>
      Set.disjoint_iUnion_right.2 fun m => disjoint_stratFibre_of_ne (by simp) 2 2
  have dAD : Disjoint (⋃ n : ℕ, stratFibre p (KodairaSymbol.I (2 * n), 2))
      (stratFibre p (KodairaSymbol.III!, 2)) :=
    Set.disjoint_iUnion_left.2 fun n => disjoint_stratFibre_of_ne (by simp) 2 2
  have dBC : Disjoint (stratFibre p (KodairaSymbol.III, 2))
      (⋃ n : ℕ, stratFibre p (KodairaSymbol.I! n, 2)) :=
    Set.disjoint_iUnion_right.2 fun m => disjoint_stratFibre_of_ne (by simp) 2 2
  have dBD : Disjoint (stratFibre p (KodairaSymbol.III, 2))
      (stratFibre p (KodairaSymbol.III!, 2)) := disjoint_stratFibre_of_ne (by simp) 2 2
  have dCD : Disjoint (⋃ n : ℕ, stratFibre p (KodairaSymbol.I! n, 2))
      (stratFibre p (KodairaSymbol.III!, 2)) :=
    Set.disjoint_iUnion_left.2 fun n => disjoint_stratFibre_of_ne (by simp) 2 2
  rw [← volume_iUnion_stratFibre_kodaira (p := p) 2, iUnion_stratFibre_two_eq,
    measure_union ((dAD.union_left dBD).union_left dCD)
      (isOpen_stratFibre (p := p) (KodairaSymbol.III!, 2)).measurableSet,
    measure_union (dAC.union_left dBC) measurableSet_iUnion_stratFibre_Istar_two,
    measure_union dAB (isOpen_stratFibre (p := p) (KodairaSymbol.III, 2)).measurableSet,
    volume_iUnion_stratFibre_I_even_two, volume_stratFibre,
    volume_iUnion_stratFibre_Istar_two, volume_stratFibre]

/-- The `Iₙ*` total of `{c = 2}` is the `I₀*` row plus the sum of the `Iₙ*` rows with `n ≥ 1`. -/
theorem tsum_deltaP_Istar_two_eq_add :
    ∑' n : ℕ, deltaP p (KodairaSymbol.I! n, 2)
      = deltaP p (KodairaSymbol.I! 0, 2) + ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2) :=
  tsum_eq_zero_add' ENNReal.summable

/-! ### The real closed forms -/

variable (p) in
/-- The sum of the table values of the rows `(I₂, 2)`, `(III, 2)`, the non-split even `(Iₙ, 2)`
for `n ≥ 4`, and `(III*, 2)`, as a real number:

  `((p-1)²/p⁴ + (p-1)/p⁴ + (p-1)/(2p⁴(p+1)) + (p-1)/p⁹) T`,   `T = (1 - p⁻¹⁰)⁻¹`.

The third summand is the total `∑_{k ≥ 2} (p-1)²/(2p^{2k+2})` of the non-split even rows. Only
`p ≥ 5` is meaningful. -/
noncomputable def gotHeadTwoEvaluated : ℝ :=
  (((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 4 + ((p : ℝ) - 1) / (p : ℝ) ^ 4
      + ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 4 * ((p : ℝ) + 1)) + ((p : ℝ) - 1) / (p : ℝ) ^ 9)
    * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

variable (p) in
/-- The table value `((p²-1)/(2p⁷)) (1 - p⁻¹⁰)⁻¹` of the whole `Iₙ*` contribution to `δ_p(2)` at
`p ≥ 5`. -/
noncomputable def gotIStarTwoTotal : ℝ :=
  ((p : ℝ) ^ 2 - 1) / (2 * (p : ℝ) ^ 7) * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

variable (p) in
/-- The table value `(p(p-1)/2) p⁻⁷ (1 - p⁻¹⁰)⁻¹` of the row `(I₀*, 2)` at `p ≥ 5`. The numerator
`p(p-1)/2` counts the depressed cubics `x³ + Ax + B` over `𝔽_p` with exactly one root in `𝔽_p`. -/
noncomputable def gotIZeroStarTwo : ℝ :=
  (p : ℝ) * ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 7) * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

variable (p) in
/-- The table value `((p-1)/2) p⁻⁷ (1 - p⁻¹⁰)⁻¹` of the non-split `Iₙ*` family, `n ≥ 1`, at
`p ≥ 5`. -/
noncomputable def gotInStarTwo : ℝ :=
  ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 7) * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

omit [Fact p.Prime] in
/-- For every `p ≥ 5`,

  `gotIZeroStarTwo p + gotInStarTwo p = gotIStarTwoTotal p`. -/
theorem gotIZeroStarTwo_add_gotInStarTwo_eq (hp : 5 ≤ p) :
    gotIZeroStarTwo p + gotInStarTwo p = gotIStarTwoTotal p := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  rw [gotIZeroStarTwo, gotInStarTwo, gotIStarTwoTotal]
  field_simp
  ring

omit [Fact p.Prime] in
private theorem inv_one_sub_inv_pow_eq {x : ℝ} (hx : x ≠ 0) (k : ℕ) :
    (1 - x⁻¹ ^ k)⁻¹ = x ^ k / (x ^ k - 1) := by
  rw [inv_pow, ← inv_div]
  congr 1
  field_simp

omit [Fact p.Prime] in
private theorem one_sub_inv_pow_pos (hp : 5 ≤ p) {k : ℕ} (hk : k ≠ 0) :
    (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ k :=
  sub_pos.2 <| pow_lt_one₀ (by positivity)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))) hk

private theorem one_sub_inv_pow_eq_ofReal (k : ℕ) :
    (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ k = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ k) := by
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos), ENNReal.ofReal_natCast]

/-- For `p ≥ 5`, the four evaluated `c = 2` rows of `δ_p(2)`, written with `N = #goodRes p` and
`T = (1 - p⁻¹⁰)⁻¹`, sum to `gotHeadTwoEvaluated p`. -/
theorem rows_add_eq_gotHeadTwoEvaluated (hp : 5 ≤ p) :
    4 * ((goodRes p).card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 4 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
        + 2 * ((goodRes p).card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 6 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
          * (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
        + 2 * ((goodRes p).card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
        + 2 * ((goodRes p).card : ℝ) * ((p : ℝ)⁻¹) ^ 9 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
      = gotHeadTwoEvaluated p := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hN : ((goodRes p).card : ℝ) = ((p : ℝ) - 1) / 2 := by
    have := congrArg (Nat.cast : ℕ → ℝ) (eq_two_mul_card_goodRes_add_one hp)
    push_cast at this
    linarith
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hnep1 : (p : ℝ) + 1 ≠ 0 := by linarith
  have hne10 : (p : ℝ) ^ 10 - 1 ≠ 0 := by
    linarith [one_lt_pow₀ (by linarith : (1 : ℝ) < p) (by norm_num : 10 ≠ 0)]
  have hne2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [gotHeadTwoEvaluated, hN, inv_one_sub_inv_pow_eq hne, inv_one_sub_inv_pow_eq hne]
  field_simp
  ring

/-- For `p ≥ 5`, the four evaluated `c = 2` rows of `δ_p(2)`, summed in `ℝ≥0∞`, give
`ENNReal.ofReal (gotHeadTwoEvaluated p)`. -/
theorem ofReal_rows_add_eq_ofReal_gotHeadTwoEvaluated (hp : 5 ≤ p) :
    ENNReal.ofReal (4 * ((goodRes p).card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 4 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
        + ENNReal.ofReal (2 * ((goodRes p).card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 6
          * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ * (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹)
        + ENNReal.ofReal (2 * ((goodRes p).card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
        + ENNReal.ofReal (2 * ((goodRes p).card : ℝ) * ((p : ℝ)⁻¹) ^ 9 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
      = ENNReal.ofReal (gotHeadTwoEvaluated p) := by
  have hT := (inv_pos.2 (one_sub_inv_pow_pos hp (k := 10) (by norm_num))).le
  have hT₂ := (inv_pos.2 (one_sub_inv_pow_pos hp (k := 2) (by norm_num))).le
  have h₁ := mul_nonneg
    (by positivity : (0 : ℝ) ≤ 4 * ((goodRes p).card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 4) hT
  have h₂ := mul_nonneg (mul_nonneg
    (by positivity : (0 : ℝ) ≤ 2 * ((goodRes p).card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 6) hT) hT₂
  have h₃ := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((goodRes p).card : ℝ) * ((p : ℝ)⁻¹) ^ 4) hT
  have h₄ := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((goodRes p).card : ℝ) * ((p : ℝ)⁻¹) ^ 9) hT
  rw [← ENNReal.ofReal_add h₁ h₂, ← ENNReal.ofReal_add (add_nonneg h₁ h₂) h₃,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg h₁ h₂) h₃) h₄, rows_add_eq_gotHeadTwoEvaluated hp]

omit [Fact p.Prime] in
/-- For every `p ≥ 5`,

  `gotHeadTwoEvaluated p + gotIStarTwoTotal p = gotδ p 2`. -/
theorem gotHeadTwoEvaluated_add_eq_gotδ_two (hp : 5 ≤ p) :
    gotHeadTwoEvaluated p + gotIStarTwoTotal p = gotδ p 2 := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hnep1 : (p : ℝ) + 1 ≠ 0 := by linarith
  have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
  have hne10 : (p : ℝ) ^ 10 - 1 ≠ 0 := by linarith
  have hneQ : (p : ℝ) ^ 8 + (p : ℝ) ^ 6 + (p : ℝ) ^ 4 + (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  rw [gotHeadTwoEvaluated, gotIStarTwoTotal, gotδ_two_of_five_le hp, gotD, gotQ,
    inv_one_sub_inv_pow_eq hne]
  field_simp
  ring

/-! ### `δ_p(2)` reduced to the `Iₙ*` family -/

/-- For every prime `p ≥ 5`,

  `δ_p(2) = gotHeadTwoEvaluated p + ∑_{n} δ_p((Iₙ*, 2))`. -/
theorem δ_two_eq_ofReal_add_tsum_Istar (hp : 5 ≤ p) :
    δ p 2 = ENNReal.ofReal (gotHeadTwoEvaluated p)
      + ∑' n : ℕ, deltaP p (KodairaSymbol.I! n, 2) := by
  have hpos10 := one_sub_inv_pow_pos hp (k := 10) (by norm_num)
  have hpos2 := one_sub_inv_pow_pos hp (k := 2) (by norm_num)
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos),
      ENNReal.ofReal_natCast]
  have key : ∀ (c : ℝ) (k : ℕ), 0 ≤ c →
      ENNReal.ofReal c * ((p : ℝ≥0∞)⁻¹) ^ k * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
        = ENNReal.ofReal (c * ((p : ℝ)⁻¹) ^ k * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
    intro c k hc
    rw [one_sub_inv_pow_eq_ofReal, ← ENNReal.ofReal_inv_of_pos hpos10, hinvE,
      ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]
  have key2 : ∀ (c : ℝ) (k : ℕ), 0 ≤ c →
      ENNReal.ofReal c * ((p : ℝ≥0∞)⁻¹) ^ k * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 2)⁻¹
        = ENNReal.ofReal (c * ((p : ℝ)⁻¹) ^ k * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
            * (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹) := by
    intro c k hc
    rw [key c k hc, one_sub_inv_pow_eq_ofReal, ← ENNReal.ofReal_inv_of_pos hpos2,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc (by positivity)) (inv_pos.2 hpos10).le)]
  have hc4N2 : (4 : ℝ≥0∞) * ((goodRes p).card : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (4 * ((goodRes p).card : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have hc2N2 : (2 : ℝ≥0∞) * ((goodRes p).card : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (2 * ((goodRes p).card : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have hc2N : (2 : ℝ≥0∞) * ((goodRes p).card : ℝ≥0∞)
      = ENNReal.ofReal (2 * ((goodRes p).card : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [δ_two_eq_add_tsum, add_right_comm, tsum_deltaP_I_even_two_eq hp, deltaP_III_eq hp,
    deltaP_IIIstar_two_eq hp, hc4N2, key _ 4 (by positivity), hc2N2, key2 _ 6 (by positivity),
    hc2N, key _ 4 (by positivity), key _ 9 (by positivity),
    ofReal_rows_add_eq_ofReal_gotHeadTwoEvaluated hp]

/-- For every prime `p ≥ 5`,

  `δ_p(2) = ENNReal.ofReal (gotδ p 2)` ↔ `∑_{n} δ_p((Iₙ*, 2)) = ENNReal.ofReal (((p²-1)/(2p⁷))T)`.
-/
theorem δ_two_eq_ofReal_gotδ_iff (hp : 5 ≤ p) :
    δ p 2 = ENNReal.ofReal (gotδ p 2) ↔
      ∑' n : ℕ, deltaP p (KodairaSymbol.I! n, 2) = ENNReal.ofReal (gotIStarTwoTotal p) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hTr := inv_pos.2 (one_sub_inv_pow_pos hp (k := 10) (by norm_num))
  have hE : (0 : ℝ) ≤ gotHeadTwoEvaluated p := by
    rw [gotHeadTwoEvaluated]
    refine mul_nonneg ?_ hTr.le
    have e1 : (0 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 4 := by positivity
    have e2 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 4 := div_nonneg hp1 (by positivity)
    have e3 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 4 * ((p : ℝ) + 1)) :=
      div_nonneg hp1 (by positivity)
    have e4 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 9 := div_nonneg hp1 (by positivity)
    linarith
  have hS : (0 : ℝ) ≤ gotIStarTwoTotal p := by
    rw [gotIStarTwoTotal]
    exact mul_nonneg (div_nonneg (by nlinarith) (by positivity)) hTr.le
  rw [δ_two_eq_ofReal_add_tsum_Istar hp, ← gotHeadTwoEvaluated_add_eq_gotδ_two hp,
    ENNReal.ofReal_add hE hS, ENNReal.add_right_inj ENNReal.ofReal_ne_top]

end WeierstrassCurve
