/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.PrimeCount.Moments
public import BSDTamagawa.FactorCount.LawProbability
public import BSDTamagawa.Covariance.JointLaw

/-!
# The joint limiting law of `(ω_Tam, Ω(Tam))` is a probability measure

The joint limiting density `π(r, b)` of the pair `(ω_Tam(E), Ω(Tam(E)))` has total mass exactly
`1`, and it defines a probability measure on `ℤ_{≥0}²` whose marginals are the limiting laws of
`ω_Tam` and of `Ω(Tam)`. Since `ω_Tam(E) ≤ Ω(Tam(E))`, the density vanishes for `b < r`, so each
sum over `r` at fixed `b` is finite and no boundary analysis of the generating function is needed.

## Main definitions

* `WeierstrassCurve.jointOmegaCardFactorsPMF`: the joint law as a `PMF (ℕ × ℕ)`.

## Main results

* `WeierstrassCurve.tamagawaOmega_le_cardFactors_tamagawaProduct`: `ω_Tam(E) ≤ Ω(Tam(E))`.
* `WeierstrassCurve.tsum_jointOmegaCardFactorsDensity_eq_one`: `∑_{(r,b)} π(r, b) = 1`.
* `WeierstrassCurve.isProbabilityMeasure_jointOmegaCardFactorsMeasure`: the joint law `P_joint` on
  `ℤ_{≥0}²` is a probability measure.
* `WeierstrassCurve.map_fst_jointOmegaCardFactorsMeasure`,
  `WeierstrassCurve.map_snd_jointOmegaCardFactorsMeasure`: the two marginals are
  `tamagawaOmegaMeasure` and `cardFactorsTamagawaMeasure`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open MeasureTheory
open BSDTamagawa.FiberCount BSDTamagawa.PrimeCountDensity

/-! ### §1. `ω_Tam(E) ≤ Ω(Tam(E))` -/

/-- **`ω_Tam(E) ≤ Ω(Tam(E))`.** The number of primes at which the local Tamagawa number exceeds `1`
is at most the number of prime factors of `Tam(E)` counted with multiplicity. -/
theorem tamagawaOmega_le_cardFactors_tamagawaProduct (a₄ a₆ : ℤ) :
    tamagawaOmega a₄ a₆ ≤ ArithmeticFunction.cardFactors (tamagawaProduct a₄ a₆) := by
  obtain ⟨S, hS, hSω⟩ := exists_finset_truncatedTamagawaOmega_eq a₄ a₆
  rw [← hSω, ← truncatedTamagawaCardFactors_eq hS, truncatedTamagawaOmega,
    truncatedTamagawaCardFactors]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : 1 < localTamagawaNumber p a₄ a₆
  · rw [ite_eq_left hp]
    exact ArithmeticFunction.cardFactors_pos_iff_one_lt.2 hp
  · rw [ite_eq_right hp]
    exact Nat.zero_le _

/-! ### §2. Summing out `r`: the `Ω(Tam)`-marginal -/

/-- **Above the diagonal the joint fibre is empty**: no curve has `ω_Tam(E) = r > b = Ω(Tam(E))`.
-/
lemma setOf_jointOmegaCardFactors_eq_empty_of_lt {r b : ℕ} (h : b < r) (X : ℝ) :
    {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
      tamagawaOmega q.1 q.2 = r ∧
        ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun q hq => ?_
  have hle := tamagawaOmega_le_cardFactors_tamagawaProduct q.1 q.2
  rw [hq.2.2.1, hq.2.2.2] at hle
  omega

/-- **The joint proportion vanishes above the diagonal.** -/
lemma jointOmegaCardFactorsProportion_eq_zero_of_lt {r b : ℕ} (h : b < r) (X : ℝ) :
    jointOmegaCardFactorsProportion r b X = 0 := by
  rw [jointOmegaCardFactorsProportion, setOf_jointOmegaCardFactors_eq_empty_of_lt h X]
  simp

/-- **The joint density vanishes above the diagonal.** -/
lemma jointOmegaCardFactorsDensity_eq_zero_of_lt {r b : ℕ} (h : b < r) :
    jointOmegaCardFactorsDensity r b = 0 := by
  refine tendsto_nhds_unique
    (tendsto_jointOmegaCardFactorsProportion_jointOmegaCardFactorsDensity r b) ?_
  simp only [jointOmegaCardFactorsProportion_eq_zero_of_lt h]
  exact tendsto_const_nhds

/-- **The fibre partition at a fixed `b`, at finite `X`.**

`∑_{r ≤ b} π(r, b; X) = #{E : Ht(E) ≤ X, Δ ≠ 0, Ω(Tam(E)) = b} / N(X)`,

for `X ≥ 0`, the right side being the proportion `ρ_b(X)`. -/
lemma sum_range_jointOmegaCardFactorsProportion (b : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ r ∈ Finset.range (b + 1), jointOmegaCardFactorsProportion r b X
      = ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b}.ncard : ℝ) /
        integralShortNFCount X := by
  classical
  set S : Set (ℤ × ℤ) := {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
    q ∈ integralShortNFFamily ∧
      ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b} with hSdef
  have hSfin : S.Finite :=
    (finite_setOf_height_le_and_mem_family hX).subset fun q hq => ⟨hq.1, hq.2.1⟩
  have hfib : ∀ r : ℕ, {q : ℤ × ℤ | q ∈ S ∧ tamagawaOmega q.1 q.2 = r} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
        tamagawaOmega q.1 q.2 = r ∧
          ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b} := by
    intro r
    exact Set.ext fun q => by simp only [hSdef, Set.mem_ofPred_eq]; tauto
  have hzero : ∀ r ∉ Finset.range (b + 1),
      ({q : ℤ × ℤ | q ∈ S ∧ tamagawaOmega q.1 q.2 = r}.ncard : ℝ) = 0 := by
    intro r hr
    have hbr : b < r := by simpa [Finset.mem_range] using hr
    rw [hfib r, setOf_jointOmegaCardFactors_eq_empty_of_lt hbr X]
    simp
  have hfin : ∑ r ∈ Finset.range (b + 1),
      ({q : ℤ × ℤ | q ∈ S ∧ tamagawaOmega q.1 q.2 = r}.ncard : ℝ) = (S.ncard : ℝ) := by
    have h1 : ∑' r : ℕ, ({q : ℤ × ℤ | q ∈ S ∧ tamagawaOmega q.1 q.2 = r}.ncard : ℝ)
        = ∑ r ∈ Finset.range (b + 1),
          ({q : ℤ × ℤ | q ∈ S ∧ tamagawaOmega q.1 q.2 = r}.ncard : ℝ) := tsum_eq_sum hzero
    rw [← h1]
    exact tsum_ncard_fiber hSfin fun q : ℤ × ℤ => tamagawaOmega q.1 q.2
  have hterm : ∀ r : ℕ, jointOmegaCardFactorsProportion r b X
      = ({q : ℤ × ℤ | q ∈ S ∧ tamagawaOmega q.1 q.2 = r}.ncard : ℝ) /
        integralShortNFCount X :=
    fun r => by rw [jointOmegaCardFactorsProportion, hfib r]
  simp only [hterm]
  rw [← Finset.sum_div, hfin]

/-- **The `Ω(Tam)`-marginal of the joint density is the density `ρ_b` of `Ω(Tam) = b`.**

`∑_{r ≤ b} π(r, b) = ρ_b`. -/
theorem sum_range_jointOmegaCardFactorsDensity (b : ℕ) :
    ∑ r ∈ Finset.range (b + 1), jointOmegaCardFactorsDensity r b
      = cardFactorsTamagawaDensity b := by
  refine tendsto_nhds_unique
    (tendsto_finsetSum (Finset.range (b + 1)) fun r _ =>
      tendsto_jointOmegaCardFactorsProportion_jointOmegaCardFactorsDensity r b) ?_
  refine (tendsto_cardFactorsTamagawaProportion_cardFactorsTamagawaDensity b).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  exact (sum_range_jointOmegaCardFactorsProportion b hX).symm

/-- **The `Ω(Tam)`-marginal, as a `tsum`.** `∑'_r π(r, b) = ρ_b`. -/
theorem tsum_jointOmegaCardFactorsDensity_left (b : ℕ) :
    ∑' r : ℕ, jointOmegaCardFactorsDensity r b = cardFactorsTamagawaDensity b := by
  have hzero : ∀ r ∉ Finset.range (b + 1), jointOmegaCardFactorsDensity r b = 0 := fun r hr =>
    jointOmegaCardFactorsDensity_eq_zero_of_lt (by simpa [Finset.mem_range] using hr)
  rw [tsum_eq_sum hzero]
  exact sum_range_jointOmegaCardFactorsDensity b

/-! ### §3. The total mass -/

/-- **The equivalence `(Bool →₀ ℕ) ≃ ℕ × ℕ`**, `𝐣 ↦ (j false, j true)`. -/
noncomputable def boolFinsuppEquivProd : (Bool →₀ ℕ) ≃ ℕ × ℕ where
  toFun j := (j false, j true)
  invFun rb := omegaCardFactorsMulti rb.1 rb.2
  left_inv j := by
    refine Finsupp.ext fun i => ?_
    cases i <;> simp
  right_inv rb := by simp

/-- **The joint density is summable over `ℤ_{≥0}²`.** -/
theorem summable_jointOmegaCardFactorsDensity :
    Summable fun rb : ℕ × ℕ => jointOmegaCardFactorsDensity rb.1 rb.2 :=
  boolFinsuppEquivProd.summable_iff.mp
    hasPolydiscExpansion_jointOmegaCardFactorsDensity.2.1

/-- **The joint density is nonnegative.** -/
theorem jointOmegaCardFactorsDensity_nonneg (r b : ℕ) :
    0 ≤ jointOmegaCardFactorsDensity r b :=
  (hasPolydiscExpansion_jointOmegaCardFactorsDensity.1 (omegaCardFactorsMulti r b)).1

/-- **The total mass of the joint density is `1`.**

`∑_{(r,b) ∈ ℤ_{≥0}²} π(r, b) = 1`.

No mass escapes to infinity. -/
theorem tsum_jointOmegaCardFactorsDensity_eq_one :
    ∑' rb : ℕ × ℕ, jointOmegaCardFactorsDensity rb.1 rb.2 = 1 := by
  have hsw : Summable fun br : ℕ × ℕ => jointOmegaCardFactorsDensity br.2 br.1 :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr summable_jointOmegaCardFactorsDensity
  have hswap : ∑' rb : ℕ × ℕ, jointOmegaCardFactorsDensity rb.1 rb.2
      = ∑' br : ℕ × ℕ, jointOmegaCardFactorsDensity br.2 br.1 :=
    ((Equiv.prodComm ℕ ℕ).tsum_eq
      fun rb : ℕ × ℕ => jointOmegaCardFactorsDensity rb.1 rb.2).symm
  rw [hswap, hsw.tsum_prod]
  simp only [tsum_jointOmegaCardFactorsDensity_left]
  exact tsum_cardFactorsTamagawaDensity_eq_one

/-! ### §4. Summing out `b`: the `ω_Tam`-marginal -/

/-- **Every finite partial `Ω(Tam)`-sum of the joint proportion is at most `π_r(X)`**, the
proportion of curves with `ω_Tam(E) = r`. -/
lemma sum_jointOmegaCardFactorsProportion_le_tamagawaOmegaProportion (r : ℕ) (s : Finset ℕ)
    {X : ℝ} (hX : 0 ≤ X) :
    ∑ b ∈ s, jointOmegaCardFactorsProportion r b X ≤ tamagawaOmegaProportion r X := by
  classical
  set A : Set (ℤ × ℤ) := {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
    q ∈ integralShortNFFamily ∧ tamagawaOmega q.1 q.2 = r} with hAdef
  have hAfin : A.Finite :=
    (finite_setOf_height_le_and_mem_family hX).subset fun q hq => ⟨hq.1, hq.2.1⟩
  have hfib : ∀ b : ℕ,
      {q : ℤ × ℤ | q ∈ A ∧ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b} =
        {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          tamagawaOmega q.1 q.2 = r ∧
            ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b} := fun b =>
    Set.ext fun q => by simp only [hAdef, Set.mem_ofPred_eq]; tauto
  have hsum : Summable fun b : ℕ =>
      ({q : ℤ × ℤ | q ∈ A ∧
        ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b}.ncard : ℝ) := by
    refine summable_of_hasFiniteSupport ((finite_setOf_ncard_fiber_ne_zero hAfin
      fun q : ℤ × ℤ => ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)).subset ?_)
    refine fun b hb hzero => hb ?_
    exact Nat.cast_eq_zero.mpr hzero
  have hpart : ∑ b ∈ s, ({q : ℤ × ℤ | q ∈ A ∧
      ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b}.ncard : ℝ)
      ≤ (A.ncard : ℝ) := by
    rw [← tsum_ncard_fiber hAfin
      fun q : ℤ × ℤ => ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)]
    exact hsum.sum_le_tsum s fun b _ => by positivity
  have hterm : ∀ b : ℕ, jointOmegaCardFactorsProportion r b X
      = ({q : ℤ × ℤ | q ∈ A ∧
          ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b}.ncard : ℝ) /
        integralShortNFCount X := fun b => by
    rw [jointOmegaCardFactorsProportion, hfib b]
  simp only [hterm]
  rw [← Finset.sum_div, tamagawaOmegaProportion, ← hAdef]
  gcongr

/-- **The `ω_Tam`-marginal is dominated by the density `π_r` of `ω_Tam = r`.**
`∑'_b π(r, b) ≤ π_r`. -/
theorem tsum_jointOmegaCardFactorsDensity_right_le (r : ℕ) :
    ∑' b : ℕ, jointOmegaCardFactorsDensity r b ≤ tamagawaOmegaDensity r := by
  have hsummable : Summable fun b : ℕ => jointOmegaCardFactorsDensity r b :=
    summable_jointOmegaCardFactorsDensity.prod_factor r
  refine hsummable.tsum_le_of_sum_le fun s => ?_
  refine le_of_tendsto_of_tendsto
    (tendsto_finsetSum s fun b _ =>
      tendsto_jointOmegaCardFactorsProportion_jointOmegaCardFactorsDensity r b)
    (tendsto_tamagawaOmegaProportion_tamagawaOmegaDensity r) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  exact sum_jointOmegaCardFactorsProportion_le_tamagawaOmegaProportion r s hX

/-- **The `ω_Tam`-marginal of the joint density is the density `π_r` of `ω_Tam = r`.**

`∑'_b π(r, b) = π_r`. -/
theorem tsum_jointOmegaCardFactorsDensity_right (r : ℕ) :
    ∑' b : ℕ, jointOmegaCardFactorsDensity r b = tamagawaOmegaDensity r := by
  have hle := tsum_jointOmegaCardFactorsDensity_right_le
  have hL : Summable fun r : ℕ => ∑' b : ℕ, jointOmegaCardFactorsDensity r b :=
    summable_jointOmegaCardFactorsDensity.prod
  have hLsum : (∑' r : ℕ, ∑' b : ℕ, jointOmegaCardFactorsDensity r b) = 1 := by
    rw [← summable_jointOmegaCardFactorsDensity.tsum_prod]
    exact tsum_jointOmegaCardFactorsDensity_eq_one
  by_contra hne
  exact absurd (hLsum.trans tsum_tamagawaOmegaDensity_eq_one.symm)
    (hL.tsum_lt_tsum hle (lt_of_le_of_ne (hle r) hne) summable_tamagawaOmegaDensity).ne

/-! ### §5. The joint law -/

/-- **The joint limiting law of `(ω_Tam(E), Ω(Tam(E)))` as a `PMF` on `ℤ_{≥0}²`.** -/
noncomputable def jointOmegaCardFactorsPMF : PMF (ℕ × ℕ) :=
  ⟨fun rb : ℕ × ℕ => ENNReal.ofReal (jointOmegaCardFactorsDensity rb.1 rb.2), by
    have h : ∑' rb : ℕ × ℕ, ENNReal.ofReal (jointOmegaCardFactorsDensity rb.1 rb.2) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun rb : ℕ × ℕ => jointOmegaCardFactorsDensity_nonneg rb.1 rb.2)
          summable_jointOmegaCardFactorsDensity,
        tsum_jointOmegaCardFactorsDensity_eq_one, ENNReal.ofReal_one]
    exact h ▸ ENNReal.summable.hasSum⟩

/-- **The mass of a point**: `P_joint({(r, b)}) = π(r, b)`. -/
lemma jointOmegaCardFactorsMeasure_singleton (rb : ℕ × ℕ) :
    jointOmegaCardFactorsMeasure {rb}
      = ENNReal.ofReal (jointOmegaCardFactorsDensity rb.1 rb.2) := by
  rw [jointOmegaCardFactorsMeasure, Measure.sum_apply _ (measurableSet_singleton rb),
    tsum_eq_single rb fun c hc => by
      simp [Measure.dirac_apply' _ (measurableSet_singleton rb), hc]]
  simp

/-- The `PMF` and the measure agree: both are `∑_{rb} π(rb) δ_{rb}`. -/
theorem jointOmegaCardFactorsPMF_toMeasure :
    jointOmegaCardFactorsPMF.toMeasure = jointOmegaCardFactorsMeasure := by
  rw [jointOmegaCardFactorsMeasure]
  conv_lhs => rw [← Measure.sum_smul_dirac jointOmegaCardFactorsPMF.toMeasure]
  simp_rw [jointOmegaCardFactorsPMF.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  rfl

/-- **`P_joint` is a probability measure.** -/
instance isProbabilityMeasure_jointOmegaCardFactorsMeasure :
    IsProbabilityMeasure jointOmegaCardFactorsMeasure := by
  rw [← jointOmegaCardFactorsPMF_toMeasure]
  infer_instance

/-! ### §6. The two marginals -/

/-- **The first marginal of `P_joint` is the limiting law `tamagawaOmegaMeasure` of `ω_Tam`.**

`Prod.fst_* P_joint = P`. -/
theorem map_fst_jointOmegaCardFactorsMeasure :
    jointOmegaCardFactorsMeasure.map Prod.fst = tamagawaOmegaMeasure := by
  refine Measure.ext_of_singleton fun r => ?_
  rw [Measure.map_apply measurable_fst (measurableSet_singleton r),
    tamagawaOmegaMeasure_singleton]
  have hpre : (Prod.fst ⁻¹' {r} : Set (ℕ × ℕ)) = ⋃ b : ℕ, {(r, b)} := by
    refine Set.ext fun rb => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Prod.ext_iff]
    exact ⟨fun h => ⟨rb.2, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [hpre, measure_iUnion (fun b b' hbb' => by
      simp only [Set.disjoint_singleton, ne_eq, Prod.mk.injEq]
      tauto)
    fun b => measurableSet_singleton _]
  simp only [jointOmegaCardFactorsMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => jointOmegaCardFactorsDensity_nonneg r b)
      (summable_jointOmegaCardFactorsDensity.prod_factor r),
    tsum_jointOmegaCardFactorsDensity_right]

/-- **The second marginal of `P_joint` is the limiting law `cardFactorsTamagawaMeasure` of
`Ω(Tam)`.**

`Prod.snd_* P_joint = P_Ω`. -/
theorem map_snd_jointOmegaCardFactorsMeasure :
    jointOmegaCardFactorsMeasure.map Prod.snd = cardFactorsTamagawaMeasure := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b),
    cardFactorsTamagawaMeasure_singleton]
  have hpre : (Prod.snd ⁻¹' {b} : Set (ℕ × ℕ)) = ⋃ r : ℕ, {(r, b)} := by
    refine Set.ext fun rb => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Prod.ext_iff]
    exact ⟨fun h => ⟨rb.1, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  rw [hpre, measure_iUnion (fun r r' hrr' => by
      simp only [Set.disjoint_singleton, ne_eq, Prod.mk.injEq]
      tauto)
    fun r => measurableSet_singleton _]
  simp only [jointOmegaCardFactorsMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => jointOmegaCardFactorsDensity_nonneg r b)
      (summable_jointOmegaCardFactorsDensity.prod_symm.prod_factor b),
    tsum_jointOmegaCardFactorsDensity_left]

end WeierstrassCurve
