/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Equidistribution.LimitMeasure
public import BSDTamagawa.Equidistribution.EmpiricalMeasure
public import BSDTamagawa.PrimeCount.TruncatedSum
public import BSDTamagawa.NumberTheory.PadicHaar

/-!
# Weak convergence `μ_{S,X} ⇒ μ_S`

For a finite set of primes `S`, the empirical measures `μ_{S,X}` converge weakly to the product
Haar measure `μ_S` on the configuration space `K_S`: for every continuous `g : K_S → ℝ`,
`∫_{K_S} g dμ_{S,X} → ∫_{K_S} g dμ_S` as `X → ∞`.

On a profinite space, convergence of the masses of all clopen sets implies convergence of the
integrals of all continuous functions, since such a function is uniformly approximated by step
functions over finite clopen partitions. Every clopen subset of `K_S` is a finite union of
cylinders `{y | y ≡ b mod p^n for p ∈ S}` at a single level `n`. Through the Chinese remainder
theorem the `μ_{S,X}`-mass of such a union is a ratio `N_A(X)/N(X)` of residue-restricted counts,
which tends to `|A|/M²`, the `μ_S`-mass of the union, with `M = ∏_{p ∈ S} p^n`.

## Main definitions

* `WeierstrassCurve.configRed`: the level-`n` reduction `K_S → ∏_{p ∈ S} (ℤ/p^nℤ)²`.
* `WeierstrassCurve.configModulus`: the modulus `M = ∏_{p ∈ S} p^n`.
* `WeierstrassCurve.configCRT`: the Chinese remainder isomorphism `ℤ/Mℤ ≃+* ∏_{p ∈ S} ℤ/p^nℤ`.

## Main results

* `BSDTamagawa.WeakConvergence.tendsto_integral_of_tendsto_measureReal_isClopen`: on a profinite
  space, convergence on clopen sets implies convergence of integrals of continuous functions.
* `WeierstrassCurve.exists_configRed_eq_of_isClopen`: every clopen subset of `K_S` is a union of
  cylinders at a single level.
* `WeierstrassCurve.isProbabilityMeasure_configEmpiricalMeasure`: `μ_{S,X}` is a probability
  measure for `X ≥ 4`.
* `WeierstrassCurve.tendsto_integral_configEmpiricalMeasure`: `μ_{S,X} ⇒ μ_S`.
-/

@[expose] public section

namespace BSDTamagawa.WeakConvergence

open Filter MeasureTheory Set Topology

open scoped ENNReal

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- If a bounded continuous `f` is within `ε` of the constant `c j` on each piece `W j` of a finite
measurable partition of `E`, then the integral of `f` against a probability measure `μ` is within
`ε` of `∑ j, c j * μ.real (W j)`. -/
theorem abs_integral_sub_sum_le [OpensMeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : BoundedContinuousFunction E ℝ)
    {n : ℕ} {W : Fin n → Set E} (hWm : ∀ j, MeasurableSet (W j))
    (hWd : Pairwise (Function.onFun Disjoint W)) (hWcov : ⋃ j, W j = univ)
    (c : Fin n → ℝ) {ε : ℝ} (hclose : ∀ j, ∀ x ∈ W j, |f x - c j| ≤ ε) :
    |(∫ x, f x ∂μ) - ∑ j, c j * μ.real (W j)| ≤ ε := by
  have h1 : (∫ x, f x ∂μ) = ∑ j, ∫ x in W j, f x ∂μ := by
    rw [← setIntegral_univ, ← hWcov, integral_iUnion_fintype hWm hWd]
    exact fun _ => (f.integrable μ).integrableOn
  have h3 : (∑ j, c j * μ.real (W j)) = ∑ j, ∫ _ in W j, c j ∂μ :=
    Finset.sum_congr rfl fun j _ => by rw [setIntegral_const, smul_eq_mul, mul_comm]
  rw [h1, h3, ← Finset.sum_sub_distrib]
  calc |∑ j, ((∫ x in W j, f x ∂μ) - ∫ _ in W j, c j ∂μ)|
      ≤ ∑ j, |(∫ x in W j, f x ∂μ) - ∫ _ in W j, c j ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |∫ x in W j, (f x - c j) ∂μ| :=
        Finset.sum_congr rfl fun j _ => by
          rw [integral_sub (f.integrable μ).integrableOn
            (integrableOn_const (measure_lt_top μ (W j)).ne)]
    _ ≤ ∑ j, ε * μ.real (W j) :=
        Finset.sum_le_sum fun j _ => by
          simpa [Real.norm_eq_abs] using
            norm_setIntegral_le_of_norm_le_const (μ := μ) (s := W j)
              (f := fun x => f x - c j) (C := ε) (measure_lt_top _ _)
              fun x hx => by simpa [Real.norm_eq_abs] using hclose j x hx
    _ = ε * ∑ j, μ.real (W j) := by rw [Finset.mul_sum]
    _ = ε * μ.real univ := by rw [← hWcov, measureReal_iUnion_fintype hWd hWm]
    _ = ε := by rw [probReal_univ, mul_one]

/-- Let `E` be a compact, Hausdorff, totally disconnected space with its Borel σ-algebra, `μ` a
probability measure on `E` and `ν i` measures that are eventually probability measures along a
filter `L`. If `(ν i) C → μ C` for every clopen `C ⊆ E`, then `∫ g dν i → ∫ g dμ` for every
continuous `g : E → ℝ`. -/
theorem tendsto_integral_of_tendsto_measureReal_isClopen
    [CompactSpace E] [T2Space E] [TotallyDisconnectedSpace E] [BorelSpace E]
    {I : Type*} {L : Filter I} {ν : I → Measure E} {μ : Measure E} [IsProbabilityMeasure μ]
    (hν : ∀ᶠ i in L, IsProbabilityMeasure (ν i))
    (H : ∀ C : Set E, IsClopen C → Tendsto (fun i => (ν i).real C) L (𝓝 (μ.real C)))
    {g : E → ℝ} (hg : Continuous g) :
    Tendsto (fun i => ∫ x, g x ∂ν i) L (𝓝 (∫ x, g x ∂μ)) := by
  set f : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩
  have hfg : ∀ x, f x = g x := fun _ => rfl
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / 4 with hη
  have hηpos : 0 < η := by positivity
  have hSopen : IsOpen {z : ℝ × ℝ | |z.1 - z.2| < η} :=
    isOpen_lt (by fun_prop) continuous_const
  obtain ⟨n, r, c, hr, hrc⟩ :=
    ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal (X := E) (V := ℝ)
      (S := {z : ℝ × ℝ | |z.1 - z.2| < η}) ⟨g, hg⟩
      (hSopen.mem_nhdsSet.2 fun z hz => by simp [show z.1 = z.2 from hz, hηpos])
  set W : Fin n → Set E := fun j => r ⁻¹' {j}
  have hWclopen : ∀ j, IsClopen (W j) := fun j => (isClopen_discrete {j}).preimage hr
  have hWm : ∀ j, MeasurableSet (W j) := fun j => (hWclopen j).1.measurableSet
  have hWd : Pairwise (Function.onFun Disjoint W) := fun j k hjk =>
    Set.disjoint_left.2 fun _ hx hx' => hjk (hx.symm.trans hx')
  have hWcov : ⋃ j, W j = univ := eq_univ_of_forall fun x => mem_iUnion.2 ⟨r x, rfl⟩
  have hclose : ∀ j, ∀ x ∈ W j, |f x - c j| ≤ η := by
    intro j x hx
    have hxj : r x = j := hx
    exact le_of_lt (hxj ▸ hrc x)
  set T : Measure E → ℝ := fun P => ∑ j, c j * P.real (W j)
  have hTtendsto : Tendsto (fun i => T (ν i)) L (𝓝 (T μ)) :=
    tendsto_finsetSum _ fun j _ => (H (W j) (hWclopen j)).const_mul (c j)
  have hTclose : ∀ᶠ i in L, |T (ν i) - T μ| < η := by
    filter_upwards [Metric.tendsto_nhds.1 hTtendsto η hηpos] with i hi
    simpa [Real.dist_eq] using hi
  filter_upwards [hν, hTclose] with i hνi hi
  have hbi : |(∫ x, f x ∂ν i) - T (ν i)| ≤ η :=
    abs_integral_sub_sum_le (ν i) f hWm hWd hWcov c hclose
  have hbμ : |T μ - ∫ x, f x ∂μ| ≤ η := by
    rw [abs_sub_comm]
    exact abs_integral_sub_sum_le μ f hWm hWd hWcov c hclose
  simp only [Real.dist_eq, ← hfg]
  calc |(∫ x, f x ∂ν i) - ∫ x, f x ∂μ|
      = |((∫ x, f x ∂ν i) - T (ν i)) + (T (ν i) - T μ) + (T μ - ∫ x, f x ∂μ)| := by
        congr 1
        ring
    _ ≤ |(∫ x, f x ∂ν i) - T (ν i)| + |T (ν i) - T μ| + |T μ - ∫ x, f x ∂μ| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ < ε := by rw [hη] at hbi hbμ; linarith

/-- For a finite set `T` and a map `g`, `∑'_{q ∈ T} 1_s(g q) = #{a ∈ T | g a ∈ s}` in `ℝ≥0∞`. -/
theorem tsum_indicator_eq_ncard {α β : Type*} {T : Set α} (hT : T.Finite) (g : α → β)
    (s : Set β) :
    ∑' q : ↥T, Set.indicator s (1 : β → ℝ≥0∞) (g (q : α))
      = ({a | a ∈ T ∧ g a ∈ s}.ncard : ℝ≥0∞) := by
  classical
  have : Fintype ↥T := hT.fintype
  have hequiv : {q : ↥T // g (q : α) ∈ s} ≃ ↥{a | a ∈ T ∧ g a ∈ s} :=
    { toFun := fun q => ⟨(q.1 : α), q.1.2, q.2⟩
      invFun := fun a => ⟨⟨(a : α), a.2.1⟩, a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [tsum_fintype]
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_congr hequiv, Nat.card_coe_set_eq]

end BSDTamagawa.WeakConvergence

namespace WeierstrassCurve

open Filter MeasureTheory Set Topology

open scoped ENNReal

open BSDTamagawa.WeakConvergence

/-- The finite residue space `∏_{p ∈ S} (ℤ/p^nℤ)²` at level `n`. -/
abbrev configResidue (S : Finset ℕ) (n : ℕ) : Type :=
  ∀ q : ↥(S.filter Nat.Prime), ZMod ((q : ℕ) ^ n) × ZMod ((q : ℕ) ^ n)

/-- The modulus `M = ∏_{p ∈ S} p^n`. -/
def configModulus (S : Finset ℕ) (n : ℕ) : ℕ := ∏ q : ↥(S.filter Nat.Prime), (q : ℕ) ^ n

/-- The level-`n` reduction `K_S → ∏_{p ∈ S} (ℤ/p^nℤ)²`, reducing both coordinates of each `p`-adic
factor modulo `p^n`. -/
noncomputable def configRed (S : Finset ℕ) (n : ℕ) (y : configSpace S) : configResidue S n :=
  fun q => (PadicInt.toZModPow n (y q).1, PadicInt.toZModPow n (y q).2)

/-- A cylinder set — a fibre of the level-`n` reduction — is a product of `p`-adic fibres. -/
theorem configRed_preimage_singleton (S : Finset ℕ) (n : ℕ) (b : configResidue S n) :
    configRed S n ⁻¹' {b}
      = Set.univ.pi fun q => (PadicInt.toZModPow n ⁻¹' {(b q).1}) ×ˢ
          (PadicInt.toZModPow n ⁻¹' {(b q).2}) := by
  ext y
  simp [configRed, funext_iff, Prod.ext_iff, Set.mem_prod]

/-- Cylinder sets are measurable. -/
theorem measurableSet_configRed_preimage_singleton (S : Finset ℕ) (n : ℕ)
    (b : configResidue S n) : MeasurableSet (configRed S n ⁻¹' {b}) := by
  rw [configRed_preimage_singleton]
  exact MeasurableSet.univ_pi fun q =>
    (PadicInt.measurableSet_preimage_toZModPow n _).prod
      (PadicInt.measurableSet_preimage_toZModPow n _)

/-- Every level-`n` cylinder has `μ_S`-mass `1 / M²`, where `M = ∏_{p ∈ S} p^n`. -/
theorem configMeasure_configRed_preimage_singleton (S : Finset ℕ) (n : ℕ)
    (b : configResidue S n) :
    configMeasure S (configRed S n ⁻¹' {b}) = ((configModulus S n : ℝ≥0∞) ^ 2)⁻¹ := by
  classical
  have hfac : ∀ q : ↥(S.filter Nat.Prime),
      volume ((PadicInt.toZModPow n ⁻¹' {(b q).1}) ×ˢ (PadicInt.toZModPow n ⁻¹' {(b q).2})
        : Set (ℤ_[(q : ℕ)] × ℤ_[(q : ℕ)]))
        = ((((q : ℕ) : ℝ≥0∞) ^ n)⁻¹) * ((((q : ℕ) : ℝ≥0∞) ^ n)⁻¹) := fun q => by
    rw [Measure.volume_eq_prod, Measure.prod_prod, PadicInt.volume_preimage_toZModPow,
      PadicInt.volume_preimage_toZModPow]
  have hM : ((configModulus S n : ℕ) : ℝ≥0∞) = ∏ q : ↥(S.filter Nat.Prime),
      (((q : ℕ) : ℝ≥0∞) ^ n) := by
    rw [configModulus]; push_cast; rfl
  rw [configRed_preimage_singleton, configMeasure, Measure.pi_pi]
  simp only [hfac]
  rw [Finset.prod_mul_distrib,
    ← ENNReal.prod_inv_distrib fun _ _ _ _ _ => Or.inr (by simp),
    ← hM, sq, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]

/-- The preimage of a finite set of level-`n` residues is the union of the corresponding cylinders.
-/
theorem configRed_preimage_coe (S : Finset ℕ) (n : ℕ) (B : Finset (configResidue S n)) :
    configRed S n ⁻¹' (B : Set (configResidue S n)) = ⋃ b ∈ B, configRed S n ⁻¹' {b} := by
  ext y
  simp

/-- A union of `|B|` level-`n` cylinders has `μ_S`-mass `|B| / M²`. -/
theorem configMeasure_configRed_preimage (S : Finset ℕ) (n : ℕ)
    (B : Finset (configResidue S n)) :
    configMeasure S (configRed S n ⁻¹' (B : Set (configResidue S n)))
      = B.card * ((configModulus S n : ℝ≥0∞) ^ 2)⁻¹ := by
  rw [configRed_preimage_coe, measure_biUnion_finset
    (fun b _ b' _ hbb' => Set.disjoint_left.2 fun _ hz hz' => hbb' (hz.symm.trans hz'))
    (fun b _ => measurableSet_configRed_preimage_singleton S n b)]
  simp [configMeasure_configRed_preimage_singleton, Finset.sum_const, nsmul_eq_mul]

/-- Two points of `K_S` with the same level-`n` reduction are within distance `2^{-n}`. -/
theorem dist_le_of_configRed_eq {S : Finset ℕ} {n : ℕ} {x y : configSpace S}
    (h : configRed S n y = configRed S n x) : dist y x ≤ ((2 : ℝ) ^ n)⁻¹ := by
  rw [dist_pi_le_iff (by positivity)]
  intro q
  have hq2 : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by
    exact_mod_cast (Fact.out : (q : ℕ).Prime).two_le
  have hle : (((q : ℕ) : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (congrFun h q)
  rw [Prod.dist_eq]
  exact (max_le (PadicInt.dist_le_of_toZModPow_eq h1)
    (PadicInt.dist_le_of_toZModPow_eq h2)).trans hle

/-- Every clopen subset of `K_S` is the union of the level-`n` cylinders it meets, for some `n`. -/
theorem exists_configRed_eq_of_isClopen {S : Finset ℕ} {C : Set (configSpace S)}
    (hC : IsClopen C) : ∃ n : ℕ, C = configRed S n ⁻¹' (configRed S n '' C) := by
  have key : ∀ x ∈ C, ∃ m : ℕ, ∀ z, dist z x ≤ ((2 : ℝ) ^ m)⁻¹ → z ∈ C := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.2 x hx
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨m, fun z hz => hball (Metric.mem_ball.2 ?_)⟩
    calc dist z x ≤ ((2 : ℝ) ^ m)⁻¹ := hz
      _ = (2 : ℝ)⁻¹ ^ m := by rw [inv_pow]
      _ < ε := hm
  choose! m hm using key
  obtain ⟨b, hbC, hbfin, hbcov⟩ :=
    hC.1.isCompact.elim_finite_subcover_image (b := C)
      (c := fun x => Metric.ball x ((2 : ℝ) ^ (m x + 1))⁻¹)
      (fun x _ => Metric.isOpen_ball)
      (fun x hx => Set.mem_biUnion hx (Metric.mem_ball_self (by positivity)))
  refine ⟨hbfin.toFinset.sup fun x => m x + 1, Set.Subset.antisymm (fun z hz => ⟨z, hz, rfl⟩) ?_⟩
  rintro z ⟨y, hyC, hzy⟩
  obtain ⟨x, hxb, hyx⟩ := Set.mem_iUnion₂.1 (hbcov hyC)
  have hxC : x ∈ C := hbC hxb
  have hnle : ((2 : ℝ) ^ (hbfin.toFinset.sup fun x => m x + 1))⁻¹
      ≤ ((2 : ℝ) ^ (m x + 1))⁻¹ := by
    have hsup : m x + 1 ≤ hbfin.toFinset.sup fun x => m x + 1 :=
      Finset.le_sup (f := fun x => m x + 1) (hbfin.mem_toFinset.2 hxb)
    exact inv_anti₀ (by positivity) (by gcongr; norm_num)
  refine hm x hxC z ?_
  have h1 : dist z y ≤ ((2 : ℝ) ^ (hbfin.toFinset.sup fun x => m x + 1))⁻¹ :=
    dist_le_of_configRed_eq hzy.symm
  have h2 : dist y x < ((2 : ℝ) ^ (m x + 1))⁻¹ := Metric.mem_ball.1 hyx
  have h3 : (2 : ℝ) * ((2 : ℝ) ^ (m x + 1))⁻¹ = ((2 : ℝ) ^ m x)⁻¹ := by
    rw [pow_succ]
    field_simp
  calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ ≤ ((2 : ℝ) ^ (m x + 1))⁻¹ + ((2 : ℝ) ^ (m x + 1))⁻¹ :=
        add_le_add (h1.trans hnle) h2.le
    _ = ((2 : ℝ) ^ m x)⁻¹ := by rw [← h3]; ring

/-- A union of cylinders is measurable. -/
theorem measurableSet_configRed_preimage (S : Finset ℕ) (n : ℕ)
    (B : Finset (configResidue S n)) :
    MeasurableSet (configRed S n ⁻¹' (B : Set (configResidue S n))) := by
  rw [configRed_preimage_coe]
  exact Finset.measurableSet_biUnion _ fun b _ => measurableSet_configRed_preimage_singleton S n b

/-! ### The Chinese remainder identification -/

/-- The modulus `M = ∏_{p ∈ S} p^n` is positive. -/
theorem configModulus_pos (S : Finset ℕ) (n : ℕ) : 0 < configModulus S n :=
  Finset.prod_pos fun q _ => pow_pos (Fact.out : (q : ℕ).Prime).pos n

/-- The Chinese remainder isomorphism `ℤ/Mℤ ≃+* ∏_{p ∈ S} ℤ/p^nℤ`, where `M = ∏_{p ∈ S} p^n`. -/
noncomputable def configCRT (S : Finset ℕ) (n : ℕ) :
    ZMod (configModulus S n) ≃+* ∀ q : ↥(S.filter Nat.Prime), ZMod ((q : ℕ) ^ n) :=
  ZMod.prodEquivPi (fun q : ↥(S.filter Nat.Prime) => (q : ℕ) ^ n) fun _ _ hqq' =>
    Nat.Coprime.pow _ _
      ((Nat.coprime_primes Fact.out Fact.out).2 fun h => hqq' (Subtype.ext h))

/-- The level-`n` reduction of the diagonal image of `(a₄, a₆) ∈ ℤ²` is the Chinese remainder image
of its residue pair modulo `M`. -/
theorem configRed_configEmbed (S : Finset ℕ) (n : ℕ) (a₄ a₆ : ℤ) :
    configRed S n (configEmbed S a₄ a₆)
      = fun q => (configCRT S n (a₄ : ZMod (configModulus S n)) q,
                  configCRT S n (a₆ : ZMod (configModulus S n)) q) := by
  have hc : ∀ a : ℤ, ∀ q : ↥(S.filter Nat.Prime),
      configCRT S n (a : ZMod (configModulus S n)) q = (a : ZMod ((q : ℕ) ^ n)) := fun a q => by
    rw [map_intCast]; rfl
  funext q
  simp only [configRed, configEmbed, map_intCast, hc]

/-- The Chinese remainder bijection on pairs of residues, `(ℤ/Mℤ)² ≃ ∏_{p ∈ S} (ℤ/p^nℤ)²`. -/
noncomputable def configResidueEquiv (S : Finset ℕ) (n : ℕ) :
    ZMod (configModulus S n) × ZMod (configModulus S n) ≃ configResidue S n where
  toFun u := fun q => (configCRT S n u.1 q, configCRT S n u.2 q)
  invFun b := ((configCRT S n).symm fun q => (b q).1, (configCRT S n).symm fun q => (b q).2)
  left_inv u := by simp
  right_inv b := by funext q; simp

/-- The subset `A ⊆ (ℤ/Mℤ)²` corresponding to a set `B` of level-`n` cylinders. -/
noncomputable def configResidueSet (S : Finset ℕ) (n : ℕ) (B : Finset (configResidue S n)) :
    Finset (ZMod (configModulus S n) × ZMod (configModulus S n)) :=
  B.map (configResidueEquiv S n).symm.toEmbedding

/-- The correspondence `B ↔ A` is a bijection, so `|A| = |B|`. -/
theorem card_configResidueSet (S : Finset ℕ) (n : ℕ) (B : Finset (configResidue S n)) :
    (configResidueSet S n B).card = B.card := Finset.card_map _

/-- Membership in `A` is membership of the Chinese-remainder image in `B`. -/
theorem mem_configResidueSet {S : Finset ℕ} {n : ℕ} {B : Finset (configResidue S n)}
    {u : ZMod (configModulus S n) × ZMod (configModulus S n)} :
    u ∈ configResidueSet S n B ↔ configResidueEquiv S n u ∈ B := by
  rw [configResidueSet, Finset.mem_map_equiv, Equiv.symm_symm]

/-- An integer pair `(a₄, a₆)` lands in the union of cylinders `B` exactly when its residue pair
modulo `M` lies in `configResidueSet S n B`. -/
theorem configEmbed_mem_configRed_preimage {S : Finset ℕ} {n : ℕ}
    {B : Finset (configResidue S n)} (a₄ a₆ : ℤ) :
    configEmbed S a₄ a₆ ∈ configRed S n ⁻¹' (B : Set (configResidue S n))
      ↔ ((a₄ : ZMod (configModulus S n)), (a₆ : ZMod (configModulus S n)))
          ∈ configResidueSet S n B := by
  rw [Set.mem_preimage, Finset.mem_coe, mem_configResidueSet, configRed_configEmbed]
  rfl

/-! ### The empirical measure on cylinders -/

/-- For `0 ≤ X` and a measurable `s ⊆ K_S`,
`μ_{S,X}(s) = (1/N(X)) · #{(a₄, a₆) : Ht ≤ X, Δ ≠ 0, ((a₄, a₆))_{p ∈ S} ∈ s}`. -/
theorem configEmpiricalMeasure_apply {S : Finset ℕ} {X : ℝ} (hX : 0 ≤ X)
    {s : Set (configSpace S)} (hs : MeasurableSet s) :
    configEmpiricalMeasure S X s = (integralShortNFCount X : ℝ≥0∞)⁻¹ *
      ({q : ℤ × ℤ | ((integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily) ∧
        configEmbed S q.1 q.2 ∈ s}.ncard : ℝ≥0∞) := by
  rw [configEmpiricalMeasure, Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ hs]
  refine congrArg _ ((tsum_congr fun q => Measure.dirac_apply' _ hs).trans ?_)
  exact tsum_indicator_eq_ncard (finite_setOf_height_le_and_mem_family hX)
    (fun q : ℤ × ℤ => configEmbed S q.1 q.2) s

/-- `μ_{S,X}` is a probability measure for `X ≥ 4`. -/
theorem isProbabilityMeasure_configEmpiricalMeasure {S : Finset ℕ} {X : ℝ} (hX : 4 ≤ X) :
    IsProbabilityMeasure (configEmpiricalMeasure S X) := by
  refine ⟨?_⟩
  have hset : {q : ℤ × ℤ | ((integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily) ∧ configEmbed S q.1 q.2 ∈ (Set.univ : Set (configSpace S))}
      = {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily} := by
    ext q; simp
  rw [configEmpiricalMeasure_apply (by linarith) MeasurableSet.univ, hset,
    show {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.ncard = integralShortNFCount X from rfl]
  exact ENNReal.inv_mul_cancel
    (Nat.cast_ne_zero.2 (integralShortNFCount_ne_zero_of_four_le hX)) (ENNReal.natCast_ne_top _)

/-- For `0 ≤ X`, the `μ_{S,X}`-mass of the union of cylinders `B` is `N_A(X) / N(X)`, where
`A = configResidueSet S n B ⊆ (ℤ/Mℤ)²`. -/
theorem configEmpiricalMeasure_configRed_preimage {S : Finset ℕ} {X : ℝ} (hX : 0 ≤ X) (n : ℕ)
    (B : Finset (configResidue S n)) :
    configEmpiricalMeasure S X (configRed S n ⁻¹' (B : Set (configResidue S n)))
      = (integralShortNFCount X : ℝ≥0∞)⁻¹ *
        (restrictedCount (configModulus S n)
          ((configResidueSet S n B : Finset _) : Set _) X : ℝ≥0∞) := by
  have hset : {q : ℤ × ℤ | ((integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily) ∧
        configEmbed S q.1 q.2 ∈ configRed S n ⁻¹' (B : Set (configResidue S n))}
      = {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ (ofShortNF p.1 p.2).Δ ≠ 0 ∧
          ((p.1 : ZMod (configModulus S n)), (p.2 : ZMod (configModulus S n)))
            ∈ ((configResidueSet S n B : Finset _) : Set _)} := by
    ext q
    simp only [Set.mem_ofPred_eq, configEmbed_mem_configRed_preimage, Finset.mem_coe,
      integralShortNFFamily]
    tauto
  rw [configEmpiricalMeasure_apply hX (measurableSet_configRed_preimage S n B), restrictedCount,
    hset]

/-! ### Weak convergence -/

/-- For every clopen `C ⊆ K_S`, `μ_{S,X}(C) → μ_S(C)` as `X → ∞`. -/
theorem tendsto_configEmpiricalMeasureReal_of_isClopen (S : Finset ℕ)
    {C : Set (configSpace S)} (hC : IsClopen C) :
    Tendsto (fun X => (configEmpiricalMeasure S X).real C) atTop
      (𝓝 ((configMeasure S).real C)) := by
  classical
  obtain ⟨n, hCn⟩ := exists_configRed_eq_of_isClopen hC
  set B : Finset (configResidue S n) := (configRed S n '' C).toFinset with hBdef
  have hC' : C = configRed S n ⁻¹' (B : Set (configResidue S n)) := by
    rw [hBdef, Set.coe_toFinset]
    exact hCn
  have hlim : (configMeasure S).real C
      = ((configResidueSet S n B).card : ℝ) / (configModulus S n : ℝ) ^ 2 := by
    rw [measureReal_def, hC', configMeasure_configRed_preimage, card_configResidueSet,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  rw [hlim]
  refine (tendsto_restrictedCount_div_Ncount (configModulus S n) (configModulus_pos S n)
    (configResidueSet S n B)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  rw [measureReal_def, hC', configEmpiricalMeasure_configRed_preimage hX n B,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_mul_inv, mul_comm]

/-- For every continuous `g : K_S → ℝ`, `∫_{K_S} g dμ_{S,X} → ∫_{K_S} g dμ_S` as `X → ∞`. -/
@[bsd_tamagawa "T033a"]
theorem tendsto_integral_configEmpiricalMeasure (S : Finset ℕ) {g : configSpace S → ℝ}
    (hg : Continuous g) :
    Tendsto (fun X => ∫ y, g y ∂configEmpiricalMeasure S X) atTop
      (𝓝 (∫ y, g y ∂configMeasure S)) :=
  BSDTamagawa.WeakConvergence.tendsto_integral_of_tendsto_measureReal_isClopen
    (by filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX using
      isProbabilityMeasure_configEmpiricalMeasure hX)
    (fun _ hC => tendsto_configEmpiricalMeasureReal_of_isClopen S hC) hg

end WeierstrassCurve
