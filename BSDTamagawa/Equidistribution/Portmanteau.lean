/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.LocalConstancy
public import BSDTamagawa.Equidistribution.WeakConvergence

/-!
# Portmanteau integration of the prime-factor functional

For each `p ∈ S` let `f_p : 𝒦 → ℂ` be bounded and let `G : K_S → ℂ` be any function with
`G((x_p)_{p ∈ S}) = ∏_{p ∈ S} f_p(τ_p(x_p))` on the nonsingular locus `∏_{p ∈ S} U_p`. Then `G` is
bounded on that locus, its discontinuity set is `μ_S`-null, and
`∫_{K_S} G dμ_{S,X} → ∫_{K_S} G dμ_S` as `X → ∞`.

The nonsingular locus is open, `G` is continuous on it, and both `μ_S` and every `μ_{S,X}` give it
full mass. Weak convergence then extends from continuous test functions to `G` by comparison with
the continuous cutoffs `φ_n = min 1 (n · ∏_p ‖Δ_p‖)`.

## Main definitions

* `WeierstrassCurve.configLocus`: the nonsingular locus `∏_{p ∈ S} U_p ⊆ K_S`.
* `WeierstrassCurve.configFactor`: `f ∘ τ_p` on `U_p`, extended by `0`.
* `WeierstrassCurve.configProd`: `∏_{p ∈ S} f_p(τ_p(x_p))` on the nonsingular locus, extended by
  `0`.

## Main results

* `BSDTamagawa.Portmanteau.tendsto_integral_of_continuousOn_of_ae_mem`: weak convergence integrates
  functions that are bounded and continuous on an open set of full measure.
* `WeierstrassCurve.norm_configProd_le`: `‖G‖ ≤ ∏_{p ∈ S} B_p` when `‖f_p‖ ≤ B_p`.
* `WeierstrassCurve.configMeasure_setOf_not_continuousAt_eq_zero`: the discontinuity set of `G` is
  `μ_S`-null.
* `WeierstrassCurve.tendsto_integral_configProd`: `∫ G dμ_{S,X} → ∫ G dμ_S`.
-/

@[expose] public section

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace BSDTamagawa.Portmanteau

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {I : Type*} {L : Filter I} {ν : I → Measure E} {μ : Measure E}

/-- If the integrals of every real continuous function against `ν i` converge to the integral
against `μ`, the same holds for every bounded continuous `g : E → ℂ`. -/
theorem tendsto_integral_complex [IsProbabilityMeasure μ]
    (hν : ∀ᶠ i in L, IsProbabilityMeasure (ν i))
    (weakR : ∀ g : E → ℝ, Continuous g →
      Tendsto (fun i => ∫ x, g x ∂ν i) L (𝓝 (∫ x, g x ∂μ)))
    {g : E → ℂ} (hg : Continuous g) {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) :
    Tendsto (fun i => ∫ x, g x ∂ν i) L (𝓝 (∫ x, g x ∂μ)) := by
  have hint : ∀ ρ : Measure E, IsProbabilityMeasure ρ → Integrable g ρ := fun ρ _ =>
    Integrable.mono' (integrable_const M) hg.aestronglyMeasurable (.of_forall hgb)
  have key : ∀ ρ : Measure E, IsProbabilityMeasure ρ →
      (∫ x, g x ∂ρ) = ((∫ x, (g x).re ∂ρ : ℝ) : ℂ)
        + ((∫ x, (g x).im ∂ρ : ℝ) : ℂ) * Complex.I := by
    intro ρ hρ
    rw [show (∫ x, (g x).re ∂ρ) = (∫ x, g x ∂ρ).re from
        Complex.reCLM.integral_comp_comm (hint ρ hρ),
      show (∫ x, (g x).im ∂ρ) = (∫ x, g x ∂ρ).im from
        Complex.imCLM.integral_comp_comm (hint ρ hρ), Complex.re_add_im]
  refine Tendsto.congr' (f₁ := fun i => ((∫ x, (g x).re ∂ν i : ℝ) : ℂ)
    + ((∫ x, (g x).im ∂ν i : ℝ) : ℂ) * Complex.I) ?_ ?_
  · filter_upwards [hν] with i hi using (key (ν i) hi).symm
  · rw [key μ inferInstance]
    exact ((Complex.continuous_ofReal.tendsto _).comp
        (weakR _ (Complex.continuous_re.comp hg))).add
      (((Complex.continuous_ofReal.tendsto _).comp
        (weakR _ (Complex.continuous_im.comp hg))).mul_const Complex.I)

/-- Let `μ` and, eventually along `L`, the `ν i` be probability measures on `E` such that the
integrals of continuous real functions against `ν i` converge to those against `μ`. Let `W ⊆ E` be
open and of full mass for `μ` and for the `ν i`, and suppose there are continuous cutoffs
`φ : E → [0, 1]`, vanishing off `W`, with `∫ (1 - φ) dμ` arbitrarily small. If `h : E → ℂ` is
continuous and bounded on `W`, then `∫ h dν i → ∫ h dμ`. -/
theorem tendsto_integral_of_continuousOn_of_ae_mem [IsProbabilityMeasure μ]
    (hν : ∀ᶠ i in L, IsProbabilityMeasure (ν i))
    (weakR : ∀ g : E → ℝ, Continuous g →
      Tendsto (fun i => ∫ x, g x ∂ν i) L (𝓝 (∫ x, g x ∂μ)))
    {W : Set E} (hWo : IsOpen W) (hμW : μ Wᶜ = 0) (hνW : ∀ᶠ i in L, ν i Wᶜ = 0)
    (cut : ∀ δ : ℝ, 0 < δ → ∃ φ : E → ℝ, Continuous φ ∧ (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∉ W, φ x = 0) ∧ ∫ x, (1 - φ x) ∂μ < δ)
    {h : E → ℂ} {M : ℝ} (hM : 0 ≤ M) (hhc : ContinuousOn h W) (hhb : ∀ x ∈ W, ‖h x‖ ≤ M) :
    Tendsto (fun i => ∫ x, h x ∂ν i) L (𝓝 (∫ x, h x ∂μ)) := by
  have hint : ∀ ρ : Measure E, IsProbabilityMeasure ρ → ρ Wᶜ = 0 → Integrable h ρ := by
    intro ρ _ hρW
    have hae : ∀ᵐ x ∂ρ, x ∈ W := mem_ae_iff.2 hρW
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · have := hhc.aestronglyMeasurable (μ := ρ) hWo.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
    · filter_upwards [hae] with x hx using hhb x hx
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M' : ℝ := M + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  obtain ⟨φ, hφc, hφ01, hφ0, hφμ⟩ := cut (ε / (4 * M')) (by positivity)
  set g : E → ℂ := W.indicator (fun x => h x * (φ x : ℂ)) with hgdef
  have hgb : ∀ x, ‖g x‖ ≤ M' * φ x := by
    intro x
    by_cases hx : x ∈ W
    · rw [hgdef, Set.indicator_of_mem hx, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hφ01 x).1]
      exact mul_le_mul_of_nonneg_right ((hhb x hx).trans (by rw [hM']; linarith)) (hφ01 x).1
    · rw [hgdef, Set.indicator_of_notMem hx]
      simpa using mul_nonneg hM'pos.le (hφ01 x).1
  have hgbd : ∀ x, ‖g x‖ ≤ M' := fun x =>
    (hgb x).trans (mul_le_of_le_one_right hM'pos.le (hφ01 x).2)
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · refine ContinuousAt.congr (f := fun y => h y * (φ y : ℂ)) ?_ ?_
      · exact (hhc.continuousAt (hWo.mem_nhds hx)).mul
          (Complex.continuous_ofReal.continuousAt.comp hφc.continuousAt)
      · exact Filter.eventuallyEq_of_mem (hWo.mem_nhds hx)
          fun y hy => by rw [hgdef, Set.indicator_of_mem hy]
    · have hgx : g x = 0 := Set.indicator_of_notMem hx _
      have hz : Tendsto (fun y => M' * φ y) (𝓝 x) (𝓝 0) := by
        have h0 : (0 : ℝ) = M' * φ x := by rw [hφ0 x hx, mul_zero]
        rw [h0]
        exact hφc.continuousAt.const_mul M'
      rw [ContinuousAt, hgx]
      exact squeeze_zero_norm hgb hz
  have key : ∀ ρ : Measure E, IsProbabilityMeasure ρ → ρ Wᶜ = 0 →
      ‖(∫ x, h x ∂ρ) - ∫ x, g x ∂ρ‖ ≤ M' * ∫ x, (1 - φ x) ∂ρ := by
    intro ρ hρ hρW
    have hae : ∀ᵐ x ∂ρ, x ∈ W := mem_ae_iff.2 hρW
    have hgint : Integrable g ρ :=
      Integrable.mono' (integrable_const M') hgc.aestronglyMeasurable (.of_forall hgbd)
    have h1 : Integrable h ρ := hint ρ hρ hρW
    have hbint : Integrable (fun x => M' * (1 - φ x)) ρ :=
      Integrable.mono' (integrable_const M')
        ((continuous_const.mul (continuous_const.sub hφc)).aestronglyMeasurable)
        (.of_forall fun x => by
          rw [Real.norm_of_nonneg (mul_nonneg hM'pos.le (by linarith [(hφ01 x).2]))]
          exact mul_le_of_le_one_right hM'pos.le (by linarith [(hφ01 x).1]))
    rw [← integral_sub h1 hgint]
    calc ‖∫ x, (h x - g x) ∂ρ‖ ≤ ∫ x, ‖h x - g x‖ ∂ρ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, M' * (1 - φ x) ∂ρ := by
          refine integral_mono_ae (h1.sub hgint).norm hbint ?_
          filter_upwards [hae] with x hx
          rw [hgdef, Set.indicator_of_mem hx, show h x - h x * (φ x : ℂ)
            = h x * ((1 - φ x : ℝ) : ℂ) by push_cast; ring, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (by linarith [(hφ01 x).2])]
          exact mul_le_mul_of_nonneg_right ((hhb x hx).trans (by rw [hM']; linarith))
            (by linarith [(hφ01 x).2])
      _ = M' * ∫ x, (1 - φ x) ∂ρ := integral_const_mul _ _
  have e1 : ∀ᶠ i in L, ∫ x, (1 - φ x) ∂ν i < ε / (4 * M') :=
    (weakR _ (continuous_const.sub hφc)).eventually_lt_const hφμ
  have e2 : ∀ᶠ i in L, ‖(∫ x, g x ∂ν i) - ∫ x, g x ∂μ‖ < ε / 4 := by
    have := Metric.tendsto_nhds.1 (tendsto_integral_complex hν weakR hgc hgbd) (ε / 4)
      (by positivity)
    filter_upwards [this] with i hi using by rwa [dist_eq_norm] at hi
  have hquarter : M' * (ε / (4 * M')) = ε / 4 := by field_simp
  have b2 : ‖(∫ x, g x ∂μ) - ∫ x, h x ∂μ‖ ≤ ε / 4 := by
    rw [norm_sub_rev, ← hquarter]
    exact (key μ inferInstance hμW).trans (by gcongr)
  filter_upwards [hν, hνW, e1, e2] with i hνi hνWi h1 h2
  have b1 : ‖(∫ x, h x ∂ν i) - ∫ x, g x ∂ν i‖ ≤ ε / 4 := by
    rw [← hquarter]; exact (key (ν i) hνi hνWi).trans (by gcongr)
  rw [dist_eq_norm]
  calc ‖(∫ x, h x ∂ν i) - ∫ x, h x ∂μ‖
      = ‖((∫ x, h x ∂ν i) - ∫ x, g x ∂ν i) + ((∫ x, g x ∂ν i) - ∫ x, g x ∂μ)
          + ((∫ x, g x ∂μ) - ∫ x, h x ∂μ)‖ := by congr 1; ring
    _ ≤ ‖(∫ x, h x ∂ν i) - ∫ x, g x ∂ν i‖ + ‖(∫ x, g x ∂ν i) - ∫ x, g x ∂μ‖
          + ‖(∫ x, g x ∂μ) - ∫ x, h x ∂μ‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

end BSDTamagawa.Portmanteau

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-! ### The nonsingular locus of the coefficient plane -/

variable {p : ℕ} [Fact p.Prime]

/-- The discriminant of the short model is continuous on `ℤ_p × ℤ_p`. -/
theorem continuous_shortNF_Δ : Continuous fun x : ℤ_[p] × ℤ_[p] => (ofShortNF x.1 x.2).Δ := by
  simp only [ofShortNF_Δ]; fun_prop

/-- The nonsingular locus `U_p = {(a₄, a₆) | Δ ≠ 0}` is open. -/
theorem isOpen_nonsingularLocus : IsOpen (nonsingularLocus p) :=
  isOpen_compl_singleton.preimage continuous_shortNF_Δ

/-- The singular locus of the coefficient plane, the complement of `U_p`, is `μ_p`-null. -/
theorem volume_compl_nonsingularLocus : volume ((nonsingularLocus p)ᶜ) = 0 := by
  have h := ShortNF.Singular.volume_eq (R := ℤ_[p])
  rw [show (volume : Measure (ShortNF ℤ_[p]))
      = Measure.map (Function.uncurry ShortNF.ofProd) volume from rfl,
    Measure.map_apply ShortNF.measurable_ofProd ShortNF.Singular.measurableSet] at h
  convert h using 2
  ext x
  simp [nonsingularLocus, Function.uncurry]

/-! ### The nonsingular locus of `K_S` -/

/-- The nonsingular locus `∏_{p ∈ S} U_p ⊆ K_S`: the configurations all of whose coordinates are
nonsingular coefficient pairs. -/
def configLocus (S : Finset ℕ) : Set (configSpace S) :=
  {y | ∀ q : ↥(S.filter Nat.Prime), y q ∈ nonsingularLocus (q : ℕ)}

/-- Membership in `∏_{p ∈ S} U_p` is coordinatewise membership in `U_p`. -/
@[simp] theorem mem_configLocus_iff {S : Finset ℕ} {y : configSpace S} :
    y ∈ configLocus S ↔ ∀ q : ↥(S.filter Nat.Prime), y q ∈ nonsingularLocus (q : ℕ) :=
  Iff.rfl

/-- `∏_{p ∈ S} U_p` is open in `K_S`. -/
theorem isOpen_configLocus (S : Finset ℕ) : IsOpen (configLocus S) := by
  have h : configLocus S
      = ⋂ q : ↥(S.filter Nat.Prime),
          (fun y : configSpace S => y q) ⁻¹' nonsingularLocus (q : ℕ) := by
    ext y; simp
  rw [h]
  exact isOpen_iInter_of_finite fun q => isOpen_nonsingularLocus.preimage (continuous_apply q)

/-- The complement of `∏_{p ∈ S} U_p` in `K_S` is `μ_S`-null. -/
theorem configMeasure_compl_configLocus (S : Finset ℕ) :
    configMeasure S (configLocus S)ᶜ = 0 := by
  have hsub : (configLocus S)ᶜ
      ⊆ ⋃ q : ↥(S.filter Nat.Prime), Function.eval q ⁻¹' ((nonsingularLocus (q : ℕ))ᶜ) := by
    intro y hy
    simp only [configLocus, mem_compl_iff, mem_ofPred_eq, not_forall] at hy
    obtain ⟨q, hq⟩ := hy
    exact mem_iUnion.2 ⟨q, hq⟩
  refine measure_mono_null hsub ?_
  rw [configMeasure]
  exact measure_iUnion_null fun q => Measure.pi_eval_preimage_null _ volume_compl_nonsingularLocus

/-- The diagonal image of an integer pair with `Δ ≠ 0` lies in `∏_{p ∈ S} U_p`. -/
theorem configEmbed_mem_configLocus {S : Finset ℕ} {a₄ a₆ : ℤ}
    (h : (a₄, a₆) ∈ integralShortNFFamily) : configEmbed S a₄ a₆ ∈ configLocus S :=
  fun q => ShortNF.ofProd_intCast_mem_Elliptic (p := (q : ℕ)) h

/-- The complement of `∏_{p ∈ S} U_p` is `μ_{S,X}`-null. -/
theorem configEmpiricalMeasure_compl_configLocus (S : Finset ℕ) (X : ℝ) :
    configEmpiricalMeasure S X (configLocus S)ᶜ = 0 := by
  have hms : MeasurableSet (configLocus S)ᶜ := (isOpen_configLocus S).measurableSet.compl
  have hz : ∀ q : {q : ℤ × ℤ // (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily},
      Measure.dirac (configEmbed S q.1.1 q.1.2) (configLocus S)ᶜ = 0 := by
    intro q
    rw [Measure.dirac_apply' _ hms]
    exact Set.indicator_of_notMem (by simpa using configEmbed_mem_configLocus q.2.2) _
  rw [configEmpiricalMeasure, Measure.smul_apply, Measure.sum_apply _ hms]
  refine mul_eq_zero_of_right _ ?_
  simp only [hz, tsum_zero]

/-! ### The prime-factor functional `G` -/

open scoped Classical in
/-- One factor of the prime-factor functional: `f ∘ τ_p` on `U_p`, extended by `0`. -/
noncomputable def configFactor (p : ℕ) [Fact p.Prime] (f : ReductionData → ℂ)
    (x : ℤ_[p] × ℤ_[p]) : ℂ :=
  if h : x ∈ nonsingularLocus p then f (strat p ⟨x, h⟩) else 0

/-- On `U_p`, `configFactor p f` is `f ∘ τ_p`. -/
@[simp] theorem configFactor_coe (f : ReductionData → ℂ) (x : ↥(nonsingularLocus p)) :
    configFactor p f (x : ℤ_[p] × ℤ_[p]) = f (strat p x) := by
  rw [configFactor, dite_eq_left x.2]

/-- Off `U_p`, `configFactor p f` vanishes. -/
theorem configFactor_of_notMem (f : ReductionData → ℂ) {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∉ nonsingularLocus p) :
    configFactor p f x = 0 := by
  rw [configFactor, dite_eq_right hx]

/-- If `‖f‖ ≤ B`, then `‖configFactor p f x‖ ≤ B` for every `x`. -/
theorem norm_configFactor_le {f : ReductionData → ℂ} {B : ℝ} (hf : ∀ k, ‖f k‖ ≤ B)
    (x : ℤ_[p] × ℤ_[p]) : ‖configFactor p f x‖ ≤ B := by
  by_cases hx : x ∈ nonsingularLocus p
  · rw [show x = ((⟨x, hx⟩ : ↥(nonsingularLocus p)) : ℤ_[p] × ℤ_[p]) from rfl, configFactor_coe]
    exact hf _
  · rw [configFactor_of_notMem f hx, norm_zero]
    exact le_trans (norm_nonneg (f (KodairaSymbol.I 0, 0))) (hf _)

/-- `f ∘ τ_p` is continuous on `U_p` for every `f : 𝒦 → ℂ`. -/
theorem continuousOn_configFactor (f : ReductionData → ℂ) :
    ContinuousOn (configFactor p f) (nonsingularLocus p) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_comp_strat p f).congr fun x => (configFactor_coe f x).symm

/-- The prime-factor functional `G((x_p)_{p ∈ S}) = ∏_{p ∈ S} f_p(τ_p(x_p))` on `∏_{p ∈ S} U_p`,
and `0` off it. -/
noncomputable def configProd (S : Finset ℕ) (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ)
    (y : configSpace S) : ℂ :=
  ∏ q : ↥(S.filter Nat.Prime), configFactor (q : ℕ) (f q) (y q)

/-- On `∏_{p ∈ S} U_p`, `configProd S f y = ∏_{p ∈ S} f_p(τ_p(y_p))`. -/
theorem configProd_apply_of_mem {S : Finset ℕ} (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ)
    {y : configSpace S} (hy : y ∈ configLocus S) :
    configProd S f y = ∏ q : ↥(S.filter Nat.Prime), f q (strat (q : ℕ) ⟨y q, hy q⟩) :=
  Finset.prod_congr rfl fun q _ => configFactor_coe (f q) ⟨y q, hy q⟩

/-- If `‖f_p‖ ≤ B_p` for each `p ∈ S`, then `‖G‖ ≤ ∏_{p ∈ S} B_p` on all of `K_S`. -/
@[bsd_tamagawa "T033b"]
theorem norm_configProd_le {S : Finset ℕ} {f : ↥(S.filter Nat.Prime) → ReductionData → ℂ}
    {B : ↥(S.filter Nat.Prime) → ℝ} (hf : ∀ q k, ‖f q k‖ ≤ B q) (y : configSpace S) :
    ‖configProd S f y‖ ≤ ∏ q : ↥(S.filter Nat.Prime), B q := by
  rw [configProd, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun q _ => norm_configFactor_le (hf q) _

/-- A bound `B_p` for `f_p` is nonnegative. -/
theorem configProd_bound_nonneg {S : Finset ℕ} {f : ↥(S.filter Nat.Prime) → ReductionData → ℂ}
    {B : ↥(S.filter Nat.Prime) → ℝ} (hf : ∀ q k, ‖f q k‖ ≤ B q) (q : ↥(S.filter Nat.Prime)) :
    0 ≤ B q :=
  le_trans (norm_nonneg (f q (KodairaSymbol.I 0, 0))) (hf q _)

/-- `G` is continuous on `∏_{p ∈ S} U_p`. -/
theorem continuousOn_configProd (S : Finset ℕ)
    (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ) :
    ContinuousOn (configProd S f) (configLocus S) :=
  continuousOn_finsetProd _ fun q _ =>
    (continuousOn_configFactor (f q)).comp (continuous_apply q).continuousOn fun _ hy => hy q

/-- If `G : K_S → ℂ` agrees with `configProd S f` on `∏_{p ∈ S} U_p`, then the discontinuity set of
`G` is `μ_S`-null. -/
@[bsd_tamagawa "T033b"]
theorem configMeasure_setOf_not_continuousAt_eq_zero (S : Finset ℕ)
    (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ) {G : configSpace S → ℂ}
    (hG : ∀ y ∈ configLocus S, G y = configProd S f y) :
    configMeasure S {y | ¬ ContinuousAt G y} = 0 := by
  refine measure_mono_null (fun y hy => ?_) (configMeasure_compl_configLocus S)
  by_contra hyl
  exact hy (((continuousOn_configProd S f).congr hG).continuousAt
    ((isOpen_configLocus S).mem_nhds (not_notMem.1 hyl)))

/-! ### The cutoff functions -/

/-- The product over `p ∈ S` of the norms of the coordinate discriminants. -/
noncomputable def configDiscrNorm (S : Finset ℕ) (y : configSpace S) : ℝ :=
  ∏ q : ↥(S.filter Nat.Prime), ‖(ofShortNF (y q).1 (y q).2).Δ‖

/-- `configDiscrNorm S` is continuous on `K_S`. -/
theorem continuous_configDiscrNorm (S : Finset ℕ) : Continuous (configDiscrNorm S) :=
  continuous_finsetProd _ fun q _ =>
    continuous_norm.comp (continuous_shortNF_Δ.comp (continuous_apply q))

/-- `configDiscrNorm S` is nonnegative. -/
theorem configDiscrNorm_nonneg (S : Finset ℕ) (y : configSpace S) : 0 ≤ configDiscrNorm S y :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- `configDiscrNorm S y` is positive exactly when `y ∈ ∏_{p ∈ S} U_p`. -/
theorem configDiscrNorm_pos_iff {S : Finset ℕ} {y : configSpace S} :
    0 < configDiscrNorm S y ↔ y ∈ configLocus S := by
  refine ⟨fun h q => ?_, fun h => Finset.prod_pos fun q _ => norm_pos_iff.2 (h q)⟩
  by_contra hq
  rw [configDiscrNorm,
    Finset.prod_eq_zero (Finset.mem_univ q) (by simpa [nonsingularLocus] using hq)] at h
  exact absurd h (lt_irrefl 0)

/-- For every `δ > 0` there is a continuous `φ : K_S → [0, 1]`, vanishing off `∏_{p ∈ S} U_p`, with
`∫ (1 - φ) dμ_S < δ`. -/
theorem exists_cutoff (S : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : configSpace S → ℝ, Continuous φ ∧ (∀ y, φ y ∈ Icc (0 : ℝ) 1) ∧
      (∀ y ∉ configLocus S, φ y = 0) ∧ ∫ y, (1 - φ y) ∂configMeasure S < δ := by
  have hIcc : ∀ (n : ℕ) (y : configSpace S),
      min 1 ((n : ℝ) * configDiscrNorm S y) ∈ Icc (0 : ℝ) 1 := fun n y =>
    ⟨le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) (configDiscrNorm_nonneg S y)),
      min_le_left _ _⟩
  have hc : ∀ n : ℕ, Continuous fun y : configSpace S => min 1 ((n : ℝ) * configDiscrNorm S y) :=
    fun n => continuous_const.min (continuous_const.mul (continuous_configDiscrNorm S))
  have hlim : Tendsto
      (fun n : ℕ => ∫ y, (1 - min 1 ((n : ℝ) * configDiscrNorm S y)) ∂configMeasure S)
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∫ _y : configSpace S, (0 : ℝ) ∂configMeasure S by simp]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (continuous_const.sub (hc n)).aestronglyMeasurable) (integrable_const 1)
      (fun n => .of_forall fun y => ?_) ?_
    · rw [Real.norm_of_nonneg (by linarith [(hIcc n y).2])]
      linarith [(hIcc n y).1]
    · filter_upwards [mem_ae_iff.2 (configMeasure_compl_configLocus S)] with y hy
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / configDiscrNorm S y)
      have hpos : 0 < configDiscrNorm S y := configDiscrNorm_pos_iff.2 hy
      have hNy : 1 ≤ (N : ℝ) * configDiscrNorm S y := by
        rw [← div_le_iff₀ hpos]; exact hN
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [min_eq_left (hNy.trans (by gcongr))]; ring
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hδ).exists
  exact ⟨_, hc n, hIcc n, fun y hy => by
    rw [show configDiscrNorm S y = 0 from le_antisymm
      (not_lt.1 fun h => hy (configDiscrNorm_pos_iff.1 h)) (configDiscrNorm_nonneg S y),
      mul_zero, min_eq_right zero_le_one], hn⟩

/-! ### Convergence of the integrals -/

/-- If `f_p` is bounded for each `p ∈ S` and `G : K_S → ℂ` agrees with `configProd S f` on
`∏_{p ∈ S} U_p`, then `∫_{K_S} G dμ_{S,X} → ∫_{K_S} G dμ_S` as `X → ∞`. -/
@[bsd_tamagawa "T033b"]
theorem tendsto_integral_configProd (S : Finset ℕ)
    (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ) {B : ↥(S.filter Nat.Prime) → ℝ}
    (hf : ∀ q k, ‖f q k‖ ≤ B q) {G : configSpace S → ℂ}
    (hG : ∀ y ∈ configLocus S, G y = configProd S f y) :
    Tendsto (fun X => ∫ y, G y ∂configEmpiricalMeasure S X) atTop
      (𝓝 (∫ y, G y ∂configMeasure S)) :=
  BSDTamagawa.Portmanteau.tendsto_integral_of_continuousOn_of_ae_mem
    (μ := configMeasure S) (ν := configEmpiricalMeasure S)
    (by filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX using
      isProbabilityMeasure_configEmpiricalMeasure hX)
    (fun _ hg => tendsto_integral_configEmpiricalMeasure S hg)
    (isOpen_configLocus S) (configMeasure_compl_configLocus S)
    (.of_forall (configEmpiricalMeasure_compl_configLocus S))
    (fun _ hδ => exists_cutoff S hδ)
    (Finset.prod_nonneg fun q _ => configProd_bound_nonneg hf q)
    ((continuousOn_configProd S f).congr hG)
    fun y hy => (hG y hy).symm ▸ norm_configProd_le hf y

end WeierstrassCurve
