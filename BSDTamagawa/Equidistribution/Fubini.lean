/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import BSDTamagawa.Equidistribution.Portmanteau
public import BSDTamagawa.PrimeCount.LocalFactorCollapse

/-!
# Fubini factorization of the limit integral

Let `S` be a finite set of primes, `f_p : 𝒦 → ℂ` bounded for `p ∈ S`, and `G : K_S → ℂ` any
function equal to `∏_{p ∈ S} f_p(τ_p(x_p))` on the nonsingular locus. Then

  `∫_{K_S} G dμ_S = ∏_{p ∈ S} (∑_{K ∈ 𝒦} δ_p(K) f_p(K))`.

The nonsingular locus has full measure, `μ_S` is a finite product measure, and each one-variable
integral is computed by decomposing `f_p ∘ τ_p` along the fibres of the reduction datum, whose
`μ_p`-masses are the densities `δ_p(K)`.

## Main definitions

* `WeierstrassCurve.stratFibre`: the fibre of the reduction datum over `K` in the coefficient
  plane.

## Main results

* `WeierstrassCurve.isOpen_stratFibre`: the fibres are open.
* `WeierstrassCurve.volume_stratFibre`: the fibre over `K` has mass `δ_p(K)`.
* `WeierstrassCurve.integral_configFactor`: `∫_{ℤ_p²} f_p(τ_p(x)) dμ_p = ∑_{K ∈ 𝒦} δ_p(K) f_p(K)`.
* `WeierstrassCurve.integral_configProd_eq_prod_tsum`: the factorization of the integral.
-/

@[expose] public section

open MeasureTheory Set

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### The fibres of the reduction datum on the coefficient plane -/

/-- The fibre of the reduction datum over `K` in the coefficient plane: the nonsingular pairs
`(a₄, a₆) ∈ U_p` whose reduction datum is `K`. -/
def stratFibre (p : ℕ) [Fact p.Prime] (K : ReductionData) : Set (ℤ_[p] × ℤ_[p]) :=
  Subtype.val '' (strat p ⁻¹' {K})

/-- A fibre of the reduction datum consists of nonsingular pairs. -/
lemma stratFibre_subset (K : ReductionData) : stratFibre p K ⊆ nonsingularLocus p := by
  rintro x ⟨y, -, rfl⟩; exact y.2

/-- A nonsingular pair `x` lies in the fibre over `K` if and only if its reduction datum is `K`. -/
lemma mem_stratFibre_iff {K : ReductionData} {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ nonsingularLocus p) :
    x ∈ stratFibre p K ↔ strat p ⟨x, hx⟩ = K := by
  refine ⟨?_, fun h => ⟨⟨x, hx⟩, h, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact hy

/-- A singular pair lies in no fibre of the reduction datum. -/
lemma notMem_stratFibre {K : ReductionData} {x : ℤ_[p] × ℤ_[p]} (hx : x ∉ nonsingularLocus p) :
    x ∉ stratFibre p K := fun h => hx (stratFibre_subset K h)

/-- The fibres of the reduction datum are open in the coefficient plane. -/
lemma isOpen_stratFibre (K : ReductionData) : IsOpen (stratFibre p K) :=
  isOpen_nonsingularLocus.isOpenMap_subtype_val _ (isLocallyConstant_strat p _)

/-! ### The masses of the fibres -/

/-- A coefficient pair is nonsingular exactly when its short model lies in the elliptic locus: both
say `Δ(E(a₄, a₆)) ≠ 0`. -/
lemma ShortNF.ofProd_mem_Elliptic_iff_mem_nonsingularLocus {x : ℤ_[p] × ℤ_[p]} :
    ShortNF.ofProd x.1 x.2 ∈ ShortNF.Elliptic ℤ_[p] ↔ x ∈ nonsingularLocus p := Iff.rfl

/-- Reading the short model of a pair back off as its coefficient pair returns the pair. -/
lemma ShortNF.Elliptic.coeffs_ofProd {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ nonsingularLocus p) :
    ShortNF.Elliptic.coeffs p ⟨ShortNF.ofProd x.1 x.2,
        ShortNF.ofProd_mem_Elliptic_iff_mem_nonsingularLocus.2 hx⟩ = ⟨x, hx⟩ :=
  rfl

/-- At a nonsingular pair, the reduction datum `strat p` is the reduction datum of `tauP` at the
short model `E(a₄, a₆)`. -/
lemma strat_eq_tauP {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ nonsingularLocus p) :
    strat p ⟨x, hx⟩
      = ((tauP p ⟨ShortNF.ofProd x.1 x.2,
            ShortNF.ofProd_mem_Elliptic_iff_mem_nonsingularLocus.2 hx⟩).kodairaSymbol,
         (tauP p ⟨ShortNF.ofProd x.1 x.2,
            ShortNF.ofProd_mem_Elliptic_iff_mem_nonsingularLocus.2 hx⟩).tamagawaNumber) := by
  rw [← ShortNF.Elliptic.coeffs_ofProd hx, strat_coeffs]

/-- The `μ_p`-mass of the fibre over `K` is `δ_p(K)`. -/
lemma volume_stratFibre (K : ReductionData) : volume (stratFibre p K) = deltaP p K := by
  rw [deltaP,
    show (volume : Measure (ShortNF.Elliptic ℤ_[p])) = Measure.comap Subtype.val volume from rfl,
    comap_subtype_coe_apply ShortNF.Elliptic.measurableSet,
    show (volume : Measure (ShortNF ℤ_[p]))
      = Measure.map (Function.uncurry ShortNF.ofProd) volume from rfl,
    Measure.map_apply ShortNF.measurable_ofProd
      (ShortNF.Elliptic.measurableSet.subtype_image (measurableSet_reductionDatum_fiber p K))]
  congr 1
  ext x
  constructor
  · intro hxF
    have hx := stratFibre_subset K hxF
    exact ⟨⟨_, ShortNF.ofProd_mem_Elliptic_iff_mem_nonsingularLocus.2 hx⟩,
      (strat_eq_tauP hx).symm.trans ((mem_stratFibre_iff hx).1 hxF), rfl⟩
  · rintro ⟨⟨_, hw⟩, hW, rfl⟩
    have hx := ShortNF.ofProd_mem_Elliptic_iff_mem_nonsingularLocus.1 hw
    exact (mem_stratFibre_iff hx).2 ((strat_eq_tauP hx).trans hW)

/-! ### The one-variable integral -/

/-- At every point `x` of the coefficient plane,
`∑'_K 1_{stratFibre p K}(x) g(K) = configFactor p g x`. -/
lemma configFactor_eq_tsum_indicator (g : ReductionData → ℂ) (x : ℤ_[p] × ℤ_[p]) :
    ∑' K : ReductionData, (stratFibre p K).indicator (fun _ => g K) x = configFactor p g x := by
  by_cases hx : x ∈ nonsingularLocus p
  · rw [tsum_eq_single (strat p ⟨x, hx⟩) fun K hK =>
      Set.indicator_of_notMem (fun h => hK ((mem_stratFibre_iff hx).1 h).symm) _,
      Set.indicator_of_mem ((mem_stratFibre_iff hx).2 rfl), configFactor, dite_eq_left hx]
  · rw [configFactor_of_notMem g hx]
    simp only [Set.indicator_of_notMem (notMem_stratFibre hx), tsum_zero]

/-- `∫⁻ ‖1_{stratFibre p K} g(K)‖ₑ dμ_p = ‖g(K)‖ₑ δ_p(K)`. -/
lemma lintegral_enorm_indicator_stratFibre (g : ReductionData → ℂ) (K : ReductionData) :
    ∫⁻ x, ‖(stratFibre p K).indicator (fun _ => g K) x‖ₑ ∂(volume : Measure (ℤ_[p] × ℤ_[p]))
      = ‖g K‖ₑ * deltaP p K := by
  have h : (fun x => ‖(stratFibre p K).indicator (fun _ => g K) x‖ₑ)
      = (stratFibre p K).indicator (fun _ => ‖g K‖ₑ) := by
    funext x
    by_cases hx : x ∈ stratFibre p K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero]
  rw [h, lintegral_indicator_const (isOpen_stratFibre K).measurableSet, volume_stratFibre]

/-- For bounded `g : 𝒦 → ℂ`, `∫_{ℤ_p²} g(τ_p(x)) dμ_p = ∑_{K ∈ 𝒦} δ_p(K) g(K)`. -/
theorem integral_configFactor {g : ReductionData → ℂ} {B : ℝ} (hg : ∀ k, ‖g k‖ ≤ B) :
    ∫ x, configFactor p g x ∂(volume : Measure (ℤ_[p] × ℤ_[p]))
      = ∑' K : ReductionData, ((deltaP p K).toReal : ℂ) * g K := by
  have hmeas : ∀ K : ReductionData,
      AEStronglyMeasurable ((stratFibre p K).indicator fun _ => g K)
        (volume : Measure (ℤ_[p] × ℤ_[p])) := fun K =>
    (stronglyMeasurable_const.indicator (isOpen_stratFibre K).measurableSet).aestronglyMeasurable
  have hfin : ∑' K : ReductionData,
      ∫⁻ x, ‖(stratFibre p K).indicator (fun _ => g K) x‖ₑ
        ∂(volume : Measure (ℤ_[p] × ℤ_[p])) ≠ ⊤ := by
    have hle : ∀ K : ReductionData,
        ∫⁻ x, ‖(stratFibre p K).indicator (fun _ => g K) x‖ₑ
          ∂(volume : Measure (ℤ_[p] × ℤ_[p])) ≤ ENNReal.ofReal B * deltaP p K := by
      intro K
      rw [lintegral_enorm_indicator_stratFibre g K]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hg K)
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_)
    rw [ENNReal.tsum_mul_left, tsum_deltaP, mul_one]
    exact ENNReal.ofReal_lt_top
  calc ∫ x, configFactor p g x ∂(volume : Measure (ℤ_[p] × ℤ_[p]))
      = ∫ x, ∑' K : ReductionData, (stratFibre p K).indicator (fun _ => g K) x
          ∂(volume : Measure (ℤ_[p] × ℤ_[p])) := by
        simp only [configFactor_eq_tsum_indicator]
    _ = ∑' K : ReductionData, ∫ x, (stratFibre p K).indicator (fun _ => g K) x
          ∂(volume : Measure (ℤ_[p] × ℤ_[p])) := integral_tsum hmeas hfin
    _ = ∑' K : ReductionData, ((deltaP p K).toReal : ℂ) * g K := by
        refine tsum_congr fun K => ?_
        rw [integral_indicator_const _ (isOpen_stratFibre K).measurableSet, measureReal_def,
          volume_stratFibre, Complex.real_smul]

/-! ### The factorization -/

/-- Let `f_p : 𝒦 → ℂ` be bounded for `p ∈ S`, and let `G : K_S → ℂ` agree with
`∏_{p ∈ S} f_p(τ_p(x_p))` on the nonsingular locus. Then
`∫_{K_S} G dμ_S = ∏_{p ∈ S} (∑_{K ∈ 𝒦} δ_p(K) f_p(K))`. -/
@[bsd_tamagawa "T033c"]
theorem integral_configProd_eq_prod_tsum (S : Finset ℕ)
    (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ) {B : ↥(S.filter Nat.Prime) → ℝ}
    (hf : ∀ q k, ‖f q k‖ ≤ B q) {G : configSpace S → ℂ}
    (hG : ∀ y ∈ configLocus S, G y = configProd S f y) :
    (∫ y, G y ∂configMeasure S)
      = ∏ q : ↥(S.filter Nat.Prime),
          ∑' K : ReductionData, ((deltaP (q : ℕ) K).toReal : ℂ) * f q K := by
  have hae : ∀ᵐ y ∂configMeasure S, G y = configProd S f y := by
    filter_upwards [mem_ae_iff.2 (configMeasure_compl_configLocus S)] with y hy
    exact hG y hy
  rw [integral_congr_ae hae, configMeasure]
  simp only [configProd]
  rw [integral_fintype_prod_eq_prod
    fun (q : ↥(S.filter Nat.Prime)) (x : ℤ_[(q : ℕ)] × ℤ_[(q : ℕ)]) =>
      configFactor (q : ℕ) (f q) x]
  exact Finset.prod_congr rfl fun q _ => integral_configFactor (hf q)

end WeierstrassCurve
