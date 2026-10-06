/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.CoefficientExtraction
public import BSDTamagawa.ReductionCount.DegeneratePoint
public import BSDTamagawa.ReductionCount.TruncatedPGFLimit

/-!
# Existence of the limiting joint density `π_Λ(𝐫)`

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every multi-index
`𝐫 = (r_K)_{K ∈ Λ} ∈ ℤ_{≥0}^Λ`,
`lim_{X → ∞} π_Λ(𝐫; X) = π_Λ(𝐫)`,
with `π_Λ(𝐫; X)` the height-truncated joint proportion `jointReductionOmegaProportion` and
`π_Λ(𝐫)` the joint density `jointReductionOmegaDensity`, the `limUnder atTop` of the same
quotient. For `X ≥ 4` the generating function `∑_𝐫 π_Λ(𝐫; X) 𝐮^𝐫` is the truncated master
generating function at the degenerate point, which converges to the joint Euler product
`F_Λ(𝐮)` on the unit polydisc; coefficient extraction then gives the convergence of each
`π_Λ(𝐫; X)`, and identifies the limits as the coefficients of `F_Λ` on the open polydisc.

## Main results

* `WeierstrassCurve.tendsto_jointReductionOmegaProportion_jointReductionOmegaDensity`: the
  displayed limit.
* `WeierstrassCurve.jointReductionOmegaProportion_nonneg`,
  `WeierstrassCurve.summable_jointReductionOmegaProportion`,
  `WeierstrassCurve.jointReductionOmegaProportion_le_one`: the truncated proportions form a
  probability vector for `X ≥ 4`.
* `WeierstrassCurve.jointReductionOmegaDensity_nonneg`,
  `WeierstrassCurve.summable_jointReductionOmegaDensity`: the densities are nonnegative and
  summable.
* `WeierstrassCurve.hasPolydiscExpansion_jointReductionOmegaDensity`: on the open unit polydisc,
  `F_Λ(𝐮) = ∑_𝐫 π_Λ(𝐫) 𝐮^𝐫` with absolute convergence.

## Implementation notes

Multi-indices are plain functions `↥Λ → ℕ`, while the coefficient-extraction theorem indexes by
`↥Λ →₀ ℕ`; on the finite type `↥Λ` the two agree by `Finsupp.equivFunOnFinite`. Since
`N(X) = 0` for `X < 4`, the family used for extraction is `π_Λ(𝐫; max X 4)`, which agrees with
`π_Λ(𝐫; X)` for `X ≥ 4`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex
open BSDTamagawa.CoeffExtraction BSDTamagawa.SubprobLimit

variable {Λ : Finset ReductionData}

/-! ### The truncated joint proportions are a probability vector -/

/-- The truncated joint proportion is nonnegative: a cardinality over a cardinality. -/
theorem jointReductionOmegaProportion_nonneg (Λ : Finset ReductionData) (r : Λ → ℕ) (X : ℝ) :
    0 ≤ jointReductionOmegaProportion Λ r X := by
  rw [jointReductionOmegaProportion]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- For `X ≥ 0`, the truncated joint proportions are summable in `𝐫`. -/
theorem summable_jointReductionOmegaProportion (Λ : Finset ReductionData) {X : ℝ} (hX : 0 ≤ X) :
    Summable fun r : Λ → ℕ => jointReductionOmegaProportion Λ r X :=
  summable_of_hasFiniteSupport (finite_setOf_jointReductionOmegaProportion_ne_zero Λ hX)

/-- For `X ≥ 4`, each truncated joint proportion is at most `1`. -/
theorem jointReductionOmegaProportion_le_one (Λ : Finset ReductionData) (r : Λ → ℕ) {X : ℝ}
    (hX : 4 ≤ X) : jointReductionOmegaProportion Λ r X ≤ 1 := by
  have h0 : (0 : ℝ) ≤ X := le_trans (by norm_num) hX
  refine le_of_le_of_eq ((summable_jointReductionOmegaProportion Λ h0).le_tsum r
    fun r' _ => jointReductionOmegaProportion_nonneg Λ r' X) ?_
  exact tsum_jointReductionOmegaProportion_eq_one Λ hX

/-! ### The multi-index bridge `↥Λ →₀ ℕ ≃ (↥Λ → ℕ)` -/

/-- A `tsum` over `Finsupp` multi-indices `↥Λ →₀ ℕ` equals the `tsum` over plain multi-indices
`↥Λ → ℕ`. -/
private theorem tsum_comp_finsuppCoe {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (Λ : Finset ReductionData) (f : (Λ → ℕ) → M) :
    ∑' j : Λ →₀ ℕ, f (⇑j) = ∑' r : Λ → ℕ, f r :=
  (Finsupp.equivFunOnFinite (α := ↥Λ) (M := ℕ)).tsum_eq f

/-- A summable family over `↥Λ → ℕ` is summable over `↥Λ →₀ ℕ`. -/
private theorem summable_comp_finsuppCoe {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (Λ : Finset ReductionData) (f : (Λ → ℕ) → M) (hf : Summable f) :
    Summable fun j : Λ →₀ ℕ => f (⇑j) :=
  (Finsupp.equivFunOnFinite (α := ↥Λ) (M := ℕ)).summable_iff (f := f) |>.mpr hf

/-- A family over `↥Λ → ℕ` that is summable over `↥Λ →₀ ℕ` is summable. -/
private theorem summable_of_summable_comp_finsuppCoe {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] (Λ : Finset ReductionData) (f : (Λ → ℕ) → M)
    (hf : Summable fun j : Λ →₀ ℕ => f (⇑j)) : Summable f :=
  (Finsupp.equivFunOnFinite (α := ↥Λ) (M := ℕ)).summable_iff (f := f) |>.mp hf

/-! ### The coefficient family of the truncated generating function -/

/-- The truncated joint proportions `π_Λ(𝐫; max X 4)`, indexed by `Finsupp` multi-indices. -/
private noncomputable def truncatedJointCoeff (Λ : Finset ReductionData) (X : ℝ)
    (j : Λ →₀ ℕ) : ℝ :=
  jointReductionOmegaProportion Λ (⇑j) (max X 4)

/-- For `X ≥ 4`, `truncatedJointCoeff Λ X j = π_Λ(j; X)`. -/
private theorem truncatedJointCoeff_apply (Λ : Finset ReductionData) {X : ℝ} (hX : 4 ≤ X)
    (j : Λ →₀ ℕ) :
    truncatedJointCoeff Λ X j = jointReductionOmegaProportion Λ (⇑j) X := by
  rw [truncatedJointCoeff, max_eq_left hX]

/-- The coefficients `truncatedJointCoeff` lie in `[0, 1]`. -/
private theorem truncatedJointCoeff_mem_Icc (Λ : Finset ReductionData) :
    ∀ X : ℝ, 1 ≤ X → ∀ j : Λ →₀ ℕ, truncatedJointCoeff Λ X j ∈ Set.Icc (0 : ℝ) 1 := by
  intro X _ j
  refine ⟨jointReductionOmegaProportion_nonneg Λ _ _, ?_⟩
  exact jointReductionOmegaProportion_le_one Λ _ (le_max_right X 4)

/-- The coefficient family `truncatedJointCoeff Λ X` is summable. -/
private theorem summable_truncatedJointCoeff (Λ : Finset ReductionData) :
    ∀ X : ℝ, 1 ≤ X → Summable (truncatedJointCoeff Λ X) := by
  intro X _
  exact summable_comp_finsuppCoe Λ _
    (summable_jointReductionOmegaProportion Λ (le_trans (by norm_num) (le_max_right X 4)))

/-- The coefficients `truncatedJointCoeff Λ X` sum to `1`. -/
private theorem tsum_truncatedJointCoeff (Λ : Finset ReductionData) :
    ∀ X : ℝ, 1 ≤ X → ∑' j : Λ →₀ ℕ, truncatedJointCoeff Λ X j = 1 := by
  intro X _
  refine Eq.trans ?_ (tsum_jointReductionOmegaProportion_eq_one Λ (le_max_right X 4))
  exact tsum_comp_finsuppCoe Λ fun r : Λ → ℕ => jointReductionOmegaProportion Λ r (max X 4)

/-- For `X ≥ 4` the generating function of the coefficient family is the truncated master
generating function at the degenerate point:
`∑_𝐫 π_Λ(𝐫; X) 𝐮^𝐫 = 𝒵_{Λ, ∅, X}(0; 1, 1, ∅, 𝐮)`. -/
private theorem genFun_truncatedJointCoeff (Λ : Finset ReductionData)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) {X : ℝ} (hX : 4 ≤ X) :
    genFun (truncatedJointCoeff Λ) X uΛ = tamagawaGeneratingFunction Λ ∅ 0 1 1 z uΛ X := by
  calc genFun (truncatedJointCoeff Λ) X uΛ
      = ∑' j : Λ →₀ ℕ, (jointReductionOmegaProportion Λ (⇑j) X : ℂ) * multiMonomial (⇑j) uΛ := by
        rw [genFun]
        exact tsum_congr fun j => by rw [truncatedJointCoeff_apply Λ hX j, smul_eq_mul]
    _ = ∑' r : Λ → ℕ, (jointReductionOmegaProportion Λ r X : ℂ) * multiMonomial r uΛ :=
        tsum_comp_finsuppCoe Λ fun r : Λ → ℕ =>
          (jointReductionOmegaProportion Λ r X : ℂ) * multiMonomial r uΛ
    _ = tamagawaGeneratingFunction Λ ∅ 0 1 1 z uΛ X :=
        (tamagawaGeneratingFunction_eq_tsum_jointReductionOmegaProportion Λ z uΛ hX).symm

/-- On the open unit polydisc the generating functions of the coefficient family converge to
`F_Λ(𝐮)`. -/
private theorem tendsto_genFun_truncatedJointCoeff (hΛ : Admissible Λ) :
    ∀ u : Λ → ℂ, (∀ K, ‖u K‖ < 1) →
      Tendsto (fun X : ℝ => genFun (truncatedJointCoeff Λ) X u) atTop
        (𝓝 (jointReductionOmegaEulerProduct Λ u)) := by
  intro u hu
  refine Tendsto.congr' ?_ (tendsto_tamagawaGeneratingFunction_jointReductionOmegaEulerProduct
    hΛ (fun _ => 0) fun K => (hu K).le)
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
  exact (genFun_truncatedJointCoeff Λ (fun _ => 0) u hX).symm

/-! ### Coefficient extraction -/

/-- For `Λ` admissible:

* every truncated proportion converges to the joint density;
* each density lies in `[0, 1]`, the family is summable and its total mass is at most `1`;
* on the open unit polydisc, `F_Λ(𝐮) = ∑_𝐫 π_Λ(𝐫) 𝐮^𝐫`, absolutely convergent. -/
private theorem jointReductionOmegaDensity_spec (hΛ : Admissible Λ) :
    (∀ r : Λ → ℕ, Tendsto (fun X : ℝ => jointReductionOmegaProportion Λ r X) atTop
        (𝓝 (jointReductionOmegaDensity Λ r))) ∧
      (∀ r : Λ → ℕ, jointReductionOmegaDensity Λ r ∈ Set.Icc (0 : ℝ) 1) ∧
      (Summable fun r : Λ → ℕ => jointReductionOmegaDensity Λ r) ∧
      (∑' r : Λ → ℕ, jointReductionOmegaDensity Λ r ≤ 1) ∧
      HasPolydiscExpansion (fun j : Λ →₀ ℕ => ((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ))
        (jointReductionOmegaEulerProduct Λ) := by
  obtain ⟨c, hcIcc, ⟨hcsum, hcmass⟩, hccoef, -, hcexp⟩ :=
    exists_coeff_tendsto_of_tendsto_genFun (truncatedJointCoeff Λ)
      (truncatedJointCoeff_mem_Icc Λ) (summable_truncatedJointCoeff Λ)
      (tsum_truncatedJointCoeff Λ) (jointReductionOmegaEulerProduct Λ)
      (tendsto_genFun_truncatedJointCoeff hΛ)
  have hcoef : ∀ j : Λ →₀ ℕ,
      Tendsto (fun X : ℝ => jointReductionOmegaProportion Λ (⇑j) X) atTop (𝓝 (c j)) := by
    intro j
    refine Tendsto.congr' ?_ (hccoef j)
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
    exact truncatedJointCoeff_apply Λ hX j
  have hc_eq : ∀ j : Λ →₀ ℕ, c j = jointReductionOmegaDensity Λ (⇑j) := by
    intro j
    rw [jointReductionOmegaDensity]
    exact ((hcoef j).limUnder_eq).symm
  have hcfun : (fun j : Λ →₀ ℕ => jointReductionOmegaDensity Λ (⇑j)) = c :=
    funext fun j => (hc_eq j).symm
  refine ⟨fun r => ?_, fun r => ?_, ?_, ?_, ?_⟩
  · have h := hcoef (Finsupp.equivFunOnFinite.symm r)
    rwa [hc_eq (Finsupp.equivFunOnFinite.symm r), Finsupp.coe_equivFunOnFinite_symm] at h
  · have h := hcIcc (Finsupp.equivFunOnFinite.symm r)
    rwa [hc_eq (Finsupp.equivFunOnFinite.symm r), Finsupp.coe_equivFunOnFinite_symm] at h
  · refine summable_of_summable_comp_finsuppCoe Λ
      (fun r : Λ → ℕ => jointReductionOmegaDensity Λ r) ?_
    rw [hcfun]
    exact hcsum
  · rw [← tsum_comp_finsuppCoe Λ fun r : Λ → ℕ => jointReductionOmegaDensity Λ r, hcfun]
    exact hcmass
  · simpa only [← hc_eq] using hcexp

/-! ### Convergence of the truncated joint proportions -/

/-- Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data. For every multi-index
`𝐫 = (r_K)_{K ∈ Λ} ∈ ℤ_{≥0}^Λ`, `lim_{X → ∞} π_Λ(𝐫; X) = π_Λ(𝐫)`, with `π_Λ(𝐫; X)` the
height-truncated joint proportion and `π_Λ(𝐫)` the joint density. -/
@[bsd_tamagawa "T040n"]
theorem tendsto_jointReductionOmegaProportion_jointReductionOmegaDensity (hΛ : Admissible Λ)
    (r : Λ → ℕ) :
    Tendsto (fun X : ℝ => jointReductionOmegaProportion Λ r X) atTop
      (𝓝 (jointReductionOmegaDensity Λ r)) :=
  (jointReductionOmegaDensity_spec hΛ).1 r

/-! ### The joint densities: nonnegativity, summability and the polydisc expansion -/

/-- The joint density is nonnegative. -/
theorem jointReductionOmegaDensity_nonneg (hΛ : Admissible Λ) (r : Λ → ℕ) :
    0 ≤ jointReductionOmegaDensity Λ r :=
  ((jointReductionOmegaDensity_spec hΛ).2.1 r).1

/-- The joint densities are summable over `𝐫 ∈ ℤ_{≥0}^Λ`. -/
theorem summable_jointReductionOmegaDensity (hΛ : Admissible Λ) :
    Summable fun r : Λ → ℕ => jointReductionOmegaDensity Λ r :=
  (jointReductionOmegaDensity_spec hΛ).2.2.1

/-- On the open unit polydisc the family `(π_Λ(𝐫) 𝐮^𝐫)_𝐫` is summable with sum `F_Λ(𝐮)`: the
joint densities are the coefficients of `F_Λ`. -/
theorem hasPolydiscExpansion_jointReductionOmegaDensity (hΛ : Admissible Λ) :
    HasPolydiscExpansion (fun j : Λ →₀ ℕ => ((jointReductionOmegaDensity Λ (⇑j) : ℝ) : ℂ))
      (jointReductionOmegaEulerProduct Λ) :=
  (jointReductionOmegaDensity_spec hΛ).2.2.2.2

end WeierstrassCurve
