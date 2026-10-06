/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarContinuity
public import BSDTamagawa.FactorCount.LimitingDensityExists

/-!
# The generating-function identity for `ρ_b` on the closed unit disc

For every `w : ℂ` with `‖w‖ ≤ 1` the series `∑_{b ≥ 0} ρ_b w^b` converges absolutely and

`∑_{b ≥ 0} ρ_b w^b = ∏_p h_p(0, w, ())`,

with `ρ_b = cardFactorsTamagawaDensity b` the limiting density of `Ω(Tam(·))` and `h_p` the scalar
local factor `scalarLocalFactor ∅ p 0 w`. Both sides are continuous on the closed disc and agree on
the open disc, which is dense in it.

## Main results

* `WeierstrassCurve.summable_norm_cardFactorsTamagawaDensity_mul_pow`: for `‖w‖ ≤ 1` the series
  `∑_b ρ_b w^b` converges absolutely.
* `WeierstrassCurve.tsum_cardFactorsTamagawaDensity_mul_pow`: for `‖w‖ ≤ 1`,
  `∑_b ρ_b w^b = ∏'_p h_p(0, w, ())`.
* `WeierstrassCurve.hasPolydiscExpansion_cardFactorsTamagawaDensity`: the densities `ρ_b` lie in
  `[0, 1]`, are summable with total mass at most `1`, and expand the Euler product on the open unit
  disc.
* `WeierstrassCurve.continuousOn_tsum_cardFactorsTamagawaDensity_mul_pow`: the series is continuous
  on the closed unit disc.
* `WeierstrassCurve.mem_closure_setOf_norm_lt_one`: the closed unit disc lies in the closure of the
  open one.
* `WeierstrassCurve.continuousOn_tprod_scalarLocalFactor_empty_zero`: the Euler product is
  continuous on the closed unit disc.

## Implementation notes

The Euler product is a `tprod`, not a `finprod`: the multiplicative support of `p ↦ h_p(0, w, ())`
is infinite for generic `w`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex BSDTamagawa.CoeffExtraction BSDTamagawa.FiberCount
open BSDTamagawa.PrimeCountDensity

/-! ### Moving a coefficient family between `Unit →₀ ℕ` and `ℕ` -/

/-- The equivalence `ℕ ≃ (Unit →₀ ℕ)` sending `b` to the `Finsupp` on `Unit` with value `b`. -/
private noncomputable def unitIndexEquiv : ℕ ≃ (Unit →₀ ℕ) :=
  (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm

private theorem summable_of_comp_unitIndexEquiv {f : (Unit →₀ ℕ) → ℝ} {d : ℕ → ℝ}
    (h : ∀ b : ℕ, f (unitIndexEquiv b) = d b) (hf : Summable f) : Summable d :=
  ((Equiv.summable_iff unitIndexEquiv).mpr hf).congr h

private theorem tsum_of_comp_unitIndexEquiv (f : (Unit →₀ ℕ) → ℝ) {d : ℕ → ℝ}
    (h : ∀ b : ℕ, f (unitIndexEquiv b) = d b) : (∑' b : ℕ, d b) = ∑' j : Unit →₀ ℕ, f j :=
  Eq.trans (tsum_congr fun b => (h b).symm) (Equiv.tsum_eq unitIndexEquiv f)

private theorem hasSum_of_comp_unitIndexEquiv {f : (Unit →₀ ℕ) → ℂ} {d : ℕ → ℂ} {a : ℂ}
    (h : ∀ b : ℕ, f (unitIndexEquiv b) = d b) (hf : HasSum f a) : HasSum d a :=
  ((Equiv.hasSum_iff unitIndexEquiv).mpr hf).congr_fun fun b => (h b).symm

/-! ### The densities as a sub-probability coefficient family on the open disc -/

/-- For a `Unit`-multi-index `j`, the `limUnder atTop` of the proportion of curves of height at
most `X` in the family whose `Ω(Tam(·))`, as a `Unit`-multi-index, equals `j` is
`cardFactorsTamagawaDensity (j ())`. -/
theorem limUnder_ncard_fiber_cardFactorsIndex (j : Unit →₀ ℕ) :
    (limUnder atTop fun X : ℝ =>
      (({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily} ∧
          Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
            ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)) = j}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ)))
      = cardFactorsTamagawaDensity (j ()) := by
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, j = Finsupp.equivFunOnFinite.symm (fun _ : Unit => b) := by
    refine ⟨j (), ?_⟩
    rw [show (fun _ : Unit => j ()) = ⇑j from funext fun i => by cases i; rfl]
    exact (Finsupp.equivFunOnFinite_symm_coe j).symm
  change _ = cardFactorsTamagawaDensity b
  rw [cardFactorsTamagawaDensity]
  refine congrArg (limUnder atTop) (funext fun X => ?_)
  rw [setOf_mem_and_cardFactorsIndex_eq b X, ncard_setOf_height_le_and_mem_family]

/-- The limiting densities `ρ_b` take values in `[0, 1]`, are summable with total mass at most `1`,
and expand the Euler product on the open unit disc: for `‖w‖ < 1`, the series `∑_{b ≥ 0} ρ_b w^b`
has sum `∏'_p h_p(0, w, ())`. -/
theorem hasPolydiscExpansion_cardFactorsTamagawaDensity :
    (∀ b : ℕ, cardFactorsTamagawaDensity b ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun b : ℕ => cardFactorsTamagawaDensity b) ∧
      (∑' b : ℕ, cardFactorsTamagawaDensity b) ≤ 1 ∧
      ∀ w : ℂ, ‖w‖ < 1 →
        HasSum (fun b : ℕ => ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b)
          (∏' p : ℕ, scalarLocalFactor ∅ p 0 w (fun _ => 0)) := by
  have hcoef : ∀ b : ℕ, (limUnder atTop fun X : ℝ =>
      (({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily} ∧
          Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
            ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)) =
              unitIndexEquiv b}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ)))
      = cardFactorsTamagawaDensity b := fun b =>
    limUnder_ncard_fiber_cardFactorsIndex (unitIndexEquiv b)
  obtain ⟨hIcc, hsum, hmass, hexp⟩ := hasPolydiscExpansion_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (fun q : ℤ × ℤ => Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
      ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)))
    (fun z : Unit → ℂ => ∏' p : ℕ, scalarLocalFactor ∅ p 0 (z ()) (fun _ => 0)) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_cardFactorsMonomial_div z hz)
  refine ⟨fun b => by rw [← hcoef b]; exact hIcc _, summable_of_comp_unitIndexEquiv hcoef hsum,
    le_of_eq_of_le (tsum_of_comp_unitIndexEquiv _ hcoef) hmass, fun w hw => ?_⟩
  refine hasSum_of_comp_unitIndexEquiv (fun b => ?_) (hexp (fun _ => w) fun _ => hw)
  simp only [hcoef b, smul_eq_mul]
  simp [unitIndexEquiv]

/-! ### Continuity of the series on the closed disc -/

/-- For `‖w‖ ≤ 1` and `0 ≤ c`, `‖c w^b‖ ≤ c`. -/
theorem norm_ofReal_mul_pow_le {w : ℂ} (hw : ‖w‖ ≤ 1) {c : ℝ} (hc : 0 ≤ c) (b : ℕ) :
    ‖((c : ℝ) : ℂ) * w ^ b‖ ≤ c := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc c * ‖w‖ ^ b ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hw) hc
    _ = c := mul_one c

/-- The function `w ↦ ∑_{b ≥ 0} ρ_b w^b` is continuous on the closed unit disc. -/
theorem continuousOn_tsum_cardFactorsTamagawaDensity_mul_pow :
    ContinuousOn (fun w : ℂ => ∑' b : ℕ, ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b)
      {w : ℂ | ‖w‖ ≤ 1} :=
  continuousOn_tsum (u := fun b : ℕ => cardFactorsTamagawaDensity b)
    (fun b => (continuous_const.mul (continuous_pow b)).continuousOn)
    hasPolydiscExpansion_cardFactorsTamagawaDensity.2.1
    fun b _ hw => norm_ofReal_mul_pow_le hw
      (hasPolydiscExpansion_cardFactorsTamagawaDensity.1 b).1 b

/-! ### Density of the open disc and continuity of the Euler product -/

/-- The closed unit disc in `ℂ` lies in the closure of the open unit disc. -/
theorem mem_closure_setOf_norm_lt_one {w : ℂ} (hw : ‖w‖ ≤ 1) :
    w ∈ closure {v : ℂ | ‖v‖ < 1} := by
  have hcont : Tendsto (fun t : ℝ => (t : ℂ) * w) (𝓝[<] (1 : ℝ)) (𝓝 w) := by
    have h : Continuous fun t : ℝ => (t : ℂ) * w :=
      Complex.continuous_ofReal.mul continuous_const
    simpa using (h.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht'
  calc ‖(t : ℂ) * w‖ = |t| * ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hw (abs_nonneg t)
    _ < 1 := by rw [mul_one]; exact abs_lt.2 ⟨ht', ht⟩

/-- The Euler product `w ↦ ∏'_p h_p(0, w, ())` is continuous on the closed unit disc. -/
theorem continuousOn_tprod_scalarLocalFactor_empty_zero :
    ContinuousOn (fun w : ℂ => ∏' p : ℕ, scalarLocalFactor ∅ p 0 w (fun _ => 0))
      {w : ℂ | ‖w‖ ≤ 1} := by
  refine (continuousOn_tprod_scalarLocalFactor ∅).comp
    (f := fun w : ℂ => ((0 : ℂ), w, (fun _ => 0 : (∅ : Finset ℕ) → ℂ))) (by fun_prop)
    fun w hw => ?_
  exact mem_scalarParamRegion.2 ⟨by simp, hw, fun _ => by simp⟩

/-! ### The generating-function identity on the closed disc -/

/-- For every `w : ℂ` with `‖w‖ ≤ 1` the series `∑_{b ≥ 0} ρ_b w^b` converges absolutely. -/
@[bsd_tamagawa "T046f"]
theorem summable_norm_cardFactorsTamagawaDensity_mul_pow {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable fun b : ℕ => ‖((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun b => norm_ofReal_mul_pow_le hw
      (hasPolydiscExpansion_cardFactorsTamagawaDensity.1 b).1 b)
    hasPolydiscExpansion_cardFactorsTamagawaDensity.2.1

/-- For every `w : ℂ` with `‖w‖ ≤ 1`,

`∑_{b ≥ 0} ρ_b w^b = ∏'_p h_p(0, w, ())`,

with `ρ_b` the limiting density of `Ω(Tam(·))` and `h_p` the scalar local factor at `Π = ∅`. -/
@[bsd_tamagawa "T046f"]
theorem tsum_cardFactorsTamagawaDensity_mul_pow {w : ℂ} (hw : ‖w‖ ≤ 1) :
    (∑' b : ℕ, ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b)
      = ∏' p : ℕ, scalarLocalFactor ∅ p 0 w (fun _ => 0) :=
  Set.EqOn.of_subset_closure
    (fun v hv => (hasPolydiscExpansion_cardFactorsTamagawaDensity.2.2.2 v hv).tsum_eq)
    continuousOn_tsum_cardFactorsTamagawaDensity_mul_pow
    continuousOn_tprod_scalarLocalFactor_empty_zero
    (fun v hv => show ‖v‖ ≤ 1 from le_of_lt hv)
    (fun _ hv => mem_closure_setOf_norm_lt_one hv) hw

end WeierstrassCurve
