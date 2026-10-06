/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarContinuity
public import BSDTamagawa.Valuation.LimitingJointDensityExists

/-!
# The joint valuation generating function on the closed unit polydisc

Let `Π` be a finite set of primes. For every `𝐳 ∈ ℂ^Π` with `‖z_ℓ‖ ≤ 1` for all `ℓ ∈ Π`, the family
`(Q_Π(𝐣) 𝐳^𝐣)_{𝐣 ∈ ℤ_{≥0}^Π}` is absolutely summable and

`∑_{𝐣} Q_Π(𝐣) 𝐳^𝐣 = ∏_p h_p(0, 1, 𝐳)`,

with `Q_Π(𝐣)` the limiting joint density of the `Π`-adic valuation vector of the Tamagawa product
and `h_p` the scalar local factor of the master Euler product.

## Main results

* `WeierstrassCurve.summable_norm_tamagawaValuationDensity_mul_multiMonomial`: on the closed unit
  polydisc the family `(Q_Π(𝐣) 𝐳^𝐣)_𝐣` is absolutely summable.
* `WeierstrassCurve.tsum_tamagawaValuationDensity_mul_multiMonomial`: on the closed unit polydisc
  `∑_{𝐣} Q_Π(𝐣) 𝐳^𝐣 = ∏_p h_p(0, 1, 𝐳)`.
* `WeierstrassCurve.hasPolydiscExpansion_tamagawaValuationDensity`: the densities `Q_Π(𝐣)` lie in
  `[0, 1]`, are summable with total mass at most `1`, and expand the Euler product on the open
  polydisc.
* `WeierstrassCurve.continuousOn_tsum_tamagawaValuationDensity_mul_multiMonomial`: the series is
  continuous on the closed polydisc.
* `WeierstrassCurve.mem_closure_setOf_forall_norm_lt_one`: the closed polydisc is contained in the
  closure of the open one.
* `WeierstrassCurve.continuousOn_tprod_scalarLocalFactor_zero_one`: the Euler product
  `𝐳 ↦ ∏_p h_p(0, 1, 𝐳)` is continuous on the closed polydisc.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex BSDTamagawa.CoeffExtraction BSDTamagawa.FiberCount
open BSDTamagawa.PrimeCountDensity

/-! ### Moving a multi-index family between `↥Π →₀ ℕ` and `↥Π → ℕ` -/

private theorem summable_of_comp_equivFunOnFinite {ι : Type*} [Finite ι] {f : (ι →₀ ℕ) → ℝ}
    {d : (ι → ℕ) → ℝ} (h : ∀ g : ι → ℕ, f (Finsupp.equivFunOnFinite.symm g) = d g)
    (hf : Summable f) : Summable d :=
  ((Equiv.summable_iff (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm).mpr hf).congr h

private theorem tsum_of_comp_equivFunOnFinite {ι : Type*} [Finite ι] (f : (ι →₀ ℕ) → ℝ)
    {d : (ι → ℕ) → ℝ} (h : ∀ g : ι → ℕ, f (Finsupp.equivFunOnFinite.symm g) = d g) :
    (∑' g : ι → ℕ, d g) = ∑' j : ι →₀ ℕ, f j :=
  Eq.trans (tsum_congr fun g => (h g).symm)
    (Equiv.tsum_eq (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm f)

private theorem hasSum_of_comp_equivFunOnFinite {ι : Type*} [Finite ι] {f : (ι →₀ ℕ) → ℂ}
    {d : (ι → ℕ) → ℂ} {a : ℂ} (h : ∀ g : ι → ℕ, f (Finsupp.equivFunOnFinite.symm g) = d g)
    (hf : HasSum f a) : HasSum d a :=
  ((Equiv.hasSum_iff (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm).mpr hf).congr_fun
    fun g => (h g).symm

/-! ### The densities are a sub-probability coefficient family on the open polydisc -/

/-- As `X → ∞`, the proportion of curves of height at most `X` whose valuation vector, read as a
finitely supported multi-index, equals that of `𝐣 : ↥Π → ℕ` has `limUnder atTop` equal to the
limiting joint density `Q_Π(𝐣)`. -/
theorem limUnder_ncard_fiber_tamagawaValuationIndex (P : Finset ℕ) (g : P → ℕ) :
    (limUnder atTop fun X : ℝ =>
      (({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily} ∧
          Finsupp.equivFunOnFinite.symm (tamagawaValuationVector P q.1 q.2) =
            Finsupp.equivFunOnFinite.symm g}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ)))
      = tamagawaValuationDensity P g := by
  rw [tamagawaValuationDensity]
  refine congrArg (limUnder atTop) (funext fun X => ?_)
  rw [setOf_mem_and_tamagawaValuationIndex_eq P g X, ncard_setOf_height_le_and_mem_family]

/-- **The densities expand the Euler product on the open polydisc.** For a finite set of primes
`Π`, the limiting joint densities `Q_Π(𝐣)` take values in `[0, 1]`, are summable with total mass at
most `1`, and expand the Euler product on the *open* unit polydisc:

`∑_{𝐣} Q_Π(𝐣) 𝐳^𝐣 = ∏'_p h_p(0, 1, 𝐳)` for `‖z_ℓ‖ < 1`, as a `HasSum`. -/
theorem hasPolydiscExpansion_tamagawaValuationDensity (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) :
    (∀ g : P → ℕ, tamagawaValuationDensity P g ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun g : P → ℕ => tamagawaValuationDensity P g) ∧
      (∑' g : P → ℕ, tamagawaValuationDensity P g) ≤ 1 ∧
      ∀ z : P → ℂ, (∀ ℓ, ‖z ℓ‖ < 1) →
        HasSum (fun g : P → ℕ => ((tamagawaValuationDensity P g : ℝ) : ℂ) * multiMonomial g z)
          (∏' p : ℕ, scalarLocalFactor P p 0 1 z) := by
  obtain ⟨hIcc, hsum, hmass, hexp⟩ := hasPolydiscExpansion_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (fun q : ℤ × ℤ => Finsupp.equivFunOnFinite.symm (tamagawaValuationVector P q.1 q.2))
    (fun z : P → ℂ => ∏' p : ℕ, scalarLocalFactor P p 0 1 z) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_tamagawaValuationMonomial_div P hP z hz)
  refine ⟨fun g => by rw [← limUnder_ncard_fiber_tamagawaValuationIndex P g]; exact hIcc _,
    summable_of_comp_equivFunOnFinite (limUnder_ncard_fiber_tamagawaValuationIndex P) hsum,
    le_of_eq_of_le
      (tsum_of_comp_equivFunOnFinite _ (limUnder_ncard_fiber_tamagawaValuationIndex P)) hmass,
    fun z hz => hasSum_of_comp_equivFunOnFinite (fun g => ?_) (hexp z hz)⟩
  simp only [limUnder_ncard_fiber_tamagawaValuationIndex P g, smul_eq_mul, multiMonomial]
  rfl

/-! ### The sum is absolutely summable and continuous on the closed polydisc -/

/-- **A monomial has norm at most `1` on the closed polydisc, so the series is dominated by its
coefficients.** For `‖z_ℓ‖ ≤ 1` and `0 ≤ c`, `‖c 𝐳^𝐣‖ ≤ c`. -/
theorem norm_ofReal_mul_multiMonomial_le {P : Finset ℕ} {z : P → ℂ} (hz : ∀ ℓ, ‖z ℓ‖ ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (g : P → ℕ) : ‖((c : ℝ) : ℂ) * multiMonomial g z‖ ≤ c := by
  have hle : ‖multiMonomial g z‖ ≤ 1 := by
    rw [multiMonomial, norm_prod]
    refine Finset.prod_le_one₀ (fun ℓ _ => norm_nonneg _) fun ℓ _ => ?_
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hz ℓ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc c * ‖multiMonomial g z‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hle hc
    _ = c := mul_one c

/-- **Each monomial is continuous in `𝐳`.** The map `𝐳 ↦ 𝐳^𝐣` is continuous. -/
theorem continuous_multiMonomial {P : Finset ℕ} (g : P → ℕ) :
    Continuous fun z : P → ℂ => multiMonomial g z := by
  simp only [multiMonomial]
  exact continuous_finsetProd _ fun ℓ _ => (continuous_apply ℓ).pow _

/-- **The sum is continuous on the closed unit polydisc.** For a finite set of primes `Π`, the
function `𝐳 ↦ ∑_{𝐣} Q_Π(𝐣) 𝐳^𝐣` is continuous on `{𝐳 : ‖z_ℓ‖ ≤ 1 for all ℓ}`. -/
theorem continuousOn_tsum_tamagawaValuationDensity_mul_multiMonomial (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) :
    ContinuousOn (fun z : P → ℂ =>
        ∑' g : P → ℕ, ((tamagawaValuationDensity P g : ℝ) : ℂ) * multiMonomial g z)
      {z : P → ℂ | ∀ ℓ, ‖z ℓ‖ ≤ 1} :=
  continuousOn_tsum (u := fun g : P → ℕ => tamagawaValuationDensity P g)
    (fun g => (continuous_const.mul (continuous_multiMonomial g)).continuousOn)
    (hasPolydiscExpansion_tamagawaValuationDensity P hP).2.1
    fun g _ hz => norm_ofReal_mul_multiMonomial_le hz
      ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 g).1 g

/-! ### The closed polydisc is the closure of the open one -/

/-- **The closed unit polydisc lies in the closure of the open one.** If `‖z_ℓ‖ ≤ 1` at every
coordinate, then `𝐳` lies in the closure of `{𝐲 : ‖y_ℓ‖ < 1 for all ℓ}`. -/
theorem mem_closure_setOf_forall_norm_lt_one {P : Type*} {z : P → ℂ} (hz : ∀ ℓ, ‖z ℓ‖ ≤ 1) :
    z ∈ closure {y : P → ℂ | ∀ ℓ, ‖y ℓ‖ < 1} := by
  have hcont : Tendsto (fun t : ℝ => (t : ℂ) • z) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
    have h : Continuous fun t : ℝ => (t : ℂ) • z :=
      Continuous.smul Complex.continuous_ofReal continuous_const
    simpa using (h.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht'
  intro ℓ
  calc ‖((t : ℂ) • z) ℓ‖ = |t| * ‖z ℓ‖ := by
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hz ℓ) (abs_nonneg t)
    _ < 1 := by rw [mul_one]; exact abs_lt.2 ⟨ht', ht⟩

/-- **The Euler product at `s = 0`, `w = 1` is continuous on the closed polydisc.** The function
`𝐳 ↦ ∏'_p h_p(0, 1, 𝐳)` is continuous on `{𝐳 : ‖z_ℓ‖ ≤ 1 for all ℓ}`. -/
theorem continuousOn_tprod_scalarLocalFactor_zero_one (P : Finset ℕ) :
    ContinuousOn (fun z : P → ℂ => ∏' p : ℕ, scalarLocalFactor P p 0 1 z)
      {z : P → ℂ | ∀ ℓ, ‖z ℓ‖ ≤ 1} := by
  refine (continuousOn_tprod_scalarLocalFactor P).comp
    (f := fun z : P → ℂ => ((0 : ℂ), (1 : ℂ), z)) (by fun_prop) fun z hz => ?_
  exact mem_scalarParamRegion.2 ⟨by simp, by simp, hz⟩

/-! ### The generating-function identity -/

/-- Let `Π` be a finite set of primes and `𝐳 ∈ ℂ^Π` with `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`. Then the
family `(Q_Π(𝐣) 𝐳^𝐣)_{𝐣 ∈ ℤ_{≥0}^Π}` is absolutely summable. -/
@[bsd_tamagawa "T044g"]
theorem summable_norm_tamagawaValuationDensity_mul_multiMonomial (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {z : P → ℂ} (hz : ∀ ℓ, ‖z ℓ‖ ≤ 1) :
    Summable fun g : P → ℕ => ‖((tamagawaValuationDensity P g : ℝ) : ℂ) * multiMonomial g z‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun g => norm_ofReal_mul_multiMonomial_le hz
      ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 g).1 g)
    (hasPolydiscExpansion_tamagawaValuationDensity P hP).2.1

/-- Let `Π` be a finite set of primes and `𝐳 ∈ ℂ^Π` with `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`. Then

`∑_{𝐣 ∈ ℤ_{≥0}^Π} Q_Π(𝐣) 𝐳^𝐣 = ∏_p h_p(0, 1, 𝐳)`,

with `Q_Π(𝐣)` the limiting joint valuation density and `h_p` the scalar local factor. -/
@[bsd_tamagawa "T044g"]
theorem tsum_tamagawaValuationDensity_mul_multiMonomial (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {z : P → ℂ} (hz : ∀ ℓ, ‖z ℓ‖ ≤ 1) :
    (∑' g : P → ℕ, ((tamagawaValuationDensity P g : ℝ) : ℂ) * multiMonomial g z)
      = ∏' p : ℕ, scalarLocalFactor P p 0 1 z :=
  Set.EqOn.of_subset_closure
    (fun y hy => ((hasPolydiscExpansion_tamagawaValuationDensity P hP).2.2.2 y hy).tsum_eq)
    (continuousOn_tsum_tamagawaValuationDensity_mul_multiMonomial P hP)
    (continuousOn_tprod_scalarLocalFactor_zero_one P) (fun _ hy ℓ => (hy ℓ).le)
    (fun _ hy => mem_closure_setOf_forall_norm_lt_one hy) hz

end WeierstrassCurve
