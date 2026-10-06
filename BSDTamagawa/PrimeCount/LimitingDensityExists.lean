/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.CoefficientExtraction
public import BSDTamagawa.PrimeCount.DegeneratePoint
public import BSDTamagawa.PrimeCount.TruncatedPGFLimit

/-!
# Existence of the limiting density `π_r`

For every `r : ℕ`, `lim_{X → ∞} π_r(X) = π_r`, where `π_r(X)` is the proportion of integral short
Weierstrass models of height at most `X` whose Tamagawa product has exactly `r` distinct prime
factors, and `π_r = limUnder atTop (π_r ·)`. The proof applies coefficientwise convergence of
generating functions on the open unit disc, with the single index set `Unit`, to the empirical
fibre proportions of the statistic `ω_Tam`.

## Main results

* `BSDTamagawa.PrimeCountDensity.tendsto_coeff_limUnder_of_tendsto_genFun`: if probability vectors
  `a X` have generating functions converging pointwise on the open unit polydisc, each coefficient
  `X ↦ a X k` converges to `limUnder atTop (a · k)`.
* `BSDTamagawa.PrimeCountDensity.hasPolydiscExpansion_limUnder_of_tendsto_genFun`: the limiting
  coefficients form a sub-probability vector expanding the limit function.
* `BSDTamagawa.PrimeCountDensity.tendsto_ncard_fiber_div_limUnder` and
  `BSDTamagawa.PrimeCountDensity.hasPolydiscExpansion_ncard_fiber_div_limUnder`: the same for the
  empirical fibre proportions `#{x ∈ S(X) : f x = 𝐣} / #S(X)` of a statistic `f`.
* `WeierstrassCurve.tendsto_tamagawaOmegaProportion_tamagawaOmegaDensity`: `π_r(X) → π_r`.
-/

@[expose] public section

open Filter Topology

namespace BSDTamagawa.PrimeCountDensity

open BSDTamagawa.MultiIndex BSDTamagawa.CoeffExtraction BSDTamagawa.SubprobLimit
open BSDTamagawa.FiberCount BSDTamagawa.DegeneratePoint

variable {α ι : Type*} [Fintype ι]

/-! ### Coefficientwise convergence with an arbitrary threshold, in `limUnder` form -/

/-- **Coefficientwise convergence, in `limUnder` form.** Let `a X : (ι →₀ ℕ) → ℝ` be a probability
vector for every `X ≥ X₀` — values in `[0, 1]`, summable, total mass `1` — and suppose the
generating functions `genFun a X` converge pointwise on the open unit polydisc to `F`. Then for
every multi-index `k` the coefficient `X ↦ a X k` converges to `Filter.limUnder atTop (a · k)`. -/
theorem tendsto_coeff_limUnder_of_tendsto_genFun (a : ℝ → (ι →₀ ℕ) → ℝ) (X₀ : ℝ)
    (ha : ∀ X : ℝ, X₀ ≤ X → ∀ k, a X k ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ X : ℝ, X₀ ≤ X → Summable (a X))
    (hmass : ∀ X : ℝ, X₀ ≤ X → ∑' k, a X k = 1)
    (F : (ι → ℂ) → ℂ)
    (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ => genFun a X z) atTop (𝓝 (F z)))
    (k : ι →₀ ℕ) :
    Tendsto (fun X : ℝ => a X k) atTop (𝓝 (limUnder atTop fun X : ℝ => a X k)) := by
  have hshift : ∀ X : ℝ, 1 ≤ X → X₀ ≤ X + (X₀ - 1) := fun X hX => by linarith
  obtain ⟨c, -, -, hcoef, -, -⟩ := exists_coeff_tendsto_of_tendsto_genFun
    (fun X => a (X + (X₀ - 1))) (fun X hX => ha _ (hshift X hX))
    (fun X hX => hsum _ (hshift X hX)) (fun X hX => hmass _ (hshift X hX)) F
    (fun z hz => (hF z hz).comp (tendsto_atTop_add_const_right atTop (X₀ - 1) tendsto_id))
  have hback : Tendsto (fun X : ℝ => a X k) atTop (𝓝 (c k)) := by
    have hmap : Tendsto (fun X : ℝ => X + -(X₀ - 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-(X₀ - 1)) tendsto_id
    refine ((hcoef k).comp hmap).congr fun X => ?_
    change a (X + -(X₀ - 1) + (X₀ - 1)) k = a X k
    rw [show X + -(X₀ - 1) + (X₀ - 1) = X from by ring]
  rw [hback.limUnder_eq]
  exact hback

/-- **The limiting coefficients expand the limit.** Under the hypotheses of
`tendsto_coeff_limUnder_of_tendsto_genFun`, the family `k ↦ limUnder atTop (a · k)` takes values in
`[0, 1]`, is summable of total mass at most `1`, and expands `F` on the open unit polydisc. -/
theorem hasPolydiscExpansion_limUnder_of_tendsto_genFun (a : ℝ → (ι →₀ ℕ) → ℝ) (X₀ : ℝ)
    (ha : ∀ X : ℝ, X₀ ≤ X → ∀ k, a X k ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ X : ℝ, X₀ ≤ X → Summable (a X))
    (hmass : ∀ X : ℝ, X₀ ≤ X → ∑' k, a X k = 1)
    (F : (ι → ℂ) → ℂ)
    (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ => genFun a X z) atTop (𝓝 (F z))) :
    (∀ k, (limUnder atTop fun X : ℝ => a X k) ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun k => limUnder atTop fun X : ℝ => a X k) ∧
      (∑' k : ι →₀ ℕ, limUnder atTop fun X : ℝ => a X k) ≤ 1 ∧
      HasPolydiscExpansion (fun k => ((limUnder atTop fun X : ℝ => a X k : ℝ) : ℂ)) F := by
  have hshift : ∀ X : ℝ, 1 ≤ X → X₀ ≤ X + (X₀ - 1) := fun X hX => by linarith
  obtain ⟨c, hc, ⟨hsumc, hmassc⟩, hcoef, -, hexp⟩ := exists_coeff_tendsto_of_tendsto_genFun
    (fun X => a (X + (X₀ - 1))) (fun X hX => ha _ (hshift X hX))
    (fun X hX => hsum _ (hshift X hX)) (fun X hX => hmass _ (hshift X hX)) F
    (fun z hz => (hF z hz).comp (tendsto_atTop_add_const_right atTop (X₀ - 1) tendsto_id))
  have hmap : Tendsto (fun X : ℝ => X + -(X₀ - 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-(X₀ - 1)) tendsto_id
  have hkey : ∀ k, (limUnder atTop fun X : ℝ => a X k) = c k := fun k => by
    refine tendsto_nhds_unique
      (tendsto_coeff_limUnder_of_tendsto_genFun a X₀ ha hsum hmass F hF k)
      (((hcoef k).comp hmap).congr fun X => ?_)
    change a (X + -(X₀ - 1) + (X₀ - 1)) k = a X k
    rw [show X + -(X₀ - 1) + (X₀ - 1) = X from by ring]
  simp only [hkey]
  exact ⟨hc, hsumc, hmassc, hexp⟩

/-! ### The three hypotheses, for an empirical fibre family -/

omit [Fintype ι] in
/-- **An empirical fibre proportion lies in `[0, 1]`.** For a finite nonempty `S` and any statistic
`f`, `#{x ∈ S : f x = 𝐣} / #S ∈ [0, 1]`. -/
theorem ncard_fiber_div_mem_Icc {S : Set α} (hS : S.Finite) (hne : S.ncard ≠ 0)
    (f : α → ι →₀ ℕ) (j : ι →₀ ℕ) :
    ({x | x ∈ S ∧ f x = j}.ncard : ℝ) / (S.ncard : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < (S.ncard : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hne)
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hpos]
  exact Nat.cast_le.2 (Set.ncard_le_ncard (fun x hx => hx.1) hS)

omit [Fintype ι] in
/-- **An empirical fibre family is summable.** For a finite `S`, the family
`𝐣 ↦ #{x ∈ S : f x = 𝐣} / #S` is summable. -/
theorem summable_ncard_fiber_div {S : Set α} (hS : S.Finite) (f : α → ι →₀ ℕ) :
    Summable fun j : ι →₀ ℕ => ({x | x ∈ S ∧ f x = j}.ncard : ℝ) / (S.ncard : ℝ) := by
  refine summable_of_hasFiniteSupport ((finite_setOf_ncard_fiber_ne_zero hS f).subset ?_)
  refine fun j hj hzero => hj ?_
  change ({x | x ∈ S ∧ f x = j}.ncard : ℝ) / (S.ncard : ℝ) = 0
  rw [hzero, Nat.cast_zero, zero_div]

/-- **The generating function of an empirical fibre family is the empirical monomial average.** For
a finite `S`,

`∑_{𝐣} (#{x ∈ S : f x = 𝐣} / #S) 𝐳^𝐣 = (1/#S) ∑_{x ∈ S} 𝐳^{f x}`. -/
theorem tsum_ncard_fiber_div_smul_multiMonomial {S : Set α} (hS : S.Finite) (f : α → ι →₀ ℕ)
    (z : ι → ℂ) :
    ∑' j : ι →₀ ℕ,
        ((({x | x ∈ S ∧ f x = j}.ncard : ℝ) / (S.ncard : ℝ) : ℝ) : ℂ) • multiMonomial (⇑j) z =
      (∑' x : α, S.indicator (fun x => multiMonomial (⇑(f x)) z) x) / (S.ncard : ℂ) := by
  rw [← tsum_ncard_fiber_div_mul hS f (fun j => multiMonomial (⇑j) z) ((S.ncard : ℕ) : ℂ)]
  refine tsum_congr fun j => ?_
  rw [smul_eq_mul]
  push_cast
  ring

/-! ### The packaged abstract statement -/

/-- **Coefficientwise convergence of empirical fibre proportions.** Let `S : ℝ → Set α` be a family
that is finite and nonempty from `X₀` on, and let `f : α → (ι →₀ ℕ)` be a statistic on it. If the
empirical monomial averages `(1/#S(X)) ∑_{x ∈ S(X)} 𝐳^{f x}` converge to `F(𝐳)` at every `𝐳` of the
open unit polydisc, then for every multi-index `𝐣` the empirical proportion
`#{x ∈ S(X) : f x = 𝐣} / #S(X)` converges, to `limUnder atTop` of itself. -/
theorem tendsto_ncard_fiber_div_limUnder (S : ℝ → Set α) (f : α → ι →₀ ℕ) (F : (ι → ℂ) → ℂ)
    (X₀ : ℝ) (hfin : ∀ X : ℝ, X₀ ≤ X → (S X).Finite)
    (hne : ∀ X : ℝ, X₀ ≤ X → (S X).ncard ≠ 0)
    (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ =>
          (∑' x : α, (S X).indicator (fun x => multiMonomial (⇑(f x)) z) x) / ((S X).ncard : ℂ))
        atTop (𝓝 (F z)))
    (j : ι →₀ ℕ) :
    Tendsto (fun X : ℝ => ({x | x ∈ S X ∧ f x = j}.ncard : ℝ) / ((S X).ncard : ℝ)) atTop
      (𝓝 (limUnder atTop fun X : ℝ =>
        ({x | x ∈ S X ∧ f x = j}.ncard : ℝ) / ((S X).ncard : ℝ))) := by
  refine tendsto_coeff_limUnder_of_tendsto_genFun
    (fun X k => ({x | x ∈ S X ∧ f x = k}.ncard : ℝ) / ((S X).ncard : ℝ)) X₀
    (fun X hX k => ncard_fiber_div_mem_Icc (hfin X hX) (hne X hX) f k)
    (fun X hX => summable_ncard_fiber_div (hfin X hX) f)
    (fun X hX => tsum_ncard_fiber_div (hfin X hX) (hne X hX) f) F (fun z hz => ?_) j
  refine (hF z hz).congr' ?_
  filter_upwards [eventually_ge_atTop X₀] with X hX
  exact (tsum_ncard_fiber_div_smul_multiMonomial (hfin X hX) f z).symm

/-- **The polydisc expansion of the limit of an empirical fibre family.** Under the hypotheses of
`tendsto_ncard_fiber_div_limUnder`, the limiting family `𝐣 ↦ lim_X #{x ∈ S(X) : f x = 𝐣} / #S(X)`
takes values in `[0, 1]`, is summable of total mass at most `1`, and expands `F` on the open unit
polydisc. -/
theorem hasPolydiscExpansion_ncard_fiber_div_limUnder (S : ℝ → Set α) (f : α → ι →₀ ℕ)
    (F : (ι → ℂ) → ℂ) (X₀ : ℝ) (hfin : ∀ X : ℝ, X₀ ≤ X → (S X).Finite)
    (hne : ∀ X : ℝ, X₀ ≤ X → (S X).ncard ≠ 0)
    (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ =>
          (∑' x : α, (S X).indicator (fun x => multiMonomial (⇑(f x)) z) x) / ((S X).ncard : ℂ))
        atTop (𝓝 (F z))) :
    (∀ j, (limUnder atTop fun X : ℝ =>
        ({x | x ∈ S X ∧ f x = j}.ncard : ℝ) / ((S X).ncard : ℝ)) ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun j => limUnder atTop fun X : ℝ =>
        ({x | x ∈ S X ∧ f x = j}.ncard : ℝ) / ((S X).ncard : ℝ)) ∧
      (∑' j : ι →₀ ℕ, limUnder atTop fun X : ℝ =>
        ({x | x ∈ S X ∧ f x = j}.ncard : ℝ) / ((S X).ncard : ℝ)) ≤ 1 ∧
      HasPolydiscExpansion (fun j => ((limUnder atTop fun X : ℝ =>
        ({x | x ∈ S X ∧ f x = j}.ncard : ℝ) / ((S X).ncard : ℝ) : ℝ) : ℂ)) F := by
  refine hasPolydiscExpansion_limUnder_of_tendsto_genFun
    (fun X k => ({x | x ∈ S X ∧ f x = k}.ncard : ℝ) / ((S X).ncard : ℝ)) X₀
    (fun X hX k => ncard_fiber_div_mem_Icc (hfin X hX) (hne X hX) f k)
    (fun X hX => summable_ncard_fiber_div (hfin X hX) f)
    (fun X hX => tsum_ncard_fiber_div (hfin X hX) (hne X hX) f) F fun z hz => ?_
  refine (hF z hz).congr' ?_
  filter_upwards [eventually_ge_atTop X₀] with X hX
  exact (tsum_ncard_fiber_div_smul_multiMonomial (hfin X hX) f z).symm

end BSDTamagawa.PrimeCountDensity

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex
open BSDTamagawa.FiberCount BSDTamagawa.DegeneratePoint BSDTamagawa.PrimeCountDensity

/-! ### The singleton index set -/

/-- **`N(X)` is the cardinality of the height-truncated family** `{(a₄, a₆) : Ht ≤ X, Δ ≠ 0}`. -/
theorem ncard_setOf_height_le_and_mem_family (X : ℝ) :
    {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.ncard = integralShortNFCount X := rfl

/-- **The `ω_Tam`-fibre, as a fibre of `Unit`-multi-indices.** Under `ℕ ≃ (Unit →₀ ℕ)` the fibre of
`q ↦ ω_Tam(q)` over the multi-index attached to `r` is the set counted by the numerator of
`π_r(X)`. -/
theorem setOf_mem_and_tamagawaOmegaIndex_eq (r : ℕ) (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧
        Finsupp.equivFunOnFinite.symm (fun _ : Unit => tamagawaOmega q.1 q.2) =
          Finsupp.equivFunOnFinite.symm (fun _ : Unit => r)} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
        tamagawaOmega q.1 q.2 = r} := by
  refine Eq.trans (Set.ext fun q => ?_) (setOf_mem_and_tamagawaOmega_eq r X)
  simp [funext_iff]

/-! ### The empirical average -/

/-- **The empirical `Unit`-monomial average is `𝒵` at the degenerate point.** For `X ≥ 4`,

`(1/N(X)) ∑_{Ht(E) ≤ X} 𝐳^{(ω_Tam(E))} = 𝒵_{∅, ∅, X}(0; z_∗, 1, ∅, ∅)`,

with `𝐳^{(ω_Tam(E))}` the `Unit`-monomial `z_∗^{ω_Tam(E)}` and `z_∗ = z ()` its single variable. -/
theorem tsum_indicator_tamagawaOmegaMonomial_div_eq (z : Unit → ℂ)
    (z₀ : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset ReductionData) → ℂ) {X : ℝ} (hX : 4 ≤ X) :
    (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.indicator
        (fun q => multiMonomial (⇑(Finsupp.equivFunOnFinite.symm
          (fun _ : Unit => tamagawaOmega q.1 q.2))) z) q) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℂ)
      = tamagawaGeneratingFunction ∅ ∅ 0 (z ()) 1 z₀ uΛ X := by
  have hS : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite :=
    finite_setOf_height_le_and_mem_family (by linarith)
  have hfun : (fun q : ℤ × ℤ => multiMonomial (⇑(Finsupp.equivFunOnFinite.symm
        (fun _ : Unit => tamagawaOmega q.1 q.2))) z) =
      fun q : ℤ × ℤ => (fun r : ℕ => z () ^ r) ((fun q : ℤ × ℤ => tamagawaOmega q.1 q.2) q) := by
    funext q
    simp [multiMonomial]
  rw [hfun, ncard_setOf_height_le_and_mem_family,
    tamagawaGeneratingFunction_eq_tsum_tamagawaOmegaProportion (z ()) z₀ uΛ hX,
    ← tsum_ncard_fiber_div_mul hS (fun q : ℤ × ℤ => tamagawaOmega q.1 q.2)
      (fun r : ℕ => z () ^ r) (integralShortNFCount X : ℂ)]
  refine tsum_congr fun r => ?_
  rw [tamagawaOmegaProportion, ← setOf_mem_and_tamagawaOmega_eq r X]
  push_cast
  rfl

/-- **The pointwise limit on the open unit disc.** For `‖z ()‖ < 1`,

`(1/N(X)) ∑_{Ht(E) ≤ X} z_∗^{ω_Tam(E)} ⟶ F(z_∗)` as `X → ∞`,

with `F` the Euler product. -/
theorem tendsto_tsum_indicator_tamagawaOmegaMonomial_div (z : Unit → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.indicator
          (fun q => multiMonomial (⇑(Finsupp.equivFunOnFinite.symm
            (fun _ : Unit => tamagawaOmega q.1 q.2))) z) q) /
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.ncard : ℂ))
      atTop (𝓝 (tamagawaOmegaEulerProduct (z ()))) := by
  refine (tendsto_tamagawaGeneratingFunction_tamagawaOmegaEulerProduct (hz ()).le
    (fun _ => 0) (fun _ => 0)).congr' ?_
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
  exact (tsum_indicator_tamagawaOmegaMonomial_div_eq z _ _ hX).symm

/-! ### Existence of the limiting density -/

/-- For every `r : ℕ`,

`lim_{X → ∞} π_r(X) = π_r`,

with `π_r(X)` the height-truncated proportion and `π_r` the limiting density: the limit exists and
equals `π_r`. -/
@[bsd_tamagawa "T041k"]
theorem tendsto_tamagawaOmegaProportion_tamagawaOmegaDensity (r : ℕ) :
    Tendsto (fun X : ℝ => tamagawaOmegaProportion r X) atTop (𝓝 (tamagawaOmegaDensity r)) := by
  have hEq : ∀ X : ℝ,
      ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily} ∧
            Finsupp.equivFunOnFinite.symm (fun _ : Unit => tamagawaOmega q.1 q.2) =
              Finsupp.equivFunOnFinite.symm (fun _ : Unit => r)}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ) = tamagawaOmegaProportion r X := fun X => by
    rw [setOf_mem_and_tamagawaOmegaIndex_eq r X, ncard_setOf_height_le_and_mem_family,
      tamagawaOmegaProportion]
  have h := tendsto_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (fun q : ℤ × ℤ => Finsupp.equivFunOnFinite.symm (fun _ : Unit => tamagawaOmega q.1 q.2))
    (fun z : Unit → ℂ => tamagawaOmegaEulerProduct (z ())) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_tamagawaOmegaMonomial_div z hz)
    (Finsupp.equivFunOnFinite.symm (fun _ : Unit => r))
  rw [tamagawaOmegaDensity]
  simpa only [hEq] using h

end WeierstrassCurve
