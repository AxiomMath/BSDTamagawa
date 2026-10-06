/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.SubprobabilityLimit

/-!
# Coefficient extraction from a convergent family of generating functions

Let `I` be a finite index set, `D = {𝐳 : ‖z_i‖ < 1 ∀ i}` the open unit polydisc and, for `X ≥ 1`,
let `F_X` be the probability generating function of an `I`-tuple of `ℕ`-valued random variables:
`F_X(𝐳) = ∑_{𝐣} a_X(𝐣) 𝐳^𝐣` with `a_X : ℕ^I → [0,1]` summable of total mass `1`. If `F_X → F`
pointwise on `D`, then there is a *single* sub-probability coefficient family `c : ℕ^I → [0,1]`,
`∑_𝐣 c(𝐣) ≤ 1`, with

* `a_X(𝐣) → c(𝐣)` as `X → ∞`, for every multi-index `𝐣`, and
* `F(𝐳) = ∑_𝐣 c(𝐣) 𝐳^𝐣` on `D`, absolutely convergent.

## Main results

* `BSDTamagawa.CoeffExtraction.exists_coeff_tendsto_of_tendsto_genFun`: the statement above.
* `BSDTamagawa.CoeffExtraction.coeff_eq_of_hasPolydiscExpansion`: the coefficients of a polydisc
  expansion are unique.
* `BSDTamagawa.CoeffExtraction.hasPolydiscExpansion_of_mapClusterPt`: every cluster point of
  `X ↦ a_X` is a coefficient family of `F`.
-/

@[expose] public section

namespace BSDTamagawa.CoeffExtraction

open Filter Topology
open BSDTamagawa.MultiIndex BSDTamagawa.SubprobLimit

variable {ι : Type*} [Fintype ι]

/-! ### Uniqueness of the coefficients of a polydisc expansion -/

/-- A constant sequence converges to its value uniformly on every set. -/
private theorem tendstoUniformlyOn_const_seq {α β : Type*} [PseudoMetricSpace β] (f : α → β)
    (s : Set α) : TendstoUniformlyOn (fun _ : ℕ => f) f atTop s :=
  Metric.tendstoUniformlyOn_iff.2 fun _ hε =>
    Eventually.of_forall fun _ x _ => by simpa using hε

/-- **Coefficients of a polydisc expansion are unique.** If `f` is the sum of the multivariate
power series with coefficients `c` and also of the one with coefficients `c'` on the open unit
polydisc, then `c = c'`. -/
theorem coeff_eq_of_hasPolydiscExpansion {c c' : (ι →₀ ℕ) → ℂ} {f : (ι → ℂ) → ℂ}
    (hc : HasPolydiscExpansion c f) (hc' : HasPolydiscExpansion c' f) : c = c' := by
  classical
  funext j
  exact tendsto_nhds_unique tendsto_const_nhds
    (cauchy_coeff_convergence_multivar (fun _ : ℕ => f) (fun _ => c) f c' (fun _ => hc) hc'
      (fun ρ _ _ => tendstoUniformlyOn_const_seq f {z : ι → ℂ | ∀ i, ‖z i‖ = ρ i}) j)

/-! ### Every cluster point of the coefficient vectors expands the same limit -/

/-- **A cluster point of the coefficient vectors is a coefficient family of `F`.** Let `y` be a
cluster point, in the cube `[0,1]^{ℕ^I}`, of `X ↦ a_X` along `atTop`, where `F_X → F` pointwise on
the open polydisc. Then `F(𝐳) = ∑_𝐣 y(𝐣) 𝐳^𝐣` on the open polydisc. -/
theorem hasPolydiscExpansion_of_mapClusterPt {a : ℝ → (ι →₀ ℕ) → ℝ} {F : (ι → ℂ) → ℂ}
    (hev : ∀ᶠ X in atTop, ∀ j, a X j ∈ Set.Icc (0 : ℝ) 1)
    (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ => genFun a X z) atTop (𝓝 (F z)))
    {y : (ι →₀ ℕ) → ℝ} (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (hcl : MapClusterPt y atTop a) :
    HasPolydiscExpansion (fun j => ((y j : ℝ) : ℂ)) F := by
  have hpp : map a (atTop ⊓ comap a (𝓝 y)) = map a atTop ⊓ 𝓝 y :=
    Filter.push_pull a atTop (𝓝 y)
  have hne : (atTop ⊓ comap a (𝓝 y) : Filter ℝ).NeBot := by
    have h : (map a (atTop ⊓ comap a (𝓝 y))).NeBot := by
      rw [hpp, inf_comm]
      exact hcl.clusterPt.neBot
    exact h.of_map
  have hGa : Tendsto a (atTop ⊓ comap a (𝓝 y)) (𝓝 y) := by
    rw [Tendsto, hpp]
    exact inf_le_right
  have hcoef : ∀ j, Tendsto (fun X : ℝ => a X j) (atTop ⊓ comap a (𝓝 y)) (𝓝 (y j)) :=
    hGa.apply_nhds
  exact (hasPolydiscExpansion_iff _ F).mpr fun z hz =>
    (summable_norm_and_hasSum_of_tendsto inf_le_left (hev.filter_mono inf_le_left) hy hcoef hz
      (hF z hz)).2

/-! ### Coefficientwise convergence -/

/-- Distribution-coefficient extraction. Let `I` be a finite index set and, for `X ≥ 1`, let
`a_X : ℕ^I → [0,1]` be summable with `∑_𝐣 a_X(𝐣) = 1`, so that `F_X(𝐳) = ∑_𝐣 a_X(𝐣) 𝐳^𝐣` is the
probability generating function of an `I`-tuple of `ℕ`-valued random variables. Suppose
`F_X(𝐳) → F(𝐳)` as `X → ∞` for every `𝐳` in the open polydisc. Then there is a coefficient family
`c : ℕ^I → [0,1]` with `∑_𝐣 c(𝐣) ≤ 1` such that

* `a_X(𝐣) → c(𝐣)` as `X → ∞`, for every `𝐣`, and
* `F(𝐳) = ∑_𝐣 c(𝐣) 𝐳^𝐣` for every `𝐳` in the open polydisc, absolutely convergent.

Only `≤ 1` holds for the total mass of `c`: mass may escape to infinity. -/
@[bsd_tamagawa "T039a"]
theorem exists_coeff_tendsto_of_tendsto_genFun (a : ℝ → (ι →₀ ℕ) → ℝ)
    (ha : ∀ X : ℝ, 1 ≤ X → ∀ j, a X j ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ X : ℝ, 1 ≤ X → Summable (a X)) (hmass : ∀ X : ℝ, 1 ≤ X → ∑' j, a X j = 1)
    (F : (ι → ℂ) → ℂ) (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ => genFun a X z) atTop (𝓝 (F z))) :
    ∃ c : (ι →₀ ℕ) → ℝ,
      (∀ j, c j ∈ Set.Icc (0 : ℝ) 1) ∧
      (Summable c ∧ ∑' j, c j ≤ 1) ∧
      (∀ j, Tendsto (fun X : ℝ => a X j) atTop (𝓝 (c j))) ∧
      (∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
        Summable fun j : ι →₀ ℕ => ‖(c j : ℂ) • multiMonomial (⇑j) z‖) ∧
      HasPolydiscExpansion (fun j => ((c j : ℝ) : ℂ)) F := by
  obtain ⟨c, hc, hmassc, hnormc, hexp⟩ :=
    exists_subprob_expansion_of_tendsto_genFun a ha hsum hmass F hF
  refine ⟨c, hc, hmassc, ?_, hnormc, hexp⟩
  have hev : ∀ᶠ X in atTop, ∀ j, a X j ∈ Set.Icc (0 : ℝ) 1 :=
    (eventually_ge_atTop (1 : ℝ)).mono fun X hX => ha X hX
  have hcube : IsCompact {x : (ι →₀ ℕ) → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  have hall : Tendsto a atTop (𝓝 c) := by
    refine hcube.tendsto_nhds_of_unique_mapClusterPt hev fun y hy hcl => ?_
    have hyexp : HasPolydiscExpansion (fun j => ((y j : ℝ) : ℂ)) F :=
      hasPolydiscExpansion_of_mapClusterPt hev hF hy hcl
    funext j
    exact Complex.ofReal_injective (congrFun (coeff_eq_of_hasPolydiscExpansion hyexp hexp) j)
  exact hall.apply_nhds

end BSDTamagawa.CoeffExtraction
