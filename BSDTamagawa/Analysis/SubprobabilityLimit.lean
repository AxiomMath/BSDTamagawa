/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module


public import BSDTamagawa.Analysis.Complex.CauchyCoeff
public import BSDTamagawa.GeneratingFunction.MultiMonomial

/-!
# Sub-probability coefficients of a pointwise limit of generating functions

Let `ι` be a finite index set and `D = {z : ι → ℂ | ∀ i, ‖z i‖ < 1}` the open unit polydisc. For
each `X ≥ 1` let `a X : (ι →₀ ℕ) → [0,1]` be a probability vector (`∑_j a X j = 1`) and let
`F_X(z) = ∑_j a X j • z^j` be its generating function. If `F_X(z) → F(z)` pointwise on `D`, then
there is a *single* coefficient function `c : (ι →₀ ℕ) → [0,1]` with total mass `∑_j c j ≤ 1` (mass
may escape to infinity, so equality is not asserted) such that on all of `D` the family
`(c j • z^j)` is absolutely summable with sum `F z`.

## Main definitions

* `BSDTamagawa.SubprobLimit.genFun`: the generating function `∑_j a X j • z^j`.

## Main results

* `BSDTamagawa.SubprobLimit.exists_tendsto_of_mem_Icc`: cube-valued coefficient vectors have a
  cluster point along `atTop`.
* `BSDTamagawa.SubprobLimit.summable_and_tsum_le_one`: a pointwise limit of probability vectors is
  a sub-probability vector.
* `BSDTamagawa.SubprobLimit.summable_norm_and_hasSum_of_tendsto`: Tannery transfer of the expansion
  to the limiting coefficients.
* `BSDTamagawa.SubprobLimit.exists_subprob_expansion_of_tendsto_genFun`: the statement above.
-/

@[expose] public section

namespace BSDTamagawa.SubprobLimit

open Filter Topology
open BSDTamagawa.MultiIndex

variable {ι : Type*} [Fintype ι]

/-- **The generating function** `F_X(z) = ∑_{j} a X j · z^j` of the coefficient family `a X`,
summed over multi-indices `j : ι →₀ ℕ`. -/
noncomputable def genFun (a : ℝ → (ι →₀ ℕ) → ℝ) (X : ℝ) (z : ι → ℂ) : ℂ :=
  ∑' j : ι →₀ ℕ, (a X j : ℂ) • multiMonomial (⇑j) z

/-- `HasPolydiscExpansion c f` holds if and only if `c j • z^j` sums to `f z` on the open polydisc,
with `z^j` the multi-index monomial `multiMonomial`. -/
theorem hasPolydiscExpansion_iff (c : (ι →₀ ℕ) → ℂ) (f : (ι → ℂ) → ℂ) :
    HasPolydiscExpansion c f ↔
      ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
        HasSum (fun j : ι →₀ ℕ => c j • multiMonomial (⇑j) z) (f z) :=
  Iff.rfl

/-! ## The majorant: multivariate geometric summability -/

/-- For radii `r i ∈ [0, 1)`, the family `j ↦ ∏ i, r i ^ j i` is summable over `j : J → ℕ`. -/
theorem summable_prod_pow {J : Type*} [Fintype J] (r : J → ℝ) (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : ∀ i, r i < 1) : Summable fun j : J → ℕ => ∏ i, r i ^ j i := by
  classical
  have hnn : ∀ j : J → ℕ, 0 ≤ ∏ i, r i ^ j i :=
    fun j => Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _
  refine summable_of_sum_le (c := ∏ i, (1 - r i)⁻¹) hnn fun u => ?_
  set N : ℕ := u.sup Finset.univ.sup
  have hsub : u ⊆ Fintype.piFinset fun _ : J => Finset.range (N + 1) := by
    intro j hj
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr ?_
    have h1 : j i ≤ Finset.univ.sup j := Finset.le_sup (Finset.mem_univ i)
    have h2 : (Finset.univ.sup j) ≤ N := Finset.le_sup hj
    omega
  calc ∑ j ∈ u, ∏ i, r i ^ j i
      ≤ ∑ j ∈ Fintype.piFinset fun _ : J => Finset.range (N + 1), ∏ i, r i ^ j i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hnn j
    _ = ∏ i, ∑ n ∈ Finset.range (N + 1), r i ^ n :=
        (Finset.prod_univ_sum (fun _ => Finset.range (N + 1)) fun i n => r i ^ n).symm
    _ ≤ ∏ i, (1 - r i)⁻¹ := by
        refine Finset.prod_le_prod₀
          (fun i _ => Finset.sum_nonneg fun n _ => pow_nonneg (hr0 i) n) fun i _ => ?_
        have h := (summable_geometric_of_lt_one (hr0 i) (hr1 i)).sum_le_tsum
          (Finset.range (N + 1)) fun n _ => pow_nonneg (hr0 i) n
        rwa [tsum_geometric_of_lt_one (hr0 i) (hr1 i)] at h

/-- The majorant of `summable_prod_pow`, transported along `Finsupp.equivFunOnFinite` to the
multi-index type `ι →₀ ℕ`. -/
theorem summable_prod_pow_finsupp (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : ∀ i, r i < 1) : Summable fun j : ι →₀ ℕ => ∏ i, r i ^ (j i) :=
  (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).summable_iff
    (f := fun j : ι → ℕ => ∏ i, r i ^ j i) |>.mpr (summable_prod_pow r hr0 hr1)

/-- On the open polydisc the monomials `z^j` are absolutely summable over `j : ι →₀ ℕ`. -/
theorem summable_norm_multiMonomial {z : ι → ℂ} (hz : ∀ i, ‖z i‖ < 1) :
    Summable fun j : ι →₀ ℕ => ‖multiMonomial (⇑j) z‖ := by
  have hnorm : ∀ j : ι →₀ ℕ, ‖multiMonomial (⇑j) z‖ = ∏ i, ‖z i‖ ^ (j i) :=
    fun j => by simp [multiMonomial, norm_prod, norm_pow]
  simpa only [hnorm] using
    summable_prod_pow_finsupp (fun i => ‖z i‖) (fun i => norm_nonneg _) hz

/-- Scaling a complex number by a real factor in `[0, 1]` does not increase its norm. -/
theorem norm_ofReal_smul_le_norm {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (w : ℂ) :
    ‖(t : ℂ) • w‖ ≤ ‖w‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

/-! ## Step 1: extracting a single limiting coefficient function -/

/-- **Cluster-point extraction.** If the coefficient vectors `a X : κ → ℝ` eventually lie in the
cube `[0,1]^κ`, which is compact for the product topology, then `a` has a cluster point `c` along
`atTop`: there is a refinement `G ≤ atTop`, still `NeBot`, along which `a X → c` pointwise, with
`c` again valued in `[0,1]`. -/
theorem exists_tendsto_of_mem_Icc {κ : Type*} (a : ℝ → κ → ℝ)
    (ha : ∀ᶠ X in atTop, ∀ j, a X j ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (c : κ → ℝ) (G : Filter ℝ), (∀ j, c j ∈ Set.Icc (0 : ℝ) 1) ∧
      G.NeBot ∧ G ≤ atTop ∧ Tendsto a G (𝓝 c) := by
  have hcube : IsCompact {x : κ → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨c, hc, hcl⟩ := hcube.exists_mapClusterPt (le_principal_iff.mpr ha)
  have hpp : map a (atTop ⊓ comap a (𝓝 c)) = map a atTop ⊓ 𝓝 c :=
    Filter.push_pull a atTop (𝓝 c)
  have hne : (atTop ⊓ comap a (𝓝 c) : Filter ℝ).NeBot := by
    have h : (map a (atTop ⊓ comap a (𝓝 c))).NeBot := by
      rw [hpp, inf_comm]
      exact hcl.clusterPt.neBot
    exact h.of_map
  exact ⟨c, atTop ⊓ comap a (𝓝 c), hc, hne, inf_le_left,
    by rw [Tendsto, hpp]; exact inf_le_right⟩

/-! ## Step 2: the mass bound -/

/-- **Total mass at most one.** A nonnegative pointwise limit, along any `NeBot` filter `G`, of
probability vectors is a summable *sub*-probability vector. Mass may escape to infinity, so only
`≤ 1` holds. -/
theorem summable_and_tsum_le_one {κ : Type*} {a : ℝ → κ → ℝ} {c : κ → ℝ} {G : Filter ℝ}
    [G.NeBot] (hc0 : ∀ j, 0 ≤ c j)
    (hcoef : ∀ j, Tendsto (fun X : ℝ => a X j) G (𝓝 (c j)))
    (hprob : ∀ᶠ X in G, (∀ j, 0 ≤ a X j) ∧ Summable (a X) ∧ ∑' j, a X j = 1) :
    Summable c ∧ ∑' j, c j ≤ 1 := by
  have hpartial : ∀ u : Finset κ, ∑ j ∈ u, c j ≤ 1 := by
    intro u
    refine le_of_tendsto (tendsto_finsetSum u fun j _ => hcoef j) ?_
    filter_upwards [hprob] with X hX
    calc ∑ j ∈ u, a X j ≤ ∑' j, a X j := hX.2.1.sum_le_tsum u fun j _ => hX.1 j
      _ = 1 := hX.2.2
  exact ⟨summable_of_sum_le hc0 hpartial, Real.tsum_le_of_sum_le hc0 hpartial⟩

/-! ## Step 3: the expansion on the open polydisc -/

/-- **Transfer of the expansion (Tannery).** Let `z` lie in the open polydisc, let `G ≤ atTop` be a
`NeBot` filter along which the `[0,1]`-valued coefficients `a X j` converge to `c j ∈ [0,1]`, and
suppose `genFun a X z → F z` along `atTop`. Then `(c j • z^j)` is absolutely summable with sum
`F z`. -/
theorem summable_norm_and_hasSum_of_tendsto {a : ℝ → (ι →₀ ℕ) → ℝ} {c : (ι →₀ ℕ) → ℝ}
    {G : Filter ℝ} [G.NeBot] (hGtop : G ≤ atTop) (ha : ∀ᶠ X in G, ∀ j, a X j ∈ Set.Icc (0 : ℝ) 1)
    (hc : ∀ j, c j ∈ Set.Icc (0 : ℝ) 1) (hcoef : ∀ j, Tendsto (fun X : ℝ => a X j) G (𝓝 (c j)))
    {F : (ι → ℂ) → ℂ} {z : ι → ℂ} (hz : ∀ i, ‖z i‖ < 1)
    (hF : Tendsto (fun X : ℝ => genFun a X z) atTop (𝓝 (F z))) :
    Summable (fun j : ι →₀ ℕ => ‖(c j : ℂ) • multiMonomial (⇑j) z‖) ∧
      HasSum (fun j : ι →₀ ℕ => (c j : ℂ) • multiMonomial (⇑j) z) (F z) := by
  have hmaj := summable_norm_multiMonomial hz
  have hsummable_norm :
      Summable (fun j : ι →₀ ℕ => ‖(c j : ℂ) • multiMonomial (⇑j) z‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_ofReal_smul_le_norm (hc j) _) hmaj
  refine ⟨hsummable_norm, ?_⟩
  have hpt : ∀ j : ι →₀ ℕ,
      Tendsto (fun X : ℝ => (a X j : ℂ) • multiMonomial (⇑j) z) G
        (𝓝 ((c j : ℂ) • multiMonomial (⇑j) z)) := fun j =>
    ((Complex.continuous_ofReal.tendsto _).comp (hcoef j)).smul_const _
  have hunif : ∀ᶠ X in G, ∀ j : ι →₀ ℕ,
      ‖(a X j : ℂ) • multiMonomial (⇑j) z‖ ≤ ‖multiMonomial (⇑j) z‖ := by
    filter_upwards [ha] with X hX j using norm_ofReal_smul_le_norm (hX j) _
  have hgen : Tendsto (fun X : ℝ => genFun a X z) G
      (𝓝 (∑' j : ι →₀ ℕ, (c j : ℂ) • multiMonomial (⇑j) z)) := by
    simpa only [genFun] using tendsto_tsum_of_dominated_convergence hmaj hpt hunif
  have hlim : (∑' j : ι →₀ ℕ, (c j : ℂ) • multiMonomial (⇑j) z) = F z :=
    tendsto_nhds_unique hgen (hF.mono_left hGtop)
  exact hlim ▸ hsummable_norm.of_norm.hasSum

/-! ## The sub-probability expansion -/

/-- Let `ι` be finite and `D = {z | ∀ i, ‖z i‖ < 1}` the open unit polydisc. Let
`a X : (ι →₀ ℕ) → ℝ`, for `X ≥ 1`, be probability vectors: `a X j ∈ [0,1]`, with `a X` summable and
`∑_j a X j = 1`. If the generating functions `genFun a X` converge pointwise on `D` to `F`, then
there is a single coefficient function `c : (ι →₀ ℕ) → ℝ` with

* `c j ∈ [0,1]` for every multi-index `j`;
* `c` summable with `∑_j c j ≤ 1` (only `≤`: mass may escape to infinity);
* for every `z ∈ D`, the family `(c j • z^j)` is absolutely summable and sums to `F z`, i.e.
  `HasPolydiscExpansion (fun j => (c j : ℂ)) F`. -/
@[bsd_tamagawa "T039b"]
theorem exists_subprob_expansion_of_tendsto_genFun (a : ℝ → (ι →₀ ℕ) → ℝ)
    (ha : ∀ X : ℝ, 1 ≤ X → ∀ j, a X j ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ X : ℝ, 1 ≤ X → Summable (a X)) (hmass : ∀ X : ℝ, 1 ≤ X → ∑' j, a X j = 1)
    (F : (ι → ℂ) → ℂ) (hF : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Tendsto (fun X : ℝ => genFun a X z) atTop (𝓝 (F z))) :
    ∃ c : (ι →₀ ℕ) → ℝ,
      (∀ j, c j ∈ Set.Icc (0 : ℝ) 1) ∧
      (Summable c ∧ ∑' j, c j ≤ 1) ∧
      (∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
        Summable fun j : ι →₀ ℕ => ‖(c j : ℂ) • multiMonomial (⇑j) z‖) ∧
      HasPolydiscExpansion (fun j => (c j : ℂ)) F := by
  obtain ⟨c, G, hc, hGne, hGtop, hGa⟩ :=
    exists_tendsto_of_mem_Icc a ((eventually_ge_atTop (1 : ℝ)).mono ha)
  have := hGne
  have hcoef : ∀ j, Tendsto (fun X : ℝ => a X j) G (𝓝 (c j)) := fun j =>
    ((continuous_apply j).tendsto c).comp hGa
  have hev : ∀ᶠ X in G,
      (∀ j, a X j ∈ Set.Icc (0 : ℝ) 1) ∧ Summable (a X) ∧ ∑' j, a X j = 1 := by
    filter_upwards [(eventually_ge_atTop (1 : ℝ)).filter_mono hGtop] with X hX
    exact ⟨ha X hX, hsum X hX, hmass X hX⟩
  have hmain : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) →
      Summable (fun j : ι →₀ ℕ => ‖(c j : ℂ) • multiMonomial (⇑j) z‖) ∧
        HasSum (fun j : ι →₀ ℕ => (c j : ℂ) • multiMonomial (⇑j) z) (F z) :=
    fun z hz => summable_norm_and_hasSum_of_tendsto hGtop
      (hev.mono fun X hX => hX.1) hc hcoef hz (hF z hz)
  refine ⟨c, hc, ?_, fun z hz => (hmain z hz).1, (hasPolydiscExpansion_iff _ F).mpr
    fun z hz => (hmain z hz).2⟩
  exact summable_and_tsum_le_one (fun j => (hc j).1) hcoef
    (hev.mono fun X hX => ⟨fun j => (hX.1 j).1, hX.2.1, hX.2.2⟩)

end BSDTamagawa.SubprobLimit
