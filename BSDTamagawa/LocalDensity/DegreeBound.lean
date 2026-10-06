/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.TailBound

/-!
# The bound `δ_p(t) = O(p^{-2})` for `t ≠ 1`

The scalar local density at a nontrivial Tamagawa number is `O(p^{-2})`, uniformly in the Tamagawa
number:

  `δ_p(t) ≤ 9/p²` for every prime `p` and every `t ≠ 1`,

and `δ_p(t) ≤ 3/p²` for `p ≥ 5`. Off the locus `{p² ∣ Δ}` Tate's algorithm terminates with
reduction datum `(I₀, 1)` or `(I₁, 1)`, so every reduction-datum stratum with Tamagawa number
`t ≠ 1` lies in that locus, whose Haar mass is at most `3/p²` for `p ≥ 5`. At `p ∈ {2, 3}` the
bound `9/p² ≥ 1` is trivial. In particular, for each `t ∈ {1, 2, 3, 4}` there are `C_t > 0` and
`p₀` with `δ_p(t) ≤ C_t p^{-d_t}` for `p ≥ p₀`, where `d_1 = 0` and `d_2 = d_3 = d_4 = 2`.

## Main results

* `WeierstrassCurve.stratFibre_subset_sqDvdΔLocus`: a stratum with Tamagawa number `≠ 1` lies in
  `{p² ∣ Δ}`.
* `WeierstrassCurve.volume_iUnion_stratFibre_kodaira`: the union over the Kodaira symbol of the
  strata over `t` has Haar mass `δ_p(t)`.
* `WeierstrassCurve.δ_le_three_div_sq`: for `p ≥ 5` and `t ≠ 1`, `δ_p(t) ≤ 3/p²`.
* `WeierstrassCurve.δ_le_one`: `δ_p(t) ≤ 1`.
* `WeierstrassCurve.δ_le_nine_div_sq`: for every prime `p` and every `t ≠ 1`, `δ_p(t) ≤ 9/p²`.
* `WeierstrassCurve.exists_polyDegree_bound_δ`: the existential form over `t ∈ {1, 2, 3, 4}`.
-/

@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### The strata over a nontrivial Tamagawa number lie in the deep-discriminant locus -/

/-- If `c(K) ≠ 1`, then the reduction-datum stratum `τ_p⁻¹(K)` of the coefficient plane is
contained in the locus `{p² ∣ Δ}`. -/
theorem stratFibre_subset_sqDvdΔLocus {K : ReductionData} (hK : K.2 ≠ 1) :
    stratFibre p K ⊆ sqDvdΔLocus p := by
  intro x hx
  by_contra hxc
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset K hx
  have hstrat : strat p ⟨x, hUp⟩ = K := (mem_stratFibre_iff hUp).1 hx
  rcases compl_sqDvdΔLocus_subset_stratFibre_union hxc with h | h <;>
    exact hK (by rw [← hstrat, (mem_stratFibre_iff hUp).1 h])

/-- The strata over a fixed Tamagawa number `t`, indexed by the Kodaira symbol, are pairwise
disjoint. -/
theorem pairwise_disjoint_stratFibre_kodaira (t : ℕ) :
    Pairwise (Disjoint on fun κ : KodairaSymbol => stratFibre p (κ, t)) := by
  intro κ κ' hκ
  simp only [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
  exact hκ (congrArg Prod.fst
    (((mem_stratFibre_iff hUp).1 hx).symm.trans ((mem_stratFibre_iff hUp).1 hx')))

/-- The union over the Kodaira symbol of the strata `τ_p⁻¹(κ, t)` of the coefficient plane has Haar
mass `δ_p(t)`. -/
theorem volume_iUnion_stratFibre_kodaira (t : ℕ) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (⋃ κ : KodairaSymbol, stratFibre p (κ, t)) = δ p t := by
  rw [measure_iUnion (pairwise_disjoint_stratFibre_kodaira t)
    fun κ => (isOpen_stratFibre (p := p) (κ, t)).measurableSet]
  simp only [volume_stratFibre]
  exact tsum_deltaP_kodaira p t

/-! ### The bound at `p ≥ 5`, and the trivial bound -/

/-- For every prime `p ≥ 5` and every `t ≠ 1`, `δ_p(t) ≤ 3/p²`. -/
theorem δ_le_three_div_sq (hp : 5 ≤ p) {t : ℕ} (ht : t ≠ 1) : δ p t ≤ 3 / (p : ℝ≥0∞) ^ 2 :=
  calc δ p t = (volume : Measure (ℤ_[p] × ℤ_[p])) (⋃ κ : KodairaSymbol, stratFibre p (κ, t)) :=
        (volume_iUnion_stratFibre_kodaira t).symm
    _ ≤ volume (sqDvdΔLocus p) :=
        measure_mono (Set.iUnion_subset fun _ => stratFibre_subset_sqDvdΔLocus ht)
    _ ≤ 3 * ((p : ℝ≥0∞) ^ 2)⁻¹ := volume_sqDvdΔLocus_le hp
    _ = 3 / (p : ℝ≥0∞) ^ 2 := (div_eq_mul_inv _ _).symm

/-- Every scalar local density is at most `1`: `δ_p(t) ≤ 1`. -/
theorem δ_le_one (t : ℕ) : δ p t ≤ 1 := by
  rw [← tsum_δ p]
  exact ENNReal.le_tsum t

/-- `1 ≤ 9/q²` in `ℝ≥0∞` for every natural number `q ≤ 3`. -/
theorem one_le_nine_div_sq {q : ℕ} (hq : q ≤ 3) : (1 : ℝ≥0∞) ≤ 9 / (q : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr (by norm_num)) (Or.inr (by norm_num)), one_mul]
  have h3 : (q : ℝ≥0∞) ≤ 3 := by exact_mod_cast hq
  calc (q : ℝ≥0∞) ^ 2 ≤ 3 ^ 2 := by gcongr
    _ = 9 := by norm_num

/-! ### The bound at every prime -/

/-- For every prime `p` and every `t ≠ 1`, `δ_p(t) ≤ 9/p²`. -/
@[bsd_tamagawa "T022a"]
theorem δ_le_nine_div_sq {t : ℕ} (ht : t ≠ 1) : δ p t ≤ 9 / (p : ℝ≥0∞) ^ 2 := by
  rcases le_or_gt 5 p with hp | hp
  · refine (δ_le_three_div_sq hp ht).trans ?_
    gcongr
    norm_num
  · have hp3 : p ≤ 3 := by
      have h4 : p ≠ 4 := fun h => absurd (h ▸ (Fact.out : p.Prime)) (by decide)
      omega
    exact (δ_le_one t).trans (one_le_nine_div_sq hp3)

/-- For each fixed `t ∈ {1, 2, 3, 4}` there are a constant `C_t > 0` and a threshold `p₀` such that
`δ_p(t) ≤ C_t / p^{d_t}` for every prime `p ≥ p₀`, where `d_1 = 0` and `d_2 = d_3 = d_4 = 2`. -/
@[bsd_tamagawa "T022a"]
theorem exists_polyDegree_bound_δ {t : ℕ} (ht : t ∈ ({1, 2, 3, 4} : Set ℕ)) :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧
      ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
        δ q t ≤ C / (q : ℝ≥0∞) ^ (if t = 1 then 0 else 2) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, 2, one_pos, fun q _ _ => by simpa using δ_le_one (p := q) 1⟩
  all_goals
    exact ⟨9, 2, by norm_num, fun q _ _ => by
      simpa using δ_le_nine_div_sq (p := q) (by norm_num)⟩

end WeierstrassCurve
