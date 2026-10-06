/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.DegreeBound

/-!
# The mass outside the trivial reduction stratum

The complement of the trivial reduction stratum carries mass `O(p^{-2})`, uniformly in `p`:

  `1 - β_p = ∑_{K ∉ 𝒦₀} δ_p(K) ≤ 9/p²` for every prime `p`,

and `≤ 3/p²` for `p ≥ 5`. Here `β_p = ∑_{K ∈ 𝒦₀} δ_p(K)` is the trivial-stratum mass and
`𝒦₀ = {(I₀, 1), (I₁, 1)}`. The identity is countable additivity of the reduction densities, of
total mass `1`. For the bound: off the locus `{p² ∣ Δ}` the reduction datum is `(I₀, 1)` or
`(I₁, 1)`, so the complement of that locus lies in the two `𝒦₀` strata, of total mass `β_p`, while
the locus itself has mass at most `3/p²` for `p ≥ 5`; at `p ∈ {2, 3}` the bound `9/p² ≥ 1` is
trivial.

## Main results

* `ENNReal.tsum_subtype_add_tsum_subtype_compl`: `∑'_{x ∈ s} f x + ∑'_{x ∉ s} f x = ∑'_x f x` for
  `ℝ≥0∞`-valued `f`.
* `WeierstrassCurve.β_add_tsum_compl_K0`: `β_p + ∑_{K ∉ 𝒦₀} δ_p(K) = 1`.
* `WeierstrassCurve.one_sub_β_eq_tsum_compl_K0`: `1 - β_p = ∑_{K ∉ 𝒦₀} δ_p(K)`.
* `WeierstrassCurve.one_le_β_add_nine_div_sq`: `1 ≤ β_p + 9/p²` for every prime `p`.
* `WeierstrassCurve.one_sub_β_le_nine_div_sq`: `1 - β_p ≤ 9/p²`.
* `WeierstrassCurve.exists_tail_bound_β`: there is `C > 0` with `1 - β_q ≤ C/q²` for every prime
  `q`.

## Implementation notes

Subtraction in `ℝ≥0∞` truncates, so the additive statements `β_p + ∑_{K ∉ 𝒦₀} δ_p(K) = 1` and
`1 ≤ β_p + 9/p²` are the primary forms; the subtractive forms are derived from them, using
`β_p ≤ 1`.
-/

@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal

/-! ### Splitting an `ℝ≥0∞`-valued sum at a set -/

namespace ENNReal

/-- For any `f : ι → ℝ≥0∞` and any `s ⊆ ι`, `∑'_{x ∈ s} f x + ∑'_{x ∉ s} f x = ∑'_x f x`. -/
theorem tsum_subtype_add_tsum_subtype_compl {ι : Type*} (f : ι → ℝ≥0∞) (s : Set ι) :
    ∑' x : ↥s, f x + ∑' x : ↥sᶜ, f x = ∑' x, f x := by
  classical
  have h := (Equiv.Set.sumCompl s).tsum_eq f
  rwa [ENNReal.summable.tsum_sum ENNReal.summable] at h

end ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable (p : ℕ) [Fact p.Prime]

/-! ### The identity -/

/-- `β_p` is the sum of `δ_p(K)` over the subtype `↥𝒦₀`. -/
theorem tsum_subtype_K0_deltaP : ∑' K : ↥(K0 : Set ReductionData), deltaP p K = β p :=
  (tsum_subtype_K0 (deltaP p)).trans (β_add p).symm

/-- `β_p + ∑_{K ∉ 𝒦₀} δ_p(K) = 1` for every prime `p`. -/
theorem β_add_tsum_compl_K0 :
    β p + ∑' K : ↥(K0ᶜ : Set ReductionData), deltaP p K = 1 := by
  rw [← tsum_subtype_K0_deltaP p, ENNReal.tsum_subtype_add_tsum_subtype_compl, tsum_deltaP]

/-- `β_p ≤ 1`. -/
theorem β_le_one : β p ≤ 1 :=
  (self_le_add_right _ _).trans_eq (β_add_tsum_compl_K0 p)

/-- `β_p ≠ ∞`. -/
theorem β_ne_top : β p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (β_le_one p)

/-- `1 - β_p = ∑_{K ∉ 𝒦₀} δ_p(K)` for every prime `p`, the difference being taken in `ℝ≥0∞`. -/
@[bsd_tamagawa "T020"]
theorem one_sub_β_eq_tsum_compl_K0 :
    1 - β p = ∑' K : ↥(K0ᶜ : Set ReductionData), deltaP p K :=
  ENNReal.sub_eq_of_eq_add (β_ne_top p) ((add_comm _ _).trans (β_add_tsum_compl_K0 p)).symm

/-! ### The bound -/

/-- The union of the two `𝒦₀` strata of the coefficient plane has mass at most `β_p`. -/
theorem volume_stratFibre_K0_union_le_β :
    (volume : Measure (ℤ_[p] × ℤ_[p]))
        (stratFibre p (KodairaSymbol.I 0, 1) ∪ stratFibre p (KodairaSymbol.I 1, 1))
      ≤ β p :=
  le_trans (measure_union_le _ _) (by rw [volume_stratFibre, volume_stratFibre, β_add])

/-- `1 ≤ β_p + 3/p²` for every prime `p ≥ 5`. -/
theorem one_le_β_add_three_div_sq (hp : 5 ≤ p) : 1 ≤ β p + 3 / (p : ℝ≥0∞) ^ 2 := by
  have hprob : IsProbabilityMeasure (volume : Measure (ℤ_[p] × ℤ_[p])) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  calc (1 : ℝ≥0∞) = volume (univ : Set (ℤ_[p] × ℤ_[p])) := measure_univ.symm
    _ = volume (sqDvdΔLocus p ∪ (sqDvdΔLocus p)ᶜ) := by rw [union_compl_self]
    _ ≤ volume (sqDvdΔLocus p) + volume ((sqDvdΔLocus p)ᶜ) := measure_union_le _ _
    _ ≤ 3 * ((p : ℝ≥0∞) ^ 2)⁻¹ + β p :=
        add_le_add (volume_sqDvdΔLocus_le hp)
          ((measure_mono compl_sqDvdΔLocus_subset_stratFibre_union).trans
            (volume_stratFibre_K0_union_le_β p))
    _ = β p + 3 / (p : ℝ≥0∞) ^ 2 := by rw [div_eq_mul_inv]; ring

/-- `1 ≤ β_p + 9/p²` for every prime `p`. -/
theorem one_le_β_add_nine_div_sq : 1 ≤ β p + 9 / (p : ℝ≥0∞) ^ 2 := by
  rcases le_or_gt 5 p with hp | hp
  · refine (one_le_β_add_three_div_sq p hp).trans ?_
    gcongr
    norm_num
  · have hp3 : p ≤ 3 := by
      have h4 : p ≠ 4 := fun h => absurd (h ▸ (Fact.out : p.Prime)) (by decide)
      omega
    exact (one_le_nine_div_sq hp3).trans le_add_self

/-- `1 - β_p ≤ 9/p²` for every prime `p`, the difference being taken in `ℝ≥0∞`. -/
@[bsd_tamagawa "T020"]
theorem one_sub_β_le_nine_div_sq : 1 - β p ≤ 9 / (p : ℝ≥0∞) ^ 2 :=
  tsub_le_iff_right.2 ((one_le_β_add_nine_div_sq p).trans_eq (add_comm _ _))

/-- The mass outside `𝒦₀` is at most `9/p²`: `∑_{K ∉ 𝒦₀} δ_p(K) ≤ 9/p²`. -/
theorem tsum_compl_K0_le_nine_div_sq :
    ∑' K : ↥(K0ᶜ : Set ReductionData), deltaP p K ≤ 9 / (p : ℝ≥0∞) ^ 2 :=
  (one_sub_β_eq_tsum_compl_K0 p).symm.trans_le (one_sub_β_le_nine_div_sq p)

/-- There is a constant `C > 0` with `1 - β_q ≤ C/q²` for every prime `q`. -/
@[bsd_tamagawa "T020"]
theorem exists_tail_bound_β :
    ∃ C : ℝ≥0∞, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], 1 - β q ≤ C / (q : ℝ≥0∞) ^ 2 :=
  ⟨9, by norm_num, fun q _ => one_sub_β_le_nine_div_sq q⟩

end WeierstrassCurve
