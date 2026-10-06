/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.PadicHaar

/-!
# Self-similarity of the coefficient plane

The dilation `σ_p(a₄, a₆) := (p⁴ a₄, p⁶ a₆)` of the coefficient plane `ℤ_[p] × ℤ_[p]` scales the
Haar measure by `p^{-10}`: `μ_p(σ_p(S)) = p^{-10} μ_p(S)` for every `S ⊆ ℤ_[p] × ℤ_[p]`, measurable
or not. More generally `(x, y) ↦ (p^m x, p^n y)` scales it by `p^{-(m+n)}`; the dilation of a set
is formalized as its image, since `Set (ℤ_[p] × ℤ_[p])` carries no scalar action.

## Main definitions

* `PadicInt.scaleProdByPPow`: the dilation `(x, y) ↦ (p^m x, p^n y)` of `ℤ_[p] × ℤ_[p]`.

## Main results

* `PadicInt.map_scaleProdByPPow`: the pushforward of `volume` along the dilation is `p^{m+n}` times
  `volume` restricted to `p^m ℤ_[p] × p^n ℤ_[p]`.
* `PadicInt.measure_image_scaleProdByPPow`: `μ_p(σ '' S) = p^{-(m+n)} μ_p(S)` for every `S`.
* `PadicInt.measure_image_scaleProdByPPow_four_six`: `μ_p(σ_p(S)) = p^{-10} μ_p(S)`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The dilation `(x, y) ↦ (p^m x, p^n y)` of `ℤ_[p] × ℤ_[p]`. -/
noncomputable def scaleProdByPPow (m n : ℕ) : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p] :=
  Prod.map (scaleByPPow m) (scaleByPPow n)

/-- `PadicInt.scaleProdByPPow m n` is a measurable embedding. -/
theorem measurableEmbedding_scaleProdByPPow (m n : ℕ) :
    MeasurableEmbedding (scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) :=
  (measurableEmbedding_scaleByPPow m).prodMap (measurableEmbedding_scaleByPPow n)

/-- The range of `PadicInt.scaleProdByPPow m n` is the product of the ranges of `scaleByPPow m` and
`scaleByPPow n`. -/
theorem range_scaleProdByPPow (m n : ℕ) :
    Set.range (scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = Set.range (scaleByPPow (p := p) m) ×ˢ Set.range (scaleByPPow (p := p) n) :=
  Set.range_prodMap ..

/-- The pushforward of `volume` along `(x, y) ↦ (p^m x, p^n y)` is `p^{m+n}` times the restriction
of `volume` to the range `p^m ℤ_[p] × p^n ℤ_[p]`. -/
theorem map_scaleProdByPPow (m n : ℕ) :
    Measure.map (scaleProdByPPow m n) (volume : Measure (ℤ_[p] × ℤ_[p]))
      = (p : ℝ≥0∞) ^ (m + n) • (volume : Measure (ℤ_[p] × ℤ_[p])).restrict
          (Set.range (scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) := by
  rw [Measure.volume_eq_prod, scaleProdByPPow, ← Measure.map_prod_map volume volume
      (measurableEmbedding_scaleByPPow m).measurable
      (measurableEmbedding_scaleByPPow n).measurable,
    map_scaleByPPow, map_scaleByPPow, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_restrict, Set.range_prodMap, smul_smul, ← pow_add]

/-- For every `S ⊆ ℤ_[p] × ℤ_[p]`, `volume ((p^m, p^n) · S) = p^{-(m+n)} · volume S`. -/
theorem measure_image_scaleProdByPPow (m n : ℕ) (S : Set (ℤ_[p] × ℤ_[p])) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (scaleProdByPPow m n '' S)
      = (p : ℝ≥0∞) ^ (-(m + n : ℤ)) * volume S := by
  have hemb : MeasurableEmbedding (scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) :=
    measurableEmbedding_scaleProdByPPow m n
  have hp0 : ((p : ℝ≥0∞) ^ (m + n)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hptop : ((p : ℝ≥0∞) ^ (m + n)) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have hcancel : (p : ℝ≥0∞) ^ (-(m + n : ℤ)) * (p : ℝ≥0∞) ^ (m + n) = 1 := by
    rw [ENNReal.zpow_neg (p : ℝ≥0∞) (m + n : ℤ), ← Nat.cast_add, zpow_natCast]
    exact ENNReal.inv_mul_cancel hp0 hptop
  have hkey : (volume : Measure (ℤ_[p] × ℤ_[p])) S
      = (p : ℝ≥0∞) ^ (m + n) * volume (scaleProdByPPow m n '' S) := by
    have h := congrArg (fun ν : Measure (ℤ_[p] × ℤ_[p]) => ν (scaleProdByPPow m n '' S))
      (map_scaleProdByPPow (p := p) m n)
    rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, Measure.smul_apply,
      Measure.restrict_apply' hemb.measurableSet_range,
      Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _), smul_eq_mul] at h
    exact h
  calc (volume : Measure (ℤ_[p] × ℤ_[p])) (scaleProdByPPow m n '' S)
      = (p : ℝ≥0∞) ^ (-(m + n : ℤ)) *
          ((p : ℝ≥0∞) ^ (m + n) * volume (scaleProdByPPow m n '' S)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ = (p : ℝ≥0∞) ^ (-(m + n : ℤ)) * volume S := by rw [← hkey]

/-- For a prime `p` and every `S ⊆ ℤ_p × ℤ_p`, the dilation `σ_p(a₄, a₆) = (p⁴ a₄, p⁶ a₆)`
satisfies `μ_p(σ_p(S)) = p^{-10} μ_p(S)`. -/
@[bsd_tamagawa "T021c"]
theorem measure_image_scaleProdByPPow_four_six (S : Set (ℤ_[p] × ℤ_[p])) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (scaleProdByPPow 4 6 '' S)
      = (p : ℝ≥0∞) ^ (-(10 : ℤ)) * volume S := by
  simpa using measure_image_scaleProdByPPow (p := p) 4 6 S

end PadicInt
