/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.Measure

/-!
# Haar measure on `ℤ_[p]`: balls, scaling, and square level sets

Mass computations for the additive Haar probability measure `volume : Measure ℤ_[p]`: the ideals
`p^m ℤ_[p]`, the fibres of the reductions `ℤ_[p] ↠ ℤ/p^nℤ` and the closed balls of radius
`p^{-n}`, which are translates of one another; the effect of multiplication by `p^m`; the valuation
level sets; and, for odd `p`, the square level sets `{x | v(x² - c) = n}`.

## Main definitions

* `PadicInt.scaleByPPow`: multiplication by `p^m` on `ℤ_[p]`.
* `PadicInt.sqLevelSet`: the level set `{x | v(x² - c) = n}`.

## Main results

* `PadicInt.measure_span_pPow`: the ideal `p^m ℤ_[p]` has mass `p^{-m}`.
* `PadicInt.volume_preimage_toZModPow`: each fibre of `ℤ_[p] ↠ ℤ/p^nℤ` has mass `p^{-n}`.
* `PadicInt.measure_image_scaleByPPow`: multiplication by `p^m` scales the mass of an
  **arbitrary** set by `p^{-m}`; equivalently `PadicInt.map_scaleByPPow` in pushforward form.
* `PadicInt.volume_setOf_emultiplicity_eq`: the valuation level set `{y | v y = n}` has mass
  `(1 - p^{-1}) p^{-n}`.
* `PadicInt.isSquare_iff_isSquare_toZMod`: for odd `p`, a unit is a square iff its residue is.
* `PadicInt.measure_sqLevelSet_of_isSquare` and
  `PadicInt.measure_sqLevelSet_of_not_isSquare`: for odd `p`, a unit `c` and `n ≥ 1`, the
  level set `{x | v(x² - c) = n}` has mass `2 (1 - p^{-1}) p^{-n}` if `c` is a square and is
  empty otherwise.

## Implementation notes

The `ℕ∞`-valued valuation is `v = emultiplicity (p : ℤ_[p])`, not `PadicInt.valuation`. The latter
is `ℕ`-valued with `valuation 0 = 0`, so `{y | m ≤ valuation y}` would exclude `0` for `m ≥ 1`,
whereas `0 ∈ p^m ℤ_[p]`; `emultiplicity` has the convention `v 0 = ⊤` and matches the ideal
exactly.

`(p^m) • S` is formalized as the image `scaleByPPow m '' S`, since `Set ℤ_[p]` carries no
action of a ring element.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ## The `ℕ∞`-valued valuation -/

/-- Membership in the ideal `p^m ℤ_[p]` is the valuation inequality `m ≤ v y`, for the
`ℕ∞`-valued valuation `v = emultiplicity (p : ℤ_[p])`. No hypothesis `y ≠ 0` is needed, since
`v 0 = ⊤`. -/
theorem mem_span_pPow_iff_le_emultiplicity {m : ℕ} {y : ℤ_[p]} :
    y ∈ (Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) ↔
      (m : ℕ∞) ≤ emultiplicity (p : ℤ_[p]) y := by
  rw [Ideal.mem_span_singleton, pow_dvd_iff_le_emultiplicity]

/-- The valuation of a unit of `ℤ_[p]` is `0`. -/
theorem emultiplicity_eq_zero_of_isUnit {u : ℤ_[p]} (hu : IsUnit u) :
    emultiplicity (p : ℤ_[p]) u = 0 :=
  emultiplicity_eq_zero.2 fun h => p_nonunit (isUnit_of_dvd_unit h hu)

/-- The valuation level set `{y | v y = n}` is the difference of two ideals: the elements
divisible by `p^n` but not by `p^{n+1}`. -/
theorem setOf_emultiplicity_eq (n : ℕ) :
    {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (n : ℕ∞)}
      = ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p])
          \ ((Ideal.span {(p : ℤ_[p]) ^ (n + 1)} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe,
    mem_span_pPow_iff_le_emultiplicity]
  refine ⟨fun h => ⟨h.ge, ?_⟩, fun ⟨hle, hnlt⟩ => ?_⟩
  · rw [h]
    exact_mod_cast Nat.not_succ_le_self n
  · rcases le_iff_lt_or_eq.mp hle with hlt | heq
    · exact absurd (by push_cast; exact Order.add_one_le_of_lt hlt) hnlt
    · exact heq.symm

/-! ## Balls, ideals and their masses -/

/-- The ideal `p^m ℤ_[p]` is the closed ball of radius `p^{-m}` about `0`; equivalently, by
`PadicInt.norm_le_pow_iff_mem_span_pow`, the norm-set `{y | ‖y‖ ≤ p^{-m}}`. -/
theorem coe_span_pPow_eq_closedBall (m : ℕ) :
    ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p])
      = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(m : ℤ))) := by
  ext y
  rw [SetLike.mem_coe, ← norm_le_pow_iff_mem_span_pow, Metric.mem_closedBall, dist_zero_right]

/-- The ideal `p^m ℤ_[p]` is measurable, being a closed ball. -/
theorem measurableSet_span_pPow (m : ℕ) :
    MeasurableSet ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  rw [coe_span_pPow_eq_closedBall]
  exact measurableSet_closedBall

/-- The additive subgroup `p^m ℤ_[p]` has index `p^m`. -/
theorem index_span_pPow (m : ℕ) :
    (Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]).toAddSubgroup.index = p ^ m := by
  have e : (ℤ_[p] ⧸ RingHom.ker (toZModPow m : ℤ_[p] →+* ZMod (p ^ m))) ≃+* ZMod (p ^ m) :=
    RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)
  have hcard : Nat.card (ℤ_[p] ⧸ (Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p])) = p ^ m := by
    have h := Nat.card_congr e.toEquiv
    rw [Nat.card_zmod] at h
    rw [← h]
    congr 1
    rw [ker_toZModPow]
  rw [AddSubgroup.index_eq_card]
  exact hcard

/-- The ideal `p^m ℤ_[p]` has mass `p^{-m}`. -/
theorem measure_span_pPow (m : ℕ) :
    (volume : Measure ℤ_[p]) ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p])
      = (p : ℝ≥0∞) ^ (-(m : ℤ)) := by
  set H := (Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]).toAddSubgroup with hH
  have hmeas : MeasurableSet (H : Set ℤ_[p]) := measurableSet_span_pPow m
  have hidx : H.index = p ^ m := index_span_pPow m
  have _ : H.FiniteIndex := ⟨by rw [hidx]; exact pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  have key := MeasureTheory.AddSubgroup.index_mul_measure H hmeas (volume : Measure ℤ_[p])
  rw [hidx, measure_univ] at key
  have hval : (volume : Measure ℤ_[p]) (H : Set ℤ_[p]) = ((p : ℝ≥0∞) ^ m)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact_mod_cast key)
  rw [show ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p]) = (H : Set ℤ_[p]) from rfl,
    hval, ENNReal.zpow_neg, zpow_natCast]

/-- The ideal `p^m ℤ_[p]` has mass `(p⁻¹)^m`. -/
theorem measure_span_pPow' (m : ℕ) :
    (volume : Measure ℤ_[p]) ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p])
      = ((p : ℝ≥0∞)⁻¹) ^ m := by
  rw [measure_span_pPow, ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]

/-- The fibre of `ℤ_[p] ↠ ℤ/p^nℤ` through `x` is the closed ball of radius `p^{-n}` about `x`. -/
theorem preimage_toZModPow_eq_closedBall (n : ℕ) (x : ℤ_[p]) :
    (toZModPow n ⁻¹' {toZModPow n x} : Set ℤ_[p]) = Metric.closedBall x (((p : ℝ) ^ n)⁻¹) := by
  ext y
  rw [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm,
    show (((p : ℝ) ^ n)⁻¹) = (p : ℝ) ^ (-n : ℤ) by rw [zpow_neg, zpow_natCast],
    norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- Two `p`-adic integers with the same image in `ℤ/p^nℤ` are within `p^{-n}` of each other. -/
theorem dist_le_of_toZModPow_eq {n : ℕ} {x y : ℤ_[p]}
    (h : toZModPow n y = toZModPow n x) : dist y x ≤ (((p : ℝ) ^ n)⁻¹) := by
  rw [← Metric.mem_closedBall, ← preimage_toZModPow_eq_closedBall n x]
  exact h

/-- Every residue `a` in `ℤ/p^nℤ` lifts to `ℤ_[p]`: it is hit by the natural number `a.val`. -/
theorem exists_toZModPow_eq (n : ℕ) (a : ZMod (p ^ n)) :
    ∃ x : ℤ_[p], toZModPow n x = a :=
  ⟨(a.val : ℤ_[p]), by rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]⟩

/-- Each fibre of `ℤ_[p] ↠ ℤ/p^nℤ` is measurable, being a closed ball. -/
theorem measurableSet_preimage_toZModPow (n : ℕ) (a : ZMod (p ^ n)) :
    MeasurableSet (toZModPow n ⁻¹' {a} : Set ℤ_[p]) := by
  obtain ⟨x, hx⟩ := exists_toZModPow_eq (p := p) n a
  rw [← hx, preimage_toZModPow_eq_closedBall]
  exact measurableSet_closedBall

/-- Each fibre of the reduction `ℤ_[p] ↠ ℤ/p^nℤ` has Haar probability measure `p^{-n}`. -/
theorem volume_preimage_toZModPow (n : ℕ) (a : ZMod (p ^ n)) :
    (volume : Measure ℤ_[p]) (toZModPow n ⁻¹' {a} : Set ℤ_[p]) = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  obtain ⟨x, hx⟩ := exists_toZModPow_eq (p := p) n a
  have hball : (toZModPow n ⁻¹' {a} : Set ℤ_[p])
      = Metric.closedBall x ((p : ℝ) ^ (-(n : ℤ))) := by
    rw [← hx, preimage_toZModPow_eq_closedBall n x, zpow_neg, zpow_natCast]
  have htr : (fun h : ℤ_[p] => x + h) ⁻¹' Metric.closedBall x ((p : ℝ) ^ (-(n : ℤ)))
      = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hball, ← measure_preimage_add (volume : Measure ℤ_[p]) x, htr,
    ← coe_span_pPow_eq_closedBall, measure_span_pPow, ENNReal.zpow_neg, zpow_natCast]

/-! ## The scaling map -/

/-- Multiplication by `p^m` on the `p`-adic integers, `x ↦ p^m x`. -/
noncomputable def scaleByPPow (m : ℕ) : ℤ_[p] → ℤ_[p] := fun x => (p : ℤ_[p]) ^ m * x

/-- Multiplication by a nonzero element of `ℤ_[p]` is a measurable embedding. -/
theorem measurableEmbedding_mul_left_of_ne_zero {c : ℤ_[p]} (hc : c ≠ 0) :
    MeasurableEmbedding (fun x : ℤ_[p] => c * x) :=
  ((continuous_const_mul c).isClosedEmbedding (mul_right_injective₀ hc)).measurableEmbedding

/-- `PadicInt.scaleByPPow m` is a measurable embedding. -/
theorem measurableEmbedding_scaleByPPow (m : ℕ) :
    MeasurableEmbedding (scaleByPPow m : ℤ_[p] → ℤ_[p]) :=
  measurableEmbedding_mul_left_of_ne_zero (pow_ne_zero m uniformizer_ne_zero)

/-- The image of a measurable set under `PadicInt.scaleByPPow m` is measurable. -/
theorem measurableSet_image_scaleByPPow {m : ℕ} {S : Set ℤ_[p]} (hS : MeasurableSet S) :
    MeasurableSet (scaleByPPow m '' S) :=
  (measurableEmbedding_scaleByPPow m).measurableSet_image.mpr hS

/-- The range of `PadicInt.scaleByPPow m` is the ideal `p^m ℤ_[p]`. -/
theorem range_scaleByPPow (m : ℕ) :
    Set.range (scaleByPPow m : ℤ_[p] → ℤ_[p])
      = ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  ext y
  simp only [Set.mem_range, SetLike.mem_coe, Ideal.mem_span_singleton']
  exact ⟨fun ⟨x, hx⟩ => ⟨x, by rw [← hx, scaleByPPow]; ring⟩,
    fun ⟨a, ha⟩ => ⟨a, by rw [← ha, scaleByPPow]; ring⟩⟩

/-- For an arbitrary set `S ⊆ ℤ_[p]`, not necessarily measurable,
`volume (p^m · S) = p^{-m} · volume S`. -/
theorem measure_image_scaleByPPow (m : ℕ) (S : Set ℤ_[p]) :
    (volume : Measure ℤ_[p]) (scaleByPPow m '' S) = (p : ℝ≥0∞) ^ (-(m : ℤ)) * volume S := by
  set g := (scaleByPPow m : ℤ_[p] → ℤ_[p]) with hg
  have hemb : MeasurableEmbedding g := measurableEmbedding_scaleByPPow m
  have hadd : ∀ x y : ℤ_[p], g (x + y) = g x + g y := by
    intro x y; simp only [hg, scaleByPPow]; ring
  have hsub : ∀ x y : ℤ_[p], g (x - y) = g x - g y := by
    intro x y; simp only [hg, scaleByPPow]; ring
  set ν := Measure.comap g (volume : Measure ℤ_[p])
  have hνapp : ∀ s : Set ℤ_[p], ν s = (volume : Measure ℤ_[p]) (g '' s) := fun s =>
    hemb.comap_apply _ _
  have _ : ν.IsAddLeftInvariant := by
    rw [← MeasureTheory.forall_measure_preimage_add_iff]
    intro a A _
    rw [hνapp, hνapp]
    have hsetimg : g '' ((fun h => a + h) ⁻¹' A) = (fun h => g a + h) ⁻¹' (g '' A) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      refine ⟨fun ⟨x, hx, hxy⟩ => ⟨a + x, hx, by rw [← hxy, hadd]⟩, fun ⟨z, hz, hzeq⟩ => ?_⟩
      exact ⟨z - a, by simpa using hz, by rw [hsub, hzeq]; abel⟩
    rw [hsetimg]
    exact measure_preimage_add (volume : Measure ℤ_[p]) (g a) (g '' A)
  have _ : IsFiniteMeasure ν :=
    ⟨by rw [hνapp]; exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _)⟩
  have heq := MeasureTheory.Measure.isAddInvariant_eq_smul_of_compactSpace ν
    (volume : Measure ℤ_[p])
  set c := ν.addHaarScalarFactor (volume : Measure ℤ_[p])
  have hcval : (c : ℝ≥0∞) = (p : ℝ≥0∞) ^ (-(m : ℤ)) := by
    have huniv : ν Set.univ = (p : ℝ≥0∞) ^ (-(m : ℤ)) := by
      rw [hνapp, Set.image_univ, range_scaleByPPow, measure_span_pPow]
    have huniv2 : ν Set.univ = (c : ℝ≥0∞) := by rw [heq]; simp
    rw [← huniv2, huniv]
  rw [← hνapp, heq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hcval]

/-- The pushforward of `volume` along multiplication by `p^m` is `p^m` times the restriction of
`volume` to `p^m ℤ_[p]`. -/
theorem map_scaleByPPow (m : ℕ) :
    Measure.map (scaleByPPow m) (volume : Measure ℤ_[p])
      = (p : ℝ≥0∞) ^ m • ((volume : Measure ℤ_[p]).restrict
          (Set.range (scaleByPPow m : ℤ_[p] → ℤ_[p]))) := by
  have hemb : MeasurableEmbedding (scaleByPPow m : ℤ_[p] → ℤ_[p]) :=
    measurableEmbedding_scaleByPPow m
  have hpm : ((p : ℝ≥0∞) ^ m) ≠ 0 :=
    pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hpm' : ((p : ℝ≥0∞) ^ m) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have hcancel : (p : ℝ≥0∞) ^ m * (p : ℝ≥0∞) ^ (-(m : ℤ)) = 1 := by
    rw [ENNReal.zpow_neg (p : ℝ≥0∞) (m : ℤ), zpow_natCast]
    exact ENNReal.mul_inv_cancel hpm hpm'
  ext A hA
  rw [hemb.map_apply, Measure.smul_apply, Measure.restrict_apply hA,
    Set.image_preimage_eq_inter_range.symm, measure_image_scaleByPPow, smul_eq_mul, ← mul_assoc,
    hcancel, one_mul]

/-! ## Valuation level sets -/

/-- The valuation level set `{y | v y = n}` is measurable. -/
theorem measurableSet_setOf_emultiplicity_eq (n : ℕ) :
    MeasurableSet {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (n : ℕ∞)} := by
  rw [setOf_emultiplicity_eq]
  exact (measurableSet_span_pPow n).diff (measurableSet_span_pPow (n + 1))

/-- The valuation level set has mass `volume {y | v y = n} = (1 - p^{-1}) p^{-n}`. -/
theorem volume_setOf_emultiplicity_eq (n : ℕ) :
    (volume : Measure ℤ_[p]) {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (n : ℕ∞)}
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ n := by
  have hpne : (p : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [(Fact.out : p.Prime).ne_zero]
  have hsub : ((Ideal.span {(p : ℤ_[p]) ^ (n + 1)} : Ideal ℤ_[p]) : Set ℤ_[p])
      ⊆ ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) := fun y hy => by
    rw [SetLike.mem_coe, mem_span_pPow_iff_le_emultiplicity] at hy ⊢
    exact le_trans (by exact_mod_cast Nat.le_succ n) hy
  have hfin : (volume : Measure ℤ_[p])
      ((Ideal.span {(p : ℤ_[p]) ^ (n + 1)} : Ideal ℤ_[p]) : Set ℤ_[p]) ≠ ⊤ := by
    rw [measure_span_pPow']
    exact ENNReal.pow_ne_top hpne
  rw [setOf_emultiplicity_eq,
    measure_sdiff hsub (measurableSet_span_pPow (n + 1)).nullMeasurableSet hfin,
    measure_span_pPow', measure_span_pPow',
    ENNReal.sub_mul fun _ _ => ENNReal.pow_ne_top hpne, one_mul, pow_succ, mul_comm]

/-! ## Square level sets -/

/-- For an odd prime `p`, `2` is a unit of `ℤ_[p]`. -/
theorem isUnit_two (hp : Odd p) : IsUnit (2 : ℤ_[p]) := by
  rw [isUnit_iff]
  rcases lt_or_eq_of_le (norm_le_one (2 : ℤ_[p])) with hlt | heq
  · exfalso
    have hn : ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by push_cast; simpa using hlt
    rw [norm_intCast_lt_one_iff] at hn
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hn)
    interval_cases p
    · exact (Nat.not_prime_zero Fact.out).elim
    · exact (Nat.not_prime_one Fact.out).elim
    · rw [Nat.odd_iff] at hp; simp at hp
  · exact heq

/-- For an odd prime `p`, a unit `s` and every `x`, at least one of `x - s`, `x + s` is a unit. -/
theorem isUnit_sub_or_isUnit_add (hp : Odd p) {s : ℤ_[p]} (hs : IsUnit s) (x : ℤ_[p]) :
    IsUnit (x - s) ∨ IsUnit (x + s) := by
  rcases em (IsUnit (x - s)) with hu | h1
  · exact Or.inl hu
  rcases em (IsUnit (x + s)) with hu | h2
  · exact Or.inr hu
  exfalso
  have hn1 : ‖-(x - s)‖ < 1 := by
    rw [norm_neg]
    exact lt_of_le_of_ne (norm_le_one _) fun he => h1 (isUnit_iff.mpr he)
  have hn2 : ‖x + s‖ < 1 :=
    lt_of_le_of_ne (norm_le_one _) fun he => h2 (isUnit_iff.mpr he)
  have hsum : ‖(x + s) + (-(x - s))‖ < 1 := norm_lt_one_add hn2 hn1
  rw [show (x + s) + (-(x - s)) = 2 * s by ring,
    isUnit_iff.mp ((isUnit_two hp).mul hs)] at hsum
  exact lt_irrefl 1 hsum

/-- For an odd prime `p` and a unit `c`, `c` is a square in `ℤ_[p]` iff its residue
`PadicInt.toZMod c` is a square in `ZMod p`. -/
theorem isSquare_iff_isSquare_toZMod (hp : Odd p) {c : ℤ_[p]} (hc : IsUnit c) :
    IsSquare c ↔ IsSquare (toZMod c) := by
  refine ⟨fun ⟨s, hs⟩ => ⟨toZMod s, by rw [hs, map_mul]⟩, fun ⟨r, hr⟩ => ?_⟩
  obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective (toZMod : ℤ_[p] →+* ZMod p) r
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C c with hF
  have haevalF : (Polynomial.aeval a₀) F = a₀ ^ 2 - c := by simp [hF]
  have hderiv : Polynomial.derivative F = 2 * Polynomial.X := by
    simp [hF]; ring
  have haevalD : (Polynomial.aeval a₀) (Polynomial.derivative F) = 2 * a₀ := by
    rw [hderiv]; simp
  have hmem : a₀ ^ 2 - c ∈ RingHom.ker (toZMod : ℤ_[p] →+* ZMod p) := by
    change toZMod (a₀ ^ 2 - c) = 0
    rw [map_sub, map_pow, ha₀, hr]; ring
  rw [ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
  have hnormlt : ‖a₀ ^ 2 - c‖ < 1 :=
    lt_of_le_of_ne (norm_le_one _) fun he => hmem (isUnit_iff.mpr he)
  have hrne : r ≠ 0 := fun h => by
    rw [h, mul_zero] at hr
    exact not_isUnit_zero (hr ▸ hc.map toZMod)
  have ha₀unit : IsUnit a₀ := by
    have hnotmem : a₀ ∉ RingHom.ker (toZMod : ℤ_[p] →+* ZMod p) := by
      rw [RingHom.mem_ker, ha₀]; exact hrne
    rwa [ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hnotmem
  have hcond : ‖(Polynomial.aeval a₀) F‖
      < ‖(Polynomial.aeval a₀) (Polynomial.derivative F)‖ ^ 2 := by
    rw [haevalF, haevalD, isUnit_iff.mp ((isUnit_two hp).mul ha₀unit)]
    simpa using hnormlt
  obtain ⟨z, hz, _⟩ := hensels_lemma hcond
  rw [show (Polynomial.aeval z) F = z ^ 2 - c by simp [hF]] at hz
  exact ⟨z, by rw [← sub_eq_zero.mp hz]; ring⟩

/-- The level set `S(c, n) = {x : ℤ_[p] | v(x² - c) = n}`, for the `ℕ∞`-valued valuation
`v = emultiplicity (p : ℤ_[p])`. Since `v 0 = ⊤`, membership fails when `x² = c`. -/
def sqLevelSet (c : ℤ_[p]) (n : ℕ) : Set ℤ_[p] :=
  {x | emultiplicity (p : ℤ_[p]) (x ^ 2 - c) = (n : ℕ∞)}

/-- Membership characterization of `PadicInt.sqLevelSet`. -/
theorem mem_sqLevelSet {c : ℤ_[p]} {n : ℕ} {x : ℤ_[p]} :
    x ∈ sqLevelSet c n ↔ emultiplicity (p : ℤ_[p]) (x ^ 2 - c) = (n : ℕ∞) := Iff.rfl

/-- For an odd prime `p`, a unit `c` that is a square, and `n ≥ 1`,
`volume {x | v(x² - c) = n} = 2 (1 - p^{-1}) p^{-n}`. -/
theorem measure_sqLevelSet_of_isSquare (hp : Odd p) {c : ℤ_[p]} (hc : IsUnit c)
    (hsq : IsSquare c) {n : ℕ} (hn : 1 ≤ n) :
    (volume : Measure ℤ_[p]) (sqLevelSet c n)
      = 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ n := by
  obtain ⟨s, hs⟩ := hsq
  have hsunit : IsUnit s := by rw [hs] at hc; exact (IsUnit.mul_iff.mp hc).1
  have hn0 : (n : ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hsplit : ∀ x : ℤ_[p], emultiplicity (p : ℤ_[p]) (x ^ 2 - c)
      = emultiplicity (p : ℤ_[p]) (x - s) + emultiplicity (p : ℤ_[p]) (x + s) := fun x => by
    rw [show x ^ 2 - c = (x - s) * (x + s) by rw [hs]; ring, emultiplicity_mul prime_p]
  have hunion : sqLevelSet c n = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - s) = (n : ℕ∞)}
      ∪ {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} := by
    ext x
    rw [Set.mem_union, mem_sqLevelSet, hsplit x]
    simp only [Set.mem_ofPred_eq]
    rcases isUnit_sub_or_isUnit_add hp hsunit x with hu | hu
    · rw [emultiplicity_eq_zero_of_isUnit hu, zero_add]
      exact ⟨Or.inr, fun h => h.resolve_left fun h0 => hn0 h0.symm⟩
    · rw [emultiplicity_eq_zero_of_isUnit hu, add_zero]
      exact ⟨Or.inl, fun h => h.resolve_right fun h0 => hn0 h0.symm⟩
  have hdisj : Disjoint {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - s) = (n : ℕ∞)}
      {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} :=
    Set.disjoint_left.2 fun x hxA hxB => by
      rcases isUnit_sub_or_isUnit_add hp hsunit x with hu | hu
      · exact hn0 (by rw [← hxA]; exact emultiplicity_eq_zero_of_isUnit hu)
      · exact hn0 (by rw [← hxB]; exact emultiplicity_eq_zero_of_isUnit hu)
  have hAeq : {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - s) = (n : ℕ∞)}
      = (fun h => (-s) + h) ⁻¹' {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (n : ℕ∞)} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_preimage]; rw [show (-s) + x = x - s by ring]
  have hBeq : {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)}
      = (fun h => s + h) ⁻¹' {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (n : ℕ∞)} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_preimage]; rw [show s + x = x + s by ring]
  have hmeasB : MeasurableSet {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} := by
    rw [hBeq]
    exact (measurableSet_setOf_emultiplicity_eq n).preimage (by fun_prop)
  rw [hunion, measure_union hdisj hmeasB, hAeq, hBeq, measure_preimage_add,
    measure_preimage_add, volume_setOf_emultiplicity_eq]
  ring

/-- For an odd prime `p`, a unit `c` that is not a square, and `n ≥ 1`, the level set
`{x | v(x² - c) = n}` is empty. -/
theorem sqLevelSet_eq_empty_of_not_isSquare (hp : Odd p) {c : ℤ_[p]} (hc : IsUnit c)
    (hns : ¬IsSquare c) {n : ℕ} (hn : 1 ≤ n) : sqLevelSet c n = (∅ : Set ℤ_[p]) := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => hns ?_
  rw [mem_sqLevelSet] at hx
  have hdvd : (p : ℤ_[p]) ∣ x ^ 2 - c := by
    have := pow_dvd_of_le_emultiplicity (a := (p : ℤ_[p])) (b := x ^ 2 - c) (k := 1)
      (by rw [hx]; exact_mod_cast hn)
    rwa [pow_one] at this
  obtain ⟨k, hk⟩ := hdvd
  have htoZ : toZMod (x ^ 2 - c) = 0 := by
    rw [hk, map_mul, show toZMod (p : ℤ_[p]) = 0 by rw [map_natCast]; exact ZMod.natCast_self p,
      zero_mul]
  rw [map_sub, map_pow, sub_eq_zero] at htoZ
  exact (isSquare_iff_isSquare_toZMod hp hc).mpr ⟨toZMod x, by rw [← htoZ]; ring⟩

/-- For an odd prime `p`, a unit `c` that is not a square, and `n ≥ 1`, the level set
`{x | v(x² - c) = n}` has mass `0`. -/
theorem measure_sqLevelSet_of_not_isSquare (hp : Odd p) {c : ℤ_[p]} (hc : IsUnit c)
    (hns : ¬IsSquare c) {n : ℕ} (hn : 1 ≤ n) :
    (volume : Measure ℤ_[p]) (sqLevelSet c n) = 0 := by
  rw [sqLevelSet_eq_empty_of_not_isSquare hp hc hns hn, measure_empty]

end PadicInt
