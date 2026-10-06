/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.SmallPrimeRatioThree
public import BSDTamagawa.LocalDensity.TailConstant

/-!
# The explicit tail constant at `p = 3`: `α_3 = 1/(3 · 29524)`

The minimal storey `τ_3⁻¹((I_t, t)) ∖ σ_3(ℤ_3²)` of the `p = 3` split-multiplicative stratum is
weighed exactly, and, granted `StratScaleInvariant 3`, this evaluates `δ_3(t) = α_3 · 3^{-t}` for
`t ≥ 5` with `α_3 = 1/(3 · 29524)`.

## Main results

* `PadicInt.volume_sqLevelSet_inter_of_unique_root`: for an odd prime, a unit centre `c = s²`, a
  constraint `Q` that is a union of residue classes mod `p`, and `n ≥ 1`, if `Q` contains exactly
  one of `s`, `-s` then `μ(sqLevelSet c n ∩ Q) = (1 - p⁻¹)p⁻ⁿ`.
* `WeierstrassCurve.splitResidueSet_unique_three`: for a unit `s` of `ℤ_3`, exactly one of `s`,
  `-s` lies in `splitResidueSet 3`.
* `WeierstrassCurve.isSquare_neg_four_mul_cube_iff_three`: for a unit `α` of `ℤ_3`, `-4α³` is a
  square iff `α ≡ -1 mod 3`.
* `WeierstrassCurve.volume_stratFibre_diff_range_three` and
  `WeierstrassCurve.volume_stratFibre_diff_range_three_eq_two_mul`: for every `t ≥ 5`,
  `μ_3(τ_3⁻¹((I_t, t)) ∖ σ_3(ℤ_3²)) = (1 - 3⁻¹) · 3^{-(t+10)} = 2 · 3^{-(t+11)}`.
* `WeierstrassCurve.δ_eq_ofReal_three` and `WeierstrassCurve.α_eq_ofReal_three`: granted
  `StratScaleInvariant 3`, `δ_3(t) = α_3 · 3^{-t}` for `t ≥ 5`, with `α_3 = 1/(3 · 29524)`.

## Implementation notes

The storeys of the `p = 3` stratum are the `σ_3`-dilates of the minimal one, and `σ_3` scales Haar
measure by `3⁻¹⁰`. Summing them is the fixed-point equation
`δ_3(t) = 3⁻¹⁰ δ_3(t) + μ_3(minimal storey)`, whose finite solution carries
`(1 - 3⁻¹⁰)⁻¹ = 3¹⁰/(3¹⁰ - 1)`. With the minimal storey weighing `2 · 3^{-(t+11)}`,

  `α_3 = 3⁵ δ_3(5) = 3⁵ · 2 · 3⁻¹⁶ · 3¹⁰/(3¹⁰ - 1) = 2/(3(3¹⁰ - 1)) = 1/(3 · 29524)`,

since `3¹⁰ - 1 = 2 · 29524`. The factor `2` cancels against the two Hensel balls of which the split
test keeps one, and the factor `3` is the `3⁻¹` by which the nonempty `a₄`-slices form one residue
class out of three. At `p = 3` the minimal storey is `{v₃(a₄) = 3}`, one Step-11 pass being forced,
and the `a₄`-condition is the single class `α ≡ -1 mod 3`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

/-! ### The absolute two-ball count, cut to one ball -/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- For an odd prime `p`, a unit `c = s²`, a set `Q` that is a union of residue classes modulo `p`,
and `n ≥ 1`, if exactly one of `s`, `-s` lies in `Q` then `μ(sqLevelSet c n ∩ Q) = (1 - p⁻¹) p⁻ⁿ`.
-/
theorem volume_sqLevelSet_inter_of_unique_root (hp : Odd p) {c s : ℤ_[p]} (hc : IsUnit c)
    (hs : c = s * s) {Q : Set ℤ_[p]}
    (hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ∣ y - z → (y ∈ Q ↔ z ∈ Q))
    (hone : (s ∈ Q ∧ -s ∉ Q) ∨ (s ∉ Q ∧ -s ∈ Q)) {n : ℕ} (hn : 1 ≤ n) :
    (volume : Measure ℤ_[p]) (sqLevelSet c n ∩ Q)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ n := by
  have hdvd : ∀ {x d : ℤ_[p]}, emultiplicity (p : ℤ_[p]) (x + d) = (n : ℕ∞) →
      (p : ℤ_[p]) ∣ x + d := fun {x d} h => by
    have := pow_dvd_of_le_emultiplicity (a := (p : ℤ_[p])) (b := x + d) (k := 1)
      (by rw [h]; exact_mod_cast hn)
    rwa [pow_one] at this
  rw [sqLevelSet_eq_union_shell hp hc hs hn, Set.union_inter_distrib_right]
  rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hAeq : {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + -s) = (n : ℕ∞)} ∩ Q
        = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + -s) = (n : ℕ∞)} :=
      Set.inter_eq_left.2 fun x hx => (hQ x s (by simpa [sub_eq_add_neg] using hdvd hx)).2 h1
    have hBeq : {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} ∩ Q
        = (∅ : Set ℤ_[p]) :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx =>
        h2 ((hQ x (-s) (by simpa [sub_neg_eq_add] using hdvd hx.1)).1 hx.2)
    rw [hAeq, hBeq, Set.union_empty, volume_setOf_emultiplicity_add_eq]
  · have hAeq : {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + -s) = (n : ℕ∞)} ∩ Q
        = (∅ : Set ℤ_[p]) :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx =>
        h1 ((hQ x s (by simpa [sub_eq_add_neg] using hdvd hx.1)).1 hx.2)
    have hBeq : {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} ∩ Q
        = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} :=
      Set.inter_eq_left.2 fun x hx => (hQ x (-s) (by simpa [sub_neg_eq_add] using hdvd hx)).2 h2
    rw [hAeq, hBeq, Set.empty_union, volume_setOf_emultiplicity_add_eq]

/-- `p^{-m} = (p⁻¹)^m` in `ℝ≥0∞`. -/
theorem zpow_neg_natCast_eq_inv_pow (m : ℕ) :
    (p : ℝ≥0∞) ^ (-(m : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ m :=
  (measure_span_pPow (p := p) m).symm.trans (measure_span_pPow' m)

end PadicInt

/-! ### The split test keeps one ball, and the nonempty slices are one residue class -/

namespace WeierstrassCurve

open BSDTamagawa.HeadSumThree

variable {p : ℕ} [Fact p.Prime]

/-- In `ZMod 3` a nonzero residue `x` has exactly one of `32x`, `-32x` a square. -/
private theorem zmod_three_split_unique :
    ∀ x : ZMod 3, x ≠ 0 →
      (IsSquare ((32 : ZMod 3) * x) ∧ ¬ IsSquare ((32 : ZMod 3) * (-x))) ∨
      (¬ IsSquare ((32 : ZMod 3) * x) ∧ IsSquare ((32 : ZMod 3) * (-x))) := by
  decide

/-- `2 ≠ 0` in `ZMod 3`. -/
private theorem two_ne_zero_zmod_three : (2 : ZMod 3) ≠ 0 := by decide

/-- In `ZMod 3` the residue `-4x³` is a square exactly when `x` is `0` or `2`. -/
private theorem zmod_three_isSquare_neg_four_cube :
    ∀ x : ZMod 3, IsSquare ((-4 : ZMod 3) * x ^ 3) ↔ (x = 0 ∨ x = 2) := by
  decide

/-- A `p`-adic integer with nonzero residue is a unit. -/
private theorem isUnit_of_toZMod_ne_zero {y : ℤ_[p]} (hy : PadicInt.toZMod y ≠ 0) : IsUnit y :=
  not_not.1 fun h => hy (PadicInt.dvd_iff_toZMod_eq_zero.1 (PadicInt.dvd_iff_not_isUnit.2 h))

/-- The residue of a unit is nonzero. -/
private theorem toZMod_ne_zero_of_isUnit {y : ℤ_[p]} (hy : IsUnit y) :
    PadicInt.toZMod y ≠ 0 := fun h =>
  PadicInt.dvd_iff_not_isUnit.1 (PadicInt.dvd_iff_toZMod_eq_zero.2 h) hy

/-- For a unit `s` of `ℤ_3`, exactly one of `s`, `-s` lies in `splitResidueSet 3`. -/
theorem splitResidueSet_unique_three (hp3 : p = 3) {s : ℤ_[p]} (hs : IsUnit s) :
    (s ∈ splitResidueSet p ∧ -s ∉ splitResidueSet p) ∨
      (s ∉ splitResidueSet p ∧ -s ∈ splitResidueSet p) := by
  have hres : ∀ y : ℤ_[p], y ∈ splitResidueSet p ↔ IsSquare ((32 : ZMod p) * PadicInt.toZMod y) :=
    fun y => by
    rw [mem_splitResidueSet_iff, isSquare_mod_iff_isSquare_toZMod, map_mul, map_ofNat]
  have hs0 : PadicInt.toZMod s ≠ 0 := toZMod_ne_zero_of_isUnit hs
  rw [hres, hres, map_neg]
  subst hp3
  exact zmod_three_split_unique _ hs0

/-- For a unit `α` of `ℤ_3`, `-4α³` is a square exactly when `α ≡ -1 mod 3`. -/
theorem isSquare_neg_four_mul_cube_iff_three (hp3 : p = 3) {a : ℤ_[p]} (ha : IsUnit a) :
    IsSquare (-4 * a ^ 3 : ℤ_[p]) ↔ PadicInt.toZMod a = (2 : ZMod p) := by
  have hodd : Odd p := hp3 ▸ (by decide : Odd 3)
  have hunit : IsUnit (-4 * a ^ 3 : ℤ_[p]) := (PadicInt.isUnit_neg_four hodd).mul (ha.pow 3)
  have h0 : PadicInt.toZMod a ≠ 0 := toZMod_ne_zero_of_isUnit ha
  rw [PadicInt.isSquare_iff_isSquare_toZMod hodd hunit, map_mul, map_pow, map_neg, map_ofNat]
  subst hp3
  rw [zmod_three_isSquare_neg_four_cube]
  exact ⟨fun h => h.resolve_left h0, Or.inr⟩

/-! ### The `a₄`-locus carrying the minimal storey -/

variable (p) in
/-- The set of `p³α` with `α ∈ ℤ_[p]` of residue `2` modulo `p`; at `p = 3` these are the
`a₄ = 27α` with `α ≡ -1 mod 3`. -/
def minimalFst : Set ℤ_[p] :=
  PadicInt.scaleByPPow 3 '' (PadicInt.toZMod ⁻¹' {(2 : ZMod p)})

/-- `minimalFst p` is measurable. -/
theorem measurableSet_minimalFst : MeasurableSet (minimalFst p) :=
  PadicInt.measurableSet_image_scaleByPPow
    (PadicInt.measurableSet_preimage_toZMod (2 : ZMod p))

/-- The mass of `minimalFst p` is `p⁻³ · p⁻¹`. -/
theorem volume_minimalFst : (volume : Measure ℤ_[p]) (minimalFst p) =
    ((p : ℝ≥0∞)⁻¹) ^ 3 * (p : ℝ≥0∞)⁻¹ := by
  rw [minimalFst, PadicInt.measure_image_scaleByPPow, PadicInt.volume_preimage_toZMod,
    PadicInt.zpow_neg_natCast_eq_inv_pow]

/-- `p³α` lies in `minimalFst p` exactly when the residue of `α` is `2`. -/
theorem pow_three_mul_mem_minimalFst_iff {a : ℤ_[p]} :
    ((p : ℤ_[p]) ^ 3 * a) ∈ minimalFst p ↔ PadicInt.toZMod a = (2 : ZMod p) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  refine ⟨fun h => ?_, fun h => ⟨a, h, rfl⟩⟩
  obtain ⟨b, hb, hbe⟩ := h
  obtain rfl : b = a := mul_left_cancel₀ (pow_ne_zero 3 hϖ) hbe
  exact hb

/-- At `p = 3`, every point `a₄` of `minimalFst p` has `v_p(a₄) = 3`. -/
theorem emultiplicity_eq_three_of_mem_minimalFst (hp3 : p = 3) {a₄ : ℤ_[p]}
    (ha₄ : a₄ ∈ minimalFst p) : emultiplicity (p : ℤ_[p]) a₄ = ((3 : ℕ) : ℕ∞) := by
  subst hp3
  obtain ⟨a, ha, rfl⟩ := ha₄
  refine PadicInt.emultiplicity_pow_mul_unit 3 (isUnit_of_toZMod_ne_zero ?_)
  rw [(by simpa using ha : PadicInt.toZMod a = (2 : ZMod 3))]
  exact two_ne_zero_zmod_three

/-! ### The minimal storey, weighed -/

/-- For `t ≥ 5`, the slice of `τ_3⁻¹((I_t, t)) ∖ σ_3(ℤ_3²)` over `a₄` has mass
`3⁻³ (1 - 3⁻¹) 3^{-(t+3)}` when `a₄ ∈ minimalFst 3`, and `0` otherwise. -/
theorem volume_slice_stratFibre_diff_range_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) (a₄ : ℤ_[p]) :
    (volume : Measure ℤ_[p]) (Prod.mk a₄ ⁻¹' (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])))
      = (minimalFst p).indicator
          (fun _ => ((p : ℝ≥0∞)⁻¹) ^ 3 * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 3))) a₄ := by
  have hodd : Odd p := hp3 ▸ (by decide : Odd 3)
  by_cases ha₄ : emultiplicity (p : ℤ_[p]) a₄ = ((3 : ℕ) : ℕ∞)
  · obtain ⟨a, hau, rfl⟩ := PadicInt.exists_isUnit_of_emultiplicity_eq_natCast ha₄
    have hunit : IsUnit (-4 * a ^ 3 : ℤ_[p]) := (PadicInt.isUnit_neg_four hodd).mul (hau.pow 3)
    have hdrop : Prod.mk ((p : ℤ_[p]) ^ 3 * a) ⁻¹'
        (stratFibre p (KodairaSymbol.I t, t) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = {a₆ : ℤ_[p] | ((p : ℤ_[p]) ^ 3 * a, a₆) ∈ stratFibre p (KodairaSymbol.I t, t)} := by
      ext a₆
      exact ⟨fun h => h.1, fun h => ⟨h, notMem_range_of_emultiplicity_fst_eq_three
        (PadicInt.emultiplicity_pow_mul_unit 3 hau)⟩⟩
    rw [hdrop, setOf_mem_stratFibre_three_eq_image hp3 ht hau,
      PadicInt.measure_image_scaleByPPow, PadicInt.zpow_neg_natCast_eq_inv_pow]
    by_cases hsq : IsSquare (-4 * a ^ 3 : ℤ_[p])
    · obtain ⟨s, hs⟩ := hsq
      have hsu : IsUnit s := by rw [hs] at hunit; exact (IsUnit.mul_iff.mp hunit).1
      rw [Set.indicator_of_mem (pow_three_mul_mem_minimalFst_iff.2
          ((isSquare_neg_four_mul_cube_iff_three hp3 hau).1 ⟨s, hs⟩)),
        PadicInt.volume_sqLevelSet_inter_of_unique_root hodd hunit hs
          (fun _ _ h => mem_splitResidueSet_congr h) (splitResidueSet_unique_three hp3 hsu)
          (by omega : 1 ≤ t + 3)]
    · rw [PadicInt.sqLevelSet_eq_empty_of_not_isSquare hodd hunit hsq (by omega : 1 ≤ t + 3),
        Set.empty_inter, measure_empty, mul_zero,
        Set.indicator_of_notMem (fun h => hsq
          ((isSquare_neg_four_mul_cube_iff_three hp3 hau).2
            (pow_three_mul_mem_minimalFst_iff.1 h)))]
  · have hempty : Prod.mk a₄ ⁻¹' (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = (∅ : Set ℤ_[p]) := setOf_mem_stratFibre_diff_eq_empty_three hp3 ht ha₄
    rw [hempty, measure_empty,
      Set.indicator_of_notMem (fun h => ha₄ (emultiplicity_eq_three_of_mem_minimalFst hp3 h))]

/-- The minimal storey of the `p = 3` split-multiplicative stratum: for every `t ≥ 5`,
`μ_3(τ_3⁻¹((I_t, t)) ∖ σ_3(ℤ_3²)) = (1 - 3⁻¹) · 3^{-(t+10)}`. -/
theorem volume_stratFibre_diff_range_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 10) := by
  have hmeas : MeasurableSet (stratFibre p (KodairaSymbol.I t, t) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :=
    (isOpen_stratFibre _).measurableSet.diff
      (PadicInt.measurableEmbedding_scaleProdByPPow 4 6).measurableSet_range
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas,
    lintegral_congr (volume_slice_stratFibre_diff_range_three hp3 ht),
    lintegral_indicator_const measurableSet_minimalFst, volume_minimalFst,
    show t + 10 = 3 + 1 + 3 + (t + 3) by omega]
  ring

/-- `1 - 3⁻¹ = 2 · 3⁻¹` in `ℝ≥0∞`. -/
private theorem one_sub_inv_eq_two_mul_inv_three (hp3 : p = 3) :
    (1 : ℝ≥0∞) - (p : ℝ≥0∞)⁻¹ = 2 * (p : ℝ≥0∞)⁻¹ := by
  subst hp3
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  rw [show (2 : ℝ≥0∞) * ((3 : ℕ) : ℝ≥0∞)⁻¹ + ((3 : ℕ) : ℝ≥0∞)⁻¹
      = 3 * ((3 : ℕ) : ℝ≥0∞)⁻¹ by ring]
  norm_num
  exact (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm

/-- The minimal storey of the `p = 3` split-multiplicative stratum: for every `t ≥ 5`,
`μ_3(τ_3⁻¹((I_t, t)) ∖ σ_3(ℤ_3²)) = 2 · 3^{-(t+11)}`. -/
theorem volume_stratFibre_diff_range_three_eq_two_mul (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 11) := by
  rw [volume_stratFibre_diff_range_three hp3 ht, one_sub_inv_eq_two_mul_inv_three hp3,
    show t + 11 = 1 + (t + 10) by omega]
  ring

/-! ### `δ_3(t)` and `α_3`, granted `StratScaleInvariant 3` -/

/-- If `r < 1`, `x ≠ ⊤` and `x = r x + c` in `ℝ≥0∞`, then `x = c (1 - r)⁻¹`. -/
private theorem eq_mul_inv_one_sub_storey {r c x : ℝ≥0∞} (hr : r < 1) (hx : x ≠ ⊤)
    (hxe : x = r * x + c) : x = c * (1 - r)⁻¹ := by
  have hrx : r * x ≠ ⊤ := ENNReal.mul_ne_top (ne_top_of_lt hr) hx
  have hsub : x - r * x = c :=
    ENNReal.sub_eq_of_eq_add hrx (by rw [add_comm]; exact hxe)
  have hmul : (1 - r) * x = c := by
    rw [ENNReal.sub_mul (fun _ _ => hx), one_mul, hsub]
  have h1 : (1 : ℝ≥0∞) - r ≠ 0 := (tsub_pos_of_lt hr).ne'
  have h2 : (1 : ℝ≥0∞) - r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  calc x = (1 - r)⁻¹ * ((1 - r) * x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h1 h2, one_mul]
    _ = c * (1 - r)⁻¹ := by rw [hmul, mul_comm]

/-- `(p⁻¹)¹⁰ < 1` in `ℝ≥0∞`. -/
private theorem inv_natCast_pow_ten_lt_one : ((p : ℝ≥0∞)⁻¹) ^ 10 < 1 := by
  have h1 : (p : ℝ≥0∞)⁻¹ < 1 :=
    ENNReal.inv_lt_one.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  exact pow_lt_one₀ zero_le h1 (by norm_num)

/-- At `p = 3`, the difference `1 - (p⁻¹)¹⁰` in `ℝ≥0∞` is `ENNReal.ofReal (1 - (p⁻¹)¹⁰)`. -/
private theorem ofReal_one_sub_inv_pow_ten (hp3 : p = 3) :
    (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10 = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by subst hp3; norm_num
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinvE,
    ← ENNReal.ofReal_pow (by positivity)]

/-- Granted `StratScaleInvariant 3`, for every `t ≥ 5`, `δ_3(t) = (1/(3 · 29524)) · 3^{-t}`. -/
theorem δ_eq_ofReal_three (hp3 : p = 3) (h : StratScaleInvariant p) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = ENNReal.ofReal (1 / (3 * 29524)) * ((p : ℝ≥0∞)⁻¹) ^ t := by
  have hne : δ p t ≠ ⊤ := by rw [δ_eq_deltaP_I ht]; exact deltaP_ne_top p _
  have hfix : δ p t = ((p : ℝ≥0∞)⁻¹) ^ 10 * δ p t + 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 11) := by
    have h1 := δ_eq_inv_pow_mul_add h ht
    rwa [volume_stratFibre_diff_range_three_eq_two_mul hp3 ht,
      show (-(10 : ℤ)) = -((10 : ℕ) : ℤ) by norm_num,
      PadicInt.zpow_neg_natCast_eq_inv_pow] at h1
  rw [eq_mul_inv_one_sub_storey inv_natCast_pow_ten_lt_one hne hfix,
    ofReal_one_sub_inv_pow_ten hp3]
  have hp0 : (0 : ℝ) < (p : ℝ) := by subst hp3; norm_num
  have hlt : ((p : ℝ)⁻¹) ^ 10 < 1 := by
    subst hp3
    norm_num
  have hpos : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 := by linarith
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_inv_of_pos hpos, hinvE, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine congrArg ENNReal.ofReal ?_
  subst hp3
  rw [show ((3 : ℕ) : ℝ)⁻¹ = (3 : ℝ)⁻¹ by norm_num, pow_add]
  field_simp
  ring

/-- Granted `StratScaleInvariant 3`, the tail constant at `p = 3` is `α_3 = 1/(3 · 29524)`. -/
theorem α_eq_ofReal_three (hp3 : p = 3) (h : StratScaleInvariant p) :
    α p = ENNReal.ofReal (1 / (3 * 29524)) := by
  obtain ⟨h0, htop⟩ := pow_five_ne_zero_and_ne_top (p := p)
  rw [α, δ_eq_ofReal_three hp3 h (le_refl 5), ← ENNReal.inv_pow, ← mul_assoc,
    mul_comm ((p : ℝ≥0∞) ^ 5) (ENNReal.ofReal (1 / (3 * 29524))), mul_assoc,
    ENNReal.mul_inv_cancel h0 htop, mul_one]

end WeierstrassCurve
