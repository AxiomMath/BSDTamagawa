/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityFourExact
public import BSDTamagawa.NumberTheory.RunInvarianceAtThree
public import BSDTamagawa.NumberTheory.RunInvarianceAtTwo

/-!
# Storey folding at the wild primes: `δ_q(t)` from the minimal part of its own fibre

At every prime `p` for which the reduction datum is invariant under the scaling
`σ_p : (a₄, a₆) ↦ (p⁴a₄, p⁶a₆)` (`StratScaleInvariant p`), the density of a fibre of the Tamagawa
number is the mass of its minimal part times the storey factor,

  `δ_p(t) = μ_p({c = t} ∖ σ_p(ℤ_p²)) · (1 - p⁻¹⁰)⁻¹`.

This holds at the wild primes `q = 2` and `q = 3`, where the storey factors are `1024/1023` and
`59049/59048`:

  `δ_2(t) = μ_2({c = t} ∖ σ_2(ℤ_2²)) · 1024/1023`,
  `δ_3(t) = μ_3({c = t} ∖ σ_3(ℤ_3²)) · 59049/59048`.

## Main results

* `WeierstrassCurve.δ_eq_volume_diff_mul_inv_one_sub_of_stratScaleInvariant`: `δ_p(t)` is the
  mass of the minimal part of `{c = t}` times `(1 - p⁻¹⁰)⁻¹`, for every `σ_p`-invariant prime `p`.
* `WeierstrassCurve.δ_eq_volume_diff_mul_at_two`, `WeierstrassCurve.δ_eq_volume_diff_mul_at_three`:
  the fibre-level identity at `q = 2` and `q = 3`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

/-! ### The two `ℝ≥0∞` inputs -/

/-- In `ℝ≥0∞`, if `r < 1` and `x ≠ ⊤` satisfies `x = rx + c`, then `x = c(1 - r)⁻¹`. -/
theorem enn_eq_mul_inv_one_sub_of_lt_one {r c x : ℝ≥0∞} (hr : r < 1) (hx : x ≠ ⊤)
    (hxe : x = r * x + c) : x = c * (1 - r)⁻¹ := by
  have hrx : r * x ≠ ⊤ := ENNReal.mul_ne_top (ne_top_of_lt hr) hx
  have hsub : x - r * x = c := ENNReal.sub_eq_of_eq_add hrx (by rwa [add_comm])
  have hmul : (1 - r) * x = c := by rw [ENNReal.sub_mul (fun _ _ => hx), one_mul, hsub]
  have h1 : (1 : ℝ≥0∞) - r ≠ 0 := (tsub_pos_of_lt hr).ne'
  have h2 : (1 : ℝ≥0∞) - r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  calc x = (1 - r)⁻¹ * ((1 - r) * x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h1 h2, one_mul]
    _ = c * (1 - r)⁻¹ := by rw [hmul, mul_comm]

/-- `(q⁻¹)¹⁰ < 1` at every `q ≥ 2`. -/
theorem enn_inv_pow_ten_lt_one {q : ℕ} (hq : 2 ≤ q) : ((q : ℝ≥0∞)⁻¹) ^ 10 < 1 :=
  pow_lt_one₀ zero_le (ENNReal.inv_lt_one.2 (by exact_mod_cast (by omega : 1 < q))) (by norm_num)

variable {p : ℕ} [Fact p.Prime]

/-! ### The identity at a `σ_p`-invariant prime -/

/-- At every prime `p` for which the reduction datum is `σ_p`-invariant, and every `t`,
`δ_p(t) = μ_p({c = t} ∖ σ_p(ℤ_p²)) · (1 - p⁻¹⁰)⁻¹`. -/
theorem δ_eq_volume_diff_mul_inv_one_sub_of_stratScaleInvariant (h : StratScaleInvariant p)
    (t : ℕ) :
    δ p t = (volume : Measure (ℤ_[p] × ℤ_[p])) ((⋃ κ : KodairaSymbol, stratFibre p (κ, t)) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have hz : (p : ℝ≥0∞) ^ (-(10 : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 10 := by
    rw [show (-(10 : ℤ)) = -((10 : ℕ) : ℤ) from by norm_num]
    exact (PadicInt.measure_span_pPow (p := p) 10).symm.trans (PadicInt.measure_span_pPow' 10)
  have hinter : (volume : Measure (ℤ_[p] × ℤ_[p])) ((⋃ κ : KodairaSymbol, stratFibre p (κ, t)) ∩
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = ((p : ℝ≥0∞)⁻¹) ^ 10 * δ p t := by
    rw [iUnion_stratFibre_inter_range_eq_image h t,
      PadicInt.measure_image_scaleProdByPPow_four_six, hz,
      volume_iUnion_stratFibre_kodaira (p := p) t]
  have hfix : δ p t = ((p : ℝ≥0∞)⁻¹) ^ 10 * δ p t
      + (volume : Measure (ℤ_[p] × ℤ_[p])) ((⋃ κ : KodairaSymbol, stratFibre p (κ, t)) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) := by
    rw [← hinter, ← volume_iUnion_stratFibre_kodaira (p := p) t]
    exact (measure_inter_add_sdiff _
      (PadicInt.measurableEmbedding_scaleProdByPPow 4 6).measurableSet_range).symm
  exact enn_eq_mul_inv_one_sub_of_lt_one (enn_inv_pow_ten_lt_one (Fact.out : p.Prime).two_le)
    (by rw [← volume_iUnion_stratFibre_kodaira (p := p) t]; exact measure_ne_top _ _) hfix

/-! ### The two storey factors, as numerals -/

/-- The `p = 2` storey factor: `(1 - 2⁻¹⁰)⁻¹ = 1024/1023`. -/
theorem enn_inv_one_sub_inv_pow_ten_two : (1 - ((2 : ℝ≥0∞)⁻¹) ^ 10)⁻¹ = 1024 / 1023 := by
  rw [show ((2 : ℝ≥0∞)⁻¹) ^ 10 = 1 / 1024 from by rw [← ENNReal.inv_pow, one_div]; norm_num,
    show (1 : ℝ≥0∞) - 1 / 1024 = 1023 / 1024 from
      ENNReal.sub_eq_of_eq_add (by simp)
        (by rw [ENNReal.div_add_div_same, show (1023 : ℝ≥0∞) + 1 = 1024 from by norm_num,
          ENNReal.div_self (by norm_num) (by norm_num)]),
    ENNReal.inv_div (by norm_num) (by norm_num)]

/-- The `p = 3` storey factor: `(1 - 3⁻¹⁰)⁻¹ = 59049/59048`. -/
theorem enn_inv_one_sub_inv_pow_ten_three : (1 - ((3 : ℝ≥0∞)⁻¹) ^ 10)⁻¹ = 59049 / 59048 := by
  rw [show ((3 : ℝ≥0∞)⁻¹) ^ 10 = 1 / 59049 from by rw [← ENNReal.inv_pow, one_div]; norm_num,
    show (1 : ℝ≥0∞) - 1 / 59049 = 59048 / 59049 from
      ENNReal.sub_eq_of_eq_add (by simp)
        (by rw [ENNReal.div_add_div_same, show (59048 : ℝ≥0∞) + 1 = 59049 from by norm_num,
          ENNReal.div_self (by norm_num) (by norm_num)]),
    ENNReal.inv_div (by norm_num) (by norm_num)]

/-! ### The two wild instantiations -/

/-- `δ_2(t) = μ_2({c = t} ∖ σ_2(ℤ_2²)) · 1024/1023`, for every `t`. -/
theorem δ_eq_volume_diff_mul_at_two (t : ℕ) :
    δ 2 t = (volume : Measure (ℤ_[2] × ℤ_[2])) ((⋃ κ : KodairaSymbol, stratFibre 2 (κ, t)) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]))
      * (1024 / 1023) := by
  rw [δ_eq_volume_diff_mul_inv_one_sub_of_stratScaleInvariant stratScaleInvariant_two t,
    show ((2 : ℕ) : ℝ≥0∞) = 2 from by norm_num,
    enn_inv_one_sub_inv_pow_ten_two]

/-- `δ_3(t) = μ_3({c = t} ∖ σ_3(ℤ_3²)) · 59049/59048`, for every `t`. -/
theorem δ_eq_volume_diff_mul_at_three (t : ℕ) :
    δ 3 t = (volume : Measure (ℤ_[3] × ℤ_[3])) ((⋃ κ : KodairaSymbol, stratFibre 3 (κ, t)) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]))
      * (59049 / 59048) := by
  rw [δ_eq_volume_diff_mul_inv_one_sub_of_stratScaleInvariant
      (stratScaleInvariant_of_ne_two (by norm_num)) t,
    show ((3 : ℕ) : ℝ≥0∞) = 3 from by norm_num, enn_inv_one_sub_inv_pow_ten_three]

end WeierstrassCurve
