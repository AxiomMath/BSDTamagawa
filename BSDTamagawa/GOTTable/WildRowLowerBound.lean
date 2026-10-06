/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildStoreyFolding
public import BSDTamagawa.NumberTheory.HeadDensityWildOneFour

/-!
# Lower bounds on a head row at `p = 2` from minimal loci

By `δ_eq_volume_diff_mul_at_two`,

  `δ_2(t) = μ_2(M_2(t)) · 1024/1023`,  where  `M_2(t) := (⋃ κ, stratFibre 2 (κ, t)) ∖ σ_2(ℤ_2²)`

is the minimal part of the `t`-fibre. Hence any subset of `M_2(t)` contributes its mass, times the
storey factor `1024/1023`, to `δ_2(t)`. A locus `L` lies in `M_2(t)` when `L ⊆ stratFibre 2 (κ, t)`
for some Kodaira symbol `κ` and no point of `L` is a dilate; by
`PadicInt.mem_range_scaleProdByPPow_iff` a point is a dilate exactly when `2⁴ ∣ a₄` and `2⁶ ∣ a₆`,
so it suffices that one coordinate fail the divisibility.

## Main results

* `WeierstrassCurve.enn_div_mul_div`: `(a/b) · (c/d) = (a·c)/(b·d)` in `ℝ≥0∞`.
* `WeierstrassCurve.div_eq_of_eq_pow_mul_two`: exact division of a multiple of `pᵏ` by `pᵏ`.
* `WeierstrassCurve.notMem_range_scaleProdByPPow_of_not_dvd_fst` and
  `WeierstrassCurve.notMem_range_scaleProdByPPow_of_not_dvd_snd`: a pair with one coordinate not
  divisible enough is not a dilate, at every prime.
* `WeierstrassCurve.le_δ_at_two_of_subset`: the row bound for one locus.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

/-! ### Numerals in `ℝ≥0∞` -/

/-- `(a/b) · (c/d) = (a·c)/(b·d)` in `ℝ≥0∞`, for nonzero `b` and `d`. -/
theorem enn_div_mul_div {a b c d : ℝ≥0∞} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b * (c / d) = a * c / (b * d) :=
  (ENNReal.mul_div_mul_comm (Or.inl hb) (Or.inr hd)).symm

/-- `8 · 2⁻¹⁰ = 8/1024 = 1/128`. -/
theorem eight_mul_inv_pow_ten_eq : (8 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 10 = 1 / 128 := by
  rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 10 = 1024 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Exact division in `ℤ_p` -/

variable {p : ℕ} [Fact p.Prime]

/-- **Exact division by a power of `p`.** If `x = pᵏ · a` in `ℤ_[p]`, then
`CommRing.div x (pᵏ) = a`. -/
theorem div_eq_of_eq_pow_mul_two {k : ℕ} {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) ^ k * a) :
    CommRing.div x ((p : ℤ_[p]) ^ k) = a := by
  subst h
  exact mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-! ### Minimality from one shallow coordinate -/

/-- A pair whose first coordinate is not divisible by `pᵐ` is not a `(pᵐ, pⁿ)`-dilate. -/
theorem notMem_range_scaleProdByPPow_of_not_dvd_fst {m n : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (h : ¬ (p : ℤ_[p]) ^ m ∣ x.1) :
    x ∉ Set.range (PadicInt.scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) :=
  fun hx => h (PadicInt.mem_range_scaleProdByPPow_iff.1 hx).1

/-- A pair whose second coordinate is not divisible by `pⁿ` is not a `(pᵐ, pⁿ)`-dilate. -/
theorem notMem_range_scaleProdByPPow_of_not_dvd_snd {m n : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (h : ¬ (p : ℤ_[p]) ^ n ∣ x.2) :
    x ∉ Set.range (PadicInt.scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) :=
  fun hx => h (PadicInt.mem_range_scaleProdByPPow_iff.1 hx).2

/-! ### The row bound for one locus -/

/-- **One locus.** A subset of the minimal part of the `t`-fibre contributes its mass, times the
storey factor, to `δ_2(t)`. The set `L` need not be measurable. -/
theorem le_δ_at_two_of_subset {t : ℕ} {L : Set (ℤ_[2] × ℤ_[2])}
    (hL : L ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, t)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2])) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) L * (1024 / 1023) ≤ δ 2 t := by
  rw [δ_eq_volume_diff_mul_at_two t]
  gcongr

end WeierstrassCurve

end
