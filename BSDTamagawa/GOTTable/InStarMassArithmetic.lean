/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityFourExact
public import BSDTamagawa.NumberTheory.HeadDensityTwoExact

/-!
# The mass of the subprocedure's entry locus is twice the non-split `Iₙ*` value

`doubleRootResidues p` consists of the residue pairs `(A, B)` on the cuspidal cubic
`4A³ + 27B² = 0` with `A ≠ 0`, where Step 7's `Iₙ*` subprocedure is entered. It has `p - 1`
elements, and a deep residue locus over `|S|` residue pairs has mass `|S| p⁻⁷`. With the factor
`T = (1 - p⁻¹⁰)⁻¹` this gives

  `μ_p(deepResidueLocus p (doubleRootResidues p)) · T = (p - 1) p⁻⁷ T = 2 · gotInStarTwo p`,

since `gotInStarTwo p = ((p - 1) / (2 p⁷)) T`. The identity is stated additively, as
`ofReal (gotInStarTwo p) + ofReal (gotInStarTwo p)`.

## Main results

* `volume_deepResidueLocus_doubleRootResidues`: the mass of the locus is `(p - 1) p⁻⁷`.
* `volume_deepResidueLocus_doubleRootResidues_mul_storey`: that mass times `T` is
  `gotInStarTwo p + gotInStarTwo p`.
-/

open scoped ENNReal

open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The mass, folded with the storey factor -/

/-- **`μ_p(deepResidueLocus p (doubleRootResidues p)) = (p - 1) p⁻⁷`** at every prime `p ≥ 5`. -/
theorem volume_deepResidueLocus_doubleRootResidues (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (deepResidueLocus p (doubleRootResidues p))
      = ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 7 := by
  rw [volume_deepResidueLocus, card_doubleRootResidues hp]

/-- **`μ_p(deepResidueLocus p (doubleRootResidues p)) · (1 - p⁻¹⁰)⁻¹
= gotInStarTwo p + gotInStarTwo p`** at every prime `p ≥ 5`.

The entry locus of Step 7's `Iₙ*` subprocedure carries exactly twice the Griffin–Ono–Tsai value
`gotInStarTwo p = ((p - 1)/(2p⁷))(1 - p⁻¹⁰)⁻¹` of the non-split `Iₙ*` family. The statement is
additive, so no `ℝ≥0∞` multiple by a numeral is formed. -/
theorem volume_deepResidueLocus_doubleRootResidues_mul_storey (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (deepResidueLocus p (doubleRootResidues p))
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      = ENNReal.ofReal (gotInStarTwo p) + ENNReal.ofReal (gotInStarTwo p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpos : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 :=
    sub_pos.2 (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by norm_cast; omega))
      (by norm_num))
  have hinvE : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  have hten : (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10
      = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinvE,
      ← ENNReal.ofReal_pow (by positivity)]
  have hgnn : (0 : ℝ) ≤ gotInStarTwo p := by
    rw [gotInStarTwo]
    exact mul_nonneg (div_nonneg (sub_nonneg.2 (by norm_cast; omega)) (by positivity))
      (inv_pos.2 hpos).le
  rw [volume_deepResidueLocus_doubleRootResidues hp, ← ENNReal.ofReal_natCast, hten,
    ← ENNReal.ofReal_inv_of_pos hpos, hinvE, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add hgnn hgnn]
  congr 1
  simp only [gotInStarTwo, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
  field_simp
  ring

end WeierstrassCurve
