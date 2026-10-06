/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityTwoExact

/-!
# The wild head values as `ℝ≥0∞` numerals

The head values `gotδ p t` of the table at the two wild primes `p = 2, 3` and rows `t = 1, 2, 3`,
written as `ENNReal.ofReal` of the table's rationals, evaluated to explicit `ℝ≥0∞` numerals. This
is the form in which they are compared with the Haar densities `δ_p(t)`, which live in `ℝ≥0∞`.

## Main results

* `ofReal_gotδ_one_at_two`, …, `ofReal_gotδ_three_at_three`: the head values at `p = 2, 3` as
  `ℝ≥0∞` numerals.
-/

@[expose] public section

open MeasureTheory

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The wild head values as `ℝ≥0∞` numerals -/

/-- `ENNReal.ofReal (gotδ 2 1) = 241/396`. -/
theorem ofReal_gotδ_one_at_two : ENNReal.ofReal (gotδ 2 1) = 241 / 396 := by
  rw [show gotδ 2 1 = (241 : ℝ) / 396 from by norm_num [gotδ, gotHeadTwo],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- `ENNReal.ofReal (gotδ 2 2) = 7495/24552`. -/
theorem ofReal_gotδ_two_at_two : ENNReal.ofReal (gotδ 2 2) = 7495 / 24552 := by
  rw [show gotδ 2 2 = (7495 : ℝ) / 24552 from by norm_num [gotδ, gotHeadTwo],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- `ENNReal.ofReal (gotδ 2 3) = 1153/16368`. -/
theorem ofReal_gotδ_three_at_two : ENNReal.ofReal (gotδ 2 3) = 1153 / 16368 := by
  rw [show gotδ 2 3 = (1153 : ℝ) / 16368 from by norm_num [gotδ, gotHeadTwo],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- `ENNReal.ofReal (gotδ 3 1) = 1924841/2125728`. -/
theorem ofReal_gotδ_one_at_three : ENNReal.ofReal (gotδ 3 1) = 1924841 / 2125728 := by
  rw [show gotδ 3 1 = (1924841 : ℝ) / 2125728 from by norm_num [gotδ, gotHeadThree],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- `ENNReal.ofReal (gotδ 3 2) = 509345/6377184`. -/
theorem ofReal_gotδ_two_at_three : ENNReal.ofReal (gotδ 3 2) = 509345 / 6377184 := by
  rw [show gotδ 3 2 = (509345 : ℝ) / 6377184 from by norm_num [gotδ, gotHeadThree],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- `ENNReal.ofReal (gotδ 3 3) = 30619/2391444`. -/
theorem ofReal_gotδ_three_at_three : ENNReal.ofReal (gotδ 3 3) = 30619 / 2391444 := by
  rw [show gotδ 3 3 = (30619 : ℝ) / 2391444 from by norm_num [gotδ, gotHeadThree],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

end WeierstrassCurve
