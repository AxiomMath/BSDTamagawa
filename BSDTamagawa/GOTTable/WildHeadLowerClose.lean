/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildHeadRowReduction
public import BSDTamagawa.GOTTable.WildHeadSum

/-!
# The whole Griffin–Ono–Tsai column from four lower bounds

At every prime the total of the four head values equals the table's total:

  `δ_p(1) + δ_p(2) + δ_p(3) + δ_p(4) = ofReal (gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4)`.

Four quantities whose total is pinned, each bounded below by the corresponding table entry, must
each equal it. So `HasGOTDensities p` follows from the four one-sided bounds

  `ofReal (gotδ p t) ≤ δ p t`,   `t = 1, 2, 3, 4`,

and no upper bound is needed. A lower bound on `δ_p(t)` amounts to exhibiting a set of the stated
mass inside the fibre `{c = t}`.

## Main results

* `ENNReal.eq_of_le_of_add_add_add_eq`: four finite lower bounds in `ℝ≥0∞` and an exact total give
  four equalities.
* `WeierstrassCurve.δ_eq_ofReal_gotδ_of_headLowerBounds`: four lower bounds on the head values give
  four equalities, at every prime.
* `WeierstrassCurve.hasGOTDensities_of_headLowerBounds`: the same four hypotheses give
  `HasGOTDensities p`.
* `WeierstrassCurve.ofReal_gotδ_four_at_two`, `WeierstrassCurve.ofReal_gotδ_four_at_three`: the
  `t = 4` entries at `p = 2, 3` as numerals.
* `WeierstrassCurve.hasGOTDensities_of_headLowerBounds_at_two`,
  `WeierstrassCurve.hasGOTDensities_of_headLowerBounds_at_three`: the statements at `p = 2` and
  `p = 3` with the four entries as numerals.
-/

open scoped ENNReal

@[expose] public section

namespace ENNReal

/-- **Four lower bounds against a pinned total are four equalities.** If `aᵢ' ≤ aᵢ` for
`i = 1,…,4`, each `aᵢ'` is finite, and the two totals agree, then `aᵢ = aᵢ'` throughout. -/
theorem eq_of_le_of_add_add_add_eq {a b c d a' b' c' d' : ℝ≥0∞} (ha' : a' ≠ ⊤) (hb' : b' ≠ ⊤)
    (hc' : c' ≠ ⊤) (hd' : d' ≠ ⊤) (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) (hd : d' ≤ d)
    (hsum : a + b + c + d = a' + b' + c' + d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have key : ∀ x y z w x' y' z' w' : ℝ≥0∞, y' ≠ ⊤ → z' ≠ ⊤ → w' ≠ ⊤ → x' ≤ x → y' ≤ y → z' ≤ z →
      w' ≤ w → x + y + z + w = x' + y' + z' + w' → x = x' := by
    intro x y z w x' y' z' w' hy' hz' hw' hx hy hz hw h
    have hfin : y' + z' + w' ≠ ⊤ := by simp [hy', hz', hw']
    refine le_antisymm ((ENNReal.add_le_add_iff_right hfin).1 ?_) hx
    calc x + (y' + z' + w') ≤ x + (y + z + w) := by gcongr
      _ = x + y + z + w := by ring
      _ = x' + y' + z' + w' := h
      _ = x' + (y' + z' + w') := by ring
  refine ⟨key a b c d a' b' c' d' hb' hc' hd' ha hb hc hd hsum,
    key b a c d b' a' c' d' ha' hc' hd' hb ha hc hd ?_,
    key c a b d c' a' b' d' ha' hb' hd' hc ha hb hd ?_,
    key d a b c d' a' b' c' ha' hb' hc' hd ha hb hc ?_⟩ <;>
    convert hsum using 1 <;> ring

end ENNReal

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The four head values, from four lower bounds -/

/-- **Each head value equals its table entry as soon as all four are bounded below by theirs**, at
every prime. -/
theorem δ_eq_ofReal_gotδ_of_headLowerBounds
    (h1 : ENNReal.ofReal (gotδ p 1) ≤ δ p 1) (h2 : ENNReal.ofReal (gotδ p 2) ≤ δ p 2)
    (h3 : ENNReal.ofReal (gotδ p 3) ≤ δ p 3) (h4 : ENNReal.ofReal (gotδ p 4) ≤ δ p 4) :
    δ p 1 = ENNReal.ofReal (gotδ p 1) ∧ δ p 2 = ENNReal.ofReal (gotδ p 2) ∧
      δ p 3 = ENNReal.ofReal (gotδ p 3) ∧ δ p 4 = ENNReal.ofReal (gotδ p 4) := by
  have hnn : ∀ t : ℕ, (0 : ℝ) ≤ gotδ p t := fun _ => gotδ_nonneg Fact.out
  have hsum : δ p 1 + δ p 2 + δ p 3 + δ p 4
      = ENNReal.ofReal (gotδ p 1) + ENNReal.ofReal (gotδ p 2) + ENNReal.ofReal (gotδ p 3)
        + ENNReal.ofReal (gotδ p 4) := by
    rw [δ_headSum_eq_ofReal_gotδ_headSum, ← ENNReal.ofReal_add (hnn 1) (hnn 2),
      ← ENNReal.ofReal_add (add_nonneg (hnn 1) (hnn 2)) (hnn 3),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hnn 1) (hnn 2)) (hnn 3)) (hnn 4)]
  exact ENNReal.eq_of_le_of_add_add_add_eq ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top h1 h2 h3 h4 hsum

/-- **`HasGOTDensities p` from four lower bounds on the head values**, at every prime. -/
theorem hasGOTDensities_of_headLowerBounds
    (h1 : ENNReal.ofReal (gotδ p 1) ≤ δ p 1) (h2 : ENNReal.ofReal (gotδ p 2) ≤ δ p 2)
    (h3 : ENNReal.ofReal (gotδ p 3) ≤ δ p 3) (h4 : ENNReal.ofReal (gotδ p 4) ≤ δ p 4) :
    HasGOTDensities p :=
  have h := δ_eq_ofReal_gotδ_of_headLowerBounds h1 h2 h3 h4
  hasGOTDensities_of_one_two_three h.1 h.2.1 h.2.2.1

/-! ### The `p = 2` face -/

/-- `ENNReal.ofReal (gotδ 2 4) = 171/10912`. -/
theorem ofReal_gotδ_four_at_two : ENNReal.ofReal (gotδ 2 4) = 171 / 10912 := by
  rw [show gotδ 2 4 = (171 : ℝ) / 10912 by norm_num [gotδ, gotHeadTwo],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **The whole `p = 2` column from four lower bounds.** If the four head values are at least
`241/396`, `7495/24552`, `1153/16368` and `171/10912`, then they are equal to them, since their
total is `32735/32736`, and `HasGOTDensities 2` holds. -/
theorem hasGOTDensities_of_headLowerBounds_at_two (h1 : (241 : ℝ≥0∞) / 396 ≤ δ 2 1)
    (h2 : (7495 : ℝ≥0∞) / 24552 ≤ δ 2 2) (h3 : (1153 : ℝ≥0∞) / 16368 ≤ δ 2 3)
    (h4 : (171 : ℝ≥0∞) / 10912 ≤ δ 2 4) :
    HasGOTDensities 2 :=
  hasGOTDensities_of_headLowerBounds (ofReal_gotδ_one_at_two ▸ h1) (ofReal_gotδ_two_at_two ▸ h2)
    (ofReal_gotδ_three_at_two ▸ h3) (ofReal_gotδ_four_at_two ▸ h4)

/-! ### The `p = 3` face -/

/-- `ENNReal.ofReal (gotδ 3 4) = 1193/652212`. -/
theorem ofReal_gotδ_four_at_three : ENNReal.ofReal (gotδ 3 4) = 1193 / 652212 := by
  rw [show gotδ 3 4 = (1193 : ℝ) / 652212 by norm_num [gotδ, gotHeadThree],
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **The whole `p = 3` column from four lower bounds.** If the four head values are at least
`1924841/2125728`, `509345/6377184`, `30619/2391444` and `1193/652212`, then they are equal to
them, since their total is `14348663/14348664`, and `HasGOTDensities 3` holds. -/
theorem hasGOTDensities_of_headLowerBounds_at_three (h1 : (1924841 : ℝ≥0∞) / 2125728 ≤ δ 3 1)
    (h2 : (509345 : ℝ≥0∞) / 6377184 ≤ δ 3 2) (h3 : (30619 : ℝ≥0∞) / 2391444 ≤ δ 3 3)
    (h4 : (1193 : ℝ≥0∞) / 652212 ≤ δ 3 4) :
    HasGOTDensities 3 :=
  hasGOTDensities_of_headLowerBounds (ofReal_gotδ_one_at_three ▸ h1)
    (ofReal_gotδ_two_at_three ▸ h2) (ofReal_gotδ_three_at_three ▸ h3)
    (ofReal_gotδ_four_at_three ▸ h4)

end WeierstrassCurve

end
