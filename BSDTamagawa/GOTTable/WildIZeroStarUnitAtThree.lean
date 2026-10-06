/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeAtThree
public import BSDTamagawa.GOTTable.WildIZeroStarOneTwoAtThree

/-!
# The `v₃(a₄) = 1` regime of `(I₀*, 1)` and `(I₀*, 2)` at `p = 3`

Each of the strata `(I₀*, 1)` and `(I₀*, 2)` at `p = 3` splits into two regimes. Over `9 ∣ a₄`
the Step-2 translation parameter satisfies `3 ∣ r`, so the Step-6 cubic has `b = 0`. Over
`v₃(a₄) = 1`, the regime treated here, the Step-2 shift is a unit, so `3 ∤ r` and the cubic has
`b ≠ 0`. The two pieces of this regime have mass `2/729` each.

Write `a₄ = 3α` with `3 ∤ α`. On this regime `3 ∤ a₆`, and

  `Δ = -16(4a₄³ + 27a₆²) = -16 · 27 · (4α³ + a₆²)`.

Setting `4α³ + a₆² = 27M`, the residue of `M` modulo `3` determines the reduction type:

* `3 ∣ M`, i.e. `v₃(4α³ + a₆²) ≥ 4`, is exactly `FamilyAThree.locus`, the `Iₘ*` family with
  `m ≥ 1`;
* `M ≡ -1 (mod 3)` gives `(I₀*, 1)`, and `M ≡ 1 (mod 3)` gives `(I₀*, 2)`.

Each `I₀*` locus is a single residue cylinder: fifty-four of the `6561` classes of `(α, a₆)`
modulo `81`, of mass `3⁻¹ · 54 · 3⁻⁸ = 2/729` after the dilation `a₄ = 3α`.

## Main definitions

* `WeierstrassCurve.IZeroStarUnitThree.Res`: the residue condition on `(α, a₆)` modulo `81`.
* `WeierstrassCurve.IZeroStarUnitThree.residues`: the residue classes satisfying it.
* `WeierstrassCurve.IZeroStarUnitThree.locus`: the corresponding cylinder in `ℤ_3 × ℤ_3`.

## Main results

* `WeierstrassCurve.not_hasDoubleRoot_of_sq_ne`, `WeierstrassCurve.card_roots_eq_zero_of_unit`
  and `WeierstrassCurve.card_roots_eq_one_of_unit`: separability and root counts of monic cubics
  over `𝔽₃` with `b ≠ 0`.
* `WeierstrassCurve.IZeroStarUnitThree.cubic_combo_eq`: the double-root quantity `X` of the
  Step-6 cubic satisfies `X ≡ -M (mod 3)`.
* `WeierstrassCurve.IZeroStarUnitThree.step5_run_eq_ok`: Steps 1 to 5 of Tate's algorithm pass.
* `WeierstrassCurve.IZeroStarUnitThree.ofShortNF_Δ_ne_zero_of_unit`: the curve is nonsingular
  when `3 ∤ M`.
* `WeierstrassCurve.IZeroStarUnitThree.run_eq_I0star_one` and
  `WeierstrassCurve.IZeroStarUnitThree.run_eq_I0star_two`: Tate's algorithm returns `(I₀*, 1)`
  and `(I₀*, 2)`.
* `WeierstrassCurve.IZeroStarUnitThree.volume_locus_of_card`: each cylinder has mass `2/729`.

## Implementation notes

The Step-6 cubic on the Step-2 translate is `⟨1, r̄, C̄, D̄⟩` with `C = (α + r²)/3` and
`D = (a₆ + 3rα + r³)/27`. In characteristic `3` a monic cubic has a double root exactly when
`X := b²c² - c³ - b³d` vanishes. When `b ≠ 0`, so that `b² = 1`,

  `b(x³ + bx² + cx + d) = (x - b(1 + c))² - ((1 + c)² - bd)`,   and   `(1 + c)² - bd = X + 1`,

so the cubic has no root when `X = 1` and exactly the root `b(1 + c)` when `X = -1`.

The threshold cylinder `27 ∣ 4α³ + a₆²` contains singular points, but on the two loci `M` is a
unit, so `Δ = -16 · 27 · 27M` is nonzero.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadSumThree
open CommRing Ideal TateAlgorithm

/-! ### The `b ≠ 0` root counts over `𝔽₃`

With `b ≠ 0` one has `b² = 1`, and multiplying the cubic by `b` turns it into a perfect square
minus `X + 1`, where `X = b²c² - c³ - b³d`. In characteristic `3` the separable cubics with
`b ≠ 0` are those with `X = ±1`. -/

variable {p : ℕ} [Fact p.Prime]

/-- A monic cubic over the residue field of `ℤ_3` with `b²c² - c³ - b³d ≠ 0` has no double
root. -/
theorem not_hasDoubleRoot_of_sq_ne (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hX : P.b ^ 2 * P.c ^ 2 - P.c ^ 3 - P.b ^ 3 * P.d ≠ 0) :
    ¬ P.HasDoubleRoot := by
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha]
  intro h
  exact hX (by
    linear_combination h + (P.c ^ 3 + P.b ^ 3 * P.d + 9 * P.d ^ 2 - 6 * P.b * P.c * P.d) * h3)

open scoped Classical in
/-- A monic cubic over the residue field of `ℤ_3` with `b ≠ 0` and `b²c² - c³ - b³d = 1` has no
root. -/
theorem card_roots_eq_zero_of_unit (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b ≠ 0)
    (hX : P.b ^ 2 * P.c ^ 2 - P.c ^ 3 - P.b ^ 3 * P.d = 1) :
    P.toPoly.roots.toFinset.card = 0 := by
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  have hb2 : P.b ^ 2 = 1 := by
    rcases residue_cases_at_three hp3 P.b with h | h | h
    · exact absurd h hb
    · rw [h]; ring
    · rw [h]; ring
  have hQ : (1 + P.c) ^ 2 - P.b * P.d = -1 := by
    linear_combination hX + residue_cube_eq_self_at_three hp3 P.c
      + (P.b * P.d - P.c ^ 2) * hb2 + (1 + P.c) * h3
  refine card_roots_toFinset_eq_zero (by simp [ha]) fun x hx => ?_
  rw [ha, one_mul] at hx
  have hsq : (x - P.b * (1 + P.c)) ^ 2 = -1 := by
    linear_combination P.b * hx + hQ - P.b * residue_cube_eq_self_at_three hp3 x
      - (x ^ 2 - (1 + P.c) ^ 2) * hb2 - P.b * x * (P.c + 1) * h3
  rcases residue_cases_at_three hp3 (x - P.b * (1 + P.c)) with h | h | h
  · rw [h] at hsq
    exact residue_zero_ne_neg_one_at_three hp3 (by linear_combination hsq)
  · rw [h] at hsq
    exact residue_one_ne_neg_one_at_three hp3 (by linear_combination hsq)
  · rw [h] at hsq
    exact residue_one_ne_neg_one_at_three hp3 (by linear_combination hsq)

open scoped Classical in
/-- A monic cubic over the residue field of `ℤ_3` with `b ≠ 0` and `b²c² - c³ - b³d = -1` has
exactly one root, namely `b(1 + c)`. -/
theorem card_roots_eq_one_of_unit (hp3 : p = 3)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hb : P.b ≠ 0)
    (hX : P.b ^ 2 * P.c ^ 2 - P.c ^ 3 - P.b ^ 3 * P.d = -1) :
    P.toPoly.roots.toFinset.card = 1 := by
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_three_eq_zero_at_three hp3
  have hb2 : P.b ^ 2 = 1 := by
    rcases residue_cases_at_three hp3 P.b with h | h | h
    · exact absurd h hb
    · rw [h]; ring
    · rw [h]; ring
  have hQ : (1 + P.c) ^ 2 - P.b * P.d = 0 := by
    linear_combination hX + residue_cube_eq_self_at_three hp3 P.c
      + (P.b * P.d - P.c ^ 2) * hb2 + P.c * h3
  refine card_roots_toFinset_eq_one (by simp [ha]) (x₀ := P.b * (1 + P.c)) ?_ fun x hx => ?_
  · rw [ha, one_mul]
    refine mul_left_cancel₀ hb ?_
    linear_combination -hQ
      + P.b * residue_cube_eq_self_at_three hp3 (P.b * (1 + P.c))
      + ((P.b * (1 + P.c)) ^ 2 - (1 + P.c) ^ 2) * hb2
      + P.b * (P.b * (1 + P.c)) * (P.c + 1) * h3
  · rw [ha, one_mul] at hx
    have hsq : (x - P.b * (1 + P.c)) ^ 2 = 0 := by
      linear_combination P.b * hx + hQ - P.b * residue_cube_eq_self_at_three hp3 x
        - (x ^ 2 - (1 + P.c) ^ 2) * hb2 - P.b * x * (P.c + 1) * h3
    linear_combination pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq

namespace IZeroStarUnitThree

private theorem smulOne_a₁ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
  simp [variableChange_a₁]

private theorem smulOne_a₂ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
  simp [variableChange_a₂]

private theorem smulOne_a₃ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 2 * t := by
  simp [variableChange_a₃]

private theorem smulOne_a₄ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = a₄ + 3 * r ^ 2 := by
  simp [variableChange_a₄]

private theorem smulOne_a₆ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
  simp [variableChange_a₆]

private theorem smulOne_b₂ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₂ = 12 * r := by
  simp [WeierstrassCurve.b₂, variableChange_a₁, variableChange_a₂]
  ring

private theorem smulOne_b₆ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₆ = 4 * (a₆ + r * a₄ + r ^ 3) := by
  simp [WeierstrassCurve.b₆, variableChange_a₃, variableChange_a₆]
  ring

private theorem smulOne_b₈ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₈
      = 12 * r * (a₆ + r * a₄ + r ^ 3) - (a₄ + 3 * r ^ 2) ^ 2 := by
  simp [WeierstrassCurve.b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring

/-- If `3 ∤ e` and `4α³ + e² = 27M`, then `α ≡ -1 (mod 3)`. -/
theorem alpha_form {α e M : ℤ_[3]} (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ e)
    (hM : 4 * α ^ 3 + e ^ 2 = 27 * M) : ∃ n : ℤ_[3], α = -1 + ((3 : ℕ) : ℤ_[3]) * n := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  exact FamilyAThree.alpha_eq_neg_one_add he ⟨9 * M, by rw [hcast]; linear_combination hM⟩

/-- If `a₄ = 3α`, `3 ∤ a₆` and `4α³ + a₆² = 27M`, the Step-2 translate of `y² = x³ + a₄x + a₆`
is the change of variables `(1, r, 0, t)` with `r = -a₆ + 3ρ`, `t = 3τ`, `α = -1 + 3n`, and
`α + r² = 3C`, `a₆ + 3rα + r³ = 27D`. -/
theorem step2_data {x : ℤ_[3] × ℤ_[3]} {α M : ℤ_[3]}
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2)
    (hM : 4 * α ^ 3 + x.2 ^ 2 = 27 * M) :
    ∃ r t ρ τ n C D : ℤ_[3],
      Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
          = (VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2 ∧
        r = -x.2 + 3 * ρ ∧ t = 3 * τ ∧ α = -1 + 3 * n ∧
        x.2 ^ 2 = -4 * (-1 + 3 * n) ^ 3 + 27 * M ∧
        (-1 + 3 * n) + r ^ 2 = 3 * C ∧ x.2 + r * (3 * (-1 + 3 * n)) + r ^ 3 = 27 * D := by
  classical
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨n, hn⟩ := alpha_form he hM
  rw [hcast] at h1 hn
  have hΔd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF x.1 x.2).Δ := by
    refine ⟨-16 * (36 * α ^ 3 + 9 * x.2 ^ 2), ?_⟩
    rw [ofShortNF_Δ, h1, hcast]; ring
  obtain ⟨r, t, hT⟩ : ∃ r t : ℤ_[3], Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
      = (VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2 := ⟨_, _, dite_eq_left hΔd⟩
  have hval := Step2.hasValuation_translate hΔd
  have ha₃ : ((3 : ℕ) : ℤ_[3]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2).a₃ := by
    rw [← hT]; simpa using hval.a₃
  have ha₆ : ((3 : ℕ) : ℤ_[3]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2).a₆ := by
    rw [← hT]; simpa using hval.a₆
  obtain ⟨hre, ht⟩ := FamilyAThree.dvd_add_of_step2_at_three (p := 3) rfl ⟨α, h1⟩ ha₃ ha₆
  obtain ⟨ρ, hρ⟩ := hre
  obtain ⟨τ, hτ⟩ := ht
  rw [hcast] at hρ hτ
  have hr : r = -x.2 + 3 * ρ := by linear_combination hρ
  have hM' : x.2 ^ 2 = -4 * (-1 + 3 * n) ^ 3 + 27 * M := by rw [← hn]; linear_combination hM
  refine ⟨r, t, ρ, τ, n,
    1 - 11 * n + 36 * n ^ 2 - 36 * n ^ 3 + 9 * M - 2 * x.2 * ρ + 3 * ρ ^ 2,
    x.2 * n - 4 * x.2 * n ^ 2 + 4 * x.2 * n ^ 3 - x.2 * M + ρ - 11 * n * ρ + 36 * n ^ 2 * ρ
      - 36 * n ^ 3 * ρ + 9 * M * ρ - x.2 * ρ ^ 2 + ρ ^ 3,
    hT, hr, by linear_combination hτ, hn, hM', ?_, ?_⟩
  · rw [hr]; linear_combination hM'
  · rw [hr]; linear_combination (9 * ρ - x.2) * hM'

/-- If `a₄ = 3α`, `3 ∤ a₆` and `27 ∣ 4α³ + a₆²`, Steps 1 to 5 of Tate's algorithm pass and return
the Step-2 translate. -/
theorem step5_run_eq_ok {x : ℤ_[3] × ℤ_[3]} {α M : ℤ_[3]}
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2)
    (hM : 4 * α ^ 3 + x.2 ^ 2 = 27 * M) :
    Step5.run ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨r, t, ρ, τ, n, C, D, hT, hr, ht, hn, hM', hC, hD⟩ := step2_data h1 he hM
  have h1' : x.1 = 3 * (-1 + 3 * n) := by rw [h1, hn, hcast]
  have hΔd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF x.1 x.2).Δ := by
    refine ⟨-16 * (36 * (-1 + 3 * n) ^ 3 + 9 * x.2 ^ 2), ?_⟩
    rw [ofShortNF_Δ, h1', hcast]; ring
  refine FlipRun.step5_run_eq_ok_of_tests hΔd ?_ ?_ ?_ ?_
  · rw [hT, smulOne_b₂, hcast]; exact ⟨4 * r, by ring⟩
  · rw [hT, smulOne_a₆, ht, hcast]
    exact ⟨3 * D - τ ^ 2, by linear_combination hD + r * h1'⟩
  · have hx1 : x.1 + 3 * r ^ 2 = 9 * C := by rw [h1']; linear_combination 3 * hC
    rw [hT, smulOne_b₈, hcast]
    refine ⟨12 * r * D - 3 * C ^ 2, ?_⟩
    linear_combination 12 * r * hD + 12 * r * r * h1' - (x.1 + 3 * r ^ 2 + 9 * C) * hx1
  · rw [hT, smulOne_b₆, hcast]
    exact ⟨4 * D, by linear_combination 4 * hD + 4 * r * h1'⟩

/-- In `ℤ_3`, if `e² = -4α³ + 27M` with `α = -1 + 3n`, `r = -e + 3ρ`, `3C = α + r²` and
`27D = e + 3rα + r³`, then `X = r²C² - C³ - r³D` satisfies `X ≡ -M (mod 3)`. -/
theorem cubic_combo_eq {e n M r ρ C D : ℤ_[3]}
    (hr : r = -e + 3 * ρ) (hM : e ^ 2 = -4 * (-1 + 3 * n) ^ 3 + 27 * M)
    (hC : (-1 + 3 * n) + r ^ 2 = 3 * C)
    (hD : e + r * (3 * (-1 + 3 * n)) + r ^ 3 = 27 * D) :
    (3 : ℤ_[3]) ∣ r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D + M := by
  have hZ : 2 * r ^ 3 - e = 9 * (8 * ρ - e + 54 * ρ * M - 72 * n * ρ - 6 * e * M + 8 * e * n
      + 6 * ρ ^ 3 + 216 * n ^ 2 * ρ - 6 * e * ρ ^ 2 - 24 * e * n ^ 2 - 216 * n ^ 3 * ρ
      + 24 * e * n ^ 3) := by
    rw [hr]; linear_combination (18 * ρ - 2 * e) * hM
  obtain ⟨Z, hZ'⟩ : ∃ Z : ℤ_[3], 2 * r ^ 3 - e = 9 * Z := ⟨_, hZ⟩
  have hmain : (4 : ℤ_[3]) * (r ^ 6 - r ^ 3 * e - (-1 + 3 * n) ^ 3) = 27 * (3 * Z ^ 2 - M) := by
    linear_combination (2 * r ^ 3 - e + 9 * Z) * hZ' - hM
  have h27 : (27 : ℤ_[3]) * (r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D)
      = r ^ 6 - r ^ 3 * e - (-1 + 3 * n) ^ 3 := by
    linear_combination (1 - 3 * C - 6 * n + r ^ 2 + 9 * C ^ 2 + 9 * n * C + 9 * n ^ 2
      - 6 * C * r ^ 2 - 3 * n * r ^ 2 - 2 * r ^ 4) * hC + r ^ 3 * hD
  have h4 : (4 : ℤ_[3]) * (r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D) = 3 * Z ^ 2 - M := by
    have h := hmain
    rw [← h27] at h
    have h27ne : (27 : ℤ_[3]) ≠ 0 := by
      rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]
      refine pow_ne_zero 3 ?_
      rw [show (3 : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) by norm_num]
      exact PadicInt.uniformizer_ne_zero
    refine mul_left_cancel₀ h27ne ?_
    linear_combination h
  have hu : IsUnit (4 : ℤ_[3]) := by
    have h := (PadicInt.isUnit_two (p := 3) (by decide)).pow 2
    simpa [show (2 : ℤ_[3]) ^ 2 = 4 by norm_num] using h
  refine hu.dvd_mul_left.mp ⟨Z ^ 2 + M, ?_⟩
  linear_combination h4

/-- If `a₄ = 3α`, `3 ∤ a₆` and `4α³ + a₆² = 27M`, Steps 1 to 5 return a curve `V` whose Step-6
cubic is `⟨1, r̄, C̄, D̄⟩` with `3 ∤ r` and `r²C² - C³ - r³D ≡ -M (mod 3)`. -/
theorem cubic_data {x : ℤ_[3] × ℤ_[3]} {α M : ℤ_[3]}
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2)
    (hM : 4 * α ^ 3 + x.2 ^ 2 = 27 * M) :
    ∃ V : WeierstrassCurve ℤ_[3], ∃ r C D : ℤ_[3],
      Step5.run ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2) = Except.ok V ∧
        (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).b
            = mod ((3 : ℕ) : ℤ_[3]) r ∧
        (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).c
            = mod ((3 : ℕ) : ℤ_[3]) C ∧
        (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).d
            = mod ((3 : ℕ) : ℤ_[3]) D ∧
        ¬ ((3 : ℕ) : ℤ_[3]) ∣ r ∧
        ((3 : ℕ) : ℤ_[3]) ∣ r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D + M := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨r, t, ρ, τ, n, C, D, hT, hr, ht, hn, hM', hC, hD⟩ := step2_data h1 he hM
  set V := Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2) with hV
  have h1' : x.1 = 3 * (-1 + 3 * n) := by rw [h1, hn, hcast]
  have hru : ¬ ((3 : ℕ) : ℤ_[3]) ∣ r := by
    intro hd
    refine he ?_
    obtain ⟨w, hw⟩ := hd
    exact ⟨ρ - w, by rw [hcast]; linear_combination -hw + hr⟩
  have ha₁ : V.a₁ = 0 := by rw [hT, smulOne_a₁]
  have ha₂ : V.a₂ = ((3 : ℕ) : ℤ_[3]) * r := by rw [hT, smulOne_a₂, hcast]
  have ha₃ : V.a₃ = 2 * (((3 : ℕ) : ℤ_[3]) * τ) := by rw [hT, smulOne_a₃, ht, hcast]
  have ha₄ : V.a₄ = ((3 : ℕ) : ℤ_[3]) ^ 2 * C := by
    rw [hT, smulOne_a₄, hcast]; linear_combination 3 * hC + h1'
  have ha₆ : V.a₆ = ((3 : ℕ) : ℤ_[3]) ^ 3 * D - ((3 : ℕ) : ℤ_[3]) ^ 2 * τ ^ 2 := by
    rw [hT, smulOne_a₆, ht, hcast]; linear_combination hD + r * h1'
  obtain ⟨σ, y, h2, h4, h6⟩ := FamilyAThree.step6_coeffs ha₁ ha₂ ha₃ ha₄ ha₆
  set W := Step6.translate ((3 : ℕ) : ℤ_[3]) V with hW
  refine ⟨V, r, C, D, step5_run_eq_ok h1 he hM, ?_, ?_, ?_, hru,
    cubic_combo_eq hr hM' hC hD⟩
  · rw [FamilyAThree.cubic_b_eq h2 1 1, map_sub, map_mul,
      show mod ((3 : ℕ) : ℤ_[3]) ((3 : ℕ) : ℤ_[3]) = 0 from by rw [mod_eq_zero],
      zero_mul, sub_zero]
  · rw [FamilyAThree.cubic_c_eq h4 1, map_sub, map_mul, map_mul,
      show mod ((3 : ℕ) : ℤ_[3]) 6 = 0 from by rw [mod_eq_zero]; exact ⟨2, by norm_num⟩,
      zero_mul, zero_mul, sub_zero]
  · rw [FamilyAThree.cubic_d_eq h6 1, map_sub, map_mul,
      show mod ((3 : ℕ) : ℤ_[3]) 3 = 0 from by rw [mod_eq_zero]; exact ⟨1, by norm_num⟩,
      zero_mul, sub_zero]

/-- If `4α³ + e² = 27M` with `3 ∤ M`, the curve `y² = x³ + 3αx + e` is nonsingular. -/
theorem ofShortNF_Δ_ne_zero_of_unit {α e M : ℤ_[3]} (hM : 4 * α ^ 3 + e ^ 2 = 27 * M)
    (hMu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ M) :
    (ofShortNF (((3 : ℕ) : ℤ_[3]) * α) e).Δ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  intro hzero
  rw [ofShortNF_Δ, hcast] at hzero
  have hD : (4 : ℤ_[3]) * (3 * α) ^ 3 + 27 * e ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left isUnit_neg_sixteen_three.ne_zero
  have h27ne : (27 : ℤ_[3]) ≠ 0 := by
    rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]
    exact pow_ne_zero 3 (by rw [← hcast]; exact PadicInt.uniformizer_ne_zero)
  have hMz : (27 : ℤ_[3]) * ((27 : ℤ_[3]) * M) = 0 := by linear_combination hD - 27 * hM
  have hMz' : (27 : ℤ_[3]) * M = 0 := (mul_eq_zero.mp hMz).resolve_left h27ne
  exact absurd ((mul_eq_zero.mp hMz').resolve_left h27ne) (fun h => hMu ⟨0, by rw [h]; ring⟩)

/-- If the cubic attached to `V` has coefficients `b = r̄`, `c = C̄`, `d = D̄` and
`3 ∣ r²C² - C³ - r³D + M`, then `b²c² - c³ - b³d` is the residue of `-M`. -/
theorem cubic_X_eq {V : WeierstrassCurve ℤ_[3]} {r C D M : ℤ_[3]}
    (hb : (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).b = mod ((3 : ℕ) : ℤ_[3]) r)
    (hc : (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).c = mod ((3 : ℕ) : ℤ_[3]) C)
    (hd : (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).d = mod ((3 : ℕ) : ℤ_[3]) D)
    (hX : ((3 : ℕ) : ℤ_[3]) ∣ r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D + M) :
    (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).b ^ 2 * (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).c ^ 2
        - (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).c ^ 3
        - (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).b ^ 3 * (cubic ((3 : ℕ) : ℤ_[3]) V 1 1).d
      = -mod ((3 : ℕ) : ℤ_[3]) M := by
  have h0 : mod ((3 : ℕ) : ℤ_[3]) (r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D + M) = 0 := by
    rw [mod_eq_zero]; exact hX
  rw [map_add, map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow] at h0
  rw [hb, hc, hd]
  linear_combination h0

/-- If `a₄ = 3α`, `3 ∤ a₆` and `4α³ + a₆² = 27M` with `M ≡ -1 (mod 3)`, Tate's algorithm returns
Kodaira symbol `I₀*` and Tamagawa number `1`. -/
theorem run_eq_I0star_one {x : ℤ_[3] × ℤ_[3]} {α M k : ℤ_[3]}
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2)
    (hM : 4 * α ^ 3 + x.2 ^ 2 = 27 * M) (hMk : M = -1 + ((3 : ℕ) : ℤ_[3]) * k)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  obtain ⟨V, r, C, D, h5, hb, hc, hd, hru, hcombo⟩ := cubic_data h1 he hM
  have hMres : mod ((3 : ℕ) : ℤ_[3]) M = -1 := by
    rw [hMk, map_add, map_mul, map_neg, map_one,
      show mod ((3 : ℕ) : ℤ_[3]) ((3 : ℕ) : ℤ_[3]) = 0 from by rw [mod_eq_zero]]
    ring
  have hXeq := cubic_X_eq hb hc hd hcombo
  rw [hMres, neg_neg] at hXeq
  have hbne : (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).b ≠ 0 := by
    rw [hb, Ne, mod_eq_zero]; exact hru
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_step5 hΔ h5
    (not_hasDoubleRoot_of_sq_ne (p := 3) rfl (by simp [cubic])
      (by rw [hXeq]; exact one_ne_zero))
  exact ⟨hk, by rw [ht, card_roots_eq_zero_of_unit (p := 3) rfl (by simp [cubic]) hbne hXeq]⟩

/-- If `a₄ = 3α`, `3 ∤ a₆` and `4α³ + a₆² = 27M` with `M ≡ 1 (mod 3)`, Tate's algorithm returns
Kodaira symbol `I₀*` and Tamagawa number `2`. -/
theorem run_eq_I0star_two {x : ℤ_[3] × ℤ_[3]} {α M k : ℤ_[3]}
    (h1 : x.1 = ((3 : ℕ) : ℤ_[3]) * α) (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2)
    (hM : 4 * α ^ 3 + x.2 ^ 2 = 27 * M) (hMk : M = 1 + ((3 : ℕ) : ℤ_[3]) * k)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  obtain ⟨V, r, C, D, h5, hb, hc, hd, hru, hcombo⟩ := cubic_data h1 he hM
  have hMres : mod ((3 : ℕ) : ℤ_[3]) M = 1 := by
    rw [hMk, map_add, map_mul, map_one,
      show mod ((3 : ℕ) : ℤ_[3]) ((3 : ℕ) : ℤ_[3]) = 0 from by rw [mod_eq_zero]]
    ring
  have hXeq := cubic_X_eq hb hc hd hcombo
  rw [hMres] at hXeq
  have hbne : (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).b ≠ 0 := by
    rw [hb, Ne, mod_eq_zero]; exact hru
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_step5 hΔ h5
    (not_hasDoubleRoot_of_sq_ne (p := 3) rfl (by simp [cubic])
      (by rw [hXeq]; exact neg_ne_zero.2 one_ne_zero))
  exact ⟨hk, by rw [ht, card_roots_eq_one_of_unit (p := 3) rfl (by simp [cubic]) hbne hXeq]⟩

/-- The condition on a pair `(α, e)` of residues modulo `81` that `α` is a unit modulo `3` and
`4α³ + e² ≡ 27u (mod 81)`. -/
abbrev Res (u : ℕ) (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) : Prop :=
  (ZMod.cast c.1 : ZMod 3) ≠ 0 ∧ 4 * c.1 ^ 3 + c.2 ^ 2 = 27 * (u : ZMod (3 ^ 4))

/-- The set of pairs of residues modulo `81` satisfying `Res u`. -/
noncomputable def residues (u : ℕ) : Finset (ZMod (3 ^ 4) × ZMod (3 ^ 4)) :=
  Finset.univ.filter (fun c => Res u c)

/-- A pair lies in `residues u` if and only if it satisfies `Res u`. -/
theorem mem_residues_iff (u : ℕ) (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) :
    c ∈ residues u ↔ Res u c := by
  simp [residues]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` evaluates `Res` at all `6561` pairs modulo `81`.
/-- Exactly `54` pairs of residues modulo `81` satisfy `Res 1`. -/
theorem card_residues_one : (residues 1).card = 54 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` evaluates `Res` at all `6561` pairs modulo `81`.
/-- Exactly `54` pairs of residues modulo `81` satisfy `Res 2`. -/
theorem card_residues_two : (residues 2).card = 54 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` evaluates `Res` at all `6561` pairs modulo `81`.
/-- If `(α, e)` satisfies `Res 1`, then `e` is a unit modulo `3`. -/
theorem res_cast_snd_one (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) (h : Res 1 c) :
    (ZMod.cast c.2 : ZMod 3) ≠ 0 := by revert c; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` evaluates `Res` at all `6561` pairs modulo `81`.
/-- If `(α, e)` satisfies `Res 2`, then `e` is a unit modulo `3`. -/
theorem res_cast_snd_two (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) (h : Res 2 c) :
    (ZMod.cast c.2 : ZMod 3) ≠ 0 := by revert c; decide

/-- The set of `(3α, e) ∈ ℤ_3 × ℤ_3` such that the residues of `(α, e)` modulo `81` satisfy
`Res u`. -/
noncomputable def locus (u : ℕ) : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.scaleProdByPPow 1 0 ''
    (PadicInt.redPairPow 3 4 ⁻¹' (residues u : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4))))

/-- `locus u` is measurable. -/
theorem measurableSet_locus (u : ℕ) : MeasurableSet (locus u) :=
  (PadicInt.measurableEmbedding_scaleProdByPPow 1 0).measurableSet_image.2
    (PadicInt.measurableSet_preimage_redPairPow 4 (residues u))

/-- If `residues u` has `54` elements, then `locus u` has volume `2/729`. -/
theorem volume_locus_of_card {u : ℕ} (hc : (residues u).card = 54) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (locus u) = 2 / 729 := by
  rw [locus, PadicInt.measure_image_scaleProdByPPow, PadicInt.volume_preimage_redPairPow, hc,
    FamilyAThree.fiftyFour_mul_inv_pow_eight_eq,
    show ((1 : ℕ) + (0 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) by norm_num,
    PadicInt.zpow_neg_natCast_eq_inv_pow, pow_one, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num]
  rw [show (3 : ℝ≥0∞)⁻¹ = 1 / 3 from by rw [one_div], enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

set_option maxRecDepth 100000 in
/-- A point `x` lies in `locus u` if and only if `x.1 = 3α` with the residues of `(α, x.2)`
modulo `81` satisfying `Res u`. -/
theorem mem_locus_iff {u : ℕ} {x : ℤ_[3] × ℤ_[3]} :
    x ∈ locus u ↔ ∃ α : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) * α ∧
      Res u (PadicInt.toZModPow 4 α, PadicInt.toZModPow 4 x.2) := by
  have hcoe : ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4),
      c ∈ (residues u : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4))) ↔ Res u c :=
    fun c => (Finset.mem_coe).trans (mem_residues_iff u c)
  constructor
  · rintro ⟨⟨α, e⟩, hmem, rfl⟩
    refine ⟨α, ?_, ?_⟩
    · rw [PadicInt.scaleProdByPPow, Prod.map_fst, PadicInt.scaleByPPow, pow_one]
    · rw [PadicInt.scaleProdByPPow, Prod.map_snd, PadicInt.scaleByPPow, pow_zero, one_mul]
      exact (hcoe _).1 hmem
  · rintro ⟨α, h1, hres⟩
    refine ⟨(α, x.2), (hcoe _).2 hres, Prod.ext ?_ ?_⟩
    · rw [PadicInt.scaleProdByPPow, Prod.map_fst, PadicInt.scaleByPPow, pow_one]
      exact h1.symm
    · rw [PadicInt.scaleProdByPPow, Prod.map_snd, PadicInt.scaleByPPow, pow_zero, one_mul]

/-- If the residue of `y ∈ ℤ_3` modulo `81` is nonzero modulo `3`, then `3 ∤ y`. -/
theorem not_dvd_of_cast_ne_zero {y : ℤ_[3]}
    (hy : (ZMod.cast (PadicInt.toZModPow 4 y) : ZMod 3) ≠ 0) : ¬ ((3 : ℕ) : ℤ_[3]) ∣ y := by
  intro hdvd
  refine hy ?_
  have h1 : (ZMod.cast (PadicInt.toZModPow 4 y) : ZMod (3 ^ 1)) = PadicInt.toZModPow 1 y :=
    PadicInt.cast_toZModPow 1 4 (by norm_num) y
  have h2 : PadicInt.toZModPow 1 y = 0 := by
    rwa [← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
  simpa using h1.trans h2

/-- If every pair satisfying `Res u` has second entry a unit modulo `3`, then each `x ∈ locus u`
has `x.1 = 3α` with `3 ∤ α`, `3 ∤ x.2`, and `4α³ + x.2² = 27M` with `M ≡ u (mod 3)`. -/
theorem exists_form_of_mem_locus {u : ℕ} {x : ℤ_[3] × ℤ_[3]}
    (hsnd : ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), Res u c → (ZMod.cast c.2 : ZMod 3) ≠ 0)
    (hx : x ∈ locus u) :
    ∃ α M : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) * α ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2 ∧ 4 * α ^ 3 + x.2 ^ 2 = 27 * M ∧
      ((3 : ℕ) : ℤ_[3]) ∣ M - (u : ℤ_[3]) := by
  obtain ⟨α, h1, hres⟩ := mem_locus_iff.1 hx
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨K, hK⟩ : ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ 4 * α ^ 3 + x.2 ^ 2 - 27 * (u : ℤ_[3]) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_add, map_mul, map_mul, map_pow,
      map_pow, map_ofNat, map_ofNat, map_natCast, hres.2, sub_self]
  rw [hcast] at hK
  exact ⟨α, (u : ℤ_[3]) + 3 * K, h1, not_dvd_of_cast_ne_zero hres.1,
    not_dvd_of_cast_ne_zero (hsnd _ hres), by linear_combination hK,
    ⟨K, by rw [hcast]; ring⟩⟩

/-- If every pair satisfying `Res u` has second entry a unit modulo `3`, then no point of
`locus u` lies in the image of `(a, b) ↦ (3⁴a, 3⁶b)`. -/
theorem locus_subset_notMem_range {u : ℕ}
    (hsnd : ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4), Res u c → (ZMod.cast c.2 : ZMod 3) ≠ 0) :
    ∀ x ∈ locus u, x ∉ Set.range
      (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  intro x hx
  obtain ⟨α, M, h1, hα, -, -, -⟩ := exists_form_of_mem_locus hsnd hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => hα ?_
  rw [h1] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨((3 : ℕ) : ℤ_[3]) ^ 2 * c, mul_left_cancel₀ PadicInt.uniformizer_ne_zero ?_⟩
  rw [hc]
  ring

/-! ### The two loci lie in the minimal parts of rows `t = 1` and `t = 2`

The `u = 2` cylinder has `M ≡ -1 (mod 3)` and so answers `(I₀*, 1)`, landing in row `t = 1`; the
`u = 1` cylinder has `M ≡ 1` and answers `(I₀*, 2)`, landing in row `t = 2`. -/

/-- If `u = v + 3w` and `3 ∣ M - u`, then `M = v + 3k` for some `k`. -/
theorem exists_form_of_dvd_sub {M : ℤ_[3]} {u : ℕ} {v w : ℤ_[3]}
    (hv : ((u : ℤ_[3])) = v + ((3 : ℕ) : ℤ_[3]) * w)
    (h : ((3 : ℕ) : ℤ_[3]) ∣ M - (u : ℤ_[3])) :
    ∃ k : ℤ_[3], M = v + ((3 : ℕ) : ℤ_[3]) * k := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c + w, by linear_combination hc + hv⟩

open scoped Classical in
/-- **The `u = 2` cylinder lies in the strata over `t = 1`.** -/
theorem locus_two_subset_iUnion_stratFibre :
    locus 2 ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1) := by
  intro x hx
  obtain ⟨α, M, h1, hα, he, hM, hsub⟩ := exists_form_of_mem_locus res_cast_snd_two hx
  obtain ⟨k, hk⟩ := exists_form_of_dvd_sub (v := -1) (w := 1) (by push_cast; norm_num) hsub
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [h1]; exact ofShortNF_Δ_ne_zero_of_unit hM (not_dvd_of_eq_add_mul_three (Or.inr rfl) hk)
  obtain ⟨hks, hts⟩ := run_eq_I0star_one h1 he hM hk hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0,
    (mem_stratFibre_iff (show x ∈ nonsingularLocus 3 from hΔ)).2
    (by rw [strat]; exact Prod.ext hks hts)⟩

open scoped Classical in
/-- **The `u = 1` cylinder lies in the strata over `t = 2`.** -/
theorem locus_one_subset_iUnion_stratFibre :
    locus 1 ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2) := by
  intro x hx
  obtain ⟨α, M, h1, hα, he, hM, hsub⟩ := exists_form_of_mem_locus res_cast_snd_one hx
  obtain ⟨k, hk⟩ := exists_form_of_dvd_sub (v := 1) (w := 0) (by push_cast; norm_num) hsub
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    rw [h1]; exact ofShortNF_Δ_ne_zero_of_unit hM (not_dvd_of_eq_add_mul_three (Or.inl rfl) hk)
  obtain ⟨hks, hts⟩ := run_eq_I0star_two h1 he hM hk hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0,
    (mem_stratFibre_iff (show x ∈ nonsingularLocus 3 from hΔ)).2
    (by rw [strat]; exact Prod.ext hks hts)⟩

/-- **The `u = 2` cylinder lies in the minimal part of the `t = 1` row.** -/
theorem locus_two_subset_headMinimal :
    locus 2 ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  fun x hx => ⟨locus_two_subset_iUnion_stratFibre hx,
    locus_subset_notMem_range res_cast_snd_two x hx⟩

/-- **The `u = 1` cylinder lies in the minimal part of the `t = 2` row.** -/
theorem locus_one_subset_headMinimal :
    locus 1 ⊆ (⋃ κ : KodairaSymbol, stratFibre 3 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) :=
  fun x hx => ⟨locus_one_subset_iUnion_stratFibre hx,
    locus_subset_notMem_range res_cast_snd_one x hx⟩

end IZeroStarUnitThree

end WeierstrassCurve

end
