/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.StepSixForwardGeneral
public import BSDTamagawa.GOTTable.WildRowLowerBound
public import BSDTamagawa.NumberTheory.SplitStoreyDescentTwo

/-!
# The two `I₀*` loci at `p = 2`

Tate's algorithm at `2` on a short model `y² = x³ + a₄x + a₆` reaches Step 6 exactly on the pairs
whose class modulo `4` is `(0, 0)` or `(1, 2)`, and there it answers `(I₀*, 1 + #roots)` when its
cubic is separable. Two explicit sets of eight residue classes modulo `16`,

    (I₀*, 2)   (0,8), (0,12), (1,14), (5,14), (8,8), (8,12), (9,6), (13,6)
    (I₀*, 1)   (1,10), (4,8), (4,12), (5,2), (9,2), (12,8), (12,12), (13,10)

carry reduction data `(I₀*, 2)` and `(I₀*, 1)` respectively. Each has mass `8 · 2⁻⁸ = 1/32`, and
each lies in the minimal part of the corresponding row of the `p = 2` column.

The three entries of Step 6's cubic are `a₂(V₂)/2`, `a₄(V₂)/4` and `a₆(V₂)/8` modulo `2`, where
`V₂` is the Step-6 translate. The separability test `b·c ≠ d` and the root-count test `b = c` over
`𝔽₂`, multiplied by `8` and `4`, become the congruences

    `¬ 16 ∣ a₂(V₂)·a₄(V₂) − a₆(V₂)`   and   `8 ∣ 2·a₂(V₂) − a₄(V₂)`

in the coefficients themselves, which hold for every choice of the lifts the algorithm makes.

## Main definitions

* `WeierstrassCurve.headResiduesIZeroStarTwo`, `WeierstrassCurve.headResiduesIZeroStarOne`,
  `WeierstrassCurve.headResiduesIZeroStar`: the two residue sets modulo `16` and their union.
* `WeierstrassCurve.iZeroStarTwo2Locus`, `WeierstrassCurve.iZeroStarOne2Locus`: the corresponding
  subsets of `ℤ_2 × ℤ_2`.

## Main results

* `WeierstrassCurve.izeroStar_step5_and_cubic`: on the sixteen classes Steps 1–5 succeed, Step 6's
  cubic is separable, and `b = c` holds exactly on the `(I₀*, 2)` classes.
* `WeierstrassCurve.card_roots_eq_one_two`, `WeierstrassCurve.card_roots_eq_zero_two`: a separable
  monic cubic over the residue field of `ℤ_2` has one distinct root when `b = c` and none when
  `b ≠ c`.
* `WeierstrassCurve.run_eq_I0star_two_two`, `WeierstrassCurve.run_eq_I0star_one_two`: Tate's
  algorithm returns `(I₀*, 2)` and `(I₀*, 1)` on the two loci.
* `WeierstrassCurve.volume_iZeroStarTwo2Locus`, `WeierstrassCurve.volume_iZeroStarOne2Locus`: both
  loci have mass `1/32`.
* `WeierstrassCurve.iZeroStarTwo2Locus_subset_headMinimal`,
  `WeierstrassCurve.iZeroStarOne2Locus_subset_headMinimal`: both loci lie in the minimal part of
  their rows.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm CommRing Ideal

/-! ### The two residue sets modulo `16` -/

/-- The eight classes `(a₄, a₆)` modulo `16` on which Tate's algorithm at `2` answers `(I₀*, 2)`:
Step 6's cubic is separable and has one root in `𝔽₂`. -/
def headResiduesIZeroStarTwo : Finset (ZMod (2 ^ 4) × ZMod (2 ^ 4)) :=
  {(0, 8), (0, 12), (1, 14), (5, 14), (8, 8), (8, 12), (9, 6), (13, 6)}

/-- The eight classes `(a₄, a₆)` modulo `16` on which Tate's algorithm at `2` answers `(I₀*, 1)`:
Step 6's cubic is separable and has no root in `𝔽₂`. -/
def headResiduesIZeroStarOne : Finset (ZMod (2 ^ 4) × ZMod (2 ^ 4)) :=
  {(1, 10), (4, 8), (4, 12), (5, 2), (9, 2), (12, 8), (12, 12), (13, 10)}

/-- The sixteen classes on which Step 6 answers `I₀*`, the union of `headResiduesIZeroStarTwo` and
`headResiduesIZeroStarOne`. -/
def headResiduesIZeroStar : Finset (ZMod (2 ^ 4) × ZMod (2 ^ 4)) :=
  {(0, 8), (0, 12), (1, 14), (5, 14), (8, 8), (8, 12), (9, 6), (13, 6),
   (1, 10), (4, 8), (4, 12), (5, 2), (9, 2), (12, 8), (12, 12), (13, 10)}

/-- The `(I₀*, 2)` residue set has eight elements. -/
theorem card_headResiduesIZeroStarTwo : headResiduesIZeroStarTwo.card = 8 := by decide

/-- The `(I₀*, 1)` residue set has eight elements. -/
theorem card_headResiduesIZeroStarOne : headResiduesIZeroStarOne.card = 8 := by decide

set_option maxRecDepth 20000 in
/-- The `(I₀*, 2)` residue set is contained in the sixteen `I₀*` classes. -/
theorem headResiduesIZeroStarTwo_subset :
    headResiduesIZeroStarTwo ⊆ headResiduesIZeroStar := by decide

set_option maxRecDepth 20000 in
/-- The `(I₀*, 1)` residue set is contained in the sixteen `I₀*` classes. -/
theorem headResiduesIZeroStarOne_subset :
    headResiduesIZeroStarOne ⊆ headResiduesIZeroStar := by decide

set_option maxRecDepth 20000 in
/-- On the sixteen `I₀*` classes, `a₆ ≢ 0` modulo `16`. -/
theorem headResiduesIZeroStar_snd_ne_zero : ∀ c ∈ headResiduesIZeroStar, c.2 ≠ 0 := by decide

/-! ### Nonsingularity

`Δ = -16(4a₄³ + 27a₆²)`, and on the sixteen classes `v_2(4a₄³ + 27a₆²) ≤ 6`, so the residue modulo
`2⁷` already decides the matter. -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 128)²` exceeds the default budget
/-- If `4A³ + 27E² = 0` in `ZMod (2 ^ 7)`, then the reduction of `(A, E)` modulo `16` is not one of
the sixteen `I₀*` classes. -/
theorem headResiduesIZeroStar_disc : ∀ A E : ZMod (2 ^ 7), 4 * A ^ 3 + 27 * E ^ 2 = 0 →
    ((ZMod.cast A : ZMod (2 ^ 4)), (ZMod.cast E : ZMod (2 ^ 4))) ∉ headResiduesIZeroStar := by
  decide

/-- **The `I₀*` classes at `2` consist of nonsingular models.** -/
theorem ofShortNF_Δ_ne_zero_izeroStar {a₄ a₆ : ℤ_[2]}
    (hA : (PadicInt.toZModPow 4 a₄, PadicInt.toZModPow 4 a₆) ∈ headResiduesIZeroStar) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[2]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left neg_sixteen_ne_zero_two
  refine headResiduesIZeroStar_disc (PadicInt.toZModPow 7 a₄) (PadicInt.toZModPow 7 a₆) ?_ ?_
  · have h := congrArg (PadicInt.toZModPow 7) hD
    rwa [map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat, map_zero] at h
  · rwa [PadicInt.cast_toZModPow 4 7 (by norm_num), PadicInt.cast_toZModPow 4 7 (by norm_num)]

/-! ### The three residue computations

`R` and `T` below are the residues of Step 2's lift pair, constrained only by the two
divisibilities of `Step2.hasValuation_translate`; `Q` is `a₆(V)/4`. -/

set_option maxRecDepth 20000 in
/-- On the sixteen `I₀*` classes, `2 ∣ a₄(V)` and `2 ∣ a₆(V)` for the Step-2 translate `V` imply
`4 ∣ a₄(V)`, `4 ∣ a₆(V)` and `2 ∣ t`. -/
theorem headResiduesIZeroStar_key : ∀ c ∈ headResiduesIZeroStar, ∀ R T : ZMod (2 ^ 4),
    (ZMod.cast (c.1 + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (c.2 + R * c.1 + R ^ 3 - T ^ 2) : ZMod (2 ^ 1)) = 0 →
      (ZMod.cast (c.1 + 3 * R ^ 2) : ZMod (2 ^ 2)) = 0 ∧
      (ZMod.cast (c.2 + R * c.1 + R ^ 3 - T ^ 2) : ZMod (2 ^ 2)) = 0 ∧
      (ZMod.cast T : ZMod (2 ^ 1)) = 0 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 16)³` on sixteen residue classes exceeds the default budget
/-- On the sixteen `I₀*` classes, `¬ 16 ∣ a₂(V₂)·a₄(V₂) − a₆(V₂)`, written as a congruence in
`(a₄, a₆)` and Step 2's lift pair: Step 6's cubic is separable. -/
theorem headResiduesIZeroStar_sep : ∀ c ∈ headResiduesIZeroStar, ∀ R T Q : ZMod (2 ^ 4),
    (ZMod.cast (c.1 + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    4 * Q = c.2 + R * c.1 + R ^ 3 - T ^ 2 →
      (3 * R - 9 * R ^ 2) * (c.1 + 3 * R ^ 2 - 6 * R * (2 * Q + T))
        - (c.2 + R * c.1 + R ^ 3 - (2 * Q + T) ^ 2) ≠ 0 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 16)³` on sixteen residue classes exceeds the default budget
/-- On the `(I₀*, 2)` classes, `8 ∣ 2·a₂(V₂) − a₄(V₂)`, written as a congruence in `(a₄, a₆)` and
Step 2's lift pair: Step 6's cubic satisfies `b = c`. -/
theorem headResiduesIZeroStarTwo_beta : ∀ c ∈ headResiduesIZeroStarTwo, ∀ R T Q : ZMod (2 ^ 4),
    (ZMod.cast (c.1 + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    4 * Q = c.2 + R * c.1 + R ^ 3 - T ^ 2 →
      (ZMod.cast (2 * (3 * R - 9 * R ^ 2)
        - (c.1 + 3 * R ^ 2 - 6 * R * (2 * Q + T))) : ZMod (2 ^ 3)) = 0 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- a `decide` over `(ZMod 16)³` on sixteen residue classes exceeds the default budget
/-- On the `(I₀*, 1)` classes, `¬ 8 ∣ 2·a₂(V₂) − a₄(V₂)`, written as a congruence in `(a₄, a₆)` and
Step 2's lift pair: Step 6's cubic satisfies `b ≠ c`. -/
theorem headResiduesIZeroStarOne_beta : ∀ c ∈ headResiduesIZeroStarOne, ∀ R T Q : ZMod (2 ^ 4),
    (ZMod.cast (c.1 + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    4 * Q = c.2 + R * c.1 + R ^ 3 - T ^ 2 →
      (ZMod.cast (2 * (3 * R - 9 * R ^ 2)
        - (c.1 + 3 * R ^ 2 - 6 * R * (2 * Q + T))) : ZMod (2 ^ 3)) ≠ 0 := by decide

/-! ### The Step-6 cubic of a short model at `2` -/

/-- Step 6's cubic on the short model `y² = x³ + a₄x + a₆` over `ℤ_2`. -/
noncomputable def stepSixCubicTwo (a₄ a₆ : ℤ_[2]) :
    Cubic (ℤ_[2] ⧸ Ideal.span {((2 : ℕ) : ℤ_[2])}) :=
  cubic ((2 : ℕ) : ℤ_[2]) (Step6.translate ((2 : ℕ) : ℤ_[2])
    (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆))) 1 1

/-- `stepSixCubicTwo a₄ a₆` is the Step-6 cubic of the Step-6 translate of the Step-2 translate
of `y² = x³ + a₄x + a₆`. -/
theorem stepSixCubicTwo_def (a₄ a₆ : ℤ_[2]) : stepSixCubicTwo a₄ a₆
    = cubic ((2 : ℕ) : ℤ_[2]) (Step6.translate ((2 : ℕ) : ℤ_[2])
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆))) 1 1 := rfl

/-- Step 6's cubic on a short model at `2` is monic. -/
theorem stepSixCubicTwo_a (a₄ a₆ : ℤ_[2]) : (stepSixCubicTwo a₄ a₆).a = 1 := rfl

/-! ### Root counts over the residue field `𝔽₂`

Step 6 reports `1 + #roots`. A separable monic cubic over `𝔽₂` has one root when `b = c` and none
when `b ≠ c`; it can never have two (`Cubic.card_roots_ne_two`), nor three, `𝔽₂` having only two
elements. -/

/-- If `a ≠ 0` and `S` is exactly the set of solutions of `ax³ + bx² + cx + d = 0`, then `S` is the
`Finset` of distinct roots of the cubic `P = ⟨a, b, c, d⟩`. -/
theorem roots_toFinset_eq_of_forall {K : Type*} [Field K] [DecidableEq K] {P : Cubic K}
    (ha : P.a ≠ 0) (S : Finset K)
    (h : ∀ x : K, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 ↔ x ∈ S) :
    P.toPoly.roots.toFinset = S := by
  have h0 : P.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
  have heval : ∀ x : K, P.toPoly.eval x = P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d := by
    intro x
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
  ext x
  rw [Multiset.mem_toFinset, Polynomial.mem_roots']
  simp only [Polynomial.IsRoot, heval]
  exact ⟨fun hx => (h x).1 hx.2, fun hx => ⟨h0, (h x).2 hx⟩⟩

/-- **A cubic with no root at all has an empty root set.** -/
theorem card_roots_toFinset_eq_zero {K : Type*} [Field K] [DecidableEq K] {P : Cubic K}
    (ha : P.a ≠ 0) (h : ∀ x : K, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d ≠ 0) :
    P.toPoly.roots.toFinset.card = 0 := by
  rw [roots_toFinset_eq_of_forall ha ∅
    fun x => ⟨fun hx => absurd hx (h x), fun hx => absurd hx (Finset.notMem_empty x)⟩,
    Finset.card_empty]

/-- **A cubic with exactly one root has a singleton root set.** -/
theorem card_roots_toFinset_eq_one {K : Type*} [Field K] [DecidableEq K] {P : Cubic K}
    (ha : P.a ≠ 0) {x₀ : K} (hx₀ : P.a * x₀ ^ 3 + P.b * x₀ ^ 2 + P.c * x₀ + P.d = 0)
    (huniq : ∀ x : K, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 → x = x₀) :
    P.toPoly.roots.toFinset.card = 1 := by
  rw [roots_toFinset_eq_of_forall ha {x₀}
    fun x => ⟨fun hx => Finset.mem_singleton.2 (huniq x hx),
      fun hx => by rwa [Finset.mem_singleton.1 hx]⟩, Finset.card_singleton]

variable {p : ℕ} [Fact p.Prime]

/-- **Step 6's separability test at `p = 2` is `b·c = d`.** In residue characteristic two the
discriminant of `X³ + bX² + cX + d` is `(bc − d)²`. -/
theorem hasDoubleRoot_iff_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 1) :
    P.HasDoubleRoot ↔ P.b * P.c = P.d := by
  have h2 : (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := Step2.residue_two_eq_zero_of_eq_two hp2
  have hb := residue_sq_eq_self_two hp2 P.b
  have hc := residue_sq_eq_self_two hp2 P.c
  have hd := residue_sq_eq_self_two hp2 P.d
  rw [Cubic.hasDoubleRoot_of_a_eq_one ha]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · linear_combination h - P.c ^ 2 * hb - P.b * hc + 27 * hd
      + (2 * P.c ^ 3 + 2 * P.b ^ 3 * P.d - 9 * P.b * P.c * P.d + 13 * P.d) * h2
  · linear_combination P.c ^ 2 * hb + P.b * hc + h - 27 * hd
      + (-13 * P.d - 2 * P.c ^ 3 - 2 * P.b ^ 3 * P.d + 9 * P.b * P.c * P.d) * h2

open scoped Classical in
/-- **A separable monic cubic over the residue field of `ℤ_2` with `b = c` has exactly one
distinct root, namely `d`.** On `𝔽₂` the cubic evaluates to `x + d`. -/
theorem card_roots_eq_one_two (hp2 : p = 2) {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hbc : P.b = P.c) : P.toPoly.roots.toFinset.card = 1 := by
  have h2 : (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := Step2.residue_two_eq_zero_of_eq_two hp2
  refine card_roots_toFinset_eq_one (by simp [ha]) (x₀ := P.d) ?_ ?_
  · have hd := residue_sq_eq_self_two hp2 P.d
    rw [ha, ← hbc]
    linear_combination (P.d + 1 + P.b) * hd + (P.b * P.d + P.d) * h2
  · intro x hx
    have hx2 := residue_sq_eq_self_two hp2 x
    rw [ha, ← hbc] at hx
    linear_combination hx - (x + 1 + P.b) * hx2 - (P.b * x + P.d) * h2

open scoped Classical in
/-- **A separable monic cubic over the residue field of `ℤ_2` with `b ≠ c` has no root.** On `𝔽₂`
the cubic evaluates to `d`, and separability forces `d ≠ 0` because `b·c = 0`. -/
theorem card_roots_eq_zero_two (hp2 : p = 2) {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 1) (hbc : P.b ≠ P.c) (hsep : P.b * P.c ≠ P.d) :
    P.toPoly.roots.toFinset.card = 0 := by
  have h2 : (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := Step2.residue_two_eq_zero_of_eq_two hp2
  have hK := Step2.residue_eq_zero_or_one_of_eq_two hp2
  have key : P.b + P.c = 1 ∧ P.b * P.c = 0 := by
    rcases hK P.b with hb | hb <;> rcases hK P.c with hc | hc
    · exact absurd (hb.trans hc.symm) hbc
    · exact ⟨by rw [hb, hc]; ring, by rw [hb]; ring⟩
    · exact ⟨by rw [hb, hc]; ring, by rw [hc]; ring⟩
    · exact absurd (hb.trans hc.symm) hbc
  have hd0 : P.d ≠ 0 := fun h => hsep (key.2.trans h.symm)
  refine card_roots_toFinset_eq_zero (by simp [ha]) fun x hx => hd0 ?_
  have hx2 := residue_sq_eq_self_two hp2 x
  rw [ha] at hx
  linear_combination hx - (x + 1 + P.b) * hx2 - x * key.1 - x * h2

/-! ### The forward run at `(I₀*, 2)` and at `(I₀*, 1)` -/

set_option maxHeartbeats 1000000 in
-- the run carries a dozen `linear_combination`s over `ℤ_2` and exceeds the default budget
open scoped Classical in
/-- On the sixteen `I₀*` classes at `2`, Steps 1–5 succeed, Step 6's cubic is separable, and its
coefficients satisfy `b = c` on the `(I₀*, 2)` classes and `b ≠ c` on the `(I₀*, 1)` classes. -/
theorem izeroStar_step5_and_cubic {a₄ a₆ : ℤ_[2]}
    (hA : (PadicInt.toZModPow 4 a₄, PadicInt.toZModPow 4 a₆) ∈ headResiduesIZeroStar) :
    Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
        = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) ∧
      ¬ (stepSixCubicTwo a₄ a₆).HasDoubleRoot ∧
      ((PadicInt.toZModPow 4 a₄, PadicInt.toZModPow 4 a₆) ∈ headResiduesIZeroStarTwo →
        (stepSixCubicTwo a₄ a₆).b = (stepSixCubicTwo a₄ a₆).c) ∧
      ((PadicInt.toZModPow 4 a₄, PadicInt.toZModPow 4 a₆) ∈ headResiduesIZeroStarOne →
        (stepSixCubicTwo a₄ a₆).b ≠ (stepSixCubicTwo a₄ a₆).c) := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hp2 : (2 : ℕ) = 2 := rfl
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hcast]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, hV1⟩ : ∃ r t : ℤ_[2], Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔdvd⟩
  have hval := Step2.hasValuation_translate hΔdvd
  rw [hV1] at hs2 hval
  rw [stepSixCubicTwo_def, hV1]
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 2 * t := by
    rw [smul_ofShortNF_a₃]
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = a₄ + 3 * r ^ 2 := by
    rw [smul_ofShortNF_a₄]; ring
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆
      = a₆ + r * a₄ + r ^ 3 - t ^ 2 := by rw [smul_ofShortNF_a₆]
  have hm4 : (ZMod.cast (PadicInt.toZModPow 4 a₄ + 3 * PadicInt.toZModPow 4 r ^ 2)
      : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 4 a₄ + 3 * PadicInt.toZModPow 4 r ^ 2
        = PadicInt.toZModPow 4 (a₄ + 3 * r ^ 2) by rw [map_add, map_mul, map_pow, map_ofNat],
      PadicInt.cast_toZModPow 1 4 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    simpa only [hV1a₄, pow_one] using hval.a₄
  have hm6 : (ZMod.cast (PadicInt.toZModPow 4 a₆
      + PadicInt.toZModPow 4 r * PadicInt.toZModPow 4 a₄ + PadicInt.toZModPow 4 r ^ 3
        - PadicInt.toZModPow 4 t ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 4 a₆
          + PadicInt.toZModPow 4 r * PadicInt.toZModPow 4 a₄ + PadicInt.toZModPow 4 r ^ 3
            - PadicInt.toZModPow 4 t ^ 2 = PadicInt.toZModPow 4 (a₆ + r * a₄ + r ^ 3 - t ^ 2) by
        rw [map_sub, map_add, map_add, map_mul, map_pow, map_pow],
      PadicInt.cast_toZModPow 1 4 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    simpa only [hV1a₆, pow_one] using hval.a₆
  obtain ⟨k1, k2, k3⟩ := headResiduesIZeroStar_key _ hA (PadicInt.toZModPow 4 r)
    (PadicInt.toZModPow 4 t) hm4 hm6
  have hd4 : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a₄ + 3 * r ^ 2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 2 4 (by norm_num),
      map_add, map_mul, map_pow, map_ofNat]
    exact k1
  have hd6 : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 2 4 (by norm_num),
      map_sub, map_add, map_add, map_mul, map_pow, map_pow]
    exact k2
  have hdt : ((2 : ℕ) : ℤ_[2]) ∣ t := by
    rw [← pow_one (((2 : ℕ) : ℤ_[2])), PadicInt.pow_dvd_iff_toZModPow_eq_zero,
      ← PadicInt.cast_toZModPow 1 4 (by norm_num)]
    exact k3
  obtain ⟨P, hP⟩ := hd4
  obtain ⟨Q, hQ⟩ := hd6
  obtain ⟨τ, hτ⟩ := hdt
  rw [hcast] at hτ
  subst hτ
  have hP4 : a₄ + 3 * r ^ 2 = 4 * P := by rw [hP, hcast]; norm_num
  have hQ4 : a₆ + r * a₄ + r ^ 3 - (2 * τ) ^ 2 = 4 * Q := by rw [hQ, hcast]; norm_num
  have hs3 : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left (by rw [hV1a₆]; exact ⟨Q, hQ⟩)
  have hs4 : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * r * Q + 6 * r * τ ^ 2 - 2 * P ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hcast]
    linear_combination (12 * r) * hQ4 - (a₄ + 3 * r ^ 2 + 4 * P) * hP4
  have hs5 : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hcast]
    linear_combination 4 * hQ4
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[2],
      x = Step6.s ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆) :=
    ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[2],
      x = Step6.t ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆) :=
    ⟨_, rfl⟩
  have hV1a₆Q : ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆).a₆
      = ((2 : ℕ) : ℤ_[2]) ^ 2 * Q := by rw [hV1a₆, hQ]
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ_[2], s = 3 * r + 2 * σ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ s - 3 * r := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hcast] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨υ, hυ⟩ : ∃ υ : ℤ_[2], t₆ = Q + 2 * υ := by
    have h : ((2 : ℕ) : ℤ_[2]) ∣ t₆ - Q := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hV1a₆Q, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hcast] at hj
    exact ⟨j, by linear_combination hj⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[2], x = ((2 : ℕ) : ℤ_[2]) * t₆ + 2 * τ := ⟨_, rfl⟩
  have hV2 : Step6.translate ((2 : ℕ) : ℤ_[2])
        ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate ((2 : ℕ) : ℤ_[2])
          ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s (((2 : ℕ) : ℤ_[2]) * t₆))
          • ((VariableChange.mk 1 r 0 (2 * τ)) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  rw [hV2]
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂ = 3 * r - s ^ 2 := by
    rw [smul_ofShortNF_a₂]
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄
      = a₄ + 3 * r ^ 2 - 2 * s * T₂ := by rw [smul_ofShortNF_a₄]
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆
      = a₆ + r * a₄ + r ^ 3 - T₂ ^ 2 := by rw [smul_ofShortNF_a₆]
  have hv2 := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ hs5)
  rw [hV2] at hv2
  obtain ⟨X₂, hX₂⟩ := hv2.a₂
  obtain ⟨X₄, hX₄⟩ := hv2.a₄
  obtain ⟨X₆, hX₆⟩ := hv2.a₆
  rw [pow_one] at hX₂
  have hcb : (cubic ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod ((2 : ℕ) : ℤ_[2]) X₂ := by
    change mod ((2 : ℕ) : ℤ_[2])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂) ((2 : ℕ) : ℤ_[2])) = _
    rw [show ((2 : ℕ) : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 1 from (pow_one _).symm,
      div_eq_of_eq_pow_mul_two (by rw [hX₂, pow_one])]
  have hcc : (cubic ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod ((2 : ℕ) : ℤ_[2]) X₄ := by
    change mod ((2 : ℕ) : ℤ_[2])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄) (((2 : ℕ) : ℤ_[2]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hX₄]
  have hcd : (cubic ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod ((2 : ℕ) : ℤ_[2]) X₆ := by
    change mod ((2 : ℕ) : ℤ_[2])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆) (((2 : ℕ) : ℤ_[2]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hX₆]
  obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hcast r
  have hzz : (3 * r - s ^ 2) * (a₄ + 3 * r ^ 2 - 2 * s * T₂)
        - (a₆ + r * a₄ + r ^ 3 - T₂ ^ 2)
      = ((3 * r - 9 * r ^ 2) * (a₄ + 3 * r ^ 2 - 6 * r * (2 * Q + 2 * τ))
          - (a₆ + r * a₄ + r ^ 3 - (2 * Q + 2 * τ) ^ 2))
        + 16 * (-(3 * r * σ + σ ^ 2) * (P - s * (Q + 2 * υ + τ))
            - (6 * r - 9 * m) * (3 * r * υ + σ * (Q + τ) + 2 * σ * υ) + υ * (Q + τ) + υ ^ 2) := by
    rw [hT₂, hυ, hσ, hcast]
    linear_combination (-4 * (3 * r * σ + σ ^ 2)) * hP4
      + (72 * (3 * r * υ + σ * (Q + τ) + 2 * σ * υ)) * hm
  have hyy : 2 * (3 * r - s ^ 2) - (a₄ + 3 * r ^ 2 - 2 * s * T₂)
      = (2 * (3 * r - 9 * r ^ 2) - (a₄ + 3 * r ^ 2 - 6 * r * (2 * Q + 2 * τ)))
        + 8 * (-3 * r * σ - σ ^ 2 + 3 * r * υ + σ * Q + σ * τ + 2 * σ * υ) := by
    rw [hT₂, hυ, hσ, hcast]; ring
  have e2 : (3 : ℤ_[2]) * r - s ^ 2 = ((2 : ℕ) : ℤ_[2]) * X₂ := by rw [← hV2a₂, hX₂]
  have e4 : a₄ + 3 * r ^ 2 - 2 * s * T₂ = ((2 : ℕ) : ℤ_[2]) ^ 2 * X₄ := by rw [← hV2a₄, hX₄]
  have e6 : a₆ + r * a₄ + r ^ 3 - T₂ ^ 2 = ((2 : ℕ) : ℤ_[2]) ^ 3 * X₆ := by rw [← hV2a₆, hX₆]
  have hbz : (8 : ℤ_[2]) * (X₂ * X₄ - X₆)
      = (3 * r - s ^ 2) * (a₄ + 3 * r ^ 2 - 2 * s * T₂)
        - (a₆ + r * a₄ + r ^ 3 - T₂ ^ 2) := by rw [e2, e4, e6, hcast]; ring
  have hby : (4 : ℤ_[2]) * (X₂ - X₄)
      = 2 * (3 * r - s ^ 2) - (a₄ + 3 * r ^ 2 - 2 * s * T₂) := by rw [e2, e4, hcast]; ring
  have h4ne : (4 : ℤ_[2]) ≠ 0 := by
    rw [show (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 by rw [hcast]; norm_num]
    exact pow_ne_zero 2 hϖ
  have hQ16 : 4 * PadicInt.toZModPow 4 Q = PadicInt.toZModPow 4 a₆
      + PadicInt.toZModPow 4 r * PadicInt.toZModPow 4 a₄ + PadicInt.toZModPow 4 r ^ 3
        - (2 * PadicInt.toZModPow 4 τ) ^ 2 := by
    have h := congrArg (PadicInt.toZModPow 4) hQ4
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h
    linear_combination -h
  have hsep16 : ¬ ((2 : ℕ) : ℤ_[2]) ^ 4 ∣
      ((3 * r - 9 * r ^ 2) * (a₄ + 3 * r ^ 2 - 6 * r * (2 * Q + 2 * τ))
        - (a₆ + r * a₄ + r ^ 3 - (2 * Q + 2 * τ) ^ 2)) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    exact headResiduesIZeroStar_sep _ hA (PadicInt.toZModPow 4 r)
      (2 * PadicInt.toZModPow 4 τ) (PadicInt.toZModPow 4 Q) hm4 hQ16
  have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (X₂ * X₄ - X₆) := by
    intro hdvd
    obtain ⟨w, hw⟩ := hdvd
    have hw2 : X₂ * X₄ - X₆ = 2 * w := by rw [hw, hcast]
    refine hsep16 ⟨w - (-(3 * r * σ + σ ^ 2) * (P - s * (Q + 2 * υ + τ))
        - (6 * r - 9 * m) * (3 * r * υ + σ * (Q + τ) + 2 * σ * υ) + υ * (Q + τ) + υ ^ 2), ?_⟩
    rw [hcast]
    linear_combination -hzz - hbz + (8 : ℤ_[2]) * hw2
  refine ⟨hs5, ?_, ?_, ?_⟩
  · intro hdr
    have hdr' := (Cubic.hasDoubleRoot_of_a_eq_one
      (P := cubic ((2 : ℕ) : ℤ_[2]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1)
      rfl).1 hdr
    rw [hcb, hcc, hcd] at hdr'
    refine hnd ?_
    rw [← mod_eq_zero, map_sub, map_mul]
    have h2 : (2 : ℤ_[2] ⧸ Ideal.span {((2 : ℕ) : ℤ_[2])}) = 0 :=
      Step2.residue_two_eq_zero_of_eq_two hp2
    have hb := residue_sq_eq_self_two hp2 (mod ((2 : ℕ) : ℤ_[2]) X₂)
    have hc := residue_sq_eq_self_two hp2 (mod ((2 : ℕ) : ℤ_[2]) X₄)
    have hd := residue_sq_eq_self_two hp2 (mod ((2 : ℕ) : ℤ_[2]) X₆)
    linear_combination hdr' - (mod ((2 : ℕ) : ℤ_[2]) X₄) ^ 2 * hb
      - (mod ((2 : ℕ) : ℤ_[2]) X₂) * hc + 27 * hd
      + (2 * (mod ((2 : ℕ) : ℤ_[2]) X₄) ^ 3
        + 2 * (mod ((2 : ℕ) : ℤ_[2]) X₂) ^ 3 * (mod ((2 : ℕ) : ℤ_[2]) X₆)
        - 9 * (mod ((2 : ℕ) : ℤ_[2]) X₂) * (mod ((2 : ℕ) : ℤ_[2]) X₄)
            * (mod ((2 : ℕ) : ℤ_[2]) X₆)
        + 13 * (mod ((2 : ℕ) : ℤ_[2]) X₆)) * h2
  · intro hmem
    rw [hcb, hcc, ← sub_eq_zero, ← map_sub, mod_eq_zero]
    obtain ⟨u, hu⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ (2 * (3 * r - 9 * r ^ 2)
        - (a₄ + 3 * r ^ 2 - 6 * r * (2 * Q + 2 * τ))) := by
      rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, ← PadicInt.cast_toZModPow 3 4 (by norm_num)]
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      exact headResiduesIZeroStarTwo_beta _ hmem (PadicInt.toZModPow 4 r)
        (2 * PadicInt.toZModPow 4 τ) (PadicInt.toZModPow 4 Q) hm4 hQ16
    have hu8 : 2 * (3 * r - 9 * r ^ 2) - (a₄ + 3 * r ^ 2 - 6 * r * (2 * Q + 2 * τ))
        = 8 * u := by rw [hu, hcast]; norm_num
    refine ⟨u + (-3 * r * σ - σ ^ 2 + 3 * r * υ + σ * Q + σ * τ + 2 * σ * υ),
      mul_left_cancel₀ h4ne ?_⟩
    rw [hcast]
    linear_combination hby + hyy + hu8
  · intro hmem heq
    rw [hcb, hcc] at heq
    obtain ⟨u, hu⟩ : ((2 : ℕ) : ℤ_[2]) ∣ X₂ - X₄ := by
      rw [← mod_eq_zero, map_sub, heq, sub_self]
    have hu2 : X₂ - X₄ = 2 * u := by rw [hu, hcast]
    have hdv : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ (2 * (3 * r - 9 * r ^ 2)
        - (a₄ + 3 * r ^ 2 - 6 * r * (2 * Q + 2 * τ))) := by
      refine ⟨u - (-3 * r * σ - σ ^ 2 + 3 * r * υ + σ * Q + σ * τ + 2 * σ * υ), ?_⟩
      rw [hcast]
      linear_combination -hyy - hby + (4 : ℤ_[2]) * hu2
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero,
      ← PadicInt.cast_toZModPow 3 4 (by norm_num)] at hdv
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hdv
    exact headResiduesIZeroStarOne_beta _ hmem (PadicInt.toZModPow 4 r)
      (2 * PadicInt.toZModPow 4 τ) (PadicInt.toZModPow 4 Q) hm4 hQ16 hdv

open scoped Classical in
/-- **The forward run at `(I₀*, 2)`, at the prime `2`.** A short model over `ℤ_2` whose coefficient
pair reduces into `headResiduesIZeroStarTwo` modulo `16` has reduction datum exactly `(I₀*, 2)`. -/
theorem run_eq_I0star_two_two {a₄ a₆ : ℤ_[2]}
    (hA : (PadicInt.toZModPow 4 a₄, PadicInt.toZModPow 4 a₆) ∈ headResiduesIZeroStarTwo)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  obtain ⟨h5, hsep, hbc, -⟩ :=
    izeroStar_step5_and_cubic (headResiduesIZeroStarTwo_subset hA)
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_dvd hΔ h5 hsep
  refine ⟨hk, ?_⟩
  rw [ht, ← stepSixCubicTwo_def,
    card_roots_eq_one_two rfl (stepSixCubicTwo_a a₄ a₆) (hbc hA)]

open scoped Classical in
/-- **The forward run at `(I₀*, 1)`, at the prime `2`.** A short model over `ℤ_2` whose coefficient
pair reduces into `headResiduesIZeroStarOne` modulo `16` has reduction datum exactly `(I₀*, 1)`. -/
theorem run_eq_I0star_one_two {a₄ a₆ : ℤ_[2]}
    (hA : (PadicInt.toZModPow 4 a₄, PadicInt.toZModPow 4 a₆) ∈ headResiduesIZeroStarOne)
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  obtain ⟨h5, hsep, -, hbc⟩ :=
    izeroStar_step5_and_cubic (headResiduesIZeroStarOne_subset hA)
  obtain ⟨hk, ht⟩ := run_eq_I0star_of_not_hasDoubleRoot_of_dvd hΔ h5 hsep
  refine ⟨hk, ?_⟩
  rw [ht, ← stepSixCubicTwo_def,
    card_roots_eq_zero_two rfl (stepSixCubicTwo_a a₄ a₆) (hbc hA)
      fun h => hsep ((hasDoubleRoot_iff_two rfl (stepSixCubicTwo_a a₄ a₆)).2 h)]

/-! ### The two loci, their masses and their minimality -/

/-- The `(I₀*, 2)` locus at `2`: eight residue classes modulo `16`. -/
noncomputable def iZeroStarTwo2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 4 ⁻¹' (headResiduesIZeroStarTwo : Set (ZMod (2 ^ 4) × ZMod (2 ^ 4)))

/-- The `(I₀*, 1)` locus at `2`: eight residue classes modulo `16`. -/
noncomputable def iZeroStarOne2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 4 ⁻¹' (headResiduesIZeroStarOne : Set (ZMod (2 ^ 4) × ZMod (2 ^ 4)))

/-- Membership in the `(I₀*, 2)` locus is the mod-`16` congruence. -/
theorem mem_iZeroStarTwo2Locus_iff {x : ℤ_[2] × ℤ_[2]} : x ∈ iZeroStarTwo2Locus ↔
    (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2) ∈ headResiduesIZeroStarTwo := by
  rw [iZeroStarTwo2Locus, Set.mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- Membership in the `(I₀*, 1)` locus is the mod-`16` congruence. -/
theorem mem_iZeroStarOne2Locus_iff {x : ℤ_[2] × ℤ_[2]} : x ∈ iZeroStarOne2Locus ↔
    (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2) ∈ headResiduesIZeroStarOne := by
  rw [iZeroStarOne2Locus, Set.mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- `8 · 2⁻⁸ = 1/32` in `ℝ≥0∞`. -/
theorem eight_mul_inv_pow_eight_eq :
    ((8 : ℕ) : ℝ≥0∞) * (((2 : ℕ) : ℝ≥0∞)⁻¹) ^ (2 * 4) = 1 / 32 := by
  rw [← ENNReal.inv_pow, show (((2 : ℕ) : ℝ≥0∞)) ^ (2 * 4) = 256 by norm_num,
    ← div_eq_mul_inv, show ((8 : ℕ) : ℝ≥0∞) = 8 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the `(I₀*, 2)` locus at `2` is `8/256 = 1/32`.** -/
theorem volume_iZeroStarTwo2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iZeroStarTwo2Locus = 1 / 32 := by
  rw [iZeroStarTwo2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIZeroStarTwo,
    eight_mul_inv_pow_eight_eq]

/-- **The mass of the `(I₀*, 1)` locus at `2` is `8/256 = 1/32`.** -/
theorem volume_iZeroStarOne2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iZeroStarOne2Locus = 1 / 32 := by
  rw [iZeroStarOne2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesIZeroStarOne,
    eight_mul_inv_pow_eight_eq]

/-- **No point of the two `I₀*` loci is a `(2⁴, 2⁶)`-dilate**, since `a₆ ≢ 0` modulo `16` on all
sixteen classes. -/
theorem notMem_range_of_mem_izeroStar {x : ℤ_[2] × ℤ_[2]}
    (hx : (PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2) ∈ headResiduesIZeroStar) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_snd fun hdvd => ?_
  refine headResiduesIZeroStar_snd_ne_zero _ hx ?_
  rw [show ((PadicInt.toZModPow 4 x.1, PadicInt.toZModPow 4 x.2)).2
      = PadicInt.toZModPow 4 x.2 from rfl, ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact dvd_trans (pow_dvd_pow _ (by norm_num)) hdvd

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₀*, 2)` locus at `2` lies in the strata over `t = 2`.** -/
theorem iZeroStarTwo2Locus_subset_iUnion_stratFibre :
    iZeroStarTwo2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  have hA := mem_iZeroStarTwo2Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
    ofShortNF_Δ_ne_zero_izeroStar (headResiduesIZeroStarTwo_subset hA)
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_I0star_two_two hA hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The `(I₀*, 1)` locus at `2` lies in the strata over `t = 1`.** -/
theorem iZeroStarOne2Locus_subset_iUnion_stratFibre :
    iZeroStarOne2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) := by
  intro x hx
  have hA := mem_iZeroStarOne2Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 :=
    ofShortNF_Δ_ne_zero_izeroStar (headResiduesIZeroStarOne_subset hA)
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_I0star_one_two hA hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I! 0,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **The `(I₀*, 2)` locus lies in the minimal part of the `t = 2` row.** -/
theorem iZeroStarTwo2Locus_subset_headMinimal :
    iZeroStarTwo2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨iZeroStarTwo2Locus_subset_iUnion_stratFibre hx,
    notMem_range_of_mem_izeroStar
      (headResiduesIZeroStarTwo_subset (mem_iZeroStarTwo2Locus_iff.1 hx))⟩

/-- **The `(I₀*, 1)` locus lies in the minimal part of the `t = 1` row.** -/
theorem iZeroStarOne2Locus_subset_headMinimal :
    iZeroStarOne2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨iZeroStarOne2Locus_subset_iUnion_stratFibre hx,
    notMem_range_of_mem_izeroStar
      (headResiduesIZeroStarOne_subset (mem_iZeroStarOne2Locus_iff.1 hx))⟩

end WeierstrassCurve

end
