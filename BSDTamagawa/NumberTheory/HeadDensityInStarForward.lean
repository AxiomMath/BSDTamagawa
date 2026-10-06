/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep7

/-!
# The two exits of Step 7's `Iₙ*` subprocedure, as square tests

The subprocedure `WeierstrassCurve.TateAlgorithm.Step7.subprocedure` of Tate's algorithm exits
with a Tamagawa number read off from a root count over the residue field `R ⧸ span {ϖ}`:

  `if 0 < (quadratic ϖ W n).roots.toFinset.card then 4 else 2`             (odd exit, `I!(2n−3)`)
  `if 0 < (cubic ϖ (translateY ϖ W n) 0 n).roots.toFinset.card then 4 else 2`
                                                                          (even exit, `I!(2n−2)`)

Both tested polynomials are `Cubic` records with `a = 0`, namely
`quadratic ϖ W n = ⟨0, 1, a₃/ϖⁿ, −a₆/ϖ²ⁿ⟩` and `cubic ϖ W' 0 n = ⟨0, a₂/ϖ, a₄/ϖⁿ⁺¹, a₆/ϖ²ⁿ⁺¹⟩`,
the latter with nonzero leading coefficient since `¬ϖ² ∣ a₂`. Over a field with `2 ≠ 0`, a
quadratic `bx² + cx + d` with `b ≠ 0` has a root exactly when `c² − 4bd` is a square. Hence each
exit reports `4` or `2` according as a discriminant is a square or not, and the subprocedure's
Tamagawa number is always `2` or `4`.

## Main results

* `WeierstrassCurve.exists_quadratic_root_iff`: over a field with `2 ≠ 0`, `bx² + cx + d` with
  `b ≠ 0` has a root if and only if `c² − 4bd` is a square.
* `Cubic.card_roots_toFinset_pos_iff_isSquare`: a `Cubic` with `a = 0` and `b ≠ 0` has
  a root if and only if `c² − 4bd` is a square.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_tamagawaNumber_of_not_hasDoubleRoot`: at the
  odd exit, with `quadratic ϖ W n = ⟨0, 1, c, −d⟩`, the Tamagawa number is `4` if `c² + 4d` is a
  square and `2` otherwise.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_tamagawaNumber_of_not_hasDoubleRoot_cubic`:
  at the even exit, with `cubic ϖ (translateY ϖ W n) 0 n = ⟨0, b, c, d⟩`, the Tamagawa number is
  `4` if `c² − 4bd` is a square and `2` otherwise.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_tamagawaNumber_eq_two_or_four`: the Tamagawa
  number returned by the subprocedure is `2` or `4`.
-/

@[expose] public section

universe u

open CommRing Ideal

namespace WeierstrassCurve

/-! ### A quadratic over a field has a root exactly when its discriminant is a square -/

/-- Over a field with `2 ≠ 0` and `b ≠ 0`, the quadratic `bx² + cx + d` has a root if and only if
`c² − 4bd` is a square. -/
theorem exists_quadratic_root_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (c d : K) : (∃ x : K, b * x ^ 2 + c * x + d = 0) ↔ IsSquare (c ^ 2 - 4 * b * d) := by
  refine ⟨fun ⟨x, hx⟩ => ⟨2 * b * x + c, by linear_combination (-4 * b) * hx⟩,
    fun ⟨s, hs⟩ => ⟨(s - c) / (2 * b), ?_⟩⟩
  field_simp
  linear_combination -hs

open scoped Classical in
/-- A `Cubic` with nonzero associated polynomial has a nonempty root `Finset` if and only if it
has a root. -/
theorem _root_.Cubic.card_roots_toFinset_pos_iff_exists_root {K : Type*} [Field K] {P : Cubic K}
    (hP : P.toPoly ≠ 0) :
    0 < P.roots.toFinset.card ↔ ∃ x : K, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [Finset.card_pos]
  refine ⟨fun ⟨x, hx⟩ => ⟨x, (Cubic.mem_roots_iff hP x).1 (Multiset.mem_toFinset.1 hx)⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact ⟨x, Multiset.mem_toFinset.2 ((Cubic.mem_roots_iff hP x).2 hx)⟩

open scoped Classical in
/-- Over a field with `2 ≠ 0`, a `Cubic` `P` with `P.a = 0` and `P.b ≠ 0` has a nonempty root
`Finset` if and only if `P.c² − 4 P.b P.d` is a square. -/
theorem _root_.Cubic.card_roots_toFinset_pos_iff_isSquare {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {P : Cubic K} (ha : P.a = 0) (hb : P.b ≠ 0) :
    0 < P.roots.toFinset.card ↔ IsSquare (P.c ^ 2 - 4 * P.b * P.d) := by
  rw [Cubic.card_roots_toFinset_pos_iff_exists_root (Cubic.ne_zero_of_b_ne_zero hb),
    ← exists_quadratic_root_iff h2 hb P.c P.d]
  refine exists_congr fun x => ?_
  rw [ha]
  exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

namespace TateAlgorithm

namespace Step7

variable {R : Type u} [CommRing R] {ϖ : R}

variable [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] {W : WeierstrassCurve R} {n : ℕ}
  {b₂ b₄ b₆ b₈ c₄' c₆' Δv : ℕ}

variable [IsNoetherianRing R] [IsDomain R] (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (hn : 2 ≤ n)
  (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄', c₆', Δv⟩)
  (ha₂ : ¬ϖ ^ 2 ∣ W.a₂)

open scoped Classical in
/-- If `quadratic ϖ W n = ⟨0, 1, c, −d⟩` has no double root, then the Tamagawa number returned by
Step 7's subprocedure is `4` if `c² + 4d` is a square and `2` otherwise. -/
theorem subprocedure_tamagawaNumber_of_not_hasDoubleRoot (h2 : (2 : R ⧸ span {ϖ}) ≠ 0)
    {c d : R ⧸ span {ϖ}} (hquad : quadratic ϖ W n = ⟨0, 1, c, -d⟩)
    (hY : ¬(quadratic ϖ W n).HasDoubleRoot) :
    (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber =
      if IsSquare (c ^ 2 + 4 * d) then 4 else 2 := by
  have hiff : 0 < (quadratic ϖ W n).roots.toFinset.card ↔ IsSquare (c ^ 2 + 4 * d) := by
    rw [Cubic.card_roots_toFinset_pos_iff_isSquare h2 (P := quadratic ϖ W n) (by rw [hquad])
      (by rw [hquad]; exact one_ne_zero), hquad,
      show c ^ 2 - 4 * 1 * -d = c ^ 2 + 4 * d by ring]
  rw [subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY]
  exact if_congr hiff rfl rfl

open scoped Classical in
/-- If `quadratic ϖ W n` has a double root and `cubic ϖ (translateY ϖ W n) 0 n = ⟨0, b, c, d⟩`,
with `b ≠ 0`, does not, then the Tamagawa number returned by Step 7's subprocedure is `4` if
`c² − 4bd` is a square and `2` otherwise. -/
theorem subprocedure_tamagawaNumber_of_not_hasDoubleRoot_cubic (h2 : (2 : R ⧸ span {ϖ}) ≠ 0)
    {b c d : R ⧸ span {ϖ}} (hb : b ≠ 0)
    (hcub : cubic ϖ (translateY ϖ W n) 0 n = ⟨0, b, c, d⟩)
    (hY : (quadratic ϖ W n).HasDoubleRoot)
    (hX : ¬(cubic ϖ (translateY ϖ W n) 0 n).HasDoubleRoot) :
    (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber =
      if IsSquare (c ^ 2 - 4 * b * d) then 4 else 2 := by
  have hiff : 0 < (cubic ϖ (translateY ϖ W n) 0 n).roots.toFinset.card
      ↔ IsSquare (c ^ 2 - 4 * b * d) := by
    rw [Cubic.card_roots_toFinset_pos_iff_isSquare h2 (P := cubic ϖ (translateY ϖ W n) 0 n)
      (by rw [hcub]) (by rw [hcub]; exact hb), hcub]
  rw [subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX]
  exact if_congr hiff rfl rfl

/-- The Tamagawa number returned by Step 7's subprocedure is `2` or `4`. -/
theorem subprocedure_tamagawaNumber_eq_two_or_four :
    (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 2 ∨
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 4 := by
  fun_induction subprocedure with
  | case1 => assumption
  | case2 => split_ifs <;> simp
  | case3 => split_ifs <;> simp

end Step7

end TateAlgorithm

end WeierstrassCurve
