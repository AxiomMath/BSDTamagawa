/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono, Ashvin A. Swaminathan, David Kurniadi Angdinata, Sidharth Hariharan
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Separation.DisjointCover
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.TaylorSeries
public meta import BSDTamagawa.Attr

/-! # The definitions of this library

The objects the results of `BSDTamagawa` are stated in, collected in one module: short Weierstrass
models over `ℤ` and their height, Tate's algorithm, local reduction data and their densities, the
generating function, and the limiting densities, laws and moments. `Challenge/Basic.lean` repeats
these definitions verbatim, in the same order, so that both files compile them to the same
constants. Where it leaves a lemma open, this file proves it, together with the lemmas that proof
needs.

The law `marginalReductionOmegaPMF` is not here: the two lemmas it is built from are deep, and it
is defined in `BSDTamagawa.ReductionCount.MarginalMoments` after their proofs.
-/

@[expose] public section

/-! ## Short Weierstrass models over `ℤ` and their height -/

namespace WeierstrassCurve

/-- The short Weierstrass curve `y² = x³ + a₄x + a₆` over `R`. -/
abbrev ofShortNF {R : Type*} [CommRing R] (a₄ a₆ : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

/-- `ofShortNF a₄ a₆` is in short normal form. -/
theorem ofShortNF_isShortNF {R : Type*} [CommRing R] (a₄ a₆ : R) :
    (ofShortNF a₄ a₆).IsShortNF := ⟨rfl, rfl, rfl⟩

/-- The discriminant of the short model `y² = x³ + a₄ x + a₆` over any commutative ring:
`Δ = -16(4a₄³ + 27a₆²)`. -/
lemma ofShortNF_Δ {R : Type*} [CommRing R] (a₄ a₆ : R) :
    (ofShortNF a₄ a₆).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
  simp only [Δ, b₂, b₄, b₆, b₈]; ring

/-- The integer pairs `(a₄, a₆)` whose short Weierstrass curve is nonsingular, `Δ ≠ 0`. (Mathlib's
`IsElliptic` asks for `Δ` to be a unit, which never holds over `ℤ`.) -/
@[bsd_tamagawa "T001"]
def integralShortNFFamily : Set (ℤ × ℤ) :=
  { p | (ofShortNF p.1 p.2).Δ ≠ 0 }

/-- The naive height `H(a₄, a₆) = max(4|a₄|³, 27a₆²)`. -/
@[bsd_tamagawa "T002"]
def integralShortNFHeight (a₄ a₆ : ℤ) : ℤ :=
  max (4 * (a₄.natAbs : ℤ) ^ 3) (27 * a₆ ^ 2)

/-- `N(X)`, the number of integer pairs `(a₄, a₆)` with `Δ ≠ 0` and height at most `X`. -/
@[bsd_tamagawa "T003"]
noncomputable def integralShortNFCount (X : ℝ) : ℕ :=
  { p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X
                  ∧ p ∈ integralShortNFFamily }.ncard

end WeierstrassCurve

/-! ## The singular point of a singular Weierstrass curve -/

section

open CharP

universe u

variable {R : Type u} [CommRing R] {F : Type u} [Field F]

namespace CharP

/-- The `p`-th root in a ring of characteristic `p`. -/
noncomputable abbrev root (p : ℕ) [ExpChar R p] (x : R) : R :=
  Function.invFun (frobenius R p) x

/-- The `p`-th root of `x` in a perfect ring of characteristic `p` has `p`-th power `x`. -/
@[simp]
lemma pow_root {p : ℕ} [ExpChar R p] [PerfectRing R p] (x : R) : root p x ^ p = x :=
  Function.rightInverse_invFun (surjective_frobenius R p) x

/-- In a perfect ring of characteristic `p`, the `p`-th root of `x ^ p` is `x`. -/
@[simp]
lemma root_pow {p : ℕ} [ExpChar R p] [PerfectRing R p] (x : R) : root p (x ^ p) = x :=
  Function.leftInverse_invFun (injective_frobenius R p) x

end CharP

namespace WeierstrassCurve

section CharTwo

variable [CharP R 2] {W : WeierstrassCurve R}

/-- In a reduced ring of characteristic `2`, `b₂ = 0` if and only if `a₁ = 0`. -/
@[simp]
lemma b₂_iff_a₁_eq_zero_of_char_two [IsReduced R] : W.b₂ = 0 ↔ W.a₁ = 0 := by
  simp [b₂_of_char_two]

/-- In a reduced ring of characteristic `2`, `c₄ = 0` if and only if `a₁ = 0`. -/
@[simp]
lemma c₄_iff_a₁_eq_zero_of_char_two [IsReduced R] : W.c₄ = 0 ↔ W.a₁ = 0 := by
  simp [c₄_of_char_two]

/-- In a reduced ring of characteristic `2`, `c₆ = 0` if and only if `a₁ = 0`. -/
@[simp]
lemma c₆_iff_a₁_eq_zero_of_char_two [IsReduced R] : W.c₆ = 0 ↔ W.a₁ = 0 := by
  simp [c₆_of_char_two]

/-- In a reduced ring of characteristic `2`, a singular Weierstrass curve with `a₁ = 0` has
`a₃ = 0`. -/
@[simp]
lemma a₃_of_a₁_eq_zero_of_char_two [IsReduced R] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) : W.a₃ = 0 := by
  simpa [Δ_of_char_two, ha₁] using hΔ

/-- In characteristic `2`, a Weierstrass curve with `a₁ = 0` has `b₄ = 0`. -/
@[simp]
lemma b₄_of_a₁_eq_zero_of_char_two (ha₁ : W.a₁ = 0) : W.b₄ = 0 := by
  simp [b₄_of_char_two, ha₁]

/-- In a reduced ring of characteristic `2`, a singular Weierstrass curve with `a₁ = 0` has
`b₆ = 0`. -/
@[simp]
lemma b₆_of_a₁_eq_zero_of_char_two [IsReduced R] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) : W.b₆ = 0 := by
  simp [b₆_of_char_two, a₃_of_a₁_eq_zero_of_char_two hΔ, ha₁]

/-- In a reduced ring of characteristic `2`, a singular Weierstrass curve with `a₁ = 0` has
`b₈ = a₄²`. -/
@[simp]
lemma b₈_of_a₁_eq_zero_of_char_two [IsReduced R] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) :
    W.b₈ = W.a₄ ^ 2 := by
  simp [b₈_of_char_two, a₃_of_a₁_eq_zero_of_char_two hΔ, ha₁]

end CharTwo

section CharThree

variable [CharP R 3] {W : WeierstrassCurve R}

/-- In a reduced ring of characteristic `3`, `c₄ = 0` if and only if `b₂ = 0`. -/
@[simp]
lemma c₄_iff_b₂_eq_zero_of_char_three [IsReduced R] : W.c₄ = 0 ↔ W.b₂ = 0 := by
  simp [c₄_of_char_three]

/-- In a reduced ring of characteristic `3`, `c₆ = 0` if and only if `b₂ = 0`. -/
@[simp]
lemma c₆_iff_b₂_eq_zero_of_char_three [IsReduced R] : W.c₆ = 0 ↔ W.b₂ = 0 := by
  simp [c₆_of_char_three]

/-- In an integral domain of characteristic `3`, a singular Weierstrass curve with `b₂ = 0` has
`b₄ = 0`. -/
@[simp]
lemma b₄_of_b₂_eq_zero_of_char_three [IsDomain R] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) :
    W.b₄ = 0 := by
  simpa [Δ_of_char_three, hb₂, show (8 : R) ≠ 0 by grind only] using hΔ

end CharThree

namespace Affine

variable {W : Affine R}

/-- The value of `W_X` at `(x, y)` is its value at the origin for the curve with `(x, y)` moved to
the origin. -/
lemma evalEval_polynomialX_eq_variableChange (x y : R) :
    W.polynomialX.evalEval x y = (VariableChange.mk 1 x 0 y • W).polynomialX.evalEval 0 0 := by
  simp_rw [evalEval_polynomialX, variableChange_a₄, inv_one, Units.val_one]
  ring1

/-- The value of `W_Y` at `(x, y)` is its value at the origin for the curve with `(x, y)` moved to
the origin. -/
lemma evalEval_polynomialY_eq_variableChange (x y : R) :
    W.polynomialY.evalEval x y = (VariableChange.mk 1 x 0 y • W).polynomialY.evalEval 0 0 := by
  simp_rw [Affine.evalEval_polynomialY, variableChange_a₃, inv_one, Units.val_one]
  ring1

variable (W) in
/-- A singular affine point of a Weierstrass curve `W` over a ring `R`. -/
@[ext]
structure SingularPoint where
  /-- The `X`-coordinate of `P`. -/
  x : R
  /-- The `Y`-coordinate of `P`. -/
  y : R
  /-- The proposition that `W(X, Y)` vanishes on `P`. -/
  equation : W.Equation x y
  /-- The proposition that `W_X(X, Y)` vanishes on `P`. -/
  equationX : W.polynomialX.evalEval x y = 0
  /-- The proposition that `W_Y(X, Y)` vanishes on `P`. -/
  equationY : W.polynomialY.evalEval x y = 0

namespace SingularPoint

/-- Translating a singular point `P` to the origin gives a curve with `a₃ = 0`. -/
lemma variableChange_a₃ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).a₃ = 0 := by
  rcases P with ⟨_, _, _, _, hy⟩
  rwa [evalEval_polynomialY_eq_variableChange, evalEval_polynomialY_zero] at hy

/-- Translating a singular point `P` to the origin gives a curve with `a₄ = 0`. -/
lemma variableChange_a₄ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).a₄ = 0 := by
  rcases P with ⟨_, _, _, hx⟩
  rwa [evalEval_polynomialX_eq_variableChange, evalEval_polynomialX_zero, neg_eq_zero] at hx

/-- Translating a singular point `P` to the origin gives a curve with `a₆ = 0`. -/
lemma variableChange_a₆ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).a₆ = 0 := by
  rcases P with ⟨_, _, h⟩
  rwa [equation_iff_variableChange, equation_zero] at h

/-- Translating a singular point `P` to the origin gives a curve with `b₄ = 0`. -/
lemma variableChange_b₄ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).b₄ = 0 := by
  simp [b₄, variableChange_a₃, variableChange_a₄]

/-- Translating a singular point `P` to the origin gives a curve with `b₆ = 0`. -/
lemma variableChange_b₆ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).b₆ = 0 := by
  simp [b₆, variableChange_a₃, variableChange_a₆]

/-- Translating a singular point `P` to the origin gives a curve with `b₈ = 0`. -/
lemma variableChange_b₈ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).b₈ = 0 := by
  simp [b₈, variableChange_a₃, variableChange_a₄, variableChange_a₆]

/-- Translating a singular point `P` to the origin gives a curve with `Δ = 0`. -/
lemma variableChange_Δ (P : W.SingularPoint) : (VariableChange.mk 1 P.x 0 P.y • W).Δ = 0 := by
  simp [Δ, variableChange_b₄, variableChange_b₆, variableChange_b₈]

/-- The `X`-coordinate of a singular point is a root of the `2`-torsion polynomial
`4X³ + b₂X² + 2b₄X + b₆`. -/
lemma eval_twoTorsionPolynomial (P : W.SingularPoint) :
    4 * P.x ^ 3 + W.b₂ * P.x ^ 2 + 2 * W.b₄ * P.x + W.b₆ = 0 := by
  rcases P; grind only [equation_iff, equationY, evalEval_polynomialY, b₂, b₄, b₆]

/-- The `X`-coordinate of a singular point is a root of `6X² + b₂X + b₄`, half the derivative of
the `2`-torsion polynomial. -/
lemma eval_derivative_twoTorsionPolynomial (P : W.SingularPoint) :
    6 * P.x ^ 2 + W.b₂ * P.x + W.b₄ = 0 := by
  grind only [equationX, evalEval_polynomialX, equationY, evalEval_polynomialY, b₂, b₄]

section CharTwo

variable [CharP R 2]

/-- In characteristic `2`, a singular point of a curve with `a₁ = 0` has `x² = a₄`. -/
lemma x_pow_of_char_two (ha₁ : W.a₁ = 0) (P : W.SingularPoint) : P.x ^ 2 = W.a₄ := by
  grind only [equationX, evalEval_polynomialX]

/-- In a perfect ring of characteristic `2`, a singular point of a curve with `a₁ = 0` has
`x = root 2 a₄`. -/
@[simp]
lemma x_of_char_two [PerfectRing R 2] (ha₁ : W.a₁ = 0) (P : W.SingularPoint) : P.x = root 2 W.a₄ :=
  injective_frobenius R 2 <| by simp [frobenius_def, P.x_pow_of_char_two ha₁]

variable [IsReduced R]

/-- In a reduced ring of characteristic `2`, a singular point of a singular curve with `a₁ = 0` has
`y² = a₂a₄ + a₆`. -/
lemma y_pow_of_char_two (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) (P : W.SingularPoint) :
    P.y ^ 2 = W.a₂ * W.a₄ + W.a₆ := by
  grind only [equation, equation_iff, P.x_pow_of_char_two, a₃_of_a₁_eq_zero_of_char_two]

/-- In a perfect reduced ring of characteristic `2`, a singular point of a singular curve with
`a₁ = 0` has `y = root 2 (a₂a₄ + a₆)`. -/
@[simp]
lemma y_of_char_two [PerfectRing R 2] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) (P : W.SingularPoint) :
    P.y = root 2 (W.a₂ * W.a₄ + W.a₆) :=
  injective_frobenius R 2 <| by simp [-map_add, frobenius_def, P.y_pow_of_char_two hΔ ha₁]

/-- A Weierstrass curve `W` over a perfect reduced ring of characteristic `2` that is singular
(`W.Δ = 0`) and cuspidal (`W.a₁ = 0`) has a unique singular affine point. -/
noncomputable abbrev uniqueOfCharTwo [PerfectRing R 2] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) :
    Unique W.SingularPoint where
  default :=
    { x := root 2 W.a₄
      y := root 2 <| W.a₂ * W.a₄ + W.a₆
      equation := injective_frobenius R 2 <| by
        grind -abstractProof only [evalEval_polynomial, pow_root,
          a₃_of_a₁_eq_zero_of_char_two hΔ ha₁]
      equationX := by grind -abstractProof only [evalEval_polynomialX, pow_root]
      equationY := by
        grind -abstractProof only [evalEval_polynomialY, a₃_of_a₁_eq_zero_of_char_two hΔ ha₁] }
  uniq P := by
    have hx := P.x_of_char_two ha₁
    have hy := P.y_of_char_two hΔ ha₁
    cases P
    dsimp only at hx hy
    subst hx hy
    rfl

end CharTwo

section CharThree

variable [IsDomain R] [CharP R 3]

/-- In an integral domain of characteristic `3`, a singular point of a singular curve with `b₂ = 0`
has `x³ = -b₆`. -/
lemma x_pow_of_char_three (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) (P : W.SingularPoint) :
    P.x ^ 3 = -W.b₆ := by
  grind only [P.eval_twoTorsionPolynomial, b₄_of_b₂_eq_zero_of_char_three hΔ hb₂]

/-- In an integral domain of characteristic `3`, a singular point of a singular curve with `b₂ = 0`
has `y³ = a₃³ - a₁³b₆`. -/
lemma y_pow_of_char_three (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) (P : W.SingularPoint) :
    P.y ^ 3 = W.a₃ ^ 3 - W.a₁ ^ 3 * W.b₆ := by
  grind only [equationY, evalEval_polynomialY, P.x_pow_of_char_three hΔ hb₂]

/-- In a perfect integral domain of characteristic `3`, a singular point of a singular curve with
`b₂ = 0` has `x = -root 3 b₆`. -/
@[simp]
lemma x_of_char_three [PerfectRing R 3] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) (P : W.SingularPoint) :
    P.x = -root 3 W.b₆ :=
  injective_frobenius R 3 <| by simp [map_neg, frobenius_def, P.x_pow_of_char_three hΔ hb₂]

/-- In a perfect integral domain of characteristic `3`, a singular point of a singular curve with
`b₂ = 0` has `y = a₃ - a₁ root 3 b₆`. -/
@[simp]
lemma y_of_char_three [PerfectRing R 3] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) (P : W.SingularPoint) :
    P.y = W.a₃ - W.a₁ * root 3 W.b₆ :=
  injective_frobenius R 3 <| by
    simp [frobenius_def, sub_pow_char, mul_pow, P.y_pow_of_char_three hΔ hb₂]

/-- A Weierstrass curve `W` over a perfect integral domain of characteristic `3` that is singular
(`W.Δ = 0`) and cuspidal (`W.b₂ = 0`) has a unique singular affine point. -/
noncomputable abbrev uniqueOfCharThree [PerfectRing R 3] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) :
    Unique W.SingularPoint where
  default :=
    { x := -root 3 W.b₆
      y := W.a₃ - W.a₁ * root 3 W.b₆
      equation := injective_frobenius R 3 <| by
        grind -abstractProof only [evalEval_polynomial, pow_root, b₂, b₄, b₆,
          b₄_of_b₂_eq_zero_of_char_three hΔ hb₂]
      equationX := by grind -abstractProof only [evalEval_polynomialX, b₂, b₄,
        b₄_of_b₂_eq_zero_of_char_three hΔ hb₂]
      equationY := by grind -abstractProof only [evalEval_polynomialY, b₂] }
  uniq P := by
    have hx := P.x_of_char_three hΔ hb₂
    have hy := P.y_of_char_three hΔ hb₂
    cases P
    dsimp only at hx hy
    subst hx hy
    rfl

end CharThree

section C₄EqZero

variable {W : Affine F}

/-- Over a field of characteristic different from `2` and `3`, a singular point of a curve with
`c₄ = 0` has `x = -b₂/12`. -/
@[simp]
lemma x_of_c₄_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hc₄ : W.c₄ = 0) (P : W.SingularPoint) :
    P.x = -W.b₂ / 12 := by
  rw [show (12 : F) = 2 * (2 * 3) by norm_num1]
  exact @quadratic_eq_zero_iff_of_discrim_eq_zero _ _ ⟨h2⟩ _ _ W.b₄ (mul_ne_zero h2 h3)
    (by grind only [discrim, c₄]) _ |>.mp <| by grind only [P.eval_derivative_twoTorsionPolynomial]

/-- Over a field of characteristic different from `2` and `3`, a singular point of a curve with
`c₄ = 0` has `y = (a₁b₂ - 12a₃)/24`. -/
@[simp]
lemma y_of_c₄_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hc₄ : W.c₄ = 0) (P : W.SingularPoint) :
    P.y = (W.a₁ * b₂ W - 12 * W.a₃) / 24 := by
  have : (12 : F) ≠ 0 := by convert mul_ne_zero h3 (pow_ne_zero 2 h2); norm_num1
  have : (24 : F) ≠ 0 := by convert mul_ne_zero h2 this; norm_num1
  grind only [equationY, evalEval_polynomialY, P.x_of_c₄_eq_zero h2 h3 hc₄]

/-- A Weierstrass curve `W` over a field of characteristic different from `2` and `3` that is
singular (`W.Δ = 0`) and cuspidal (`W.c₄ = 0`) has a unique singular affine point. -/
abbrev uniqueOfC₄EqZero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    Unique W.SingularPoint where
  default :=
    have : (12 : F) ≠ 0 := by convert mul_ne_zero h3 (pow_ne_zero 2 h2); norm_num1
    have : (24 : F) ≠ 0 := by convert mul_ne_zero h2 this; norm_num1
    { x := -W.b₂ / 12
      y := (W.a₁ * W.b₂ - 12 * W.a₃) / 24
      equation := equation_iff .. |>.mpr <| by
        field_simp; grind -abstractProof only [b₂, b₄, b₆, b₈, c₄, Δ]
      equationX := by simp only [b₂, b₄, c₄] at *; grind -abstractProof only [evalEval_polynomialX]
      equationY := by grind -abstractProof only [evalEval_polynomialY, c₄] }
  uniq P := by
    have hx := P.x_of_c₄_eq_zero h2 h3 hc₄
    have hy := P.y_of_c₄_eq_zero h2 h3 hc₄
    cases P
    dsimp only at hx hy
    subst hx hy
    rfl

end C₄EqZero

section C₄NeZero

/-- A singular point satisfies `x c₄ = 18b₆ - b₂b₄`. -/
lemma x_mul (P : W.SingularPoint) : P.x * W.c₄ = 18 * W.b₆ - W.b₂ * W.b₄ := by
  grind only [P.eval_twoTorsionPolynomial, P.eval_derivative_twoTorsionPolynomial, c₄]

/-- In characteristic `2`, a singular point satisfies `y b₂³ = a₁³(b₂a₄ + b₆)`. -/
lemma y_mul_of_char_two [CharP R 2] (P : W.SingularPoint) :
    P.y * W.b₂ ^ 3 = W.a₁ ^ 3 * (W.b₂ * W.a₄ + W.b₆) := by
  grind only [equationX, evalEval_polynomialX, P.x_mul, b₂, b₄, b₆, c₄]

/-- A singular point satisfies `2y c₄ = a₁(b₂b₄ - 18b₆) - a₃c₄`. -/
lemma y_mul (P : W.SingularPoint) :
    P.y * (2 * W.c₄) = W.a₁ * (W.b₂ * W.b₄ - 18 * W.b₆) - W.a₃ * W.c₄ := by
  grind only [equationY, evalEval_polynomialY, P.x_mul]

variable {W : Affine F}

/-- Over a field, a singular point of a curve with `c₄ ≠ 0` has `x = (18b₆ - b₂b₄)/c₄`. -/
@[simp]
lemma x_of_c₄_ne_zero (hc₄ : W.c₄ ≠ 0) (P : W.SingularPoint) :
    P.x = (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄ :=
  eq_div_of_mul_eq hc₄ P.x_mul

/-- Over a field, a singular point of a curve with `c₄ ≠ 0` has
`y = (a₁a₄b₂ - 2a₂a₃b₂ + 12a₃b₄ - 9a₁b₆)/c₄`. -/
@[simp]
lemma y_of_c₄_ne_zero (hc₄ : W.c₄ ≠ 0) (P : W.SingularPoint) : P.y =
    (W.a₁ * W.a₄ * W.b₂ - 2 * W.a₂ * W.a₃ * W.b₂ + 12 * W.a₃ * W.b₄ - 9 * W.a₁ * W.b₆) / W.c₄ :=
  eq_div_of_mul_eq hc₄ <| by
    by_cases h2 : (2 : F) = 0
    · have : CharP F 2 := (charP_iff_prime_eq_zero <| by decide).mpr h2
      grind only [y_mul_of_char_two, b₂, c₄]
    · grind only [y_mul, b₂, b₄, c₄]

/-- A Weierstrass curve `W` over a field that is singular (`W.Δ = 0`) and nodal (`W.c₄ ≠ 0`) has a
unique singular affine point. -/
abbrev uniqueOfC₄NeZero (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) : Unique W.SingularPoint where
  default :=
    { x := (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄
      y := (W.a₁ * W.a₄ * W.b₂ - 2 * W.a₂ * W.a₃ * W.b₂ + 12 * W.a₃ * W.b₄ - 9 * W.a₁ * W.b₆) / W.c₄
      equation := by
        simp only [b₂, b₄, b₆, b₈, c₄, Δ] at *; grind -abstractProof only [equation_iff]
      equationX := by
        simp only [b₂, b₄, b₆, b₈, c₄, Δ] at *; grind -abstractProof only [evalEval_polynomialX]
      equationY := by grind -abstractProof only [evalEval_polynomialY, b₂, b₄, c₄] }
  uniq P := by
    have hx := P.x_of_c₄_ne_zero hc₄
    have hy := P.y_of_c₄_ne_zero hc₄
    cases P
    dsimp only at hx hy
    subst hx hy
    rfl

end C₄NeZero

open scoped Classical in
/-- A Weierstrass curve `W` over a field that is singular (`W.Δ = 0`) has a unique singular affine
point. -/
noncomputable abbrev unique {W : Affine F} [PerfectField F] (hΔ : W.Δ = 0) :
    Unique W.SingularPoint :=
  if hc₄ : W.c₄ = 0 then
    if h2 : (2 : F) = 0 then
      have : CharP F 2 := (charP_iff_prime_eq_zero <| by decide).mpr h2
      uniqueOfCharTwo hΔ <| c₄_iff_a₁_eq_zero_of_char_two.mp hc₄
    else if h3 : (3 : F) = 0 then
      have : CharP F 3 := (charP_iff_prime_eq_zero <| by decide).mpr h3
      uniqueOfCharThree hΔ <| c₄_iff_b₂_eq_zero_of_char_three.mp hc₄
    else uniqueOfC₄EqZero h2 h3 hΔ hc₄
  else uniqueOfC₄NeZero hΔ hc₄

end SingularPoint

end Affine

end WeierstrassCurve

end

/-! ## Basic lemmas for Tate's algorithm -/

section

attribute [grind =] inv_one Units.val_one
attribute [instance] Ideal.Quotient.field

universe u

variable {R : Type u} [CommRing R]

namespace Except

/-- `x >>= f = ok y` if and only if `x = ok a` and `f a = ok y` for some `a`. -/
lemma bind_eq_ok_iff {ε α β : Type u} {x : Except ε α} {f : α → Except ε β} {y : β} :
    x >>= f = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  rcases x with _ | a
  · simp_rw [reduceCtorEq, false_and, exists_false, iff_false]
    intro
    contradiction
  · exact ⟨fun h ↦ ⟨a, rfl, h⟩, fun ⟨a, ha, hy⟩ ↦ by simpa [ha]⟩

end Except

section Dvd

/-- If `cᵐ ∣ a` and `cⁿ ∣ b`, then `c ^ min m n ∣ a - b`. -/
lemma min_pow_dvd_sub {a b c : R} {m n : ℕ} (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) :
    c ^ min m n ∣ a - b :=
  (pow_dvd_pow c <| m.min_le_left n).trans ha |>.sub <| (pow_dvd_pow c <| m.min_le_right n).trans hb

/-- If `aⁿ ∣ b` with `n ≠ 0`, then `a ∣ b`. -/
lemma pow_dvd {a b : R} {n : ℕ} (hn : n ≠ 0) (ha : a ^ n ∣ b) : a ∣ b :=
  dvd_pow_self a hn |>.trans ha

alias Dvd.dvd.add_left := dvd_add_left
alias Dvd.dvd.add_right := dvd_add_right
alias Dvd.dvd.min_add := min_pow_dvd_add
alias Dvd.dvd.sub_left := dvd_sub_left
alias Dvd.dvd.sub_right := dvd_sub_right
alias Dvd.dvd.min_sub := min_pow_dvd_sub
alias Dvd.dvd.mul := mul_dvd_mul
alias Dvd.dvd.mul_left' := mul_dvd_mul_left
alias Dvd.dvd.mul_right' := mul_dvd_mul_right
alias Dvd.dvd.of_pow := pow_dvd
alias Dvd.dvd.pow' := pow_dvd_pow_of_dvd

/-- For `ϖ ≠ 0` in a ring without zero divisors, `ϖⁿ⁺¹ ∣ ϖⁿx` if and only if `ϖ ∣ x`. -/
lemma pow_succ_dvd_pow_mul [NoZeroDivisors R] {ϖ : R} (hϖ : ϖ ≠ 0) {x : R} (n : ℕ) :
    ϖ ^ (n + 1) ∣ ϖ ^ n * x ↔ ϖ ∣ x := by
  rw [pow_succ, mul_dvd_mul_iff_left <| pow_ne_zero n hϖ]

/-- For a prime `ϖ`, `ϖ² ∣ x` if and only if `ϖ³ ∣ x²`. -/
lemma sq_dvd_iff_cb_dvd_sq [NoZeroDivisors R] {ϖ : R} (hϖ : Prime ϖ) {x : R} :
    ϖ ^ 2 ∣ x ↔ ϖ ^ 3 ∣ x ^ 2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert h.mul (pow_dvd two_ne_zero h) <;> ring1
  · rcases hϖ.dvd_of_dvd_pow <| h.of_pow three_ne_zero with ⟨x, rfl⟩
    rw [mul_pow, pow_succ_dvd_pow_mul hϖ.ne_zero, hϖ.dvd_pow_iff_dvd two_ne_zero] at h
    exact ⟨h.choose, by grind⟩

end Dvd

namespace CommRing

/-- The canonical surjection from a commutative ring to its residue field at a prime. -/
def mod (ϖ : R) : R →+* R ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.mk _

/-- The image of `ϖ` in `R ⧸ (ϖ)` is zero. -/
@[simp]
lemma mod_self (ϖ : R) : mod ϖ ϖ = 0 :=
  Ideal.Quotient.mk_singleton_self ϖ

/-- The image of `x` in `R ⧸ (ϖ)` is zero if and only if `ϖ ∣ x`. -/
@[simp]
lemma mod_eq_zero (ϖ x : R) : mod ϖ x = 0 ↔ ϖ ∣ x :=
  Ideal.Quotient.eq_zero_iff_dvd ..

/-- The image in `R ⧸ (ϖ)` of a chosen representative of `x` is `x`. -/
@[simp]
lemma mod_out {ϖ : R} (x : R ⧸ Ideal.span {ϖ}) : mod ϖ x.out = x :=
  Ideal.Quotient.mk_out x

open scoped Classical in
/-- A better abbreviation for `IsDiscreteValuationRing.quotient`. -/
noncomputable def div (x y : R) : R :=
  if y = 0 then 0 else if h : y ∣ x then h.choose else 0

/-- If `ϖ ≠ 0` divides `x`, then `ϖ * (x / ϖ) = x`. -/
@[simp]
lemma mul_div {ϖ x : R} (hϖ : ϖ ≠ 0) (hx : ϖ ∣ x) : ϖ * div x ϖ = x := by
  rw [div, ite_eq_right hϖ, dite_eq_left hx, ← hx.choose_spec]

/-- If `ϖ ≠ 0` divides `x`, then `(x / ϖ) * ϖ = x`. -/
@[simp]
lemma div_mul {ϖ x : R} (hϖ : ϖ ≠ 0) (hx : ϖ ∣ x) : div x ϖ * ϖ = x := by
  rw [mul_comm, mul_div hϖ hx]

variable [NoZeroDivisors R]

/-- If `ϖ ≠ 0` divides `x` and `y`, then `(x + y) / ϖ = x / ϖ + y / ϖ`. -/
@[simp]
lemma div_add {ϖ x y : R} (hϖ : ϖ ≠ 0) (hx : ϖ ∣ x) (hy : ϖ ∣ y) :
    div (x + y) ϖ = div x ϖ + div y ϖ := by
  rw [← mul_right_inj' hϖ, mul_div hϖ <| hx.add hy, mul_add, mul_div hϖ hx, mul_div hϖ hy]

/-- If `ϖ ≠ 0` divides `x` and `y`, then `(x - y) / ϖ = x / ϖ - y / ϖ`. -/
@[simp]
lemma div_sub {ϖ x y : R} (hϖ : ϖ ≠ 0) (hx : ϖ ∣ x) (hy : ϖ ∣ y) :
    div (x - y) ϖ = div x ϖ - div y ϖ := by
  rw [← mul_right_inj' hϖ, mul_div hϖ <| hx.sub hy, mul_sub, mul_div hϖ hx, mul_div hϖ hy]

/-- If `ϖ ≠ 0` divides `y`, then `(x * y) / ϖ = x * (y / ϖ)`. -/
@[simp]
lemma div_mul_left {ϖ x y : R} (hϖ : ϖ ≠ 0) (hy : ϖ ∣ y) : div (x * y) ϖ = x * div y ϖ := by
  rw [← mul_left_inj' hϖ, div_mul hϖ <| hy.mul_left _, mul_assoc, div_mul hϖ hy]

/-- If `ϖ ≠ 0` divides `x`, then `(x * y) / ϖ = (x / ϖ) * y`. -/
@[simp]
lemma div_mul_right {ϖ x y : R} (hϖ : ϖ ≠ 0) (hx : ϖ ∣ x) : div (x * y) ϖ = div x ϖ * y := by
  rw [← mul_right_inj' hϖ, mul_div hϖ <| hx.mul_right _, ← mul_assoc, mul_div hϖ hx]

/-- For `n ≠ 0`, `xᵐ⁺ⁿ ∣ y` if and only if `xⁿ ∣ y` and `xᵐ ∣ y / xⁿ`. -/
@[simp]
lemma pow_add_dvd {x y : R} {m n : ℕ} (hn : n ≠ 0) :
    x ^ (m + n) ∣ y ↔ x ^ n ∣ y ∧ x ^ m ∣ div y (x ^ n) := by
  by_cases hx : x = 0
  · simp_all [div]
  · rw [pow_add, div, ite_eq_right <| pow_ne_zero n hx]
    refine ⟨fun h ↦ ⟨dvd_of_mul_left_dvd h, ?_⟩, fun ⟨h, z, _⟩ ↦ ⟨z, by grind only [h.choose_spec]⟩⟩
    rw [dite_eq_left <| dvd_of_mul_left_dvd h, ← mul_dvd_mul_iff_left <| pow_ne_zero n hx]
    exact ⟨h.choose, by grind⟩

/-- For `n ≠ 0`, `xⁿ⁺¹ ∣ y` if and only if `xⁿ ∣ y` and `x ∣ y / xⁿ`. -/
@[simp]
lemma pow_succ_dvd {x y : R} {n : ℕ} (hn : n ≠ 0) :
    x ^ (n + 1) ∣ y ↔ x ^ n ∣ y ∧ x ∣ div y (x ^ n) := by
  rw [add_comm]
  nth_rw 3 [← pow_one x]
  exact pow_add_dvd hn

/-- `x² ∣ y` if and only if `x ∣ y` and `x ∣ y / x`. -/
lemma sq_dvd {x y : R} : x ^ 2 ∣ y ↔ x ∣ y ∧ x ∣ div y x := by
  simp

end CommRing

namespace Cubic

/-- The proposition that a cubic has a double root. -/
def HasDoubleRoot (P : Cubic R) : Prop :=
  P.discr = 0

/-- A monic cubic `X³ + bX² + cX + d` has a double root if and only if
`b²c² = 4c³ + 4b³d + 27d² - 18bcd`. -/
lemma hasDoubleRoot_of_a_eq_one {P : Cubic R} (ha : P.a = 1) : P.HasDoubleRoot ↔ P.b ^ 2 * P.c ^ 2 =
    4 * P.c ^ 3 + 4 * P.b ^ 3 * P.d + 27 * P.d ^ 2 - 18 * P.b * P.c * P.d := by
  grind only [HasDoubleRoot, discr]

/-- A cubic `bX² + cX + d` with zero leading coefficient has a double root if and only if
`b²c² = 4b³d`. -/
lemma hasDoubleRoot_of_a_eq_zero {P : Cubic R} (ha : P.a = 0) :
    P.HasDoubleRoot ↔ P.b ^ 2 * P.c ^ 2 = 4 * P.b ^ 3 * P.d := by
  grind only [HasDoubleRoot, discr]

/-- A quadratic `X² + cX + d` has a double root if and only if `c² = 4d`. -/
lemma hasDoubleRoot_of_b_eq_one {P : Cubic R} (ha : P.a = 0) (hb : P.b = 1) :
    P.HasDoubleRoot ↔ P.c ^ 2 = 4 * P.d := by
  grind [HasDoubleRoot, discr]

/-- The proposition that a cubic has a triple root. -/
def HasTripleRoot (P : Cubic R) : Prop :=
  P.b ^ 2 = 3 * P.c

end Cubic

section Ideal

/-- A nonzero `ϖ` generating a maximal ideal is prime. -/
lemma Ideal.IsMaximal.prime {ϖ : R} [span {ϖ} |>.IsMaximal] (hϖ : ϖ ≠ 0) : Prime ϖ :=
  span_singleton_prime hϖ |>.mp <| isPrime' _

/-- If `(x)` is a proper ideal of a Noetherian domain, then `x` has finite multiplicity in `y` if
and only if `y ≠ 0`. -/
lemma FiniteMultiplicity.span_ne_top [IsNoetherianRing R] [IsDomain R] {x y : R}
    (h : Ideal.span {x} ≠ ⊤) : FiniteMultiplicity x y ↔ y ≠ 0 := by
  rw [iff_not_comm, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isDomain _ h, Ideal.mem_iInf]
  simp_rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, FiniteMultiplicity.not_iff_forall]

/-- If `(x)` is a proper ideal of a Noetherian domain, then the multiplicity of `x` in `y` is
infinite if and only if `y = 0`. -/
lemma emultiplicity_of_span_ne_top [IsNoetherianRing R] [IsDomain R] {x y : R}
    (h : Ideal.span {x} ≠ ⊤) : emultiplicity x y = ⊤ ↔ y = 0 := by
  rw [emultiplicity_eq_top, FiniteMultiplicity.span_ne_top h, not_not]

end Ideal

namespace WeierstrassCurve

variable {ϖ : R} {W : WeierstrassCurve R}

/-- If `ϖ` divides `a₁` and `a₂` to the powers `m₁` and `m₂`, it divides `b₂` to the power
`min (2m₁) m₂`. -/
lemma dvd_b₂ {a₁ a₂ : ℕ} (ha₁ : ϖ ^ a₁ ∣ W.a₁) (ha₂ : ϖ ^ a₂ ∣ W.a₂) : ϖ ^ min (2 * a₁) a₂ ∣ W.b₂ :=
  Dvd.dvd.min_add (by convert ha₁.pow' 2 using 1; ring1) <| ha₂.mul_left 4

/-- If `ϖ` divides `a₁`, `a₃` and `a₄` to the powers `m₁`, `m₃` and `m₄`, it divides `b₄` to the
power `min m₄ (m₁ + m₃)`. -/
lemma dvd_b₄ {a₁ a₃ a₄ : ℕ} (ha₁ : ϖ ^ a₁ ∣ W.a₁) (ha₃ : ϖ ^ a₃ ∣ W.a₃) (ha₄ : ϖ ^ a₄ ∣ W.a₄) :
    ϖ ^ min a₄ (a₁ + a₃) ∣ W.b₄ :=
  ha₄.mul_left 2 |>.min_add <| by convert ha₁.mul ha₃; ring1

/-- If `ϖ` divides `a₃` and `a₆` to the powers `m₃` and `m₆`, it divides `b₆` to the power
`min (2m₃) m₆`. -/
lemma dvd_b₆ {a₃ a₆ : ℕ} (ha₃ : ϖ ^ a₃ ∣ W.a₃) (ha₆ : ϖ ^ a₆ ∣ W.a₆) : ϖ ^ min (2 * a₃) a₆ ∣ W.b₆ :=
  Dvd.dvd.min_add (by convert ha₃.pow' 2 using 1; ring1) <| ha₆.mul_left 4

/-- If `ϖ` divides `a₁`, `a₂`, `a₃`, `a₄` and `a₆` to the powers `m₁`, `m₂`, `m₃`, `m₄` and `m₆`,
it divides `b₈` to the power the minimum of `2m₁ + m₆`, `m₂ + m₆`, `m₁ + m₃ + m₄`, `m₂ + 2m₃` and
`2m₄`. -/
lemma dvd_b₈ {a₁ a₂ a₃ a₄ a₆ : ℕ} (ha₁ : ϖ ^ a₁ ∣ W.a₁) (ha₂ : ϖ ^ a₂ ∣ W.a₂) (ha₃ : ϖ ^ a₃ ∣ W.a₃)
    (ha₄ : ϖ ^ a₄ ∣ W.a₄) (ha₆ : ϖ ^ a₆ ∣ W.a₆) : ϖ ^
    min (min (min (min (2 * a₁ + a₆) (a₂ + a₆)) (a₁ + a₃ + a₄)) (a₂ + 2 * a₃)) (2 * a₄) ∣ W.b₈ := by
  refine Dvd.dvd.min_add ?_ ?_ |>.min_sub ?_ |>.min_add ?_ |>.min_sub ?_
  · convert ha₁.pow' 2 |>.mul ha₆; ring1
  · convert ha₂.mul_left 4 |>.mul ha₆; ring1
  · convert ha₁.mul ha₃ |>.mul ha₄; ring1
  · convert ha₂.mul <| ha₃.pow' 2; ring1
  · convert ha₄.pow' 2 using 1; ring1

/-- If `ϖ` divides `b₂` and `b₄` to the powers `n₂` and `n₄`, it divides `c₄` to the power
`min (2n₂) n₄`. -/
lemma dvd_c₄ {b₂ b₄ : ℕ} (hb₂ : ϖ ^ b₂ ∣ W.b₂) (hb₄ : ϖ ^ b₄ ∣ W.b₄) : ϖ ^ min (2 * b₂) b₄ ∣ W.c₄ :=
  Dvd.dvd.min_sub (by convert hb₂.pow' 2 using 1; ring1) <| hb₄.mul_left 24

/-- If `ϖ` divides `b₂`, `b₄` and `b₆` to the powers `n₂`, `n₄` and `n₆`, it divides `c₆` to the
power the minimum of `3n₂`, `n₂ + n₄` and `n₆`. -/
lemma dvd_c₆ {b₂ b₄ b₆ : ℕ} (hb₂ : ϖ ^ b₂ ∣ W.b₂) (hb₄ : ϖ ^ b₄ ∣ W.b₄) (hb₆ : ϖ ^ b₆ ∣ W.b₆) :
    ϖ ^ min (min (3 * b₂) (b₂ + b₄)) b₆ ∣ W.c₆ := by
  refine (Dvd.dvd.neg_right ?_).min_add ?_ |>.min_sub <| hb₆.mul_left 216
  · convert hb₂.pow' 3 using 1; ring1
  · convert hb₂.mul_left 36 |>.mul hb₄; ring1

/-- If `ϖ` divides `b₂`, `b₄`, `b₆` and `b₈` to the powers `n₂`, `n₄`, `n₆` and `n₈`, it divides
`Δ` to the power the minimum of `2n₂ + n₈`, `3n₄`, `2n₆` and `n₂ + n₄ + n₆`. -/
lemma dvd_Δ {b₂ b₄ b₆ b₈ : ℕ} (hb₂ : ϖ ^ b₂ ∣ W.b₂) (hb₄ : ϖ ^ b₄ ∣ W.b₄) (hb₆ : ϖ ^ b₆ ∣ W.b₆)
    (hb₈ : ϖ ^ b₈ ∣ W.b₈) :
    ϖ ^ min (min (min (2 * b₂ + b₈) (3 * b₄)) (2 * b₆)) (b₂ + b₄ + b₆) ∣ W.Δ := by
  refine Dvd.dvd.min_sub ?_ ?_ |>.min_sub ?_ |>.min_add ?_
  · convert dvd_neg.mpr (hb₂.pow' 2) |>.mul hb₈; ring1
  · convert hb₄.pow' 3 |>.mul_left 8 using 1; ring1
  · convert hb₆.pow' 2 |>.mul_left 27 using 1; ring1
  · convert hb₂.mul_left 9 |>.mul hb₄ |>.mul hb₆; ring1

end WeierstrassCurve

end

/-! ## Kodaira symbols and the types of Tate's algorithm -/

section

open CommRing Ideal

universe u

variable {R : Type u} [CommRing R] {ϖ : R} {W : WeierstrassCurve R}

namespace WeierstrassCurve

/-- The Kodaira–Néron reduction type of the special fiber `C` of a Weierstrass curve. -/
inductive KodairaSymbol
  /-- `C` is a non-singular curve of genus one (`n = 0`), a rational curve with a node (`n = 1`),
    or consists of `n` non-singular rational curves arranged in the shape of an `n`-gon
    (`n ≥ 2`). -/
  | I (n : ℕ)
  /-- `C` is a rational curve with a cusp. -/
  | II
  /-- `C` consists of two non-singular rational curves which intersect tangentially at a single
    point. -/
  | III
  /-- `C` consists of three non-singular rational curves intersecting at a single point. -/
  | IV
  /-- `C` is a non-singular rational curve of multiplicity two with four non-singular rational
  curves of multiplicity one attached (`n = 0`), or consists of a chain of `n + 1` non-singular
  rational curves of multiplicity two with two non-singular rational curves of multiplicity one
  attached at either end (`n ≥ 1`). -/
  | I! (n : ℕ)
  /-- `C` consists of seven non-singular rational curves in a particular arrangement. -/
  | IV!
  /-- `C` consists of eight non-singular rational curves in a particular arrangement. -/
  | III!
  /-- `C` consists of nine non-singular rational curves in a particular arrangement. -/
  | II!

namespace TateAlgorithm

variable (R) in
/-- The output of Tate's algorithm to compute the special fiber of a Weierstrass curve `W`. -/
structure Output where
  /-- The Weierstrass curve after running (a step of) Tate's algorithm on `W`. -/
  weierstrassCurve : WeierstrassCurve R
  /-- The Kodaira–Néron reduction type of the special fiber of `W`. -/
  kodairaSymbol : KodairaSymbol
  /-- The Tamagawa number of `W`, which is equal to the number of components of the special fiber
  of `W` which have multiplicity one and are defined over the residue field. -/
  tamagawaNumber : ℕ

/-- A tuple recording the additive valuations of the coefficients of a Weierstrass curve `W`. -/
structure Valuation where
  /-- The valuation of the `a₁` coefficient of `W`. -/
  a₁ : ℕ
  /-- The valuation of the `a₂` coefficient of `W`. -/
  a₂ : ℕ
  /-- The valuation of the `a₃` coefficient of `W`. -/
  a₃ : ℕ
  /-- The valuation of the `a₄` coefficient of `W`. -/
  a₄ : ℕ
  /-- The valuation of the `a₆` coefficient of `W`. -/
  a₆ : ℕ
  /-- The valuation of the `b₂` coefficient of `W`. -/
  b₂ : ℕ
  /-- The valuation of the `b₄` coefficient of `W`. -/
  b₄ : ℕ
  /-- The valuation of the `b₆` coefficient of `W`. -/
  b₆ : ℕ
  /-- The valuation of the `b₈` coefficient of `W`. -/
  b₈ : ℕ
  /-- The valuation of the `c₄` coefficient of `W`. -/
  c₄ : ℕ
  /-- The valuation of the `c₆` coefficient of `W`. -/
  c₆ : ℕ
  /-- The valuation of the discriminant `Δ` of `W`. -/
  Δ : ℕ

variable (ϖ W) in
/-- The coefficients of `W` have `ϖ`-adic valuations at least those recorded in `v`. -/
structure HasValuation (v : Valuation) : Prop where
  a₁ : ϖ ^ v.a₁ ∣ W.a₁
  a₂ : ϖ ^ v.a₂ ∣ W.a₂
  a₃ : ϖ ^ v.a₃ ∣ W.a₃
  a₄ : ϖ ^ v.a₄ ∣ W.a₄
  a₆ : ϖ ^ v.a₆ ∣ W.a₆
  b₂ : ϖ ^ v.b₂ ∣ W.b₂
  b₄ : ϖ ^ v.b₄ ∣ W.b₄
  b₆ : ϖ ^ v.b₆ ∣ W.b₆
  b₈ : ϖ ^ v.b₈ ∣ W.b₈
  c₄ : ϖ ^ v.c₄ ∣ W.c₄
  c₆ : ϖ ^ v.c₆ ∣ W.c₆
  Δ : ϖ ^ v.Δ ∣ W.Δ

variable (ϖ W) in
/-- The cubic `aX³ + a₂X²/ϖ + a₄X/ϖⁿ⁺¹ + a₆/ϖ²ⁿ⁺¹` of Steps 6, 7 and 8 of Tate's algorithm. -/
noncomputable def cubic (a : R) (n : ℕ) : Cubic <| R ⧸ span {ϖ} :=
  ⟨a, mod ϖ <| div W.a₂ ϖ, mod ϖ <| div W.a₄ <| ϖ ^ (n + 1), mod ϖ <| div W.a₆ <| ϖ ^ (2 * n + 1)⟩

variable (ϖ W) in
/-- The quadratic `Y² + a₃Y/ϖⁿ - a₆/ϖ²ⁿ` of Steps 5, 7, 8 and 9 of Tate's algorithm. -/
noncomputable def quadratic (n : ℕ) : Cubic <| R ⧸ span {ϖ} :=
  ⟨0, 1, mod ϖ <| div W.a₃ <| ϖ ^ n, -mod ϖ (div W.a₆ <| ϖ ^ (2 * n))⟩

end TateAlgorithm

end WeierstrassCurve

end

/-! ## Changes of variables in Tate's algorithm -/

section

open CharP CommRing Ideal

universe u

variable {R : Type u} [CommRing R] (ϖ : R) [span {ϖ} |>.IsMaximal] (W : WeierstrassCurve R)

namespace WeierstrassCurve.TateAlgorithm

namespace Step2

variable {ϖ W} in
/-- The unique singular affine point of a singular Weierstrass curve. -/
noncomputable def singularPoint [PerfectField <| R ⧸ span {ϖ}] (hΔ : ϖ ∣ W.Δ) :
    Affine.SingularPoint <| W.map <| mod ϖ :=
  Affine.SingularPoint.unique (map_Δ _ (mod ϖ) ▸ mod_eq_zero .. |>.mpr hΔ) |>.default

open scoped Classical in
/-- The change of variables that translates the unique singular affine point to the origin. -/
noncomputable abbrev translate [PerfectField <| R ⧸ span {ϖ}] : WeierstrassCurve R :=
  if hΔ : ϖ ∣ W.Δ then VariableChange.mk 1 (singularPoint hΔ).x.out 0 (singularPoint hΔ).y.out • W
  else W

/-- The change of variables of Step 2 preserves `a₁`. -/
@[simp]
lemma translate_a₁ [PerfectField <| R ⧸ span {ϖ}] : (translate ϖ W).a₁ = W.a₁ := by
  rw [translate]; split_ifs <;> simp [variableChange_a₁]

/-- The change of variables of Step 2 preserves `c₄`. -/
@[simp]
lemma translate_c₄ [PerfectField <| R ⧸ span {ϖ}] : (translate ϖ W).c₄ = W.c₄ := by
  rw [translate]; split_ifs <;> simp [variableChange_c₄]

/-- The change of variables of Step 2 preserves `c₆`. -/
@[simp]
lemma translate_c₆ [PerfectField <| R ⧸ span {ϖ}] : (translate ϖ W).c₆ = W.c₆ := by
  rw [translate]; split_ifs <;> simp [variableChange_c₆]

/-- The change of variables of Step 2 preserves `Δ`. -/
@[simp]
lemma translate_Δ [PerfectField <| R ⧸ span {ϖ}] : (translate ϖ W).Δ = W.Δ := by
  rw [translate]; split_ifs <;> simp [variableChange_Δ]

variable {ϖ W} in
/-- If `ϖ ∣ Δ`, then after the change of variables of Step 2, `ϖ` divides `a₃`, `a₄`, `a₆`, `b₄`,
`b₆`, `b₈` and `Δ`. -/
lemma hasValuation_translate [PerfectField <| R ⧸ span {ϖ}] (hΔ : ϖ ∣ W.Δ) :
    HasValuation ϖ (translate ϖ W) ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1⟩ := by
  constructor <;> simp only [pow_zero, isUnit_one, IsUnit.dvd] <;> simp only [pow_one,
    ← mod_eq_zero, dite_eq_left hΔ, ← map_a₃, ← map_a₄, ← map_a₆, ← map_b₄, ← map_b₆, ← map_b₈,
    ← map_Δ, ← map_variableChange, VariableChange.map, map_one, map_zero, mod_out,
    Affine.SingularPoint.variableChange_a₃, Affine.SingularPoint.variableChange_a₄,
    Affine.SingularPoint.variableChange_a₆, Affine.SingularPoint.variableChange_b₄,
    Affine.SingularPoint.variableChange_b₆, Affine.SingularPoint.variableChange_b₈,
    Affine.SingularPoint.variableChange_Δ]

end Step2

namespace Step6

open scoped Classical in
/-- The root `Y = s` of the polynomial `Y² + a₁Y - a₂ ≡ (Y - s)² (mod ϖ)`. -/
noncomputable def s : R :=
  (if h2 : 2 = 0 then letI : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    root 2 <| mod ϖ W.a₂ else -mod ϖ W.a₁ / 2).out

open scoped Classical in
/-- The root `Y = t` of the polynomial `Y² + a₃Y/ϖ - a₆/ϖ² ≡ (Y - t)² (mod ϖ)`. -/
noncomputable def t : R :=
  (if h2 : 2 = 0 then letI : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    root 2 <| mod ϖ <| div W.a₆ <| ϖ ^ 2 else -mod ϖ (div W.a₃ ϖ) / 2).out

/-- The change of variables that translates `(x, y)` to `(x, y + sx + t)`. -/
noncomputable abbrev translate : WeierstrassCurve R :=
  VariableChange.mk 1 0 (s ϖ W) (ϖ * t ϖ W) • W

/-- The change of variables of Step 6 preserves `b₂`. -/
@[simp] lemma translate_b₂ : (translate ϖ W).b₂ = W.b₂ := by simp [variableChange_b₂]
/-- The change of variables of Step 6 preserves `b₄`. -/
@[simp] lemma translate_b₄ : (translate ϖ W).b₄ = W.b₄ := by simp [variableChange_b₄]
/-- The change of variables of Step 6 preserves `b₆`. -/
@[simp] lemma translate_b₆ : (translate ϖ W).b₆ = W.b₆ := by simp [variableChange_b₆]
/-- The change of variables of Step 6 preserves `b₈`. -/
@[simp] lemma translate_b₈ : (translate ϖ W).b₈ = W.b₈ := by simp [variableChange_b₈]
/-- The change of variables of Step 6 preserves `c₄`. -/
@[simp] lemma translate_c₄ : (translate ϖ W).c₄ = W.c₄ := by simp [variableChange_c₄]
/-- The change of variables of Step 6 preserves `c₆`. -/
@[simp] lemma translate_c₆ : (translate ϖ W).c₆ = W.c₆ := by simp [variableChange_c₆]
/-- The change of variables of Step 6 preserves `Δ`. -/
@[simp] lemma translate_Δ : (translate ϖ W).Δ = W.Δ := by simp [variableChange_Δ]

variable {ϖ W}

private lemma translate_a₁ : (translate ϖ W).a₁ = W.a₁ + 2 * s ϖ W := by
  simp [variableChange_a₁]

private lemma translate_a₂ : (translate ϖ W).a₂ = W.a₂ - s ϖ W ^ 2 - W.a₁ * s ϖ W := by
  grind [variableChange_a₂]

private lemma translate_a₃ (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ 1 ∣ W.a₃) :
    (translate ϖ W).a₃ = ϖ ^ 1 * (div W.a₃ ϖ + 2 * t ϖ W) := by
  grind [variableChange_a₃, CommRing.mul_div]

private lemma translate_a₄ (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ 1 ∣ W.a₃) (ha₄ : ϖ ^ 1 ∣ W.a₄) :
    (translate ϖ W).a₄ = ϖ ^ 1 * (div W.a₄ ϖ - div W.a₃ ϖ * s ϖ W - W.a₁ * t ϖ W
      - 2 * s ϖ W * t ϖ W) := by
  grind [variableChange_a₄, CommRing.mul_div]

private lemma translate_a₆ [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ 1 ∣ W.a₃)
    (ha₆ : ϖ ^ 2 ∣ W.a₆) : (translate ϖ W).a₆ = ϖ ^ 2 * (div W.a₆ (ϖ ^ 2) - t ϖ W ^ 2
      - div W.a₃ ϖ * t ϖ W) := by
  grind [variableChange_a₆, CommRing.mul_div, pow_ne_zero]

/-- The change of variables of Step 6 takes a curve with the valuations reached after Step 5 to one
with the valuations `(1, 1, 2, 2, 3)` on `(a₁, a₂, a₃, a₄, a₆)`. -/
lemma hasValuation_translate [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    {a₁ a₂ c₄ c₆ Δ : ℕ} (hW : HasValuation ϖ W ⟨a₁, a₂, 1, 1, 2, 1, 2, 3, 3, c₄, c₆, Δ⟩) :
    HasValuation ϖ (translate ϖ W) ⟨1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 3, 6⟩ := by
  have h2' [CharP (R ⧸ span {ϖ}) 2] : ϖ ∣ 2 := mod_eq_zero .. |>.mp <| cast_eq_zero ..
  have h4' [CharP (R ⧸ span {ϖ}) 2] : ϖ ∣ 4 := by convert h2'.pow two_ne_zero; norm_num1
  have ha₁' [CharP (R ⧸ span {ϖ}) 2] : ϖ ∣ W.a₁ := IsMaximal.prime hϖ |>.dvd_of_dvd_pow <|
    h4'.mul_right _ |>.add_left.mp <| pow_one ϖ ▸ hW.b₂
  have ha₃' [CharP (R ⧸ span {ϖ}) 2] : ϖ ^ 2 ∣ W.a₃ := sq_dvd_iff_cb_dvd_sq
    (IsMaximal.prime hϖ) |>.mpr <| pow_succ' ϖ 2 ▸ h4'.mul hW.a₆ |>.add_left.mp hW.b₆
  let W' : WeierstrassCurve R := translate ϖ W
  have ha₁ : ϖ ^ 1 ∣ W'.a₁ := by
    rw [translate_a₁, pow_one, ← mod_eq_zero]
    simp_rw [map_add, map_mul, map_ofNat, s, mod_out]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      simp [h2, ha₁']
    · field
  have ha₂ : ϖ ^ 1 ∣ W'.a₂ := by
    rw [translate_a₂, pow_one, ← mod_eq_zero]
    simp_rw [map_sub, map_mul, map_pow, s, mod_out]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
      simp [ha₁']
    · field_simp; rw [mul_zero]
      refine mod_eq_zero .. |>.mpr ?_
      convert pow_one ϖ ▸ hW.b₂; clear hR; grind only [b₂]
  have ha₃ : ϖ ^ 2 ∣ W'.a₃ := by
    rw [translate_a₃ hϖ hW.a₃, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_add, map_mul, map_ofNat, t, mod_out]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      simp [h2, sq_dvd.mp ha₃']
    · field
  have ha₄ : ϖ ^ 2 ∣ W'.a₄ := by
    rw [translate_a₄ hϖ hW.a₃ hW.a₄, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_sub, map_mul, map_ofNat, s, t, mod_out]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
      simp_rw [← pow_eq_zero_iff two_ne_zero (a := _ -_), sub_pow_char, mul_pow, pow_root]
      refine mod_eq_zero .. |>.mpr <| pow_succ_dvd_pow_mul hϖ 2 |>.mp ?_
      convert pow_succ' ϖ 2 ▸ ha₁'.mul ha₃' |>.mul_right W.a₄ |>.neg_right |>.sub hW.b₈ using 1
      grind only [b₈, CommRing.mul_div, pow_ne_zero, hW.a₃, hW.a₄, hW.a₆]
    · field_simp; rw [mul_zero]
      refine mod_eq_zero .. |>.mpr <| pow_succ_dvd_pow_mul hϖ 1 |>.mp ?_
      convert hW.b₄; clear hR; grind only [b₄, CommRing.mul_div, hW.a₃, hW.a₄]
  have ha₆ : ϖ ^ 3 ∣ W'.a₆ := by
    rw [translate_a₆ hϖ hW.a₃ hW.a₆, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_sub, map_mul, map_pow, t, mod_out]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
      simp [sq_dvd.mp ha₃']
    · field_simp; rw [mul_zero]
      refine mod_eq_zero .. |>.mpr <| pow_succ_dvd_pow_mul hϖ 2 |>.mp ?_
      convert hW.b₆; clear hR; grind only [b₆, CommRing.mul_div, pow_ne_zero, hW.a₃, hW.a₆]
  have hb₂ : ϖ ^ 1 ∣ W'.b₂ := by convert dvd_b₂ ha₁ ha₂; norm_num
  have hb₄ : ϖ ^ 2 ∣ W'.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄; norm_num
  have hb₆ : ϖ ^ 3 ∣ W'.b₆ := by convert dvd_b₆ ha₃ ha₆; norm_num
  have hb₈ : ϖ ^ 4 ∣ W'.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₄ : ϖ ^ 2 ∣ W'.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hc₆ : ϖ ^ 3 ∣ W'.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 6 ∣ W'.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step6

namespace Step7

section Translate

open scoped Classical in
/-- The double root `X = r` of the polynomial `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³`. -/
noncomputable def r : R :=
  (if h2 : 2 = 0 then letI : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    root 2 (cubic ϖ W 1 1).c
  else letI P : Cubic <| R ⧸ span {ϖ} := cubic ϖ W 1 1
    (9 * P.d - P.b * P.c) / 2 / (P.b ^ 2 - 3 * P.c)).out

/-- The change of variables that translates the double root `X = r` to `X = 0`. -/
noncomputable abbrev translate : WeierstrassCurve R :=
  VariableChange.mk 1 (ϖ * r ϖ W) 0 0 • W

/-- The change of variables of Step 7 preserves `a₁`. -/
@[simp] lemma translate_a₁ : (translate ϖ W).a₁ = W.a₁ := by simp [variableChange_a₁]
/-- The change of variables of Step 7 preserves `c₄`. -/
@[simp] lemma translate_c₄ : (translate ϖ W).c₄ = W.c₄ := by simp [variableChange_c₄]
/-- The change of variables of Step 7 preserves `c₆`. -/
@[simp] lemma translate_c₆ : (translate ϖ W).c₆ = W.c₆ := by simp [variableChange_c₆]
/-- The change of variables of Step 7 preserves `Δ`. -/
@[simp] lemma translate_Δ : (translate ϖ W).Δ = W.Δ := by simp [variableChange_Δ]

variable {ϖ W}

private lemma translate_a₂ (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) :
    (translate ϖ W).a₂ = ϖ ^ 1 * (div W.a₂ ϖ + 3 * r ϖ W) := by
  grind [variableChange_a₂, CommRing.mul_div]

/-- If `ϖ ∣ a₂` and the cubic `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` has a double root but no triple root,
then `ϖ² ∤ a₂` after the change of variables of Step 7. -/
lemma not_dvd_translate_a₂ [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    (ha₂ : ϖ ^ 1 ∣ W.a₂) (h : cubic ϖ W 1 1 |>.HasDoubleRoot)
    (h' : ¬(cubic ϖ W 1 1).HasTripleRoot) : ¬ϖ ^ 2 ∣ (translate ϖ W).a₂ := by
  rw [Cubic.hasDoubleRoot_of_a_eq_one rfl, cubic] at h
  rw [Cubic.HasTripleRoot, cubic] at h'
  simp_rw [translate_a₂ hϖ ha₂, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero, map_add, map_mul, map_ofNat,
    r, mod_out, cubic]
  split_ifs with h2
  · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
    grind only [pow_root]
  · have h'' := sub_ne_zero.mpr h'
    contrapose h''
    rw [eq_neg_of_add_eq_zero_left h'']
    field_simp; clear hR; grind only

private lemma translate_a₃ [IsReduced R] (hϖ : ϖ ≠ 0) (ha₁ : ϖ ^ 1 ∣ W.a₁) (ha₃ : ϖ ^ 2 ∣ W.a₃) :
    (translate ϖ W).a₃ = ϖ ^ 2 * (div W.a₃ (ϖ ^ 2) + div W.a₁ ϖ * r ϖ W) := by
  grind [variableChange_a₃, CommRing.mul_div, pow_ne_zero]

private lemma translate_a₄ [IsReduced R] (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₄ : ϖ ^ 2 ∣ W.a₄) :
    (translate ϖ W).a₄ = ϖ ^ 2 * (div W.a₄ (ϖ ^ 2) + 2 * div W.a₂ ϖ * r ϖ W + 3 * r ϖ W ^ 2) := by
  grind [variableChange_a₄, CommRing.mul_div, pow_ne_zero]

private lemma translate_a₆ [IsReduced R] (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₄ : ϖ ^ 2 ∣ W.a₄)
    (ha₆ : ϖ ^ 3 ∣ W.a₆) : (translate ϖ W).a₆ = ϖ ^ 3 * (div W.a₆ (ϖ ^ 3) + div W.a₄ (ϖ ^ 2) * r ϖ W
      + div W.a₂ ϖ * r ϖ W ^ 2 + r ϖ W ^ 3) := by
  grind [variableChange_a₆, CommRing.mul_div, pow_ne_zero]

/-- If the cubic `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` has a double root but no triple root, the change of
variables of Step 7 gives the valuations `(1, 1, 2, 3, 4)` on `(a₁, a₂, a₃, a₄, a₆)`. -/
lemma hasValuation_translate [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ} (hW : HasValuation ϖ W ⟨1, 1, 2, 2, 3, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (h : cubic ϖ W 1 1 |>.HasDoubleRoot) (h' : ¬(cubic ϖ W 1 1).HasTripleRoot) :
    HasValuation ϖ (translate ϖ W) ⟨1, 1, 2, 3, 4, 1, 3, 4, 5, 2, 3, 7⟩ := by
  let W : WeierstrassCurve R := translate ϖ W
  rw [Cubic.hasDoubleRoot_of_a_eq_one rfl, cubic] at h
  rw [Cubic.HasTripleRoot, cubic] at h'
  have ha₁ : ϖ ^ 1 ∣ W.a₁ := by rw [translate_a₁]; exact hW.a₁
  have ha₂ : ϖ ^ 1 ∣ W.a₂ := by rw [translate_a₂ hϖ hW.a₂]; exact dvd_mul_right ..
  have ha₃ : ϖ ^ 2 ∣ W.a₃ := by rw [translate_a₃ hϖ hW.a₁ hW.a₃]; exact dvd_mul_right ..
  have ha₄ : ϖ ^ 3 ∣ W.a₄ := by
    rw [translate_a₄ hϖ hW.a₂ hW.a₄, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_add, map_mul, map_pow, map_ofNat, r, mod_out, cubic]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
      grind only [pow_root]
    · field_simp [sub_ne_zero_of_ne <| mul_comm 3 (mod ϖ _) ▸ h']; clear hR; grind only
  have ha₆ : ϖ ^ 4 ∣ W.a₆ := by
    rw [translate_a₆ hϖ hW.a₂ hW.a₄ hW.a₆, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_add, map_mul, map_pow, r, mod_out, cubic]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
      grind only [pow_root]
    · field_simp [sub_ne_zero_of_ne <| mul_comm 3 (mod ϖ _) ▸ h']; clear hR; grind only
  have hb₂ : ϖ ^ 1 ∣ W.b₂ := by convert dvd_b₂ ha₁ ha₂; norm_num
  have hb₄ : ϖ ^ 3 ∣ W.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄; norm_num
  have hb₆ : ϖ ^ 4 ∣ W.b₆ := by convert dvd_b₆ ha₃ ha₆; norm_num
  have hb₈ : ϖ ^ 5 ∣ W.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₄ : ϖ ^ 2 ∣ W.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hc₆ : ϖ ^ 3 ∣ W.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 7 ∣ W.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Translate

section TranslateY

open scoped Classical in
/-- The double root `Y = t` of the polynomial `Y² + a₃Y/ϖⁿ - a₆/ϖ²ⁿ`. -/
noncomputable def tY (n : ℕ) : R :=
  (if h2 : 2 = 0 then letI : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    root 2 (quadratic ϖ W n).d else -(quadratic ϖ W n).c / 2).out

/-- The change of variables that translates the double root `Y = t` to `Y = 0`. -/
noncomputable abbrev translateY (n : ℕ) : WeierstrassCurve R :=
  VariableChange.mk 1 0 0 (ϖ ^ n * tY ϖ W n) • W

/-- The change of variables `translateY` preserves `a₁`. -/
@[simp] lemma translateY_a₁ (n : ℕ) : (translateY ϖ W n).a₁ = W.a₁ := by simp [variableChange_a₁]
/-- The change of variables `translateY` preserves `a₂`. -/
@[simp] lemma translateY_a₂ (n : ℕ) : (translateY ϖ W n).a₂ = W.a₂ := by simp [variableChange_a₂]
/-- The change of variables `translateY` preserves `b₂`. -/
@[simp] lemma translateY_b₂ (n : ℕ) : (translateY ϖ W n).b₂ = W.b₂ := by simp [variableChange_b₂]
/-- The change of variables `translateY` preserves `b₄`. -/
@[simp] lemma translateY_b₄ (n : ℕ) : (translateY ϖ W n).b₄ = W.b₄ := by simp [variableChange_b₄]
/-- The change of variables `translateY` preserves `b₆`. -/
@[simp] lemma translateY_b₆ (n : ℕ) : (translateY ϖ W n).b₆ = W.b₆ := by simp [variableChange_b₆]
/-- The change of variables `translateY` preserves `b₈`. -/
@[simp] lemma translateY_b₈ (n : ℕ) : (translateY ϖ W n).b₈ = W.b₈ := by simp [variableChange_b₈]
/-- The change of variables `translateY` preserves `c₄`. -/
@[simp] lemma translateY_c₄ (n : ℕ) : (translateY ϖ W n).c₄ = W.c₄ := by simp [variableChange_c₄]
/-- The change of variables `translateY` preserves `c₆`. -/
@[simp] lemma translateY_c₆ (n : ℕ) : (translateY ϖ W n).c₆ = W.c₆ := by simp [variableChange_c₆]
/-- The change of variables `translateY` preserves `Δ`. -/
@[simp] lemma translateY_Δ (n : ℕ) : (translateY ϖ W n).Δ = W.Δ := by simp [variableChange_Δ]

variable {ϖ W}

/-- If `ϖ² ∤ a₂`, then `ϖ² ∤ a₂` after the change of variables `translateY`. -/
lemma not_dvd_translateY_a₂ (n : ℕ) (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) : ¬ϖ ^ 2 ∣ (translateY ϖ W n).a₂ := by
  rwa [translateY_a₂]

private lemma translateY_a₃ [IsReduced R] {n : ℕ} (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ n ∣ W.a₃) :
    (translateY ϖ W n).a₃ = ϖ ^ n * (div W.a₃ (ϖ ^ n) + 2 * tY ϖ W n) := by
  grind [variableChange_a₃, CommRing.mul_div, pow_ne_zero]

private lemma dvd_translateY_a₃ [NoZeroDivisors R] {n : ℕ} (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ n ∣ W.a₃)
    (h : quadratic ϖ W n |>.HasDoubleRoot) : ϖ ^ (n + 1) ∣ (translateY ϖ W n).a₃ := by
  simp_rw [translateY_a₃ hϖ ha₃, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero, map_add, map_mul,
    map_ofNat, tY, mod_out, quadratic]
  grind only [Cubic.hasDoubleRoot_of_b_eq_one, quadratic]

private lemma translateY_a₄ [IsReduced R] {n : ℕ} (hϖ : ϖ ≠ 0) (ha₁ : ϖ ^ 1 ∣ W.a₁)
    (ha₄ : ϖ ^ (n + 1) ∣ W.a₄) :
    (translateY ϖ W n).a₄ = ϖ ^ (n + 1) * (div W.a₄ (ϖ ^ (n + 1)) - div W.a₁ ϖ * tY ϖ W n) := by
  grind [variableChange_a₄, CommRing.mul_div, pow_ne_zero]

private lemma translateY_a₆ [IsReduced R] {n : ℕ} (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ n ∣ W.a₃)
    (ha₆ : ϖ ^ (2 * n) ∣ W.a₆) : (translateY ϖ W n).a₆ = ϖ ^ (2 * n) * (div W.a₆ (ϖ ^ (2 * n))
      - tY ϖ W n ^ 2 - div W.a₃ (ϖ ^ n) * tY ϖ W n) := by
  grind [variableChange_a₆, CommRing.mul_div, pow_ne_zero, pow_mul']

private lemma dvd_translateY_a₆ [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] {n : ℕ}
    (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ n ∣ W.a₃) (ha₆ : ϖ ^ (2 * n) ∣ W.a₆)
    (h : quadratic ϖ W n |>.HasDoubleRoot) : ϖ ^ (2 * n + 1) ∣ (translateY ϖ W n).a₆ := by
  rw [Cubic.hasDoubleRoot_of_b_eq_one rfl rfl, quadratic] at h
  simp_rw [translateY_a₆ hϖ ha₃ ha₆, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero, map_sub, map_mul,
    map_pow, tY, mod_out, quadratic]
  split_ifs with h2
  · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
    grind only [pow_root]
  · field_simp; clear hR; grind only

/-- If the quadratic `Y² + a₃Y/ϖⁿ - a₆/ϖ²ⁿ` has a double root, `translateY` raises the valuations
of `a₃` and `a₆` to `n + 1` and `2n + 1`. -/
lemma hasValuation_translateY [NoZeroDivisors R] [PerfectField <| R ⧸ span {ϖ}] {n : ℕ}
    (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (h : quadratic ϖ W n |>.HasDoubleRoot) : HasValuation ϖ (translateY ϖ W n) ⟨1, 1, n + 1,
      n + 1, 2 * n + 1, 1, n + 1, 2 * n + 1, 2 * n + 2, 2, 3, 2 * n + 4⟩ := by
  let W : WeierstrassCurve R := translateY ϖ W n
  have ha₁ : ϖ ^ 1 ∣ W.a₁ := by rw [translateY_a₁]; exact hW.a₁
  have ha₂ : ϖ ^ 1 ∣ W.a₂ := by rw [translateY_a₂]; exact hW.a₂
  have ha₃ : ϖ ^ (n + 1) ∣ W.a₃ := dvd_translateY_a₃ hϖ hW.a₃ h
  have ha₄ : ϖ ^ (n + 1) ∣ W.a₄ := by rw [translateY_a₄ hϖ hW.a₁ hW.a₄]; exact dvd_mul_right ..
  have ha₆ : ϖ ^ (2 * n + 1) ∣ W.a₆ := dvd_translateY_a₆ hϖ hW.a₃ hW.a₆ h
  have hb₂ : ϖ ^ 1 ∣ W.b₂ := by convert dvd_b₂ ha₁ ha₂; norm_num
  have hb₄ : ϖ ^ (n + 1) ∣ W.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄ using 2; omega
  have hb₆ : ϖ ^ (2 * n + 1) ∣ W.b₆ := by convert dvd_b₆ ha₃ ha₆ using 2; omega
  have hb₈ : ϖ ^ (2 * n + 2) ∣ W.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆ using 2; omega
  have hc₄ : ϖ ^ 2 ∣ W.c₄ := by convert dvd_c₄ hb₂ hb₄ using 2; omega
  have hc₆ : ϖ ^ 3 ∣ W.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆ using 2; omega
  have hΔ : ϖ ^ (2 * n + 4) ∣ W.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈ using 2; omega
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end TranslateY

section TranslateX

open scoped Classical in
/-- The double root `X = r` of the polynomial `a₂X²/ϖ + a₄X/ϖⁿ⁺¹ + a₆/ϖ²ⁿ⁺¹`. -/
noncomputable def rX (n : ℕ) : R :=
  (if h2 : 2 = 0 then letI : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
    root 2 <| (cubic ϖ W 1 n).d / (cubic ϖ W 1 n).b
  else -(cubic ϖ W 1 n).c / 2 / (cubic ϖ W 1 n).b).out

/-- The change of variables that translates the double root `X = r` to `X = 0`. -/
noncomputable abbrev translateX (n : ℕ) : WeierstrassCurve R :=
  VariableChange.mk 1 (ϖ ^ n * rX ϖ W n) 0 0 • W

/-- The change of variables `translateX` preserves `a₁`. -/
@[simp] lemma translateX_a₁ (n : ℕ) : (translateX ϖ W n).a₁ = W.a₁ := by simp [variableChange_a₁]
/-- The change of variables `translateX` preserves `c₄`. -/
@[simp] lemma translateX_c₄ (n : ℕ) : (translateX ϖ W n).c₄ = W.c₄ := by simp [variableChange_c₄]
/-- The change of variables `translateX` preserves `c₆`. -/
@[simp] lemma translateX_c₆ (n : ℕ) : (translateX ϖ W n).c₆ = W.c₆ := by simp [variableChange_c₆]
/-- The change of variables `translateX` preserves `Δ`. -/
@[simp] lemma translateX_Δ (n : ℕ) : (translateX ϖ W n).Δ = W.Δ := by simp [variableChange_Δ]

variable {ϖ W}

private lemma translateX_a₂ {n : ℕ} (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) :
    (translateX ϖ W n).a₂ = ϖ ^ 1 * (div W.a₂ ϖ + 3 * ϖ ^ (n - 1) * rX ϖ W n) := by
  grind [variableChange_a₂, CommRing.mul_div, mul_pow_sub_one]

/-- For `n ≥ 2`, if `ϖ ∣ a₂` and `ϖ² ∤ a₂`, then `ϖ² ∤ a₂` after the change of variables
`translateX`. -/
lemma not_dvd_translateX_a₂ [NoZeroDivisors R] {n : ℕ} (hn : 2 ≤ n) (hϖ : ϖ ≠ 0)
    (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₂' : ¬ϖ ^ 2 ∣ W.a₂) : ¬ϖ ^ 2 ∣ (translateX ϖ W n).a₂ := by
  rw [translateX_a₂ hn hϖ ha₂, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero, map_add, map_mul, map_mul,
    map_pow, mod_self, zero_pow <| by omega, mul_zero, zero_mul, add_zero, mod_eq_zero]
  exact fun h ↦ ha₂' <| sq_dvd.mpr ⟨pow_one ϖ ▸ ha₂, h⟩

private lemma translateX_a₃ [IsReduced R] {n : ℕ} (hϖ : ϖ ≠ 0) (ha₁ : ϖ ^ 1 ∣ W.a₁)
    (ha₃ : ϖ ^ (n + 1) ∣ W.a₃) :
    (translateX ϖ W n).a₃ = ϖ ^ (n + 1) * (div W.a₃ (ϖ ^ (n + 1)) + div W.a₁ ϖ * rX ϖ W n) := by
  grind [variableChange_a₃, CommRing.mul_div, pow_ne_zero]

private lemma translateX_a₄ [IsReduced R] {n : ℕ} (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂)
    (ha₄ : ϖ ^ (n + 1) ∣ W.a₄) : (translateX ϖ W n).a₄ = ϖ ^ (n + 1) * (div W.a₄ (ϖ ^ (n + 1))
      + 3 * ϖ ^ (n - 1) * rX ϖ W n ^ 2 + 2 * div W.a₂ ϖ * rX ϖ W n) := by
  grind [variableChange_a₄, CommRing.mul_div, pow_ne_zero, mul_pow_sub_one]

private lemma translateX_a₆ [IsReduced R] {n : ℕ} (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂)
    (ha₄ : ϖ ^ (n + 1) ∣ W.a₄) (ha₆ : ϖ ^ (2 * n + 1) ∣ W.a₆) : (translateX ϖ W n).a₆ =
      ϖ ^ (2 * n + 1) * (div W.a₆ (ϖ ^ (2 * n + 1)) + ϖ ^ (n - 1) * rX ϖ W n ^ 3
        + div W.a₂ ϖ * rX ϖ W n ^ 2 + div W.a₄ (ϖ ^ (n + 1)) * rX ϖ W n) := by
  grind [variableChange_a₆, CommRing.mul_div, pow_ne_zero, pow_mul', mul_pow_sub_one]

/-- If the polynomial `a₂X²/ϖ + a₄X/ϖⁿ⁺¹ + a₆/ϖ²ⁿ⁺¹` has a double root, `translateX` raises the
valuations of `a₄` and `a₆` to `n + 2` and `2n + 2`. -/
lemma hasValuation_translateX [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] {n : ℕ}
    (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n + 1, n + 1, 2 * n + 1, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) (h : cubic ϖ W 0 n |>.HasDoubleRoot) : HasValuation ϖ (translateX ϖ W n)
      ⟨1, 1, n + 1, n + 2, 2 * n + 2, 1, n + 2, 2 * n + 2, 2 * n + 3, 2, 3, 2 * n + 5⟩ := by
  let W : WeierstrassCurve R := translateX ϖ W n
  replace ha₂ := ha₂ ∘ (sq_dvd.mpr ⟨pow_one ϖ ▸ hW.a₂, ·⟩) ∘ (mod_eq_zero ..).mp
  rw [Cubic.hasDoubleRoot_of_a_eq_zero rfl, cubic] at h
  have ha₁ : ϖ ^ 1 ∣ W.a₁ := by rw [translateX_a₁]; exact hW.a₁
  have ha₂ : ϖ ^ 1 ∣ W.a₂ := by rw [translateX_a₂ hn hϖ hW.a₂]; exact dvd_mul_right ..
  have ha₃ : ϖ ^ (n + 1) ∣ W.a₃ := by rw [translateX_a₃ hϖ hW.a₁ hW.a₃]; exact dvd_mul_right ..
  have ha₄ : ϖ ^ (n + 2) ∣ W.a₄ := by
    rw [translateX_a₄ hn hϖ hW.a₂ hW.a₄, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_add, map_mul, map_pow, map_ofNat, rX, mod_self, zero_pow (by omega : n - 1 ≠ 0),
      mod_out, cubic]
    clear hR; grind only
  have ha₆ : ϖ ^ (2 * n + 2) ∣ W.a₆ := by
    rw [translateX_a₆ hn hϖ hW.a₂ hW.a₄ hW.a₆, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_add, map_mul, map_pow, rX, mod_self, zero_pow (by omega : n - 1 ≠ 0), mod_out,
      cubic]
    split_ifs with h2
    · have : CharP (R ⧸ span {ϖ}) 2 := charP_iff_prime_eq_zero (by decide) |>.mpr h2
      replace hR : PerfectRing (R ⧸ span {ϖ}) 2 := PerfectField.toPerfectRing 2
      grind only [pow_root]
    · field_simp; clear hR; grind only
  have hb₂ : ϖ ^ 1 ∣ W.b₂ := by convert dvd_b₂ ha₁ ha₂; norm_num
  have hb₄ : ϖ ^ (n + 2) ∣ W.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄ using 2; omega
  have hb₆ : ϖ ^ (2 * n + 2) ∣ W.b₆ := by convert dvd_b₆ ha₃ ha₆ using 2; omega
  have hb₈ : ϖ ^ (2 * n + 3) ∣ W.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆ using 2; omega
  have hc₄ : ϖ ^ 2 ∣ W.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hc₆ : ϖ ^ 3 ∣ W.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆ using 2; omega
  have hΔ : ϖ ^ (2 * n + 5) ∣ W.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈ using 2; omega
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end TranslateX

end Step7

namespace Step8

open scoped Classical in
/-- The triple root `X = -r` of the polynomial `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³`. -/
noncomputable def r : R :=
  (if h3 : 3 = 0 then letI : CharP (R ⧸ span {ϖ}) 3 := charP_iff_prime_eq_zero (by decide) |>.mpr h3
    root 3 (cubic ϖ W 1 1).d else (cubic ϖ W 1 1).b / 3).out

/-- The change of variables that translates the triple root `X = -r` to `X = 0`. -/
noncomputable abbrev translate : WeierstrassCurve R :=
  VariableChange.mk 1 (-ϖ * r ϖ W) 0 0 • W

/-- The change of variables of Step 8 preserves `a₁`. -/
@[simp] lemma translate_a₁ : (translate ϖ W).a₁ = W.a₁ := by simp [variableChange_a₁]
/-- The change of variables of Step 8 preserves `c₄`. -/
@[simp] lemma translate_c₄ : (translate ϖ W).c₄ = W.c₄ := by simp [variableChange_c₄]
/-- The change of variables of Step 8 preserves `c₆`. -/
@[simp] lemma translate_c₆ : (translate ϖ W).c₆ = W.c₆ := by simp [variableChange_c₆]
/-- The change of variables of Step 8 preserves `Δ`. -/
@[simp] lemma translate_Δ : (translate ϖ W).Δ = W.Δ := by simp [variableChange_Δ]

variable {ϖ W}

private lemma translate_a₂ (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) :
    (translate ϖ W).a₂ = ϖ ^ 1 * (div W.a₂ ϖ - 3 * r ϖ W) := by
  grind [variableChange_a₂, CommRing.mul_div]

private lemma translate_a₃ [IsReduced R] (hϖ : ϖ ≠ 0) (ha₁ : ϖ ^ 1 ∣ W.a₁) (ha₃ : ϖ ^ 2 ∣ W.a₃) :
    (translate ϖ W).a₃ = ϖ ^ 2 * (div W.a₃ (ϖ ^ 2) - div W.a₁ ϖ * r ϖ W) := by
  grind [variableChange_a₃, CommRing.mul_div, pow_ne_zero]

private lemma translate_a₄ [IsReduced R] (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₄ : ϖ ^ 2 ∣ W.a₄) :
    (translate ϖ W).a₄ = ϖ ^ 2 * (div W.a₄ (ϖ ^ 2) + 3 * r ϖ W ^ 2 - 2 * div W.a₂ ϖ * r ϖ W) := by
  grind [variableChange_a₄, CommRing.mul_div, pow_ne_zero]

private lemma translate_a₆ [IsReduced R] (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₄ : ϖ ^ 2 ∣ W.a₄)
    (ha₆ : ϖ ^ 3 ∣ W.a₆) : (translate ϖ W).a₆ = ϖ ^ 3 * (div W.a₆ (ϖ ^ 3) - r ϖ W ^ 3
      + div W.a₂ ϖ * r ϖ W ^ 2 - div W.a₄ (ϖ ^ 2) * r ϖ W) := by
  grind [variableChange_a₆, CommRing.mul_div, pow_ne_zero]

/-- If the cubic `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` has a triple root, the change of variables of Step
8 gives the valuations `(1, 2, 2, 3, 4)` on `(a₁, a₂, a₃, a₄, a₆)`. -/
lemma hasValuation_translate [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ} (hW : HasValuation ϖ W ⟨1, 1, 2, 2, 3, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (h : cubic ϖ W 1 1 |>.HasDoubleRoot) (h' : cubic ϖ W 1 1 |>.HasTripleRoot) :
    HasValuation ϖ (translate ϖ W) ⟨1, 2, 2, 3, 4, 2, 3, 4, 6, 3, 4, 8⟩ := by
  let W : WeierstrassCurve R := translate ϖ W
  rw [Cubic.hasDoubleRoot_of_a_eq_one rfl, cubic] at h
  rw [Cubic.HasTripleRoot, cubic] at h'
  have ha₁ : ϖ ^ 1 ∣ W.a₁ := by rw [translate_a₁]; exact hW.a₁
  have ha₂ : ϖ ^ 2 ∣ W.a₂ := by
    rw [translate_a₂ hϖ hW.a₂, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_sub, map_mul, map_ofNat, r, mod_out, cubic]
    clear hR; grind only
  have ha₃ : ϖ ^ 2 ∣ W.a₃ := by rw [translate_a₃ hϖ hW.a₁ hW.a₃]; exact dvd_mul_right ..
  have ha₄ : ϖ ^ 3 ∣ W.a₄ := by
    rw [translate_a₄ hϖ hW.a₂ hW.a₄, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_sub, map_add, map_mul, map_pow, map_ofNat, r, mod_out, cubic]
    clear hR; grind only
  have ha₆ : ϖ ^ 4 ∣ W.a₆ := by
    rw [translate_a₆ hϖ hW.a₂ hW.a₄ hW.a₆, pow_succ_dvd_pow_mul hϖ, ← mod_eq_zero]
    simp_rw [map_sub, map_add, map_sub, map_mul, map_pow, r, mod_out, cubic]
    split_ifs with h3
    · have : CharP (R ⧸ span {ϖ}) 3 := charP_iff_prime_eq_zero (by decide) |>.mpr h3
      replace hR : PerfectRing (R ⧸ span {ϖ}) 3 := PerfectField.toPerfectRing 3
      grind only [pow_root]
    · field_simp; clear hR; grind only
  have hb₂ : ϖ ^ 2 ∣ W.b₂ := by convert dvd_b₂ ha₁ ha₂; norm_num
  have hb₄ : ϖ ^ 3 ∣ W.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄; norm_num
  have hb₆ : ϖ ^ 4 ∣ W.b₆ := by convert dvd_b₆ ha₃ ha₆; norm_num
  have hb₈ : ϖ ^ 6 ∣ W.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₄ : ϖ ^ 3 ∣ W.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hc₆ : ϖ ^ 4 ∣ W.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 8 ∣ W.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step8

namespace Step9

/-- The change of variables that translates the double root `Y = t` to `Y = 0`. -/
noncomputable abbrev translate : WeierstrassCurve R := Step7.translateY ϖ W 2

variable {ϖ W} in
/-- If the quadratic `Y² + a₃Y/ϖ² - a₆/ϖ⁴` has a double root, the change of variables of Step 9
gives the valuations `(1, 2, 3, 3, 5)` on `(a₁, a₂, a₃, a₄, a₆)`. -/
lemma hasValuation_translate [NoZeroDivisors R] [PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ} (hW : HasValuation ϖ W ⟨1, 2, 2, 3, 4, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (h : quadratic ϖ W 2 |>.HasDoubleRoot) :
    HasValuation ϖ (translate ϖ W) ⟨1, 2, 3, 3, 5, 2, 3, 5, 6, 3, 5, 9⟩ := by
  let W : WeierstrassCurve R := translate ϖ W
  have ha₁ : ϖ ^ 1 ∣ W.a₁ := by rw [Step7.translateY_a₁]; exact hW.a₁
  have ha₂ : ϖ ^ 2 ∣ W.a₂ := by rw [Step7.translateY_a₂]; exact hW.a₂
  have ha₃ : ϖ ^ 3 ∣ W.a₃ := Step7.dvd_translateY_a₃ hϖ hW.a₃ h
  have ha₄ : ϖ ^ 3 ∣ W.a₄ := by rw [Step7.translateY_a₄ hϖ hW.a₁ hW.a₄]; exact dvd_mul_right ..
  have ha₆ : ϖ ^ 5 ∣ W.a₆ := Step7.dvd_translateY_a₆ hϖ hW.a₃ hW.a₆ h
  have hb₂ : ϖ ^ 2 ∣ W.b₂ := by convert dvd_b₂ ha₁ ha₂; norm_num
  have hb₄ : ϖ ^ 3 ∣ W.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄; norm_num
  have hb₆ : ϖ ^ 5 ∣ W.b₆ := by convert dvd_b₆ ha₃ ha₆; norm_num
  have hb₈ : ϖ ^ 6 ∣ W.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₄ : ϖ ^ 3 ∣ W.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hc₆ : ϖ ^ 5 ∣ W.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 9 ∣ W.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step9

namespace Step11

/-- The change of variables that divides each coefficient `aᵢ` by `ϖ ^ i`. -/
noncomputable def translate : WeierstrassCurve R :=
  ⟨div W.a₁ ϖ, div W.a₂ <| ϖ ^ 2, div W.a₃ <| ϖ ^ 3, div W.a₄ <| ϖ ^ 4, div W.a₆ <| ϖ ^ 6⟩

variable [IsReduced R] {ϖ : R} {W : WeierstrassCurve R}

omit [IsReduced R] in
/-- If `ϖ ∣ W.a₁`, the curve `W'` of Step 11 satisfies `ϖ * W'.a₁ = W.a₁`. -/
@[simp]
lemma translate_a₁ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) : ϖ * (translate ϖ W).a₁ = W.a₁ := by
  rw [translate, CommRing.mul_div hϖ ha₁]

/-- If `ϖ ^ 2 ∣ W.a₂`, the curve `W'` of Step 11 satisfies `ϖ ^ 2 * W'.a₂ = W.a₂`. -/
@[simp]
lemma translate_a₂ (hϖ : ϖ ≠ 0) (ha₂ : ϖ ^ 2 ∣ W.a₂) : ϖ ^ 2 * (translate ϖ W).a₂ = W.a₂ := by
  rw [translate, CommRing.mul_div (pow_ne_zero 2 hϖ) ha₂]

/-- If `ϖ ^ 3 ∣ W.a₃`, the curve `W'` of Step 11 satisfies `ϖ ^ 3 * W'.a₃ = W.a₃`. -/
@[simp]
lemma translate_a₃ (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ 3 ∣ W.a₃) : ϖ ^ 3 * (translate ϖ W).a₃ = W.a₃ := by
  rw [translate, CommRing.mul_div (pow_ne_zero 3 hϖ) ha₃]

/-- If `ϖ ^ 4 ∣ W.a₄`, the curve `W'` of Step 11 satisfies `ϖ ^ 4 * W'.a₄ = W.a₄`. -/
@[simp]
lemma translate_a₄ (hϖ : ϖ ≠ 0) (ha₄ : ϖ ^ 4 ∣ W.a₄) : ϖ ^ 4 * (translate ϖ W).a₄ = W.a₄ := by
  rw [translate, CommRing.mul_div (pow_ne_zero 4 hϖ) ha₄]

/-- If `ϖ ^ 6 ∣ W.a₆`, the curve `W'` of Step 11 satisfies `ϖ ^ 6 * W'.a₆ = W.a₆`. -/
@[simp]
lemma translate_a₆ (hϖ : ϖ ≠ 0) (ha₆ : ϖ ^ 6 ∣ W.a₆) : ϖ ^ 6 * (translate ϖ W).a₆ = W.a₆ := by
  rw [translate, CommRing.mul_div (pow_ne_zero 6 hϖ) ha₆]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 2 * W'.b₂ = W.b₂`. -/
@[simp]
lemma translate_b₂ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) :
    ϖ ^ 2 * (translate ϖ W).b₂ = W.b₂ := by
  grind only [b₂, translate_a₁, translate_a₂]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 4 * W'.b₄ = W.b₄`. -/
@[simp]
lemma translate_b₄ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₄ : ϖ ^ 4 ∣ W.a₄) :
    ϖ ^ 4 * (translate ϖ W).b₄ = W.b₄ := by
  grind only [b₄, translate_a₁, translate_a₃, translate_a₄]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 6 * W'.b₆ = W.b₆`. -/
@[simp]
lemma translate_b₆ (hϖ : ϖ ≠ 0) (ha₃ : ϖ ^ 3 ∣ W.a₃) (ha₆ : ϖ ^ 6 ∣ W.a₆) :
    ϖ ^ 6 * (translate ϖ W).b₆ = W.b₆ := by
  grind only [b₆, translate_a₃, translate_a₆]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 8 * W'.b₈ = W.b₈`. -/
@[simp]
lemma translate_b₈ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃)
    (ha₄ : ϖ ^ 4 ∣ W.a₄) (ha₆ : ϖ ^ 6 ∣ W.a₆) : ϖ ^ 8 * (translate ϖ W).b₈ = W.b₈ := by
  simp_rw [b₈]; grind only [translate_a₁, translate_a₂, translate_a₃, translate_a₄, translate_a₆]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 4 * W'.c₄ = W.c₄`. -/
@[simp]
lemma translate_c₄ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃)
    (ha₄ : ϖ ^ 4 ∣ W.a₄) : ϖ ^ 4 * (translate ϖ W).c₄ = W.c₄ := by
  grind only [c₄, translate_b₂, translate_b₄]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 6 * W'.c₆ = W.c₆`. -/
@[simp]
lemma translate_c₆ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃)
    (ha₄ : ϖ ^ 4 ∣ W.a₄) (ha₆ : ϖ ^ 6 ∣ W.a₆) : ϖ ^ 6 * (translate ϖ W).c₆ = W.c₆ := by
  grind only [c₆, translate_b₂, translate_b₄, translate_b₆]

/-- Under the divisibilities of Step 11, its curve `W'` satisfies `ϖ ^ 12 * W'.Δ = W.Δ`. -/
@[simp]
lemma translate_Δ (hϖ : ϖ ≠ 0) (ha₁ : ϖ ∣ W.a₁) (ha₂ : ϖ ^ 2 ∣ W.a₂) (ha₃ : ϖ ^ 3 ∣ W.a₃)
    (ha₄ : ϖ ^ 4 ∣ W.a₄) (ha₆ : ϖ ^ 6 ∣ W.a₆) : ϖ ^ 12 * (translate ϖ W).Δ = W.Δ := by
  simp_rw [Δ]; grind only [translate_b₂, translate_b₄, translate_b₆,
    translate_b₈ hϖ ha₁ ha₂ ha₃ ha₄ ha₆]

end Step11

end WeierstrassCurve.TateAlgorithm

end

/-! ## Tate's algorithm -/

section

open CharP Except Ideal

universe u

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}]
  {W : WeierstrassCurve R} (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

namespace WeierstrassCurve.TateAlgorithm

namespace Step1

open scoped Classical in
variable (ϖ W) in
/-- Step 1 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) :=
  if ϖ ∣ W.Δ then ok W else error ⟨W, .I 0, 1⟩

variable {ϖ : R} {W' : WeierstrassCurve R}

/-- If Step 1 of Tate's algorithm continues, then `ϖ ∣ Δ`. -/
lemma run_Δ (h : run ϖ W = ok W') : ϖ ∣ W.Δ := by
  grind only [run]

/-- If Step 1 of Tate's algorithm continues, it returns the curve unchanged. -/
lemma run_weierstrassCurve (h : run ϖ W = ok W') : W' = W := by
  grind only [run]

end Step1

namespace Step2

open scoped Classical in
open Polynomial in
variable (ϖ W) in
/-- Step 2 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step1.run ϖ W >>= fun W ↦
  letI W : WeierstrassCurve R := translate ϖ W
  if ϖ ∣ W.b₂ then ok W else letI n : ℕ := emultiplicity ϖ W.Δ |>.toNat
    error ⟨W, .I n, if X ^ 2 + C W.a₁ * X - C W.a₂ |>.map (CommRing.mod ϖ) |>.Splits then n else
      if Odd n then 1 else 2⟩

variable {W' : WeierstrassCurve R}

/-- If Step 2 of Tate's algorithm continues with a curve `W'`, then `W'.a₁ = W.a₁`. -/
lemma run_a₁ (h : run ϖ W = ok W') : W'.a₁ = W.a₁ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step1.run_weierstrassCurve h', translate_a₁]

/-- If Step 2 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run ϖ W = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step1.run_weierstrassCurve h', translate_c₄]

/-- If Step 2 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run ϖ W = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step1.run_weierstrassCurve h', translate_c₆]

/-- If Step 2 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run ϖ W = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step1.run_weierstrassCurve h', translate_Δ]

/-- If Step 2 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(0, 0, 1, 1, 1)`. -/
lemma run_hasValuation (h : run ϖ W = ok W') :
    HasValuation ϖ W' ⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with hb₂
  rcases hasValuation_translate <| Step1.run_Δ h' with ⟨ha₁, ha₂, ha₃, ha₄, ha₆, _, hb₄, hb₆, hb₈⟩
  simp_rw [Step1.run_weierstrassCurve h', ok.inj h] at *
  have hc₄ : ϖ ^ 1 ∣ W'.c₄ := by convert dvd_c₄ (pow_one ϖ ▸ hb₂) hb₄; norm_num
  have hc₆ : ϖ ^ 1 ∣ W'.c₆ := by convert dvd_c₆ (pow_one ϖ ▸ hb₂) hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 2 ∣ W'.Δ := by convert dvd_Δ (pow_one ϖ ▸ hb₂) hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, pow_one ϖ |>.symm ▸ hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step2

namespace Step3

open scoped Classical in
variable (ϖ W) in
/-- Step 3 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step2.run ϖ W >>= fun W ↦
  if ϖ ^ 2 ∣ W.a₆ then ok W else error ⟨W, .II, 1⟩

variable {W' : WeierstrassCurve R}

/-- If Step 3 of Tate's algorithm continues with a curve `W'`, then `W'.a₁ = W.a₁`. -/
lemma run_a₁ (h : run ϖ W = ok W') : W'.a₁ = W.a₁ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step2.run_a₁ h'

/-- If Step 3 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run ϖ W = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step2.run_c₄ h'

/-- If Step 3 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run ϖ W = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step2.run_c₆ h'

/-- If Step 3 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run ϖ W = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step2.run_Δ h'

/-- If Step 3 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(0, 0, 1, 1, 2)`. -/
lemma run_hasValuation (h : run ϖ W = ok W') :
    HasValuation ϖ W' ⟨0, 0, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with ha₆
  rcases Step2.run_hasValuation h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄, _, hb₂, hb₄, _, _, hc₄⟩, ⟨⟩⟩
  have hb₆ : ϖ ^ 2 ∣ W'.b₆ := by convert dvd_b₆ ha₃ ha₆; norm_num
  have hb₈ : ϖ ^ 2 ∣ W'.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₆ : ϖ ^ 2 ∣ W'.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 3 ∣ W'.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step3

namespace Step4

open scoped Classical in
variable (ϖ W) in
/-- Step 4 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step3.run ϖ W >>= fun W ↦
  if ϖ ^ 3 ∣ W.b₈ then ok W else error ⟨W, .III, 2⟩

variable {W' : WeierstrassCurve R}

/-- If Step 4 of Tate's algorithm continues with a curve `W'`, then `W'.a₁ = W.a₁`. -/
lemma run_a₁ (h : run ϖ W = ok W') : W'.a₁ = W.a₁ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step3.run_a₁ h'

/-- If Step 4 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run ϖ W = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step3.run_c₄ h'

/-- If Step 4 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run ϖ W = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step3.run_c₆ h'

/-- If Step 4 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run ϖ W = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step3.run_Δ h'

/-- If Step 4 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(0, 0, 1, 1, 2)`. -/
lemma run_hasValuation [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (h : run ϖ W = ok W') :
    HasValuation ϖ W' ⟨0, 0, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with hb₈
  rcases Step3.run_hasValuation h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, _, hb₆, _, _, hc₆⟩, ⟨⟩⟩
  have hb₄ : ϖ ^ 2 ∣ W'.b₄ := (sq_dvd_iff_cb_dvd_sq <| IsMaximal.prime hϖ).mpr <| sub_eq_iff_comm.mp
    W'.b_relation.symm ▸ (pow_succ' ϖ 2 ▸ (pow_one ϖ ▸ hb₂).mul hb₆).sub <| hb₈.mul_left _
  have hc₄ : ϖ ^ 2 ∣ W'.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hΔ : ϖ ^ 4 ∣ W'.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step4

namespace Step5

open scoped Classical in
variable (ϖ W) in
/-- Step 5 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step4.run ϖ W >>= fun W ↦
  if ϖ ^ 3 ∣ W.b₆ then ok W else error ⟨W, .IV, if quadratic ϖ W 1 |>.toPoly.Splits then 3 else 1⟩

variable {W' : WeierstrassCurve R}

/-- If Step 5 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run ϖ W = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step4.run_c₄ h'

/-- If Step 5 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run ϖ W = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step4.run_c₆ h'

/-- If Step 5 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run ϖ W = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step4.run_Δ h'

/-- If Step 5 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(0, 0, 1, 1, 2)`. -/
lemma run_hasValuation [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (h : run ϖ W = ok W') :
    HasValuation ϖ W' ⟨0, 0, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with hb₆
  rcases Step4.run_hasValuation hϖ h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, _, hb₈, hc₄⟩, ⟨⟩⟩
  have hc₆ : ϖ ^ 3 ∣ W'.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 5 ∣ W'.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step5

namespace Step6

open scoped Classical in
variable (ϖ W) in
/-- Step 6 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step5.run ϖ W >>= fun W ↦
  letI W : WeierstrassCurve R := translate ϖ W
  if cubic ϖ W 1 1 |>.HasDoubleRoot then ok W else
    error ⟨W, .I! 0, 1 + (cubic ϖ W 1 1).toPoly.roots.toFinset.card⟩

variable {W' : WeierstrassCurve R}

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then the cubic
`X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` of `W'` has a double root. -/
lemma run_hasDoubleRoot (h : run ϖ W = ok W') : cubic ϖ W' 1 1 |>.HasDoubleRoot := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with h'; cases h; exact h'

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run ϖ W = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [translate_c₄, Step5.run_c₄ h']

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run ϖ W = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [translate_c₆, Step5.run_c₆ h']

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run ϖ W = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [translate_Δ, Step5.run_Δ h']

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(1, 1, 2, 2, 3)`. -/
lemma run_hasValuation [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (h : run ϖ W = ok W') :
    HasValuation ϖ W' ⟨1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 3, 6⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  exact hasValuation_translate hϖ <| Step5.run_hasValuation hϖ h'

end Step6

variable [IsNoetherianRing R] [IsDomain R]

namespace Step7

-- `[IsNoetherianRing R]` below is needed by the `decreasing_by` termination proof (via
-- `inferInstance`), where the section variable is not auto-included; the
-- `overlappingInstances` "redundant binder" report is therefore a false positive here.

set_option linter.overlappingInstances false in
open scoped Classical in
/-- The subprocedure of Step 7 of Tate's algorithm. -/
noncomputable def subprocedure [IsNoetherianRing R] {W : WeierstrassCurve R} (hϖ : ϖ ≠ 0)
    (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) : Output R :=
  if hY : quadratic ϖ W n |>.HasDoubleRoot then
    let W' : WeierstrassCurve R := translateY ϖ W n
    have hW' := hasValuation_translateY hn hϖ hW hY
    have ha₂' : ¬ϖ ^ 2 ∣ W'.a₂ := not_dvd_translateY_a₂ n ha₂
    have hΔ' : W'.Δ ≠ 0 := translateY_Δ ϖ W n ▸ hΔ
    if hX : cubic ϖ W' 0 n |>.HasDoubleRoot then
      let W'' : WeierstrassCurve R := translateX ϖ W' n
      have hW'' := hasValuation_translateX hn hϖ hW' ha₂' hX
      have ha₂'' : ¬ϖ ^ 2 ∣ W''.a₂ := not_dvd_translateX_a₂ hn hϖ hW'.a₂ ha₂'
      have hΔ'' : W''.Δ ≠ 0 := translateX_Δ ϖ W' n ▸ hΔ'
      subprocedure hϖ hΔ'' (Nat.le_succ_of_le hn) hW'' ha₂''
    else ⟨W', .I! <| 2 * n - 2, if 0 < (cubic ϖ W' 0 n).roots.toFinset.card then 4 else 2⟩
  else ⟨W, .I! <| 2 * n - 3, if 0 < (quadratic ϖ W n).roots.toFinset.card then 4 else 2⟩
termination_by multiplicity ϖ W.Δ - n decreasing_by
  rw [translateX_Δ, translateY_Δ]
  refine Nat.sub_lt_sub_left ?_ <| lt_add_one n
  linarith only [FiniteMultiplicity.span_ne_top (IsMaximal.ne_top inferInstance) |>.mpr hΔ
    |>.le_multiplicity_of_pow_dvd <| translateY_Δ ϖ .. ▸ translateX_Δ ϖ .. ▸ hW''.Δ]

open scoped Classical in
/-- Step 7 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := match h : Step6.run ϖ W with
  | error out => error out
  | ok W' => if h' : cubic ϖ W' 1 1 |>.HasTripleRoot then ok W' else error <| subprocedure hϖ
    (translate_Δ ϖ W' ▸ Step6.run_Δ h ▸ hΔ) le_rfl
    (hasValuation_translate hϖ (Step6.run_hasValuation hϖ h) (Step6.run_hasDoubleRoot h) h')
    (not_dvd_translate_a₂ hϖ (Step6.run_hasValuation hϖ h).a₂ (Step6.run_hasDoubleRoot h) h')

variable {W' : WeierstrassCurve R}

/-- If Step 7 of Tate's algorithm continues with a curve `W'`, then the cubic
`X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` of `W'` has a double root. -/
lemma run_hasDoubleRoot (h : run hϖ hΔ = ok W') : cubic ϖ W' 1 1 |>.HasDoubleRoot := by
  rw [run] at h; split at h; · contradiction
  next _ h₆ => split_ifs at h; cases h; exact Step6.run_hasDoubleRoot h₆

/-- If Step 7 of Tate's algorithm continues with a curve `W'`, then the cubic
`X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` of `W'` has a triple root. -/
lemma run_hasTripleRoot (h : run hϖ hΔ = ok W') : cubic ϖ W' 1 1 |>.HasTripleRoot := by
  rw [run] at h; split at h; · contradiction
  split_ifs at h with h₃; cases h; exact h₃

/-- If Step 7 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run hϖ hΔ = ok W') : W'.c₄ = W.c₄ := by
  rw [run] at h; split at h; · contradiction
  next _ h₆ => split_ifs at h; cases h; exact Step6.run_c₄ h₆

/-- If Step 7 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run hϖ hΔ = ok W') : W'.c₆ = W.c₆ := by
  rw [run] at h; split at h; · contradiction
  next _ h₆ => split_ifs at h; cases h; exact Step6.run_c₆ h₆

/-- If Step 7 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run hϖ hΔ = ok W') : W'.Δ = W.Δ := by
  rw [run] at h; split at h; · contradiction
  next _ h₆ => split_ifs at h; cases h; exact Step6.run_Δ h₆

/-- If Step 7 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(1, 1, 2, 2, 3)`. -/
lemma run_hasValuation (h : run hϖ hΔ = ok W') :
    HasValuation ϖ W' ⟨1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 3, 6⟩ := by
  rw [run] at h; split at h; · contradiction
  next _ h₆ => split_ifs at h; cases h; exact Step6.run_hasValuation hϖ h₆

end Step7

namespace Step8

open scoped Classical in
/-- Step 8 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step7.run hϖ hΔ >>= fun W ↦
  letI W : WeierstrassCurve R := translate ϖ W
  if quadratic ϖ W 2 |>.HasDoubleRoot then ok W else
    error ⟨W, .IV!, if quadratic ϖ W 2 |>.toPoly.Splits then 3 else 1⟩

variable {W' : WeierstrassCurve R}

/-- If Step 8 of Tate's algorithm continues with a curve `W'`, then the quadratic
`Y² + a₃Y/ϖ² - a₆/ϖ⁴` of `W'` has a double root. -/
lemma run_hasDoubleRoot (h : run hϖ hΔ = ok W') : quadratic ϖ W' 2 |>.HasDoubleRoot := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with h'; cases h; exact h'

/-- If Step 8 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run hϖ hΔ = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [translate_c₄, Step7.run_c₄ hϖ hΔ h']

/-- If Step 8 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run hϖ hΔ = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [translate_c₆, Step7.run_c₆ hϖ hΔ h']

/-- If Step 8 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run hϖ hΔ = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [translate_Δ, Step7.run_Δ hϖ hΔ h']

/-- If Step 8 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(1, 2, 2, 3, 4)`. -/
lemma run_hasValuation (h : run hϖ hΔ = ok W') :
    HasValuation ϖ W' ⟨1, 2, 2, 3, 4, 2, 3, 4, 6, 3, 4, 8⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  exact hasValuation_translate hϖ (Step7.run_hasValuation hϖ hΔ h')
    (Step7.run_hasDoubleRoot hϖ hΔ h') (Step7.run_hasTripleRoot hϖ hΔ h')

end Step8

namespace Step9

open scoped Classical in
/-- Step 9 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step8.run hϖ hΔ >>= fun W ↦
  letI W : WeierstrassCurve R := translate ϖ W
  if ϖ ^ 4 ∣ W.a₄ then ok W else error ⟨W, .III!, 2⟩

variable {W' : WeierstrassCurve R}

/-- If Step 9 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run hϖ hΔ = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step7.translateY_c₄, Step8.run_c₄ hϖ hΔ h']

/-- If Step 9 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run hϖ hΔ = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step7.translateY_c₆, Step8.run_c₆ hϖ hΔ h']

/-- If Step 9 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run hϖ hΔ = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h
  rw [Step7.translateY_Δ, Step8.run_Δ hϖ hΔ h']

/-- If Step 9 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(1, 2, 3, 4, 5)`. -/
lemma run_hasValuation (h : run hϖ hΔ = ok W') :
    HasValuation ϖ W' ⟨1, 2, 3, 4, 5, 2, 4, 5, 7, 4, 5, 10⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with ha₄
  rcases hasValuation_translate hϖ (Step8.run_hasValuation hϖ hΔ h')
    (Step8.run_hasDoubleRoot hϖ hΔ h') with ⟨ha₁, ha₂, ha₃, _, ha₆, hb₂, _, hb₆, _, _, hc₆, _⟩
  simp only [ok.inj h] at *
  have hb₄ : ϖ ^ 4 ∣ W'.b₄ := by convert dvd_b₄ ha₁ ha₃ ha₄; norm_num
  have hb₈ : ϖ ^ 7 ∣ W'.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₄ : ϖ ^ 4 ∣ W'.c₄ := by convert dvd_c₄ hb₂ hb₄; norm_num
  have hΔ : ϖ ^ 10 ∣ W'.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step9

namespace Step10

open scoped Classical in
/-- Step 10 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step9.run hϖ hΔ >>= fun W ↦
  if ϖ ^ 6 ∣ W.a₆ then ok W else error ⟨W, .II!, 1⟩

variable {W' : WeierstrassCurve R}

/-- If Step 10 of Tate's algorithm continues with a curve `W'`, then `W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run hϖ hΔ = ok W') : W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step9.run_c₄ hϖ hΔ h'

/-- If Step 10 of Tate's algorithm continues with a curve `W'`, then `W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run hϖ hΔ = ok W') : W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step9.run_c₆ hϖ hΔ h'

/-- If Step 10 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
lemma run_Δ (h : run hϖ hΔ = ok W') : W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h; cases h; exact Step9.run_Δ hϖ hΔ h'

/-- If Step 10 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(1, 2, 3, 4, 6)`. -/
lemma run_hasValuation (h : run hϖ hΔ = ok W') :
    HasValuation ϖ W' ⟨1, 2, 3, 4, 6, 2, 4, 6, 8, 4, 6, 12⟩ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩; split_ifs at h with ha₆
  rcases Step9.run_hasValuation hϖ hΔ h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄, _, hb₂, hb₄, _, _, hc₄⟩, ⟨⟩⟩
  have hb₆ : ϖ ^ 6 ∣ W'.b₆ := by convert dvd_b₆ ha₃ ha₆; norm_num
  have hb₈ : ϖ ^ 8 ∣ W'.b₈ := by convert dvd_b₈ ha₁ ha₂ ha₃ ha₄ ha₆; norm_num
  have hc₆ : ϖ ^ 6 ∣ W'.c₆ := by convert dvd_c₆ hb₂ hb₄ hb₆; norm_num
  have hΔ : ϖ ^ 12 ∣ W'.Δ := by convert dvd_Δ hb₂ hb₄ hb₆ hb₈; norm_num
  exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hb₄, hb₆, hb₈, hc₄, hc₆, hΔ⟩

end Step10

namespace Step11

open scoped Classical in
/-- Step 11 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) :=
  Step10.run hϖ hΔ >>= fun W ↦ ok <| translate ϖ W

variable {W' : WeierstrassCurve R}

/-- If Step 11 of Tate's algorithm continues with a curve `W'`, then `ϖ⁴ * W'.c₄ = W.c₄`. -/
lemma run_c₄ (h : run hϖ hΔ = ok W') : ϖ ^ 4 * W'.c₄ = W.c₄ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩
  rcases Step10.run_hasValuation hϖ hΔ h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄⟩, ⟨⟩⟩
  rw [translate_c₄ hϖ (pow_one ϖ ▸ ha₁) ha₂ ha₃ ha₄, Step10.run_c₄ hϖ hΔ h']

/-- If Step 11 of Tate's algorithm continues with a curve `W'`, then `ϖ⁶ * W'.c₆ = W.c₆`. -/
lemma run_c₆ (h : run hϖ hΔ = ok W') : ϖ ^ 6 * W'.c₆ = W.c₆ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩
  rcases Step10.run_hasValuation hϖ hΔ h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩, ⟨⟩⟩
  rw [translate_c₆ hϖ (pow_one ϖ ▸ ha₁) ha₂ ha₃ ha₄ ha₆, Step10.run_c₆ hϖ hΔ h']

/-- If Step 11 of Tate's algorithm continues with a curve `W'`, then `ϖ¹² * W'.Δ = W.Δ`. -/
lemma run_Δ (h : run hϖ hΔ = ok W') : ϖ ^ 12 * W'.Δ = W.Δ := by
  rcases bind_eq_ok_iff.mp h with ⟨_, h', h⟩
  rcases Step10.run_hasValuation hϖ hΔ h', h with ⟨⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩, ⟨⟩⟩
  rw [translate_Δ hϖ (pow_one ϖ ▸ ha₁) ha₂ ha₃ ha₄ ha₆, Step10.run_Δ hϖ hΔ h']

end Step11

open scoped Classical in
/-- The execution of Tate's algorithm to compute the special fiber of a Weierstrass curve. -/
noncomputable def run {W : WeierstrassCurve R} (hΔ : W.Δ ≠ 0) : Output R :=
  match h : Step11.run hϖ hΔ with
  | error out => out
  | ok W => run <| (Step11.run_Δ hϖ hΔ h ▸ mul_ne_zero_iff_left <| pow_ne_zero 12 hϖ).mp hΔ
termination_by emultiplicity ϖ W.Δ decreasing_by
  rcases ENat.ne_top_iff_exists.mp fun h' : emultiplicity ϖ W.Δ = ⊤ ↦ hΔ <| by
    rw [← Step11.run_Δ hϖ hΔ h, mul_eq_zero_iff_left <| pow_ne_zero _ hϖ,
      ← emultiplicity_of_span_ne_top (x := ϖ) <| IsMaximal.ne_top inferInstance, h'] with ⟨n, hn⟩
  rw [← Step11.run_Δ hϖ hΔ h, emultiplicity_mul, emultiplicity_pow_self_of_prime, ← hn]
  · exact ENat.natCast_lt_natCast.mpr <| Nat.lt_add_of_pos_left <| by decide
  all_goals exact IsMaximal.prime hϖ

end WeierstrassCurve.TateAlgorithm

end


/-! ## Local reduction data and their densities -/

section

open Ideal MeasureTheory Measure

variable {R : Type*} {p : ℕ} [Fact p.Prime]

namespace PadicInt

/-- The uniformizer `p` of `ℤ_[p]` is nonzero. -/
theorem uniformizer_ne_zero : (p : ℤ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The ideal `(p)` of `ℤ_[p]` is maximal. -/
instance instIsMaximalSpanSingletonSetCast_bSDTamagawa : span {(p : ℤ_[p])} |>.IsMaximal :=
  (IsLocalRing.isMaximal_iff _).mpr maximalIdeal_eq_span_p.symm

/-- The residue field `ℤ_[p] ⧸ (p)` is perfect. -/
instance instPerfectFieldQuotientIdealSpanSingletonSetCast_bSDTamagawa :
    PerfectField <| ℤ_[p] ⧸ span {(p : ℤ_[p])} :=
  .of_ringEquiv <| residueField.symm.trans <| quotEquivOfEq maximalIdeal_eq_span_p

/-- The Borel `σ`-algebra on `ℤ_[p]`. -/
@[nolint defsWithUnderscore]
noncomputable instance instMeasurableSpace_bSDTamagawa : MeasurableSpace ℤ_[p] := borel _

/-- The measurable structure on `ℤ_[p]` is the Borel one. -/
instance instBorelSpace_bSDTamagawa : BorelSpace ℤ_[p] :=
  ⟨rfl⟩

/-- The volume on `ℤ_[p]`: the Haar measure giving `ℤ_[p]` measure one. -/
@[nolint defsWithUnderscore]
noncomputable instance instMeasureSpace_bSDTamagawa : MeasureSpace ℤ_[p] := ⟨addHaarMeasure ⊤⟩

end PadicInt

variable [CommRing R]

namespace WeierstrassCurve

variable (R) in
/-- Short Weierstrass models over `R`: Weierstrass curves with `a₁ = a₂ = a₃ = 0`. -/
abbrev ShortNF : Type _ := {W : WeierstrassCurve R // W.IsShortNF}

namespace ShortNF

/-- The measurable structure on `ShortNF R` pulled back along `W ↦ (a₄, a₆)`. -/
instance instMeasurableSpace [MeasurableSpace R] : MeasurableSpace <| ShortNF R :=
  Prod.instMeasurableSpace.comap fun W ↦ (W.val.a₄, W.val.a₆)

/-- The short Weierstrass model with coefficients `(a₄, a₆)`. -/
noncomputable abbrev ofProd (a₄ a₆ : R) : ShortNF R := ⟨ofShortNF a₄ a₆, ofShortNF_isShortNF a₄ a₆⟩

/-- The volume on `ShortNF R` is the pushforward of `volume` on `R × R` along `ofProd`. -/
noncomputable instance instMeasureSpace [MeasureSpace R] : MeasureSpace <| ShortNF R :=
  ⟨volume.map ofProd.uncurry⟩

variable (R) in
/-- The singular short Weierstrass models, `Δ = 0`. -/
abbrev Singular : Set <| ShortNF R := {W : ShortNF R | W.val.Δ = 0}

variable (R) in
/-- The nonsingular short Weierstrass models, `Δ ≠ 0`. -/
abbrev Elliptic : Set <| ShortNF R := (ShortNF.Singular R)ᶜ

namespace Elliptic

/-- The measure `μ_p`: the volume of `ShortNF R` restricted to the nonsingular models. -/
@[bsd_tamagawa "T009"]
noncomputable instance measureSpace [MeasureSpace R] : MeasureSpace <| Elliptic R :=
  Subtype.measureSpace

end Elliptic

end ShortNF

end WeierstrassCurve

end

namespace WeierstrassCurve

/-- The trivial reduction data `𝒦₀ = {(I₀, 1), (I₁, 1)}`. Split and non-split `I₁` are not
distinguished. -/
@[bsd_tamagawa "T011a"]
def K0 : Set (KodairaSymbol × ℕ) := {(KodairaSymbol.I 0, 1), (KodairaSymbol.I 1, 1)}
/-- Base change of the short-model discriminant along `ℤ → ℤ_p`:
`Δ(E(↑a₄, ↑a₆)) = ↑Δ(E(a₄, a₆))`. -/
lemma ofShortNF_Δ_intCast {p : ℕ} [Fact p.Prime] (a₄ a₆ : ℤ) :
    (ofShortNF (a₄ : ℤ_[p]) (a₆ : ℤ_[p])).Δ = ((ofShortNF a₄ a₆).Δ : ℤ_[p]) := by
  rw [ofShortNF_Δ, ofShortNF_Δ]; push_cast; ring

namespace ShortNF

variable {p : ℕ} [Fact p.Prime]

/-- A nonsingular integer pair gives a nonsingular model over `ℤ_[p]`. -/
theorem ofProd_intCast_mem_Elliptic {a₄ a₆ : ℤ} (h : (ofShortNF a₄ a₆).Δ ≠ 0) :
    ofProd (a₄ : ℤ_[p]) (a₆ : ℤ_[p]) ∈ Elliptic ℤ_[p] := by
  change (ofShortNF (a₄ : ℤ_[p]) (a₆ : ℤ_[p])).Δ ≠ 0
  rw [ofShortNF_Δ_intCast]; exact_mod_cast h

end ShortNF

/-- The reduction map `τ_p`: Tate's algorithm at `p` on `E(a₄, a₆)` over `ℤ_[p]`. On the singular
locus, where it is irrelevant, the value is good reduction. -/
@[bsd_tamagawa "T008"]
noncomputable def tauZ (p : ℕ) [Fact p.Prime] (a₄ a₆ : ℤ) : TateAlgorithm.Output ℤ_[p] :=
  if h : (ofShortNF a₄ a₆).Δ ≠ 0 then
    TateAlgorithm.run PadicInt.uniformizer_ne_zero (ShortNF.ofProd_intCast_mem_Elliptic h)
  else ⟨ofShortNF (a₄ : ℤ_[p]) (a₆ : ℤ_[p]), KodairaSymbol.I 0, 1⟩

variable (p : ℕ) [Fact p.Prime]

/-- Tate's algorithm at `p` on a nonsingular short Weierstrass model over `ℤ_[p]`. -/
noncomputable def tauP (W : ShortNF.Elliptic ℤ_[p]) : TateAlgorithm.Output ℤ_[p] :=
  TateAlgorithm.run (W := W.val.val) PadicInt.uniformizer_ne_zero W.property

/-- `δ_p(K)`, the `μ_p`-measure of the models over `ℤ_[p]` whose reduction datum (Kodaira symbol,
Tamagawa number) is `K`. -/
@[bsd_tamagawa "T009"]
noncomputable def deltaP (K : KodairaSymbol × ℕ) : ENNReal :=
  MeasureTheory.volume
    {W : ShortNF.Elliptic ℤ_[p] |
      ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = K}

end WeierstrassCurve

namespace WeierstrassCurve

/-- The local Tamagawa number `c_p(E)` of `E(a₄, a₆)`, read off Tate's algorithm; `1` when `p` is
not prime. -/
@[bsd_tamagawa "T004"]
noncomputable def localTamagawaNumber (p : ℕ) (a₄ a₆ : ℤ) : ℕ :=
  if h : p.Prime then (@tauZ p ⟨h⟩ a₄ a₆).tamagawaNumber else 1

/-- The Tamagawa product `Tam(E) = ∏_p c_p(E)`, a `finprod` (which is `1` on an infinite
support). -/
@[bsd_tamagawa "T004"]
noncomputable def tamagawaProduct (a₄ a₆ : ℤ) : ℕ :=
  ∏ᶠ p : ℕ, localTamagawaNumber p a₄ a₆

/-- `ω_Tam(E)`, the number of primes `p` with `c_p(E) > 1`. -/
@[bsd_tamagawa "T005"]
noncomputable def tamagawaOmega (a₄ a₆ : ℤ) : ℕ :=
  {p : ℕ | 1 < localTamagawaNumber p a₄ a₆}.ncard

end WeierstrassCurve

section

open WeierstrassCurve

namespace BSDTamagawa.LocalReduction

/-- A local reduction datum: a Kodaira symbol and a Tamagawa number. -/
@[bsd_tamagawa "T006a"]
abbrev ReductionData : Type := KodairaSymbol × ℕ

end BSDTamagawa.LocalReduction

end

section

open MeasureTheory

variable {p : ℕ} [Fact p.Prime]

namespace WeierstrassCurve

variable (p) in
/-- `δ_p(n)`, the `μ_p`-measure of the models over `ℤ_[p]` with local Tamagawa number `n`. -/
@[bsd_tamagawa "T010"]
noncomputable def δ (n : ℕ) : ENNReal :=
  volume {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = n}

end WeierstrassCurve

end

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-- `β_p = ∑_{K ∈ 𝒦₀} δ_p(K)`. -/
@[bsd_tamagawa "T011b"]
noncomputable def β : ENNReal := ∑ᶠ K ∈ K0, deltaP p K

end WeierstrassCurve

namespace WeierstrassCurve

/-- The reduction datum of `E(a₄, a₆)` at `p`; `(I₀, 1)` when `p` is not prime. -/
noncomputable def localReductionDatum (p : ℕ) (a₄ a₆ : ℤ) : KodairaSymbol × ℕ :=
  if h : p.Prime then
    ((@tauZ p ⟨h⟩ a₄ a₆).kodairaSymbol, (@tauZ p ⟨h⟩ a₄ a₆).tamagawaNumber)
  else (KodairaSymbol.I 0, 1)

/-- `ω_K(E)`, the number of primes at which `E(a₄, a₆)` has reduction datum `K` (`Set.ncard`, so
`0` when there are infinitely many). -/
@[bsd_tamagawa "T012"]
noncomputable def reductionOmega (K : KodairaSymbol × ℕ) (a₄ a₆ : ℤ) : ℕ :=
  {p : ℕ | localReductionDatum p a₄ a₆ = K}.ncard

end WeierstrassCurve

/-! ## The generating function -/

namespace BSDTamagawa.PrimeParam

/-- The parameter space `ℂ^Π`. -/
@[bsd_tamagawa "T014b"]
abbrev ParamSpace (P : Type*) := P → ℂ

end BSDTamagawa.PrimeParam

section

open BSDTamagawa.LocalReduction BSDTamagawa.PrimeParam

namespace BSDTamagawa.KodairaParam

/-- A finite set of reduction data is admissible if it is disjoint from `𝒦₀`. -/
def Admissible (Λ : Finset ReductionData) : Prop :=
  ∀ K ∈ Λ, K ∉ WeierstrassCurve.K0

end BSDTamagawa.KodairaParam

end

namespace BSDTamagawa.MultiIndex

open BSDTamagawa.PrimeParam

variable {P : Type*} [Fintype P]

/-- The multi-index monomial `z^j = ∏_ℓ z_ℓ ^ j_ℓ`. -/
@[bsd_tamagawa "T014c"]
def multiMonomial (j : P → ℕ) (z : ParamSpace P) : ℂ :=
  ∏ ℓ, z ℓ ^ j ℓ

end BSDTamagawa.MultiIndex

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- The Kodaira monomial `𝐮^ω = ∏_{K ∈ Λ} u_K ^ ω_K(E)`. -/
@[bsd_tamagawa "T014d"]
noncomputable def kodairaMonomial (Λ : Finset (KodairaSymbol × ℕ)) (u : Λ → ℂ)
    (a₄ a₆ : ℤ) : ℂ :=
  multiMonomial (fun K : Λ => reductionOmega (K : KodairaSymbol × ℕ) a₄ a₆) u

end WeierstrassCurve

namespace WeierstrassCurve

/-- The valuation vector `v_Π(Tam(E)) = (v_ℓ(Tam(E)))_{ℓ ∈ Π}`. -/
@[bsd_tamagawa "T014e"]
noncomputable def tamagawaValuationVector (P : Finset ℕ) (a₄ a₆ : ℤ) (ℓ : P) : ℕ :=
  padicValNat ℓ (tamagawaProduct a₄ a₆)

open BSDTamagawa.MultiIndex

open scoped Classical in
/-- The local weight
`Φ(K; s, u, w, 𝐳, 𝐮) = u^{[c > 1]} w^{Ω(c)} 𝐳^{v_Π(c)} c^{-s} ∏_{K' ∈ Λ} u_{K'}^{[K = K']}`, where
`c = K.2` and `Ω` counts prime factors with multiplicity. -/
@[bsd_tamagawa "T015"]
noncomputable def localWeight (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ)
    (K : KodairaSymbol × ℕ) (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) : ℂ :=
  u ^ (if 1 < K.2 then 1 else 0) *
      w ^ ArithmeticFunction.cardFactors K.2 *
      multiMonomial (fun ℓ : P => padicValNat ℓ K.2) z *
      (K.2 : ℂ) ^ (-s) *
      multiMonomial (fun K' : Λ => if K = (K' : KodairaSymbol × ℕ) then 1 else 0) uΛ

end WeierstrassCurve

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

open scoped Classical in
/-- The generating function
`𝒵_{Λ,Π,X} = N(X)⁻¹ ∑_{H(E) ≤ X} u^{ω_Tam(E)} w^{Ω(Tam(E))} 𝐳^{v_Π(Tam(E))} Tam(E)^{-s} 𝐮^{ω_Λ(E)}`
with `E(a₄, a₆)` running over the nonsingular curves (and `0` when `N(X) = 0`). -/
@[bsd_tamagawa "T017"]
noncomputable def tamagawaGeneratingFunction (Λ : Finset (KodairaSymbol × ℕ))
    (P : Finset ℕ) (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) (X : ℝ) : ℂ :=
  (∑' q : ℤ × ℤ,
      if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
        u ^ tamagawaOmega q.1 q.2 *
          w ^ ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) *
          multiMonomial (tamagawaValuationVector P q.1 q.2) z *
          (tamagawaProduct q.1 q.2 : ℂ) ^ (-s) *
          kodairaMonomial Λ uΛ q.1 q.2
      else 0) / (integralShortNFCount X : ℂ)

end WeierstrassCurve

/-! ## Limiting densities, laws and moments -/

namespace WeierstrassCurve

/-- `π_r(X)`, the proportion of the nonsingular `E` of height at most `X` with `ω_Tam(E) = r`. -/
@[bsd_tamagawa "T041a"]
noncomputable def tamagawaOmegaProportion (r : ℕ) (X : ℝ) : ℝ :=
  ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
      ∧ tamagawaOmega q.1 q.2 = r }.ncard : ℝ) / integralShortNFCount X

open Filter Topology

/-- The proportion of the nonsingular `E` of height at most `X` with `Tam(E) = m`. -/
noncomputable def tamagawaProportion (m : ℕ) (X : ℝ) : ℝ :=
  ({ p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily
      ∧ tamagawaProduct p.1 p.2 = m }.ncard : ℝ) / integralShortNFCount X

/-- `P_Tam(m)`, the `limsup` of `tamagawaProportion m` as `X → ∞`, which is the limit whenever that
exists. -/
@[bsd_tamagawa "T018a"]
noncomputable def tamagawaDensity (m : ℕ) : ℝ :=
  limsup (tamagawaProportion m) atTop

end WeierstrassCurve

namespace WeierstrassCurve

open Filter

/-- `π_r = lim_{X → ∞} π_r(X)` (`limUnder`: a junk value if there is no limit). -/
@[bsd_tamagawa "T041c"]
noncomputable def tamagawaOmegaDensity (r : ℕ) : ℝ :=
  limUnder atTop fun X : ℝ => tamagawaOmegaProportion r X

end WeierstrassCurve

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- The scalar weight `ψ(t) = w^{Ω(t)} 𝐳^{v_Π(t)} t^{-s}`. -/
@[bsd_tamagawa "T036d"]
noncomputable def scalarWeight (P : Finset ℕ) (s w : ℂ) (z : P → ℂ) (t : ℕ) : ℂ :=
  w ^ ArithmeticFunction.cardFactors t *
      multiMonomial (fun ℓ : P => padicValNat ℓ t) z *
      (t : ℂ) ^ (-s)

end WeierstrassCurve

namespace WeierstrassCurve

/-- `h_p = ∑_{t ≥ 1} δ_p(t) ψ(t)` (a `tsum`, so `0` if not summable); `1` when `p` is not prime. -/
@[bsd_tamagawa "T036e"]
noncomputable def scalarLocalFactor (P : Finset ℕ) (p : ℕ) (s w : ℂ) (z : P → ℂ) : ℂ :=
  if h : p.Prime then
    ∑' t : ℕ, if t = 0 then 0 else ((@δ p ⟨h⟩ t).toReal : ℂ) * scalarWeight P s w z t
  else 1

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction

end WeierstrassCurve

end

namespace WeierstrassCurve

/-- The Euler factor `δ_p(1) + (1 - δ_p(1)) u`, the subtraction in `ℂ`; `1` when `p` is not
prime. -/
@[bsd_tamagawa "T041b"]
noncomputable def tamagawaOmegaEulerFactor (p : ℕ) (u : ℂ) : ℂ :=
  if h : p.Prime then
    ((@δ p ⟨h⟩ 1).toReal : ℂ) + (1 - ((@δ p ⟨h⟩ 1).toReal : ℂ)) * u
  else 1

open BSDTamagawa.MultiIndex

/-- `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x`, which is `h_p` at `Π = ∅`, `w = 1`, `s = -x`. -/
@[bsd_tamagawa "T059d"]
noncomputable def momentLocalFactor (p : ℕ) (x : ℝ) : ℂ :=
  scalarLocalFactor ∅ p (-(x : ℂ)) 1 isEmptyElim

end WeierstrassCurve

namespace WeierstrassCurve

/-- The moment `M_k = ∑_{m ≥ 1} P_Tam(m) m^k` (a `tsum`, so `0` if not summable). -/
@[bsd_tamagawa "T059c"]
noncomputable def tamagawaMoment (k : ℕ) : ℝ :=
  ∑' n : ℕ, tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction

end WeierstrassCurve

end

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction
open scoped ENNReal

/-- `δ_p(K)` as a real number; `0` when `p` is not prime. -/
noncomputable def stratumLocalMass (K : ReductionData) (p : ℕ) : ℝ :=
  if h : p.Prime then (@deltaP p ⟨h⟩ K).toReal else 0

end WeierstrassCurve

namespace WeierstrassCurve

/-- `π_Λ(𝐫; X)`, the proportion of the nonsingular `E` of height at most `X` with `ω_K(E) = r_K`
for every `K ∈ Λ`. -/
@[bsd_tamagawa "T040d"]
noncomputable def jointReductionOmegaProportion (Λ : Finset (KodairaSymbol × ℕ))
    (r : Λ → ℕ) (X : ℝ) : ℝ :=
  ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
      ∧ ∀ K : Λ, reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2 = r K }.ncard : ℝ)
    / integralShortNFCount X

open Filter

/-- `π_Λ(𝐫) = lim_{X → ∞} π_Λ(𝐫; X)` (`limUnder`). -/
@[bsd_tamagawa "T040f"]
noncomputable def jointReductionOmegaDensity (Λ : Finset (KodairaSymbol × ℕ))
    (r : Λ → ℕ) : ℝ :=
  limUnder atTop fun X : ℝ => jointReductionOmegaProportion Λ r X

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

variable {Λ : Finset ReductionData}

end WeierstrassCurve

end

namespace WeierstrassCurve

open MeasureTheory

/-- The joint law `P_Λ = ∑_𝐫 π_Λ(𝐫) δ_𝐫` on `ℤ_{≥0}^Λ`. -/
@[bsd_tamagawa "T040g"]
noncomputable def jointReductionOmegaMeasure (Λ : Finset (KodairaSymbol × ℕ)) :
    Measure (Λ → ℕ) :=
  Measure.sum fun r : Λ → ℕ =>
    ENNReal.ofReal (jointReductionOmegaDensity Λ r) • Measure.dirac r

end WeierstrassCurve

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology
open BSDTamagawa BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

variable {K : ReductionData}

/-- The marginal density `π_{K}(r)`: the joint density at `Λ = {K}`. -/
noncomputable def marginalReductionOmegaDensity (K : ReductionData) (r : ℕ) : ℝ :=
  jointReductionOmegaDensity {K} fun _ => r

end WeierstrassCurve

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology
open BSDTamagawa BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

variable {m : ℕ → ℝ}

section Pair

variable {K K' : ReductionData}

/-- The two-element set `{K, K'}` of distinct reduction data. -/
def pairFinset (K K' : ReductionData) (hne : K ≠ K') : Finset ReductionData :=
  Finset.cons K {K'} (by simpa using hne)

/-- `pairFinset K K' hne` is the two-element set `{K, K'}`. -/
theorem mem_pairFinset (hne : K ≠ K') {L : ReductionData} :
    L ∈ pairFinset K K' hne ↔ L = K ∨ L = K' := by
  rw [pairFinset, Finset.mem_cons, Finset.mem_singleton]

/-- The element `K` of `{K, K'}`. -/
def pairIndexFst (K K' : ReductionData) (hne : K ≠ K') : ↥(pairFinset K K' hne) :=
  ⟨K, (mem_pairFinset hne).mpr (Or.inl rfl)⟩

/-- The element `K'` of `{K, K'}`. -/
def pairIndexSnd (K K' : ReductionData) (hne : K ≠ K') : ↥(pairFinset K K' hne) :=
  ⟨K', (mem_pairFinset hne).mpr (Or.inr rfl)⟩

/-- The index type `↥{K, K'}` is exhausted by its two named elements. -/
theorem eq_pairIndexSnd_of_ne (hne : K ≠ K') {j : ↥(pairFinset K K' hne)}
    (h : j ≠ pairIndexFst K K' hne) : j = pairIndexSnd K K' hne := by
  rcases (mem_pairFinset hne).mp j.property with h1 | h1
  · exact absurd (Subtype.ext h1) h
  · exact Subtype.ext h1

/-- Distinct reduction data give distinct indices. -/
theorem pairIndexFst_ne_pairIndexSnd (hne : K ≠ K') :
    pairIndexFst K K' hne ≠ pairIndexSnd K K' hne := fun he => hne (congrArg Subtype.val he)

end Pair

section Main

variable {K K' : ReductionData}

/-- The multi-index on `{K, K'}` taking the value `q.1` at `K` and `q.2` at `K'`. -/
noncomputable def pairIndexOfProd (hne : K ≠ K') (q : ℕ × ℕ)
    (j : ↥(pairFinset K K' hne)) : ℕ :=
  open scoped Classical in if j = pairIndexFst K K' hne then q.1 else q.2

/-- The multi-index built from a pair carries the pair's first component at `K`. -/
@[simp]
theorem pairIndexOfProd_fst (hne : K ≠ K') (q : ℕ × ℕ) :
    pairIndexOfProd hne q (pairIndexFst K K' hne) = q.1 := by
  simp [pairIndexOfProd]

/-- The multi-index built from a pair carries the pair's second component at `K'`. -/
@[simp]
theorem pairIndexOfProd_snd (hne : K ≠ K') (q : ℕ × ℕ) :
    pairIndexOfProd hne q (pairIndexSnd K K' hne) = q.2 := by
  simp [pairIndexOfProd, (pairIndexFst_ne_pairIndexSnd hne).symm]

/-- `ℤ_{≥0}^{K, K'} ≃ ℤ_{≥0}²`, sending `𝐫` to `(r_K, r_{K'})`: the `K`-coordinate first. -/
noncomputable def pairIndexEquiv (hne : K ≠ K') : (↥(pairFinset K K' hne) → ℕ) ≃ ℕ × ℕ where
  toFun r := (r (pairIndexFst K K' hne), r (pairIndexSnd K K' hne))
  invFun q := pairIndexOfProd hne q
  left_inv r := by
    funext j
    by_cases h : j = pairIndexFst K K' hne
    · simp only [h, pairIndexOfProd_fst]
    · simp only [eq_pairIndexSnd_of_ne hne h, pairIndexOfProd_snd]
  right_inv q := Prod.ext (pairIndexOfProd_fst hne q) (pairIndexOfProd_snd hne q)

/-- The joint law `P_{K, K'}` moved to `ℤ_{≥0}²` along `pairIndexEquiv`. -/
noncomputable def pairReductionOmegaMeasure (K K' : ReductionData) (hne : K ≠ K') :
    Measure (ℕ × ℕ) :=
  (jointReductionOmegaMeasure (pairFinset K K' hne)).map (pairIndexEquiv hne)

end Main

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory

/-- The law `P = ∑_r π_r δ_r` of `ω_Tam` on `ℕ`. -/
@[bsd_tamagawa "T041d"]
noncomputable def tamagawaOmegaMeasure : Measure ℕ :=
  Measure.sum fun r : ℕ => ENNReal.ofReal (tamagawaOmegaDensity r) • Measure.dirac r

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory ProbabilityTheory Set
open BSDTamagawa

end WeierstrassCurve

namespace WeierstrassCurve

open Filter Topology
open BSDTamagawa

end WeierstrassCurve

namespace WeierstrassCurve

open Filter

/-- `Q_Π(𝐣)`, the limiting proportion of the nonsingular `E` with `v_Π(Tam(E)) = 𝐣`
(`limUnder`). -/
@[bsd_tamagawa "T044e"]
noncomputable def tamagawaValuationDensity (P : Finset ℕ) (j : P → ℕ) : ℝ :=
  limUnder atTop fun X : ℝ =>
    ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
        ∧ ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ }.ncard : ℝ)
      / integralShortNFCount X

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory

/-- The joint valuation law `P_Π = ∑_𝐣 Q_Π(𝐣) δ_𝐣` on `ℤ_{≥0}^Π`. -/
@[bsd_tamagawa "T044i"]
noncomputable def tamagawaValuationMeasure (P : Finset ℕ) : Measure (P → ℕ) :=
  Measure.sum fun j : P → ℕ =>
    ENNReal.ofReal (tamagawaValuationDensity P j) • Measure.dirac j

end WeierstrassCurve

namespace BSDTamagawa.ValuationMean

open Set
open WeierstrassCurve
open scoped ENNReal

/-- The unique index of the singleton parameter set `{ℓ}`. -/
def singletonIdx (ℓ : ℕ) : ↥({ℓ} : Finset ℕ) := ⟨ℓ, Finset.mem_singleton_self ℓ⟩

open MeasureTheory

end BSDTamagawa.ValuationMean

namespace WeierstrassCurve

open BSDTamagawa.ValuationMean MeasureTheory

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

end WeierstrassCurve

end

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex

variable (p : ℕ)

end WeierstrassCurve

end

namespace WeierstrassCurve

open Filter

/-- `ρ_b`, the limiting proportion of the nonsingular `E` with `Ω(Tam(E)) = b` (`limUnder`). -/
@[bsd_tamagawa "T046d"]
noncomputable def cardFactorsTamagawaDensity (b : ℕ) : ℝ :=
  limUnder atTop fun X : ℝ =>
    ({ p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily
        ∧ ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b }.ncard : ℝ)
      / integralShortNFCount X

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

end WeierstrassCurve

end

namespace WeierstrassCurve

open MeasureTheory

/-- The law `P_Ω = ∑_b ρ_b δ_b` of `Ω(Tam(E))` on `ℕ`. -/
@[bsd_tamagawa "T046h"]
noncomputable def cardFactorsTamagawaMeasure : Measure ℕ :=
  Measure.sum fun b : ℕ => ENNReal.ofReal (cardFactorsTamagawaDensity b) • Measure.dirac b

end WeierstrassCurve

namespace WeierstrassCurve

open BSDTamagawa.ValuationMean MeasureTheory

end WeierstrassCurve

namespace WeierstrassCurve

open scoped ENNReal

/-- The term `δ_p(t) v_r(t)` of `μ_{p,r} = ∑_t δ_p(t) v_r(t)`. -/
noncomputable def valuationTerm (p : ℕ) [Fact p.Prime] (r t : ℕ) : ℝ :=
  (δ p t).toReal * (padicValNat r t : ℝ)

/-- The term `δ_p(t) v_ℓ(t) v_{ℓ'}(t)` of the cross moment. -/
noncomputable def crossValuationTerm (p : ℕ) [Fact p.Prime] (ℓ ℓ' t : ℕ) : ℝ :=
  (δ p t).toReal * (padicValNat ℓ t : ℝ) * (padicValNat ℓ' t : ℝ)

/-- The marginal first moment `μ_{p,r} = ∑_{t ≥ 1} δ_p(t) v_r(t)`, as a real number. -/
noncomputable def valuationMoment (p : ℕ) [Fact p.Prime] (r : ℕ) : ℝ :=
  ∑' t : ℕ, valuationTerm p r t

/-- The cross-moment `∑_{t ≥ 1} δ_p(t) v_ℓ(t) v_{ℓ'}(t)`, as a real number. -/
noncomputable def crossValuationMoment (p : ℕ) [Fact p.Prime] (ℓ ℓ' : ℕ) : ℝ :=
  ∑' t : ℕ, crossValuationTerm p ℓ ℓ' t

/-- The local covariance
`C_p(ℓ, ℓ') = ∑_t δ_p(t) v_ℓ(t) v_{ℓ'}(t) - (∑_t δ_p(t) v_ℓ(t)) (∑_t δ_p(t) v_{ℓ'}(t))`. -/
@[bsd_tamagawa "T051"]
noncomputable def localCov (p : ℕ) [Fact p.Prime] (ℓ ℓ' : ℕ) : ℝ :=
  crossValuationMoment p ℓ ℓ' - valuationMoment p ℓ * valuationMoment p ℓ'

end WeierstrassCurve

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open BSDTamagawa

variable {p : ℕ} [Fact p.Prime]

section Pair

variable {ℓ ℓ' : ℕ}

/-- The element `ℓ` of `{ℓ, ℓ'}`. -/
def valPairFst (ℓ ℓ' : ℕ) : ↥({ℓ, ℓ'} : Finset ℕ) := ⟨ℓ, by simp⟩

/-- The element `ℓ'` of `{ℓ, ℓ'}`. -/
def valPairSnd (ℓ ℓ' : ℕ) : ↥({ℓ, ℓ'} : Finset ℕ) := ⟨ℓ', by simp⟩

/-- The index type `↥{ℓ, ℓ'}` is exhausted by its two named elements. -/
theorem eq_valPairSnd_of_ne {i : ↥({ℓ, ℓ'} : Finset ℕ)} (h : i ≠ valPairFst ℓ ℓ') :
    i = valPairSnd ℓ ℓ' := by
  have hi := i.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with h1 | h1
  · exact absurd (Subtype.ext h1) h
  · exact Subtype.ext h1

/-- Distinct primes give distinct indices. -/
theorem valPairFst_ne_valPairSnd (hne : ℓ ≠ ℓ') : valPairFst ℓ ℓ' ≠ valPairSnd ℓ ℓ' :=
  fun he => hne (congrArg Subtype.val he)

end Pair

section Main

variable {ℓ ℓ' : ℕ}

/-- The multi-index built from a pair, sending `ℓ ↦ r.1` and `ℓ' ↦ r.2`. -/
def valPairIndexOfProd (ℓ ℓ' : ℕ) (r : ℕ × ℕ) (i : ↥({ℓ, ℓ'} : Finset ℕ)) : ℕ :=
  if i = valPairFst ℓ ℓ' then r.1 else r.2

/-- The multi-index built from a pair carries the pair's first component at `ℓ`. -/
theorem valPairIndexOfProd_fst (r : ℕ × ℕ) :
    valPairIndexOfProd ℓ ℓ' r (valPairFst ℓ ℓ') = r.1 := by
  simp [valPairIndexOfProd]

/-- The multi-index built from a pair carries the pair's second component at `ℓ'`. -/
theorem valPairIndexOfProd_snd (hne : ℓ ≠ ℓ') (r : ℕ × ℕ) :
    valPairIndexOfProd ℓ ℓ' r (valPairSnd ℓ ℓ') = r.2 := by
  simp [valPairIndexOfProd, (valPairFst_ne_valPairSnd hne).symm]

/-- `ℤ_{≥0}^{ℓ, ℓ'} ≃ ℤ_{≥0}²`, sending `𝐣` to `(j_ℓ, j_{ℓ'})`: the `ℓ`-coordinate first. -/
def valPairIndexEquiv (hne : ℓ ≠ ℓ') : (↥({ℓ, ℓ'} : Finset ℕ) → ℕ) ≃ ℕ × ℕ where
  toFun j := (j (valPairFst ℓ ℓ'), j (valPairSnd ℓ ℓ'))
  invFun r := valPairIndexOfProd ℓ ℓ' r
  left_inv j := by
    funext i
    by_cases h : i = valPairFst ℓ ℓ'
    · simp only [h, valPairIndexOfProd_fst]
    · simp only [eq_valPairSnd_of_ne h, valPairIndexOfProd_snd hne]
  right_inv r := Prod.ext (valPairIndexOfProd_fst r) (valPairIndexOfProd_snd hne r)

/-- The joint valuation law `P_{ℓ, ℓ'}` moved to `ℤ_{≥0}²` along `valPairIndexEquiv`. -/
noncomputable def tamagawaValuationProdMeasure (ℓ ℓ' : ℕ) (hne : ℓ ≠ ℓ') : Measure (ℕ × ℕ) :=
  (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)).map (valPairIndexEquiv hne)

end Main

end WeierstrassCurve

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open BSDTamagawa

section Main

variable {ℓ ℓ' : ℕ}

end Main

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BSDTamagawa

section Main

variable {ℓ ℓ' : ℕ}

end Main

end WeierstrassCurve

section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex

variable (p : ℕ)

/-- The proportion of the nonsingular `E` of height at most `X` with `ω_Tam(E) = r` and
`Ω(Tam(E)) = b`. -/
noncomputable def jointOmegaCardFactorsProportion (r b : ℕ) (X : ℝ) : ℝ :=
  ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
      tamagawaOmega q.1 q.2 = r ∧
        ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2) = b}.ncard : ℝ)
    / integralShortNFCount X

/-- `π(r, b) = lim_{X → ∞}` of that proportion (`limUnder`). -/
noncomputable def jointOmegaCardFactorsDensity (r b : ℕ) : ℝ :=
  limUnder atTop fun X : ℝ => jointOmegaCardFactorsProportion r b X

end WeierstrassCurve

end

section

open Filter Topology

namespace WeierstrassCurve

open MeasureTheory

/-- The joint law `∑_{(r, b)} π(r, b) δ_{(r, b)}` of `(ω_Tam, Ω ∘ Tam)` on `ℕ²`. -/
noncomputable def jointOmegaCardFactorsMeasure : Measure (ℕ × ℕ) :=
  Measure.sum fun rb : ℕ × ℕ =>
    ENNReal.ofReal (jointOmegaCardFactorsDensity rb.1 rb.2) • Measure.dirac rb

end WeierstrassCurve

end
