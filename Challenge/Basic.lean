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

/-! # Local factors in the BSD conjecture: the formal challenge

The 21 objectives of `BSDTamagawa`, stated over Mathlib alone, with every definition they use
copied verbatim. The lemmas left open above the objectives only let those definitions elaborate.
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
    (ofShortNF a₄ a₆).IsShortNF :=
  sorry

/-- The integer pairs `(a₄, a₆)` whose short Weierstrass curve is nonsingular, `Δ ≠ 0`. (Mathlib's
`IsElliptic` asks for `Δ` to be a unit, which never holds over `ℤ`.) -/
def integralShortNFFamily : Set (ℤ × ℤ) :=
  { p | (ofShortNF p.1 p.2).Δ ≠ 0 }

/-- The naive height `H(a₄, a₆) = max(4|a₄|³, 27a₆²)`. -/
def integralShortNFHeight (a₄ a₆ : ℤ) : ℤ :=
  max (4 * (a₄.natAbs : ℤ) ^ 3) (27 * a₆ ^ 2)

/-- `N(X)`, the number of integer pairs `(a₄, a₆)` with `Δ ≠ 0` and height at most `X`. -/
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
theorem pow_root {p : ℕ} [ExpChar R p] [PerfectRing R p] (x : R) : root p x ^ p = x :=
  sorry

end CharP

namespace WeierstrassCurve

section CharTwo

variable [CharP R 2] {W : WeierstrassCurve R}

/-- In a reduced ring of characteristic `2`, `c₄ = 0` if and only if `a₁ = 0`. -/
@[simp]
theorem c₄_iff_a₁_eq_zero_of_char_two [IsReduced R] : W.c₄ = 0 ↔ W.a₁ = 0 :=
  sorry

/-- In a reduced ring of characteristic `2`, a singular Weierstrass curve with `a₁ = 0` has
`a₃ = 0`. -/
@[simp]
theorem a₃_of_a₁_eq_zero_of_char_two [IsReduced R] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) : W.a₃ = 0 :=
  sorry

end CharTwo

section CharThree

variable [CharP R 3] {W : WeierstrassCurve R}

/-- In a reduced ring of characteristic `3`, `c₄ = 0` if and only if `b₂ = 0`. -/
@[simp]
theorem c₄_iff_b₂_eq_zero_of_char_three [IsReduced R] : W.c₄ = 0 ↔ W.b₂ = 0 :=
  sorry

/-- In an integral domain of characteristic `3`, a singular Weierstrass curve with `b₂ = 0` has
`b₄ = 0`. -/
@[simp]
theorem b₄_of_b₂_eq_zero_of_char_three [IsDomain R] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) :
    W.b₄ = 0 :=
  sorry

end CharThree

namespace Affine

variable {W : Affine R}

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

section CharTwo

variable [CharP R 2]

/-- In a perfect ring of characteristic `2`, a singular point of a curve with `a₁ = 0` has
`x = root 2 a₄`. -/
@[simp]
theorem x_of_char_two [PerfectRing R 2] (ha₁ : W.a₁ = 0) (P : W.SingularPoint) :
    P.x = root 2 W.a₄ :=
  sorry

variable [IsReduced R]

/-- In a perfect reduced ring of characteristic `2`, a singular point of a singular curve with
`a₁ = 0` has `y = root 2 (a₂a₄ + a₆)`. -/
@[simp]
theorem y_of_char_two [PerfectRing R 2] (hΔ : W.Δ = 0) (ha₁ : W.a₁ = 0) (P : W.SingularPoint) :
    P.y = root 2 (W.a₂ * W.a₄ + W.a₆) :=
  sorry

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

/-- In a perfect integral domain of characteristic `3`, a singular point of a singular curve with
`b₂ = 0` has `x = -root 3 b₆`. -/
@[simp]
theorem x_of_char_three [PerfectRing R 3] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) (P : W.SingularPoint) :
    P.x = -root 3 W.b₆ :=
  sorry

/-- In a perfect integral domain of characteristic `3`, a singular point of a singular curve with
`b₂ = 0` has `y = a₃ - a₁ root 3 b₆`. -/
@[simp]
theorem y_of_char_three [PerfectRing R 3] (hΔ : W.Δ = 0) (hb₂ : W.b₂ = 0) (P : W.SingularPoint) :
    P.y = W.a₃ - W.a₁ * root 3 W.b₆ :=
  sorry

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
theorem x_of_c₄_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hc₄ : W.c₄ = 0)
    (P : W.SingularPoint) :
    P.x = -W.b₂ / 12 :=
  sorry

/-- Over a field of characteristic different from `2` and `3`, a singular point of a curve with
`c₄ = 0` has `y = (a₁b₂ - 12a₃)/24`. -/
@[simp]
theorem y_of_c₄_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hc₄ : W.c₄ = 0)
    (P : W.SingularPoint) :
    P.y = (W.a₁ * b₂ W - 12 * W.a₃) / 24 :=
  sorry

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

variable {W : Affine F}

/-- Over a field, a singular point of a curve with `c₄ ≠ 0` has `x = (18b₆ - b₂b₄)/c₄`. -/
@[simp]
theorem x_of_c₄_ne_zero (hc₄ : W.c₄ ≠ 0) (P : W.SingularPoint) :
    P.x = (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄ :=
  sorry

/-- Over a field, a singular point of a curve with `c₄ ≠ 0` has
`y = (a₁a₄b₂ - 2a₂a₃b₂ + 12a₃b₄ - 9a₁b₆)/c₄`. -/
@[simp]
theorem y_of_c₄_ne_zero (hc₄ : W.c₄ ≠ 0) (P : W.SingularPoint) : P.y =
    (W.a₁ * W.a₄ * W.b₂ - 2 * W.a₂ * W.a₃ * W.b₂ + 12 * W.a₃ * W.b₄ - 9 * W.a₁ * W.b₆) / W.c₄ :=
  sorry

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

/-! ## Tate's algorithm -/

section

attribute [instance] Ideal.Quotient.field

universe u

variable {R : Type u} [CommRing R]

namespace CommRing

/-- The canonical surjection from a commutative ring to its residue field at a prime. -/
def mod (ϖ : R) : R →+* R ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.mk _

/-- The image of `x` in `R ⧸ (ϖ)` is zero if and only if `ϖ ∣ x`. -/
@[simp]
theorem mod_eq_zero (ϖ x : R) : mod ϖ x = 0 ↔ ϖ ∣ x :=
  sorry

open scoped Classical in
/-- A better abbreviation for `IsDiscreteValuationRing.quotient`. -/
noncomputable def div (x y : R) : R :=
  if y = 0 then 0 else if h : y ∣ x then h.choose else 0

variable [NoZeroDivisors R]

end CommRing

namespace Cubic

/-- The proposition that a cubic has a double root. -/
def HasDoubleRoot (P : Cubic R) : Prop :=
  P.discr = 0

/-- The proposition that a cubic has a triple root. -/
def HasTripleRoot (P : Cubic R) : Prop :=
  P.b ^ 2 = 3 * P.c

end Cubic

section Ideal

/-- A nonzero `ϖ` generating a maximal ideal is prime. -/
theorem Ideal.IsMaximal.prime {ϖ : R} [span {ϖ} |>.IsMaximal] (hϖ : ϖ ≠ 0) : Prime ϖ :=
  sorry

/-- If `(x)` is a proper ideal of a Noetherian domain, then `x` has finite multiplicity in `y` if
and only if `y ≠ 0`. -/
theorem FiniteMultiplicity.span_ne_top [IsNoetherianRing R] [IsDomain R] {x y : R}
    (h : Ideal.span {x} ≠ ⊤) : FiniteMultiplicity x y ↔ y ≠ 0 :=
  sorry

/-- If `(x)` is a proper ideal of a Noetherian domain, then the multiplicity of `x` in `y` is
infinite if and only if `y = 0`. -/
theorem emultiplicity_of_span_ne_top [IsNoetherianRing R] [IsDomain R] {x y : R}
    (h : Ideal.span {x} ≠ ⊤) : emultiplicity x y = ⊤ ↔ y = 0 :=
  sorry

end Ideal

end

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

variable {ϖ W}

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

/-- The change of variables of Step 7 preserves `Δ`. -/
@[simp] theorem translate_Δ : (translate ϖ W).Δ = W.Δ :=
  sorry

variable {ϖ W}

/-- If `ϖ ∣ a₂` and the cubic `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` has a double root but no triple root,
then `ϖ² ∤ a₂` after the change of variables of Step 7. -/
theorem not_dvd_translate_a₂ [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    (ha₂ : ϖ ^ 1 ∣ W.a₂) (h : cubic ϖ W 1 1 |>.HasDoubleRoot)
    (h' : ¬(cubic ϖ W 1 1).HasTripleRoot) : ¬ϖ ^ 2 ∣ (translate ϖ W).a₂ :=
  sorry

/-- If the cubic `X³ + a₂X²/ϖ + a₄X/ϖ² + a₆/ϖ³` has a double root but no triple root, the change of
variables of Step 7 gives the valuations `(1, 1, 2, 3, 4)` on `(a₁, a₂, a₃, a₄, a₆)`. -/
theorem hasValuation_translate [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] (hϖ : ϖ ≠ 0)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ} (hW : HasValuation ϖ W ⟨1, 1, 2, 2, 3, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (h : cubic ϖ W 1 1 |>.HasDoubleRoot) (h' : ¬(cubic ϖ W 1 1).HasTripleRoot) :
    HasValuation ϖ (translate ϖ W) ⟨1, 1, 2, 3, 4, 1, 3, 4, 5, 2, 3, 7⟩ :=
  sorry

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

/-- The change of variables `translateY` preserves `Δ`. -/
@[simp] theorem translateY_Δ (n : ℕ) : (translateY ϖ W n).Δ = W.Δ :=
  sorry

variable {ϖ W}

/-- If `ϖ² ∤ a₂`, then `ϖ² ∤ a₂` after the change of variables `translateY`. -/
theorem not_dvd_translateY_a₂ (n : ℕ) (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) : ¬ϖ ^ 2 ∣ (translateY ϖ W n).a₂ :=
  sorry

/-- If the quadratic `Y² + a₃Y/ϖⁿ - a₆/ϖ²ⁿ` has a double root, `translateY` raises the valuations
of `a₃` and `a₆` to `n + 1` and `2n + 1`. -/
theorem hasValuation_translateY [NoZeroDivisors R] [PerfectField <| R ⧸ span {ϖ}] {n : ℕ}
    (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (h : quadratic ϖ W n |>.HasDoubleRoot) : HasValuation ϖ (translateY ϖ W n) ⟨1, 1, n + 1,
      n + 1, 2 * n + 1, 1, n + 1, 2 * n + 1, 2 * n + 2, 2, 3, 2 * n + 4⟩ :=
  sorry

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

/-- The change of variables `translateX` preserves `Δ`. -/
@[simp] theorem translateX_Δ (n : ℕ) : (translateX ϖ W n).Δ = W.Δ :=
  sorry

variable {ϖ W}

/-- For `n ≥ 2`, if `ϖ ∣ a₂` and `ϖ² ∤ a₂`, then `ϖ² ∤ a₂` after the change of variables
`translateX`. -/
theorem not_dvd_translateX_a₂ [NoZeroDivisors R] {n : ℕ} (hn : 2 ≤ n) (hϖ : ϖ ≠ 0)
    (ha₂ : ϖ ^ 1 ∣ W.a₂) (ha₂' : ¬ϖ ^ 2 ∣ W.a₂) : ¬ϖ ^ 2 ∣ (translateX ϖ W n).a₂ :=
  sorry

/-- If the polynomial `a₂X²/ϖ + a₄X/ϖⁿ⁺¹ + a₆/ϖ²ⁿ⁺¹` has a double root, `translateX` raises the
valuations of `a₄` and `a₆` to `n + 2` and `2n + 2`. -/
theorem hasValuation_translateX [NoZeroDivisors R] [hR : PerfectField <| R ⧸ span {ϖ}] {n : ℕ}
    (hn : 2 ≤ n) (hϖ : ϖ ≠ 0) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n + 1, n + 1, 2 * n + 1, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) (h : cubic ϖ W 0 n |>.HasDoubleRoot) : HasValuation ϖ (translateX ϖ W n)
      ⟨1, 1, n + 1, n + 2, 2 * n + 2, 1, n + 2, 2 * n + 2, 2 * n + 3, 2, 3, 2 * n + 5⟩ :=
  sorry

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

variable {ϖ W}

end Step8

namespace Step9

/-- The change of variables that translates the double root `Y = t` to `Y = 0`. -/
noncomputable abbrev translate : WeierstrassCurve R := Step7.translateY ϖ W 2

end Step9

namespace Step11

/-- The change of variables that divides each coefficient `aᵢ` by `ϖ ^ i`. -/
noncomputable def translate : WeierstrassCurve R :=
  ⟨div W.a₁ ϖ, div W.a₂ <| ϖ ^ 2, div W.a₃ <| ϖ ^ 3, div W.a₄ <| ϖ ^ 4, div W.a₆ <| ϖ ^ 6⟩

variable [IsReduced R] {ϖ : R} {W : WeierstrassCurve R}

end Step11

end WeierstrassCurve.TateAlgorithm

end

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

end Step2

namespace Step3

open scoped Classical in
variable (ϖ W) in
/-- Step 3 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step2.run ϖ W >>= fun W ↦
  if ϖ ^ 2 ∣ W.a₆ then ok W else error ⟨W, .II, 1⟩

variable {W' : WeierstrassCurve R}

end Step3

namespace Step4

open scoped Classical in
variable (ϖ W) in
/-- Step 4 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step3.run ϖ W >>= fun W ↦
  if ϖ ^ 3 ∣ W.b₈ then ok W else error ⟨W, .III, 2⟩

variable {W' : WeierstrassCurve R}

end Step4

namespace Step5

open scoped Classical in
variable (ϖ W) in
/-- Step 5 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step4.run ϖ W >>= fun W ↦
  if ϖ ^ 3 ∣ W.b₆ then ok W else error ⟨W, .IV, if quadratic ϖ W 1 |>.toPoly.Splits then 3 else 1⟩

variable {W' : WeierstrassCurve R}

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
theorem run_hasDoubleRoot (h : run ϖ W = ok W') : cubic ϖ W' 1 1 |>.HasDoubleRoot :=
  sorry

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then `W'.Δ = W.Δ`. -/
theorem run_Δ (h : run ϖ W = ok W') : W'.Δ = W.Δ :=
  sorry

/-- If Step 6 of Tate's algorithm continues with a curve `W'`, then the `ϖ`-adic valuations of
`(a₁, a₂, a₃, a₄, a₆)` of `W'` are at least `(1, 1, 2, 2, 3)`. -/
theorem run_hasValuation [NoZeroDivisors R] (hϖ : ϖ ≠ 0) (h : run ϖ W = ok W') :
    HasValuation ϖ W' ⟨1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 3, 6⟩ :=
  sorry

end Step6

variable [IsNoetherianRing R] [IsDomain R]

namespace Step7

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

end Step7

namespace Step8

open scoped Classical in
/-- Step 8 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step7.run hϖ hΔ >>= fun W ↦
  letI W : WeierstrassCurve R := translate ϖ W
  if quadratic ϖ W 2 |>.HasDoubleRoot then ok W else
    error ⟨W, .IV!, if quadratic ϖ W 2 |>.toPoly.Splits then 3 else 1⟩

variable {W' : WeierstrassCurve R}

end Step8

namespace Step9

open scoped Classical in
/-- Step 9 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step8.run hϖ hΔ >>= fun W ↦
  letI W : WeierstrassCurve R := translate ϖ W
  if ϖ ^ 4 ∣ W.a₄ then ok W else error ⟨W, .III!, 2⟩

variable {W' : WeierstrassCurve R}

end Step9

namespace Step10

open scoped Classical in
/-- Step 10 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) := Step9.run hϖ hΔ >>= fun W ↦
  if ϖ ^ 6 ∣ W.a₆ then ok W else error ⟨W, .II!, 1⟩

variable {W' : WeierstrassCurve R}

end Step10

namespace Step11

open scoped Classical in
/-- Step 11 of Tate's algorithm. -/
noncomputable def run : Except (Output R) (WeierstrassCurve R) :=
  Step10.run hϖ hΔ >>= fun W ↦ ok <| translate ϖ W

variable {W' : WeierstrassCurve R}

/-- If Step 11 of Tate's algorithm continues with a curve `W'`, then `ϖ¹² * W'.Δ = W.Δ`. -/
theorem run_Δ (h : run hϖ hΔ = ok W') : ϖ ^ 12 * W'.Δ = W.Δ :=
  sorry

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
  sorry

/-- The ideal `(p)` of `ℤ_[p]` is maximal. -/
instance instIsMaximalSpanSingletonSetCast_bSDTamagawa : span {(p : ℤ_[p])} |>.IsMaximal :=
  sorry

/-- The residue field `ℤ_[p] ⧸ (p)` is perfect. -/
instance instPerfectFieldQuotientIdealSpanSingletonSetCast_bSDTamagawa :
    PerfectField <| ℤ_[p] ⧸ span {(p : ℤ_[p])} :=
  sorry

/-- The Borel `σ`-algebra on `ℤ_[p]`. -/
@[nolint defsWithUnderscore]
noncomputable instance instMeasurableSpace_bSDTamagawa : MeasurableSpace ℤ_[p] := borel _

/-- The measurable structure on `ℤ_[p]` is the Borel one. -/
instance instBorelSpace_bSDTamagawa : BorelSpace ℤ_[p] :=
  sorry

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
noncomputable instance measureSpace [MeasureSpace R] : MeasureSpace <| Elliptic R :=
  Subtype.measureSpace

end Elliptic

end ShortNF

end WeierstrassCurve

end

namespace WeierstrassCurve

/-- The trivial reduction data `𝒦₀ = {(I₀, 1), (I₁, 1)}`. Split and non-split `I₁` are not
distinguished. -/
def K0 : Set (KodairaSymbol × ℕ) := {(KodairaSymbol.I 0, 1), (KodairaSymbol.I 1, 1)}

namespace ShortNF

variable {p : ℕ} [Fact p.Prime]

/-- A nonsingular integer pair gives a nonsingular model over `ℤ_[p]`. -/
theorem ofProd_intCast_mem_Elliptic {a₄ a₆ : ℤ} (h : (ofShortNF a₄ a₆).Δ ≠ 0) :
    ofProd (a₄ : ℤ_[p]) (a₆ : ℤ_[p]) ∈ Elliptic ℤ_[p] :=
  sorry

end ShortNF

/-- The reduction map `τ_p`: Tate's algorithm at `p` on `E(a₄, a₆)` over `ℤ_[p]`. On the singular
locus, where it is irrelevant, the value is good reduction. -/
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
noncomputable def deltaP (K : KodairaSymbol × ℕ) : ENNReal :=
  MeasureTheory.volume
    {W : ShortNF.Elliptic ℤ_[p] |
      ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = K}

end WeierstrassCurve

namespace WeierstrassCurve

/-- The local Tamagawa number `c_p(E)` of `E(a₄, a₆)`, read off Tate's algorithm; `1` when `p` is
not prime. -/
noncomputable def localTamagawaNumber (p : ℕ) (a₄ a₆ : ℤ) : ℕ :=
  if h : p.Prime then (@tauZ p ⟨h⟩ a₄ a₆).tamagawaNumber else 1

/-- The Tamagawa product `Tam(E) = ∏_p c_p(E)`, a `finprod` (which is `1` on an infinite
support). -/
noncomputable def tamagawaProduct (a₄ a₆ : ℤ) : ℕ :=
  ∏ᶠ p : ℕ, localTamagawaNumber p a₄ a₆

/-- `ω_Tam(E)`, the number of primes `p` with `c_p(E) > 1`. -/
noncomputable def tamagawaOmega (a₄ a₆ : ℤ) : ℕ :=
  {p : ℕ | 1 < localTamagawaNumber p a₄ a₆}.ncard

end WeierstrassCurve

section

open WeierstrassCurve

namespace BSDTamagawa.LocalReduction

/-- A local reduction datum: a Kodaira symbol and a Tamagawa number. -/
abbrev ReductionData : Type := KodairaSymbol × ℕ

end BSDTamagawa.LocalReduction

end

section

open MeasureTheory

variable {p : ℕ} [Fact p.Prime]

namespace WeierstrassCurve

variable (p) in
/-- `δ_p(n)`, the `μ_p`-measure of the models over `ℤ_[p]` with local Tamagawa number `n`. -/
noncomputable def δ (n : ℕ) : ENNReal :=
  volume {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = n}

end WeierstrassCurve

end

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-- `β_p = ∑_{K ∈ 𝒦₀} δ_p(K)`. -/
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
noncomputable def reductionOmega (K : KodairaSymbol × ℕ) (a₄ a₆ : ℤ) : ℕ :=
  {p : ℕ | localReductionDatum p a₄ a₆ = K}.ncard

end WeierstrassCurve

/-! ## The generating function -/

namespace BSDTamagawa.PrimeParam

/-- The parameter space `ℂ^Π`. -/
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
def multiMonomial (j : P → ℕ) (z : ParamSpace P) : ℂ :=
  ∏ ℓ, z ℓ ^ j ℓ

end BSDTamagawa.MultiIndex

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- The Kodaira monomial `𝐮^ω = ∏_{K ∈ Λ} u_K ^ ω_K(E)`. -/
noncomputable def kodairaMonomial (Λ : Finset (KodairaSymbol × ℕ)) (u : Λ → ℂ)
    (a₄ a₆ : ℤ) : ℂ :=
  multiMonomial (fun K : Λ => reductionOmega (K : KodairaSymbol × ℕ) a₄ a₆) u

end WeierstrassCurve

namespace WeierstrassCurve

/-- The valuation vector `v_Π(Tam(E)) = (v_ℓ(Tam(E)))_{ℓ ∈ Π}`. -/
noncomputable def tamagawaValuationVector (P : Finset ℕ) (a₄ a₆ : ℤ) (ℓ : P) : ℕ :=
  padicValNat ℓ (tamagawaProduct a₄ a₆)

open BSDTamagawa.MultiIndex

open scoped Classical in
/-- The local weight
`Φ(K; s, u, w, 𝐳, 𝐮) = u^{[c > 1]} w^{Ω(c)} 𝐳^{v_Π(c)} c^{-s} ∏_{K' ∈ Λ} u_{K'}^{[K = K']}`, where
`c = K.2` and `Ω` counts prime factors with multiplicity. -/
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
noncomputable def tamagawaDensity (m : ℕ) : ℝ :=
  limsup (tamagawaProportion m) atTop

end WeierstrassCurve

namespace WeierstrassCurve

open Filter

/-- `π_r = lim_{X → ∞} π_r(X)` (`limUnder`: a junk value if there is no limit). -/
noncomputable def tamagawaOmegaDensity (r : ℕ) : ℝ :=
  limUnder atTop fun X : ℝ => tamagawaOmegaProportion r X

end WeierstrassCurve

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- The scalar weight `ψ(t) = w^{Ω(t)} 𝐳^{v_Π(t)} t^{-s}`. -/
noncomputable def scalarWeight (P : Finset ℕ) (s w : ℂ) (z : P → ℂ) (t : ℕ) : ℂ :=
  w ^ ArithmeticFunction.cardFactors t *
      multiMonomial (fun ℓ : P => padicValNat ℓ t) z *
      (t : ℂ) ^ (-s)

end WeierstrassCurve

namespace WeierstrassCurve

/-- `h_p = ∑_{t ≥ 1} δ_p(t) ψ(t)` (a `tsum`, so `0` if not summable); `1` when `p` is not prime. -/
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
noncomputable def tamagawaOmegaEulerFactor (p : ℕ) (u : ℂ) : ℂ :=
  if h : p.Prime then
    ((@δ p ⟨h⟩ 1).toReal : ℂ) + (1 - ((@δ p ⟨h⟩ 1).toReal : ℂ)) * u
  else 1

open BSDTamagawa.MultiIndex

/-- `G_p(x) = ∑_{t ≥ 1} δ_p(t) t^x`, which is `h_p` at `Π = ∅`, `w = 1`, `s = -x`. -/
noncomputable def momentLocalFactor (p : ℕ) (x : ℝ) : ℂ :=
  scalarLocalFactor ∅ p (-(x : ℂ)) 1 isEmptyElim

end WeierstrassCurve

namespace WeierstrassCurve

/-- The moment `M_k = ∑_{m ≥ 1} P_Tam(m) m^k` (a `tsum`, so `0` if not summable). -/
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
noncomputable def jointReductionOmegaProportion (Λ : Finset (KodairaSymbol × ℕ))
    (r : Λ → ℕ) (X : ℝ) : ℝ :=
  ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
      ∧ ∀ K : Λ, reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2 = r K }.ncard : ℝ)
    / integralShortNFCount X

open Filter

/-- `π_Λ(𝐫) = lim_{X → ∞} π_Λ(𝐫; X)` (`limUnder`). -/
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
    L ∈ pairFinset K K' hne ↔ L = K ∨ L = K' :=
  sorry

/-- The element `K` of `{K, K'}`. -/
def pairIndexFst (K K' : ReductionData) (hne : K ≠ K') : ↥(pairFinset K K' hne) :=
  ⟨K, (mem_pairFinset hne).mpr (Or.inl rfl)⟩

/-- The element `K'` of `{K, K'}`. -/
def pairIndexSnd (K K' : ReductionData) (hne : K ≠ K') : ↥(pairFinset K K' hne) :=
  ⟨K', (mem_pairFinset hne).mpr (Or.inr rfl)⟩

/-- The index type `↥{K, K'}` is exhausted by its two named elements. -/
theorem eq_pairIndexSnd_of_ne (hne : K ≠ K') {j : ↥(pairFinset K K' hne)}
    (h : j ≠ pairIndexFst K K' hne) : j = pairIndexSnd K K' hne :=
  sorry

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
    pairIndexOfProd hne q (pairIndexFst K K' hne) = q.1 :=
  sorry

/-- The multi-index built from a pair carries the pair's second component at `K'`. -/
@[simp]
theorem pairIndexOfProd_snd (hne : K ≠ K') (q : ℕ × ℕ) :
    pairIndexOfProd hne q (pairIndexSnd K K' hne) = q.2 :=
  sorry

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
noncomputable def tamagawaValuationDensity (P : Finset ℕ) (j : P → ℕ) : ℝ :=
  limUnder atTop fun X : ℝ =>
    ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
        ∧ ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ }.ncard : ℝ)
      / integralShortNFCount X

end WeierstrassCurve

namespace WeierstrassCurve

open MeasureTheory

/-- The joint valuation law `P_Π = ∑_𝐣 Q_Π(𝐣) δ_𝐣` on `ℤ_{≥0}^Π`. -/
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
    i = valPairSnd ℓ ℓ' :=
  sorry

end Pair

section Main

variable {ℓ ℓ' : ℕ}

/-- The multi-index built from a pair, sending `ℓ ↦ r.1` and `ℓ' ↦ r.2`. -/
def valPairIndexOfProd (ℓ ℓ' : ℕ) (r : ℕ × ℕ) (i : ↥({ℓ, ℓ'} : Finset ℕ)) : ℕ :=
  if i = valPairFst ℓ ℓ' then r.1 else r.2

/-- The multi-index built from a pair carries the pair's first component at `ℓ`. -/
theorem valPairIndexOfProd_fst (r : ℕ × ℕ) :
    valPairIndexOfProd ℓ ℓ' r (valPairFst ℓ ℓ') = r.1 :=
  sorry

/-- The multi-index built from a pair carries the pair's second component at `ℓ'`. -/
theorem valPairIndexOfProd_snd (hne : ℓ ≠ ℓ') (r : ℕ × ℕ) :
    valPairIndexOfProd ℓ ℓ' r (valPairSnd ℓ ℓ') = r.2 :=
  sorry

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

/-! ## The law of `ω_K` -/

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology
open BSDTamagawa BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex

variable {K : ReductionData}

/-- The marginal densities are nonnegative. -/
theorem marginalReductionOmegaDensity_nonneg (hK : K ∉ (K0 : Set ReductionData)) (r : ℕ) :
    0 ≤ marginalReductionOmegaDensity K r :=
  sorry

/-- The marginal densities sum to `1`. -/
theorem hasSum_marginalReductionOmegaDensity_one (hK : K ∉ (K0 : Set ReductionData)) :
    HasSum (marginalReductionOmegaDensity K) 1 :=
  sorry

/-- The law of `ω_K(E)` as a `PMF ℕ`, with mass `π_{K}(r)` at `r`. -/
noncomputable def marginalReductionOmegaPMF (hK : K ∉ (K0 : Set ReductionData)) : PMF ℕ :=
  ⟨fun r => ENNReal.ofReal (marginalReductionOmegaDensity K r),
    ENNReal.summable.hasSum_iff.mpr <| by
      rw [← ENNReal.ofReal_tsum_of_nonneg (marginalReductionOmegaDensity_nonneg hK)
          (hasSum_marginalReductionOmegaDensity_one hK).summable,
        (hasSum_marginalReductionOmegaDensity_one hK).tsum_eq, ENNReal.ofReal_one]⟩

end WeierstrassCurve

/-! ## The objectives -/

namespace BSDTamagawa.Challenge

open Filter Topology MeasureTheory ProbabilityTheory WeierstrassCurve

open BSDTamagawa.LocalReduction in
/-- **`T036` — the master Euler product.** For a finite `Λ ⊆ 𝒦 ∖ 𝒦₀`, a finite set of primes `Π`
and parameters with `Re(s) ≥ 0` and `‖u‖, ‖w‖, ‖z_ℓ‖, ‖u_K‖ ≤ 1`, `𝒵_{Λ,Π,X}` tends to
`∏_p (β_p + ∑_{K ∉ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮))`; the product converges absolutely, and
uniformly on every compact set of such parameters. -/
theorem T036 :
    (∀ (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ},
      (∀ K ∈ Λ, K ∉ K0) → (∀ ℓ ∈ P, Nat.Prime ℓ) → 0 ≤ s.re → ‖u‖ ≤ 1 → ‖w‖ ≤ 1 →
      (∀ ℓ : P, ‖z ℓ‖ ≤ 1) → (∀ K : Λ, ‖uΛ K‖ ≤ 1) →
      Tendsto (tamagawaGeneratingFunction Λ P s u w z uΛ) atTop
        (𝓝 (∏' p : {q : ℕ // q.Prime},
          (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
            ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
              * localWeight Λ P (K : ReductionData) s u w z uΛ)))) ∧
    (∀ (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ},
      0 ≤ s.re → ‖u‖ ≤ 1 → ‖w‖ ≤ 1 → (∀ ℓ : P, ‖z ℓ‖ ≤ 1) → (∀ K : Λ, ‖uΛ K‖ ≤ 1) →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight Λ P (K : ReductionData) s u w z uΛ) ∧
    (∀ (Λ : Finset ReductionData) (P : Finset ℕ) {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))},
      IsCompact D →
      (∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
        (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) →
      HasProdUniformlyOn
        (fun (p : {q : ℕ // q.Prime}) (x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)) =>
          ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
            ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
              * localWeight Λ P (K : ReductionData) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (fun x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ) =>
          ∏' p : {q : ℕ // q.Prime},
            (((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
              ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
                * localWeight Λ P (K : ReductionData) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
        D) :=
  sorry

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.MultiIndex in
/-- **`T040a` — the joint law of the reduction counts.** For an admissible finite `Λ`, the joint
density `π_Λ(𝐫)` exists for every `𝐫`,
`∑_𝐫 π_Λ(𝐫) 𝐮^𝐫 = ∏_p (1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K)`, and the product converges
absolutely and locally uniformly on `ℂ^Λ`. -/
theorem T040a :
    (∀ {Λ : Finset ReductionData}, Admissible Λ → ∀ (r : Λ → ℕ),
      Tendsto (fun X : ℝ =>
          ({ q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
              ∧ ∀ K : Λ, reductionOmega (K : ReductionData) q.1 q.2 = r K }.ncard : ℝ)
            / integralShortNFCount X)
        atTop (𝓝 (jointReductionOmegaDensity Λ r))) ∧
    (∀ {Λ : Finset ReductionData}, Admissible Λ → ∀ (u : Λ → ℂ),
      ∑' r : Λ → ℕ, ((jointReductionOmegaDensity Λ r : ℝ) : ℂ) * multiMonomial r u
        = ∏' p : {q : ℕ // q.Prime},
          (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K)) ∧
    (∀ {Λ : Finset ReductionData}, Admissible Λ → ∀ (u : Λ → ℂ),
      Multipliable fun p : {q : ℕ // q.Prime} =>
        1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
          + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * u K) ∧
    (∀ {Λ : Finset ReductionData}, Admissible Λ →
      HasProdLocallyUniformly
        (fun (p : {q : ℕ // q.Prime}) (v : Λ → ℂ) =>
          1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * v K)
        (fun v : Λ → ℂ => ∏' p : {q : ℕ // q.Prime},
          (1 - ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            + ∑ K : ↥Λ, ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ) * v K))) :=
  sorry

open BSDTamagawa.LocalReduction in
/-- **`T040b` — mean and variance of `ω_K`.** For `K ∉ 𝒦₀`, under the law of `ω_K(E)`,
`𝔼[ω_K] = ∑_p δ_p(K)` and `Var(ω_K) = ∑_p δ_p(K)(1 - δ_p(K))`, both series convergent. -/
theorem T040b :
    (∀ {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)),
      Summable (stratumLocalMass K) ∧
        ∫ n, (n : ℝ) ∂ (marginalReductionOmegaPMF hK).toMeasure
          = ∑' p : ℕ, stratumLocalMass K p) ∧
    (∀ {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)),
      Summable (fun p : ℕ => stratumLocalMass K p * (1 - stratumLocalMass K p)) ∧
        variance (fun n : ℕ => (n : ℝ)) (marginalReductionOmegaPMF hK).toMeasure
          = ∑' p : ℕ, stratumLocalMass K p * (1 - stratumLocalMass K p)) :=
  sorry

open BSDTamagawa.LocalReduction in
/-- **`T040c` — the covariance of `ω_K` and `ω_{K'}`.** For distinct `K, K' ∉ 𝒦₀`, under the joint
law, `Cov(ω_K, ω_{K'}) = -∑_p δ_p(K) δ_p(K')`, the series convergent; on `ℤ_{≥0}^{K, K'}` and on
`ℤ_{≥0}²`. -/
theorem T040c :
    (∀ {K K' : ReductionData}, K ∉ (K0 : Set ReductionData) → K' ∉ (K0 : Set ReductionData) →
      ∀ (hne : K ≠ K'),
      Summable (fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p) ∧
        covariance (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexFst K K' hne) : ℝ))
            (fun r : ↥(pairFinset K K' hne) → ℕ => (r (pairIndexSnd K K' hne) : ℝ))
            (jointReductionOmegaMeasure (pairFinset K K' hne))
          = -∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p) ∧
    (∀ {K K' : ReductionData}, K ∉ (K0 : Set ReductionData) → K' ∉ (K0 : Set ReductionData) →
      ∀ (hne : K ≠ K'),
      Summable (fun p : ℕ => stratumLocalMass K p * stratumLocalMass K' p) ∧
        covariance (fun q : ℕ × ℕ => (q.1 : ℝ)) (fun q : ℕ × ℕ => (q.2 : ℝ))
            (pairReductionOmegaMeasure K K' hne)
          = -∑' p : ℕ, stratumLocalMass K p * stratumLocalMass K' p) :=
  sorry

/-- **`T041` — the law of `ω_Tam`.** The density `π_r` exists for every `r`;
`∑_r π_r u^r = ∏_p (δ_p(1) + (1 - δ_p(1)) u)` for every `u ∈ ℂ`, the product converging absolutely
and locally uniformly; and `𝔼[ω_Tam] = ∑_p (1 - δ_p(1))`, `Var(ω_Tam) = ∑_p δ_p(1)(1 - δ_p(1))`,
both series convergent. -/
theorem T041 :
    (∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure
      = ∑' p : ℕ, if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) ∧
    (Summable fun p : ℕ => if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal)
      else 0) ∧
    (variance (fun n : ℕ => (n : ℝ)) tamagawaOmegaMeasure
      = ∑' p : ℕ, if h : p.Prime then (@δ p ⟨h⟩ 1).toReal * (1 - (@δ p ⟨h⟩ 1).toReal) else 0) ∧
    (∀ r : ℕ,
      Filter.Tendsto (fun X : ℝ =>
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
            tamagawaOmega q.1 q.2 = r}.ncard : ℝ) / integralShortNFCount X)
        Filter.atTop (nhds (tamagawaOmegaDensity r))) ∧
    (∀ u : ℂ,
      (∑' r : ℕ, ((tamagawaOmegaDensity r : ℝ) : ℂ) * u ^ r)
        = ∏' p : ℕ, (if h : p.Prime then
            ((@δ p ⟨h⟩ 1).toReal : ℂ) + (1 - ((@δ p ⟨h⟩ 1).toReal : ℂ)) * u else 1)) ∧
    (Summable fun p : ℕ => if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) ∧
    ((∀ u : ℂ, Multipliable fun p : ℕ => tamagawaOmegaEulerFactor p u) ∧
      HasProdLocallyUniformly tamagawaOmegaEulerFactor
        (fun u => ∏' p : ℕ, tamagawaOmegaEulerFactor p u)) :=
  sorry

/-- **`T042` — the densities `π_r` in closed form.**
`π_r = ∑_{S ⊆ 𝒫, |S| = r} ∏_{p ∈ S} (1 - δ_p(1)) ∏_{q ∉ S} δ_q(1)`, written out for `r = 0, 1, 2`,
with every series and product in it convergent. -/
theorem T042 :
    (∀ r : ℕ,
      tamagawaOmegaDensity r
        = ∑' S : {S : Finset ℕ // S.card = r},
            (∏ p ∈ (S : Finset ℕ), (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0)) *
              ∏' q : {x : ℕ // x ∉ (S : Finset ℕ)},
                (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (tamagawaOmegaDensity 0 = ∏' q : ℕ, (if h : q.Prime then (@δ q ⟨h⟩ 1).toReal else 1)) ∧
    (tamagawaOmegaDensity 1
      = ∑' p : ℕ, (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) *
          ∏' q : {x : ℕ // x ≠ p},
            (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (tamagawaOmegaDensity 2
      = ∑' pq : {pq : ℕ × ℕ // pq.1 < pq.2},
          (if h : (pq : ℕ × ℕ).1.Prime then 1 - (@δ (pq : ℕ × ℕ).1 ⟨h⟩ 1).toReal else 0) *
            (if h : (pq : ℕ × ℕ).2.Prime then 1 - (@δ (pq : ℕ × ℕ).2 ⟨h⟩ 1).toReal else 0) *
            ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
              (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (∀ S : Finset ℕ,
      Multipliable fun q : {x : ℕ // x ∉ S} =>
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (Multipliable fun q : ℕ => (if h : q.Prime then (@δ q ⟨h⟩ 1).toReal else 1)) ∧
    (∀ p : ℕ,
      Multipliable fun q : {x : ℕ // x ≠ p} =>
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (∀ p q : ℕ,
      Multipliable fun r : {x : ℕ // x ≠ p ∧ x ≠ q} =>
        (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (∀ r : ℕ,
      Summable fun S : {S : Finset ℕ // S.card = r} =>
        (∏ p ∈ (S : Finset ℕ), (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0)) *
          ∏' q : {x : ℕ // x ∉ (S : Finset ℕ)},
            (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (Summable fun p : ℕ => (if h : p.Prime then 1 - (@δ p ⟨h⟩ 1).toReal else 0) *
      ∏' q : {x : ℕ // x ≠ p},
        (if h : (q : ℕ).Prime then (@δ (q : ℕ) ⟨h⟩ 1).toReal else 1)) ∧
    (Summable fun pq : {pq : ℕ × ℕ // pq.1 < pq.2} =>
      (if h : (pq : ℕ × ℕ).1.Prime then 1 - (@δ (pq : ℕ × ℕ).1 ⟨h⟩ 1).toReal else 0) *
        (if h : (pq : ℕ × ℕ).2.Prime then 1 - (@δ (pq : ℕ × ℕ).2 ⟨h⟩ 1).toReal else 0) *
        ∏' r : {x : ℕ // x ≠ (pq : ℕ × ℕ).1 ∧ x ≠ (pq : ℕ × ℕ).2},
          (if h : (r : ℕ).Prime then (@δ (r : ℕ) ⟨h⟩ 1).toReal else 1)) :=
  sorry

open BSDTamagawa.ValuationMean in
/-- **`T043` — the mean of `v_ℓ(Tam)`.** For a prime `ℓ`, under the law of `v_ℓ(Tam(E))`,
`𝔼[v_ℓ(Tam)] = ∑_p ∑_{t ≥ 1} δ_p(t) v_ℓ(t)`, the double series convergent. -/
theorem T043 :
    ∀ {ℓ : ℕ}, ℓ.Prime →
      (Summable fun p : ℕ => if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0) ∧
        ∫ j, ((j (singletonIdx ℓ) : ℕ) : ℝ) ∂(tamagawaValuationMeasure {ℓ})
          = ∑' p : ℕ, if h : p.Prime then
              ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (((t.factorization) ℓ : ℕ) : ℝ) else 0 :=
  sorry

open BSDTamagawa.MultiIndex in
/-- **`T044a` — the joint law of the valuations of `Tam`.** For a finite set of primes `Π`, the
density `Q_Π(𝐣)` exists for every `𝐣`, and for `‖z_ℓ‖ ≤ 1`,
`∑_𝐣 Q_Π(𝐣) 𝐳^𝐣 = ∏_p ∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}`, the product converging absolutely
and uniformly on the closed polydisc. -/
theorem T044a :
    (∀ (P : Finset ℕ), (∀ ℓ ∈ P, Nat.Prime ℓ) → ∀ (j : P → ℕ),
      Tendsto (fun X : ℝ =>
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
            ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ}.ncard : ℝ) /
            integralShortNFCount X)
        atTop (𝓝 (tamagawaValuationDensity P j))) ∧
    (∀ (P : Finset ℕ), (∀ ℓ ∈ P, Nat.Prime ℓ) → ∀ {z : P → ℂ}, (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
      ∑' j : P → ℕ, ((tamagawaValuationDensity P j : ℝ) : ℂ) * multiMonomial j z
        = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) ∧
    (∀ (P : Finset ℕ) {z : P → ℂ}, (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) ∧
    (∀ (P : Finset ℕ) {z : P → ℂ}, (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
      Summable fun p : {q : ℕ // q.Prime} =>
        ‖(∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) - 1‖) ∧
    (∀ (P : Finset ℕ),
      HasProdUniformlyOn
        (fun (p : {q : ℕ // q.Prime}) (z : P → ℂ) =>
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
        (fun z : P → ℂ => ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
        {z : P → ℂ | ∀ ℓ : P, ‖z ℓ‖ ≤ 1}) :=
  sorry

/-- **`T044b` — no prime of `A` divides `Tam`.** For a finite set `A` of primes,
`P(ℓ ∤ Tam(E) for all ℓ ∈ A) = ∏_p ∑_{(t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t)`, the product convergent. -/
theorem T044b :
    (∀ (A : Finset ℕ), (∀ ℓ ∈ A, Nat.Prime ℓ) →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) ∧
    (∀ (A : Finset ℕ), (∀ ℓ ∈ A, Nat.Prime ℓ) →
      (tamagawaValuationMeasure A {j : A → ℕ | ∀ ℓ : A, j ℓ = 0}).toReal
        = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) :=
  sorry

/-- **`T044c` — `ℓ` divides `Tam`.** For a prime `ℓ`, `P(ℓ ∣ Tam(E)) = 1 - ∏_p ∑_{ℓ ∤ t} δ_p(t)`,
the product convergent. -/
theorem T044c :
    (∀ {l : ℕ}, l.Prime →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) ∧
    (∀ {l : ℕ}, l.Prime →
      (tamagawaValuationMeasure {l}
          {j : ↥({l} : Finset ℕ) → ℕ | j ⟨l, Finset.mem_singleton_self l⟩ ≠ 0}).toReal
        = 1 - ∏' p : {q : ℕ // q.Prime},
          ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) :=
  sorry

/-- **`T044d` — `Tam` is odd.** `P(Tam(E) odd) = ∏_p ∑_{t odd} δ_p(t)`, the product convergent. -/
theorem T044d :
    (Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ↥{t : ℕ | Odd t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) ∧
    ((tamagawaValuationMeasure {2}
        {j : ↥({2} : Finset ℕ) → ℕ | ∀ ℓ : ↥({2} : Finset ℕ), j ℓ = 0}).toReal
      = ∏' p : {q : ℕ // q.Prime}, ∑' t : ↥{t : ℕ | Odd t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal) :=
  sorry

open scoped Classical in
/-- **`T045` — the joint generating function of `(ω_Tam, Tam)`.** For `Re(s) ≥ 0` and `‖u‖ ≤ 1`,
`N(X)⁻¹ ∑_{H(E) ≤ X} u^{ω_Tam(E)} Tam(E)^{-s}` tends to
`∏_p (δ_p(1) + u ∑_{t ≥ 2} δ_p(t) t^{-s})`. -/
theorem T045 :
    ∀ {s u : ℂ}, 0 ≤ s.re → ‖u‖ ≤ 1 →
      Tendsto (fun X : ℝ =>
          (∑' q : ℤ × ℤ,
              if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
                u ^ tamagawaOmega q.1 q.2 * (tamagawaProduct q.1 q.2 : ℂ) ^ (-s)
              else 0) / (integralShortNFCount X : ℂ)) atTop
        (𝓝 (∏' p : {q : ℕ // q.Prime},
          (((@δ (p : ℕ) ⟨p.2⟩ 1).toReal : ℂ)
            + u * ∑' t : ℕ,
                if 2 ≤ t then ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) else 0))) :=
  sorry

/-- **`T046a` — the law of `Ω(Tam)`.** The density `ρ_b` exists for every `b`, and for `‖w‖ ≤ 1`,
`∑_b ρ_b w^b = ∏_p ∑_{t ≥ 1} δ_p(t) w^{Ω(t)}`, the product converging absolutely. -/
theorem T046a :
    (∀ b : ℕ,
      Tendsto (fun X : ℝ =>
          ({p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
            ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b}.ncard : ℝ) /
            integralShortNFCount X)
        atTop (𝓝 (cardFactorsTamagawaDensity b))) ∧
    (∀ {w : ℂ}, ‖w‖ ≤ 1 →
      ∑' b : ℕ, ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b
        = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t) ∧
    (∀ {w : ℂ}, ‖w‖ ≤ 1 →
      Multipliable fun p : {q : ℕ // q.Prime} =>
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t) ∧
    (∀ {w : ℂ}, ‖w‖ ≤ 1 →
      Summable fun p : {q : ℕ // q.Prime} =>
        ‖(∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t)
          - 1‖) :=
  sorry

/-- **`T046b` — the mean of `Ω(Tam)`.** `𝔼[Ω(Tam)] = ∑_p ∑_{t ≥ 1} δ_p(t) Ω(t)`, the double series
convergent. -/
theorem T046b :
    (Summable fun p : ℕ => if h : p.Prime then
        ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0) ∧
      ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
        = ∑' p : ℕ, if h : p.Prime then
            ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  sorry

/-- **`T046c` — `𝔼[ω_Tam] ≤ 𝔼[Ω(Tam)] < ∞`.** The second mean is the convergent double series
`∑_p ∑_{t ≥ 1} δ_p(t) Ω(t)`. -/
theorem T046c :
    (∫ n, (n : ℝ) ∂ tamagawaOmegaMeasure ≤ ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure) ∧
      (Summable fun p : ℕ => if h : p.Prime then
          ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0) ∧
        ∫ n, (n : ℝ) ∂ cardFactorsTamagawaMeasure
          = ∑' p : ℕ, if h : p.Prime then
              ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) else 0 :=
  sorry

/-- **`T057a` — the covariance of two valuations.** For distinct primes `ℓ, ℓ'`,
`Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) = ∑_p C_p(ℓ, ℓ')`, the series absolutely convergent; on
`ℤ_{≥0}^{ℓ, ℓ'}` and on `ℤ_{≥0}²`. -/
theorem T057a :
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
        covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
            (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
            (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))
          = ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ') ∧
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ∀ (hne : ℓ ≠ ℓ'),
      (Summable fun q : {n : ℕ // n.Prime} => |@localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ'|) ∧
        covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
            (tamagawaValuationProdMeasure ℓ ℓ' hne)
          = ∑' q : {n : ℕ // n.Prime}, @localCov (q : ℕ) ⟨q.2⟩ ℓ ℓ') :=
  sorry

/-- **`T057b` — the covariance is negative.** For distinct primes `ℓ, ℓ'`,
`Cov(v_ℓ(Tam), v_{ℓ'}(Tam)) < 0`; on `ℤ_{≥0}^{ℓ, ℓ'}` and on `ℤ_{≥0}²`. -/
theorem T057b :
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ)) < 0) ∧
    (∀ {ℓ ℓ' : ℕ}, ℓ.Prime → ℓ'.Prime → ∀ (hne : ℓ ≠ ℓ'),
      covariance (fun r : ℕ × ℕ => (r.1 : ℝ)) (fun r : ℕ × ℕ => (r.2 : ℝ))
          (tamagawaValuationProdMeasure ℓ ℓ' hne) < 0) :=
  sorry

/-- **`T057c` — the covariance decays.** There is an absolute `C > 0` with
`|Cov(v_ℓ(Tam), v_{ℓ'}(Tam))| ≤ C / (ℓℓ')²` for all distinct primes `ℓ, ℓ'`; in particular the
covariance tends to `0` as `ℓℓ' → ∞`. -/
theorem T057c :
    (∃ C : ℝ, 0 < C ∧ ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' →
      |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
          (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
          (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
        ≤ C / ((ℓ : ℝ) * (ℓ' : ℝ)) ^ 2) ∧
    (∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ≠ ℓ' → N ≤ ℓ * ℓ' →
        |covariance (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairFst ℓ ℓ') : ℝ))
            (fun j : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ => (j (valPairSnd ℓ ℓ') : ℝ))
            (tamagawaValuationMeasure ({ℓ, ℓ'} : Finset ℕ))|
          < ε) :=
  sorry

/-- **`T058` — the correlation of `ω_Tam` and `Ω(Tam)`.** Under their joint law,
`Cov(ω_Tam, Ω(Tam)) = ∑_p δ_p(1) ∑_{t ≥ 1} δ_p(t) Ω(t)`, the series absolutely convergent, and both
variances are positive, so the correlation is a well-defined real number. -/
theorem T058 :
    ((Summable fun p : ℕ => |if h : p.Prime then
        (@δ p ⟨h⟩ 1).toReal
          * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
        else 0|) ∧
      covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
          jointOmegaCardFactorsMeasure
        = ∑' p : ℕ, if h : p.Prime then
            (@δ p ⟨h⟩ 1).toReal
              * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
            else 0) ∧
    (0 < variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure ∧
      0 < variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure ∧
      0 < Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
            * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure) ∧
      covariance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) (fun rb : ℕ × ℕ => (rb.2 : ℝ))
            jointOmegaCardFactorsMeasure
          / Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
            * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure)
        = (∑' p : ℕ, if h : p.Prime then
              (@δ p ⟨h⟩ 1).toReal
                * ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * ((ArithmeticFunction.cardFactors t : ℕ) : ℝ)
              else 0)
            / Real.sqrt (variance (fun rb : ℕ × ℕ => (rb.1 : ℝ)) jointOmegaCardFactorsMeasure
              * variance (fun rb : ℕ × ℕ => (rb.2 : ℝ)) jointOmegaCardFactorsMeasure)) :=
  sorry

/-- **`T059a` — the moments of `Tam`.** For every `k`, `M_k = ∑_{m ≥ 1} P_Tam(m) m^k` converges
absolutely and `M_k = ∏_p ∑_{t ≥ 1} δ_p(t) t^k`. -/
theorem T059a :
    (∀ k : ℕ, Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k) ∧
    (∀ k : ℕ,
      ((tamagawaMoment k : ℝ) : ℂ)
        = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)) :=
  sorry

/-- **`T059b` — the tail of `Tam`.** For every `k` and `M ≥ 1`, `∑_{m ≥ M} P_Tam(m) ≤ M_k / M^k`;
so the tail decays faster than every power of `M`. -/
theorem T059b :
    (∀ (k : ℕ) {M : ℕ}, 1 ≤ M →
      (∑' n : ℕ, tamagawaDensity (n + M)) ≤ tamagawaMoment k / (M : ℝ) ^ k) ∧
    (∀ k : ℕ,
      ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M → (∑' n : ℕ, tamagawaDensity (n + M)) ≤ C / (M : ℝ) ^ k) :=
  sorry

end BSDTamagawa.Challenge

end
