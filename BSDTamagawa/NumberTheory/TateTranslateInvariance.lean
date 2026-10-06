/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateScaleInvariance

/-!
# Tate's algorithm on integral translates: the residue-field sites

Let `ϖ` be a uniformiser of `R` and let `V` be a Weierstrass curve over `R`. An integral translate
of `V` is its image under a change of variables `⟨1, r, s, t⟩`. At several steps, Tate's algorithm
reads off a monic quadratic or cubic over the residue field `R ⧸ (ϖ)`: the `Splits` tests of Steps
2, 5 and 8, the root count of Step 6, and the two root counts inside Step 7's subprocedure. This
file shows that for `V` and an integral translate of it, under the divisibility conditions in force
at each step, these polynomials differ by a substitution `X ↦ X + γ`. Hence whether they split and
how many distinct roots they have are the same for both curves; the shift also preserves the
double- and triple-root predicates of a cubic.

## Main definitions

* `Cubic.shiftBy`: the cubic `P(X + γ)`.
* `WeierstrassCurve.TateAlgorithm.Step2.splitsCubic`: the quadratic `X² + a₁X - a₂` over the
  residue field, as a `Cubic`.

## Main results

* `Cubic.discr_shiftBy`, `Cubic.card_toFinset_roots_shiftBy`, `Cubic.splits_shiftBy`: a shift
  leaves the discriminant, the number of distinct roots and splitting unchanged.
* `Cubic.exists_shiftBy_of_discr_eq`: two monic quadratics with the same discriminant are shifts of
  one another when `2` is a unit.
* `WeierstrassCurve.IsIntTranslate.symm'`: being an integral translate is a symmetric relation.
* `WeierstrassCurve.dvd_r_of_dvd_b₄_b₆`: if `ϖ` divides `b₄` and `b₆` of both curves and `2` is a
  unit, then `ϖ ∣ r`.
* `WeierstrassCurve.TateAlgorithm.Step2.splits_smul`,
  `WeierstrassCurve.TateAlgorithm.Step5.quadratic_smul`,
  `WeierstrassCurve.TateAlgorithm.Step6.cubic_smul`,
  `WeierstrassCurve.TateAlgorithm.Step8.quadratic_smul`,
  `WeierstrassCurve.TateAlgorithm.Step7.quadratic_smul`,
  `WeierstrassCurve.TateAlgorithm.Step7.cubic_smul`: the residue-field polynomial of each step on
  an integral translate is a shift of the one on the original curve.
-/

@[expose] public section

universe u

open CommRing Ideal Polynomial

/-! ### The shift calculus for cubics

The substitution `X ↦ X + γ` as an operation on `Cubic`, and its invariance of the discriminant,
the number of distinct roots, splitting, and the double- and triple-root predicates. -/

namespace Cubic

variable {k : Type u} [CommRing k]

/-- The cubic `P(X + γ)`, with coefficients given by Taylor expansion of `P` at `γ`. -/
def shiftBy (P : Cubic k) (γ : k) : Cubic k :=
  ⟨P.a, P.b + 3 * P.a * γ, P.c + 2 * P.b * γ + 3 * P.a * γ ^ 2,
    P.d + P.c * γ + P.b * γ ^ 2 + P.a * γ ^ 3⟩

/-- The leading coefficient of `P(X + γ)` is that of `P`. -/
@[simp] theorem shiftBy_a (P : Cubic k) (γ : k) : (P.shiftBy γ).a = P.a := rfl

/-- The `X²`-coefficient of `P(X + γ)`. -/
@[simp] theorem shiftBy_b (P : Cubic k) (γ : k) : (P.shiftBy γ).b = P.b + 3 * P.a * γ := rfl

/-- The `X`-coefficient of `P(X + γ)`. -/
@[simp] theorem shiftBy_c (P : Cubic k) (γ : k) :
    (P.shiftBy γ).c = P.c + 2 * P.b * γ + 3 * P.a * γ ^ 2 := rfl

/-- The constant coefficient of `P(X + γ)` is `P(γ)`. -/
@[simp] theorem shiftBy_d (P : Cubic k) (γ : k) :
    (P.shiftBy γ).d = P.d + P.c * γ + P.b * γ ^ 2 + P.a * γ ^ 3 := rfl

/-- `shiftBy` is substitution of `X + γ` into the associated polynomial. -/
theorem toPoly_shiftBy (P : Cubic k) (γ : k) : (P.shiftBy γ).toPoly = P.toPoly.comp (X + C γ) := by
  simp only [toPoly, shiftBy_a, shiftBy_b, shiftBy_c, shiftBy_d, C_add, C_mul, C_pow, C_ofNat,
    add_comp, mul_comp, pow_comp, C_comp, X_comp]
  ring

/-- The discriminant of `P(X + γ)` equals the discriminant of `P`. -/
theorem discr_shiftBy (P : Cubic k) (γ : k) : (P.shiftBy γ).discr = P.discr := by
  simp only [discr, shiftBy_a, shiftBy_b, shiftBy_c, shiftBy_d]
  ring

/-- `P(X + γ)` has a double root if and only if `P` does. -/
theorem hasDoubleRoot_shiftBy (P : Cubic k) (γ : k) :
    (P.shiftBy γ).HasDoubleRoot ↔ P.HasDoubleRoot := by
  rw [HasDoubleRoot, HasDoubleRoot, discr_shiftBy]

/-- For a monic cubic `P`, `P(X + γ)` has a triple root if and only if `P` does. -/
theorem hasTripleRoot_shiftBy {P : Cubic k} (ha : P.a = 1) (γ : k) :
    (P.shiftBy γ).HasTripleRoot ↔ P.HasTripleRoot := by
  simp only [HasTripleRoot, shiftBy_b, shiftBy_c, ha]
  constructor <;> intro h <;> linear_combination h

variable {k : Type u} [Field k]

/-- Translating the roots of `P(X + γ)` by `γ` gives the roots of `P`. -/
theorem roots_map_shiftBy (P : Cubic k) (γ : k) :
    (P.shiftBy γ).toPoly.roots.map (· + γ) = P.toPoly.roots := by
  have h := P.toPoly.map_roots_comp_C_mul_X_add_C 1 γ isUnit_one
  rw [C_1, one_mul] at h
  simpa [toPoly_shiftBy] using h

open scoped Classical in
/-- `P(X + γ)` and `P` have the same number of distinct roots. -/
theorem card_toFinset_roots_shiftBy (P : Cubic k) (γ : k) :
    (P.shiftBy γ).toPoly.roots.toFinset.card = P.toPoly.roots.toFinset.card := by
  rw [← roots_map_shiftBy P γ, Multiset.toFinset_map,
    Finset.card_image_of_injective _ (add_left_injective γ)]

/-- `P(X + γ)` splits if and only if `P` splits. -/
theorem splits_shiftBy (P : Cubic k) (γ : k) :
    (P.shiftBy γ).toPoly.Splits ↔ P.toPoly.Splits := by
  rw [toPoly_shiftBy]
  exact (splits_iff_comp_splits_of_natDegree_eq_one (f := P.toPoly) (g := X + C γ) (by simp)).symm

/-- If `2` is a unit, two monic quadratics `Y² + cY + d` (as cubics `Cubic.mk 0 1 c d`) with the
same discriminant `c² - 4d` are shifts of one another. -/
theorem exists_shiftBy_of_discr_eq {k : Type u} [CommRing k] (h2 : IsUnit (2 : k)) {P Q : Cubic k}
    (hPa : P.a = 0) (hPb : P.b = 1) (hQa : Q.a = 0) (hQb : Q.b = 1)
    (h : Q.c ^ 2 - 4 * Q.d = P.c ^ 2 - 4 * P.d) : ∃ γ, Q = P.shiftBy γ := by
  obtain ⟨e, he⟩ : ∃ e : k, 2 * e = 1 := ⟨↑h2.unit⁻¹, by simp⟩
  have h4 : IsUnit (4 : k) := by simpa [show (4 : k) = 2 * 2 by norm_num] using h2.mul h2
  refine ⟨(Q.c - P.c) * e, ?_⟩
  have hc : Q.c = P.c + 2 * ((Q.c - P.c) * e) := by linear_combination (P.c - Q.c) * he
  have hd : Q.d = P.d + P.c * ((Q.c - P.c) * e) + ((Q.c - P.c) * e) ^ 2 := by
    refine sub_eq_zero.mp (h4.mul_right_eq_zero.mp ?_)
    linear_combination -h + (Q.c + P.c + 2 * ((Q.c - P.c) * e)) * hc
  refine Cubic.ext ?_ ?_ ?_ ?_
  · simp [hPa, hQa]
  · simp [hPa, hPb, hQb]
  · simp only [shiftBy_c, hPa, hPb]; linear_combination hc
  · simp only [shiftBy_d, hPa, hPb]; linear_combination hd

end Cubic

/-! ### An integral translation, coefficient by coefficient

The coefficients of the image of a Weierstrass curve under a change of variables `⟨1, r, s, t⟩`,
that is, Mathlib's `variableChange_*` formulas with `u = 1`. -/

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {ϖ : R}

section Coeffs

variable (V : WeierstrassCurve R) (r s t : R)

/-- The coefficient `a₁` of the image of `V` under `⟨1, r, s, t⟩` is `a₁ + 2s`. -/
theorem smulOne_a₁ : ((VariableChange.mk 1 r s t) • V).a₁ = V.a₁ + 2 * s := by
  simp [variableChange_a₁]

/-- The coefficient `a₂` of the image of `V` under `⟨1, r, s, t⟩`. -/
theorem smulOne_a₂ :
    ((VariableChange.mk 1 r s t) • V).a₂ = V.a₂ - s * V.a₁ + 3 * r - s ^ 2 := by
  simp [variableChange_a₂]

/-- The coefficient `a₃` of the image of `V` under `⟨1, r, s, t⟩`. -/
theorem smulOne_a₃ : ((VariableChange.mk 1 r s t) • V).a₃ = V.a₃ + r * V.a₁ + 2 * t := by
  simp [variableChange_a₃]

/-- The coefficient `a₄` of the image of `V` under `⟨1, r, s, t⟩`. -/
theorem smulOne_a₄ : ((VariableChange.mk 1 r s t) • V).a₄ =
    V.a₄ - s * V.a₃ + 2 * r * V.a₂ - (t + r * s) * V.a₁ + 3 * r ^ 2 - 2 * s * t := by
  simp [variableChange_a₄]

/-- The coefficient `a₆` of the image of `V` under `⟨1, r, s, t⟩`. -/
theorem smulOne_a₆ : ((VariableChange.mk 1 r s t) • V).a₆ =
    V.a₆ + r * V.a₄ + r ^ 2 * V.a₂ + r ^ 3 - t * V.a₃ - t ^ 2 - r * t * V.a₁ := by
  simp [variableChange_a₆]

/-- The quantity `b₂` of the image of `V` under `⟨1, r, s, t⟩` is `b₂ + 12r`. -/
theorem smulOne_b₂ : ((VariableChange.mk 1 r s t) • V).b₂ = V.b₂ + 12 * r := by
  simp [variableChange_b₂]

/-- The quantity `b₄` of the image of `V` under `⟨1, r, s, t⟩`. -/
theorem smulOne_b₄ : ((VariableChange.mk 1 r s t) • V).b₄ = V.b₄ + r * V.b₂ + 6 * r ^ 2 := by
  simp [variableChange_b₄]

/-- The quantity `b₆` of the image of `V` under `⟨1, r, s, t⟩`. -/
theorem smulOne_b₆ : ((VariableChange.mk 1 r s t) • V).b₆ =
    V.b₆ + 2 * r * V.b₄ + r ^ 2 * V.b₂ + 4 * r ^ 3 := by
  simp [variableChange_b₆]

/-- `c₄` is invariant under an integral translation. -/
theorem smulOne_c₄ : ((VariableChange.mk 1 r s t) • V).c₄ = V.c₄ := by
  simp [variableChange_c₄]

/-- `c₆` is invariant under an integral translation. -/
theorem smulOne_c₆ : ((VariableChange.mk 1 r s t) • V).c₆ = V.c₆ := by
  simp [variableChange_c₆]

/-- `Δ` is invariant under an integral translation. -/
theorem smulOne_Δ : ((VariableChange.mk 1 r s t) • V).Δ = V.Δ := by
  simp [variableChange_Δ]

end Coeffs

/-- `IsIntTranslate` is symmetric: the inverse of `⟨1, r, s, t⟩` is `⟨1, -r, -s, rs - t⟩`. -/
theorem IsIntTranslate.symm' {W W' : WeierstrassCurve R} (h : IsIntTranslate W W') :
    IsIntTranslate W' W := by
  obtain ⟨r, s, t, rfl⟩ := h
  refine ⟨-r, -s, r * s - t, ?_⟩
  ext <;> simp only [variableChange_def, inv_one, Units.val_one, one_pow, one_mul]
  · ring
  · ring
  · ring
  · ring
  · ring

/-! ### Exact division -/

/-- If `x = q * y` with `q ≠ 0`, then `div x q = y`. -/
private theorem div_eq_of_eq [NoZeroDivisors R] {q x y : R} (hq : q ≠ 0) (h : x = q * y) :
    div x q = y :=
  mul_left_cancel₀ hq (by rw [mul_div hq ⟨y, h⟩, h])

/-- If `ϖ ^ n ∣ x` and `y ≡ x` modulo `ϖ ^ (n + 1)`, then the quotients of `y` and `x` by `ϖ ^ n`
agree modulo `ϖ`. -/
private theorem mod_div_eq_of_dvd_sub [NoZeroDivisors R] (hϖ : ϖ ≠ 0) {x y : R} {n : ℕ}
    (hn : n ≠ 0) (hx : ϖ ^ n ∣ x) (h : ϖ ^ (n + 1) ∣ y - x) :
    mod ϖ (div y (ϖ ^ n)) = mod ϖ (div x (ϖ ^ n)) := by
  have hy : ϖ ^ n ∣ y := by
    simpa using (dvd_add ((pow_succ_dvd hn).mp h).1 hx)
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero,
    ← div_sub (pow_ne_zero n hϖ) hy hx]
  exact ((pow_succ_dvd hn).mp h).2

/-! ### The parameters of an integral translation are pinned by the two curves' valuations

Divisibility of coefficients of a curve and of its image under `⟨1, r, s, t⟩` by powers of `ϖ`
forces divisibility of `r`, `s`, `t`, assuming `2` or `3` is a unit as needed. -/

section Pinning

variable {V : WeierstrassCurve R} {r s t : R}

/-- `ϖ ^ i ∣ a₁` on both curves forces `ϖ ^ i ∣ s`, because `a₁` moves by `2s`. -/
theorem dvd_s_of_dvd_a₁ {i : ℕ} (h2 : IsUnit (2 : R)) (ha₁ : ϖ ^ i ∣ V.a₁)
    (ha₁' : ϖ ^ i ∣ ((VariableChange.mk 1 r s t) • V).a₁) : ϖ ^ i ∣ s := by
  rw [smulOne_a₁] at ha₁'
  have h : ϖ ^ i ∣ 2 * s := by
    have hx := dvd_sub ha₁' ha₁
    rwa [add_sub_cancel_left] at hx
  rwa [h2.dvd_mul_left] at h

/-- `ϖ ^ j ∣ a₂` on both curves forces `ϖ ^ j ∣ r`, because `a₂` moves by `-sa₁ + 3r - s²`. -/
theorem dvd_r_of_dvd_a₂ {j : ℕ} (h3 : IsUnit (3 : R)) (ha₂ : ϖ ^ j ∣ V.a₂)
    (ha₂' : ϖ ^ j ∣ ((VariableChange.mk 1 r s t) • V).a₂) (hsa : ϖ ^ j ∣ s * V.a₁)
    (hss : ϖ ^ j ∣ s ^ 2) : ϖ ^ j ∣ r := by
  rw [smulOne_a₂] at ha₂'
  have h : ϖ ^ j ∣ 3 * r := by
    have hx := dvd_add (dvd_add (dvd_sub ha₂' ha₂) hsa) hss
    rwa [show V.a₂ - s * V.a₁ + 3 * r - s ^ 2 - V.a₂ + s * V.a₁ + s ^ 2 = 3 * r from by ring] at hx
  rwa [h3.dvd_mul_left] at h

/-- `ϖ ^ m ∣ a₃` on both curves forces `ϖ ^ m ∣ t`, once `ϖ ^ m ∣ ra₁`. -/
theorem dvd_t_of_dvd_a₃ {m : ℕ} (h2 : IsUnit (2 : R)) (ha₃ : ϖ ^ m ∣ V.a₃)
    (ha₃' : ϖ ^ m ∣ ((VariableChange.mk 1 r s t) • V).a₃) (hra : ϖ ^ m ∣ r * V.a₁) : ϖ ^ m ∣ t := by
  rw [smulOne_a₃] at ha₃'
  have h : ϖ ^ m ∣ 2 * t := by
    have hx := dvd_sub (dvd_sub ha₃' ha₃) hra
    rwa [show V.a₃ + r * V.a₁ + 2 * t - V.a₃ - r * V.a₁ = 2 * t from by ring] at hx
  rwa [h2.dvd_mul_left] at h

/-- `ϖ ^ j ∣ b₂` on both curves forces `ϖ ^ j ∣ r`, because `b₂` moves by `12r`. -/
theorem dvd_r_of_dvd_b₂ {j : ℕ} (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (hb₂ : ϖ ^ j ∣ V.b₂)
    (hb₂' : ϖ ^ j ∣ ((VariableChange.mk 1 r s t) • V).b₂) : ϖ ^ j ∣ r := by
  have h12 : IsUnit (12 : R) := by
    simpa [show (12 : R) = 2 * 2 * 3 from by norm_num] using (h2.mul h2).mul h3
  rw [smulOne_b₂] at hb₂'
  have h : ϖ ^ j ∣ 12 * r := by
    have hx := dvd_sub hb₂' hb₂
    rwa [add_sub_cancel_left] at hx
  rwa [h12.dvd_mul_left] at h

/-- For a prime `ϖ` with `2` a unit, `ϖ ∣ b₄` and `ϖ ∣ b₆` on both curves force `ϖ ∣ r`. -/
theorem dvd_r_of_dvd_b₄_b₆ (hp : Prime ϖ) (h2 : IsUnit (2 : R)) (hb₄ : ϖ ∣ V.b₄)
    (hb₄' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).b₄) (hb₆ : ϖ ∣ V.b₆)
    (hb₆' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).b₆) : ϖ ∣ r := by
  rw [smulOne_b₄] at hb₄'
  rw [smulOne_b₆] at hb₆'
  by_contra hr
  have h₄ : ϖ ∣ V.b₂ + 6 * r := by
    have hx : ϖ ∣ r * (V.b₂ + 6 * r) := by
      have := dvd_sub hb₄' hb₄
      rwa [show V.b₄ + r * V.b₂ + 6 * r ^ 2 - V.b₄ = r * (V.b₂ + 6 * r) from by ring] at this
    exact (hp.dvd_mul.mp hx).resolve_left hr
  have h₆ : ϖ ∣ V.b₂ + 4 * r := by
    have hx : ϖ ∣ r * (r * (V.b₂ + 4 * r)) := by
      have h' := dvd_sub (dvd_sub hb₆' hb₆) (hb₄.mul_left (2 * r))
      rwa [show V.b₆ + 2 * r * V.b₄ + r ^ 2 * V.b₂ + 4 * r ^ 3 - V.b₆ - 2 * r * V.b₄ =
        r * (r * (V.b₂ + 4 * r)) from by ring] at h'
    exact (hp.dvd_mul.mp ((hp.dvd_mul.mp hx).resolve_left hr)).resolve_left hr
  refine hr ?_
  have h : ϖ ∣ 2 * r := by
    have := dvd_sub h₄ h₆
    rwa [show V.b₂ + 6 * r - (V.b₂ + 4 * r) = 2 * r from by ring] at this
  rwa [h2.dvd_mul_left] at h

end Pinning

end WeierstrassCurve

/-! ### The `Output` sites of Steps 2, 5, 6 and 8

For a curve and an integral translate of it, the residue-field cubic read at each of these steps is
a shift of the other's. For the quadratic sites the shift comes from equality of discriminants; for
Step 6 it is `r/ϖ`. -/

namespace WeierstrassCurve.TateAlgorithm

variable {R : Type u} [CommRing R] {ϖ : R}

/-- The discriminant of the quadratic `Y² + (a₃/ϖⁿ)Y - a₆/ϖ²ⁿ` is `b₆/ϖ²ⁿ` modulo `ϖ`. -/
theorem quadratic_discr [NoZeroDivisors R] (hϖ : ϖ ≠ 0) {V : WeierstrassCurve R} {n m : ℕ}
    (hm : m = 2 * n) (ha₃ : ϖ ^ n ∣ V.a₃) (ha₆ : ϖ ^ m ∣ V.a₆) :
    (quadratic ϖ V n).c ^ 2 - 4 * (quadratic ϖ V n).d = mod ϖ (div V.b₆ (ϖ ^ m)) := by
  subst hm
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₆, e₆⟩ := ha₆
  have hd₃ : div V.a₃ (ϖ ^ n) = α₃ := div_eq_of_eq (pow_ne_zero n hϖ) e₃
  have hd₆ : div V.a₆ (ϖ ^ (2 * n)) = α₆ := div_eq_of_eq (pow_ne_zero _ hϖ) e₆
  have hb : V.b₆ = ϖ ^ (2 * n) * (α₃ ^ 2 + 4 * α₆) := by
    rw [WeierstrassCurve.b₆, e₃, e₆, pow_mul']; ring
  have hdb : div V.b₆ (ϖ ^ (2 * n)) = α₃ ^ 2 + 4 * α₆ := div_eq_of_eq (pow_ne_zero _ hϖ) hb
  change (mod ϖ (div V.a₃ (ϖ ^ n))) ^ 2 - 4 * (-mod ϖ (div V.a₆ (ϖ ^ (2 * n)))) = _
  rw [hd₃, hd₆, hdb]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

/-- If `ϖ ^ n ∣ a₃` and `ϖ ^ (2n) ∣ a₆`, then `ϖ ^ (2n) ∣ b₆`. -/
private theorem dvd_b₆_of [NoZeroDivisors R] {V : WeierstrassCurve R} {n m : ℕ} (hm : m = 2 * n)
    (ha₃ : ϖ ^ n ∣ V.a₃) (ha₆ : ϖ ^ m ∣ V.a₆) : ϖ ^ m ∣ V.b₆ := by
  subst hm
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₆, e₆⟩ := ha₆
  exact ⟨α₃ ^ 2 + 4 * α₆, by rw [WeierstrassCurve.b₆, e₃, e₆, pow_mul']; ring⟩

/-! #### Step 2 -/

namespace Step2

/-- The quadratic `X² + a₁X - a₂` over the residue field, as the `Cubic` `⟨0, 1, a₁, -a₂⟩`. -/
noncomputable def splitsCubic (ϖ : R) (V : WeierstrassCurve R) : Cubic (R ⧸ span {ϖ}) :=
  ⟨0, 1, mod ϖ V.a₁, -mod ϖ V.a₂⟩

/-- The polynomial of `splitsCubic ϖ V` is the reduction of `X² + a₁X - a₂` modulo `ϖ`. -/
theorem toPoly_splitsCubic (ϖ : R) (V : WeierstrassCurve R) :
    (splitsCubic ϖ V).toPoly = (X ^ 2 + C V.a₁ * X - C V.a₂).map (mod ϖ) := by
  simp only [splitsCubic, Cubic.toPoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, C_0, C_1, C_neg, zero_mul, zero_add, one_mul]
  ring

/-- The discriminant of Step 2's quadratic is `b₂ = a₁² + 4a₂`. -/
theorem discr_splitsCubic (ϖ : R) (V : WeierstrassCurve R) :
    (splitsCubic ϖ V).c ^ 2 - 4 * (splitsCubic ϖ V).d = mod ϖ V.b₂ := by
  change (mod ϖ V.a₁) ^ 2 - 4 * (-mod ϖ V.a₂) = _
  rw [WeierstrassCurve.b₂]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

/-- If `2` is a unit and `ϖ ∣ r`, Step 2's quadratic for the image of `V` under `⟨1, r, s, t⟩` is a
shift of Step 2's quadratic for `V`. -/
theorem splitsCubic_smul (h2 : IsUnit (2 : R)) {V : WeierstrassCurve R} {r s t : R} (hr : ϖ ∣ r) :
    ∃ γ, splitsCubic ϖ ((VariableChange.mk 1 r s t) • V) = (splitsCubic ϖ V).shiftBy γ := by
  refine Cubic.exists_shiftBy_of_discr_eq ?_ rfl rfl rfl rfl ?_
  · have hu := h2.map (mod ϖ)
    rwa [map_ofNat] at hu
  · rw [discr_splitsCubic, discr_splitsCubic, smulOne_b₂, map_add, map_mul,
      (mod_eq_zero ϖ r).mpr hr]
    ring

/-- If `2` is a unit and `ϖ ∣ r`, then `X² + a₁X - a₂` splits modulo `ϖ` for the image of `V` under
`⟨1, r, s, t⟩` if and only if it does for `V`. -/
theorem splits_smul [(span {ϖ}).IsMaximal] (h2 : IsUnit (2 : R)) {V : WeierstrassCurve R}
    {r s t : R} (hr : ϖ ∣ r) :
    ((X ^ 2 + C ((VariableChange.mk 1 r s t) • V).a₁ * X
        - C ((VariableChange.mk 1 r s t) • V).a₂).map (mod ϖ)).Splits
      ↔ ((X ^ 2 + C V.a₁ * X - C V.a₂).map (mod ϖ)).Splits := by
  obtain ⟨γ, hγ⟩ := splitsCubic_smul (ϖ := ϖ) (V := V) (r := r) (s := s) (t := t) h2 hr
  rw [← toPoly_splitsCubic, ← toPoly_splitsCubic, hγ, Cubic.splits_shiftBy]

end Step2

/-! #### Step 5 -/

namespace Step5

/-- Suppose `2` and `3` are units, `ϖ ∣ a₃`, `ϖ² ∣ a₆`, `ϖ ∣ b₂`, `ϖ² ∣ b₄` for `V`, and `ϖ ∣ a₃`,
`ϖ² ∣ a₆`, `ϖ ∣ b₂` for its image under `⟨1, r, s, t⟩`. Then Step 5's quadratic
`Y² + (a₃/ϖ)Y - a₆/ϖ²` for the image is a shift of the one for `V`. -/
theorem quadratic_smul [IsDomain R] (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (hϖ : ϖ ≠ 0)
    {V : WeierstrassCurve R} {r s t : R} (ha₃ : ϖ ∣ V.a₃) (ha₆ : ϖ ^ 2 ∣ V.a₆) (hb₂ : ϖ ∣ V.b₂)
    (hb₄ : ϖ ^ 2 ∣ V.b₄) (ha₃' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₆' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₆)
    (hb₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).b₂) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) 1 = (quadratic ϖ V 1).shiftBy γ := by
  have hr : ϖ ∣ r := by
    simpa using dvd_r_of_dvd_b₂ (j := 1) h2 h3 (by simpa using hb₂) (by simpa using hb₂')
  have hdiff : ϖ ^ 3 ∣ ((VariableChange.mk 1 r s t) • V).b₆ - V.b₆ := by
    obtain ⟨ρ, hρ⟩ := hr
    obtain ⟨u₄, hu₄⟩ := hb₄
    obtain ⟨u₂, hu₂⟩ := hb₂
    exact ⟨2 * ρ * u₄ + ρ ^ 2 * u₂ + 4 * ρ ^ 3, by rw [smulOne_b₆, hρ, hu₄, hu₂]; ring⟩
  refine Cubic.exists_shiftBy_of_discr_eq ?_ rfl rfl rfl rfl ?_
  · have hu := h2.map (mod ϖ)
    rwa [map_ofNat] at hu
  · rw [quadratic_discr hϖ (n := 1) (m := 2) (by norm_num) (by simpa using ha₃') ha₆',
      quadratic_discr hϖ (n := 1) (m := 2) (by norm_num) (by simpa using ha₃) ha₆]
    exact mod_div_eq_of_dvd_sub hϖ two_ne_zero
      (dvd_b₆_of (n := 1) (by norm_num) (by simpa using ha₃) ha₆) hdiff

end Step5

/-! #### Step 8 -/

namespace Step8

/-- Suppose `2` and `3` are units, `ϖ ∣ a₁`, `ϖ² ∣ a₂, a₃`, `ϖ⁴ ∣ a₆`, `ϖ² ∣ b₂`, `ϖ³ ∣ b₄` for
`V`, and `ϖ ∣ a₁`, `ϖ² ∣ a₂, a₃`, `ϖ⁴ ∣ a₆` for its image under `⟨1, r, s, t⟩`. Then Step 8's
quadratic `Y² + (a₃/ϖ²)Y - a₆/ϖ⁴` for the image is a shift of the one for `V`. -/
theorem quadratic_smul [IsDomain R] (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (hϖ : ϖ ≠ 0)
    {V : WeierstrassCurve R} {r s t : R} (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ^ 2 ∣ V.a₂)
    (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₆ : ϖ ^ 4 ∣ V.a₆) (hb₂ : ϖ ^ 2 ∣ V.b₂) (hb₄ : ϖ ^ 3 ∣ V.b₄)
    (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₁)
    (ha₂' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₆' : ϖ ^ 4 ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) 2 = (quadratic ϖ V 2).shiftBy γ := by
  have hs : ϖ ∣ s := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using ha₁) (by simpa using ha₁')
  have hr : ϖ ^ 2 ∣ r :=
    dvd_r_of_dvd_a₂ h3 ha₂ ha₂' (by rw [pow_two]; exact mul_dvd_mul hs ha₁)
      (by rw [pow_two, pow_two]; exact mul_dvd_mul hs hs)
  have hdiff : ϖ ^ 5 ∣ ((VariableChange.mk 1 r s t) • V).b₆ - V.b₆ := by
    obtain ⟨ρ, hρ⟩ := hr
    obtain ⟨u₄, hu₄⟩ := hb₄
    obtain ⟨u₂, hu₂⟩ := hb₂
    exact ⟨2 * ρ * u₄ + ϖ * ρ ^ 2 * u₂ + 4 * ϖ * ρ ^ 3,
      by rw [smulOne_b₆, hρ, hu₄, hu₂]; ring⟩
  refine Cubic.exists_shiftBy_of_discr_eq ?_ rfl rfl rfl rfl ?_
  · have hu := h2.map (mod ϖ)
    rwa [map_ofNat] at hu
  · rw [quadratic_discr hϖ (n := 2) (m := 4) (by norm_num) ha₃' ha₆',
      quadratic_discr hϖ (n := 2) (m := 4) (by norm_num) ha₃ ha₆]
    exact mod_div_eq_of_dvd_sub hϖ (by norm_num)
      (dvd_b₆_of (n := 2) (by norm_num) ha₃ ha₆) hdiff

end Step8

/-! #### Step 6, and Step 7's branch -/

namespace Step6

/-- Suppose `2` and `3` are units, `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆` for `V`, and
`ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃` for its image under `⟨1, r, s, t⟩`. Then Step 6's cubic
`X³ + (a₂/ϖ)X² + (a₄/ϖ²)X + a₆/ϖ³` for the image is the shift by `r/ϖ` of the one for `V`. -/
theorem cubic_smul [IsDomain R] (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (hϖ : ϖ ≠ 0)
    {V : WeierstrassCurve R} {r s t : R} (ha₁ : ϖ ∣ V.a₁) (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃)
    (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆)
    (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₁)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃) :
    cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1
      = (cubic ϖ V 1 1).shiftBy (mod ϖ (div r ϖ)) := by
  have hs : ϖ ∣ s := by
    simpa using dvd_s_of_dvd_a₁ (i := 1) h2 (by simpa using ha₁) (by simpa using ha₁')
  have hr : ϖ ∣ r := by
    simpa using dvd_r_of_dvd_a₂ (j := 1) h3 (by simpa using ha₂) (by simpa using ha₂')
      (by simpa using hs.mul_right V.a₁) (by simpa using dvd_pow hs two_ne_zero)
  have ht : ϖ ^ 2 ∣ t :=
    dvd_t_of_dvd_a₃ h2 ha₃ ha₃' (by rw [pow_two]; exact mul_dvd_mul hr ha₁)
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht
  have dr : div r ϖ = ρ := div_eq_of_eq hϖ hρ
  have d₂ : div V.a₂ ϖ = α₂ := div_eq_of_eq hϖ e₂
  have d₄ : div V.a₄ (ϖ ^ 2) = α₄ := div_eq_of_eq (pow_ne_zero 2 hϖ) e₄
  have d₆ : div V.a₆ (ϖ ^ 3) = α₆ := div_eq_of_eq (pow_ne_zero 3 hϖ) e₆
  have g₂ : div ((VariableChange.mk 1 r s t) • V).a₂ ϖ
      = α₂ - ϖ * σ * α₁ + 3 * ρ - ϖ * σ ^ 2 :=
    div_eq_of_eq hϖ (by rw [smulOne_a₂, e₁, e₂, hρ, hσ]; ring)
  have g₄ : div ((VariableChange.mk 1 r s t) • V).a₄ (ϖ ^ 2)
      = α₄ - ϖ * σ * α₃ + 2 * ρ * α₂ - ϖ * (τ + ρ * σ) * α₁ + 3 * ρ ^ 2 - 2 * ϖ * σ * τ :=
    div_eq_of_eq (pow_ne_zero 2 hϖ) (by rw [smulOne_a₄, e₁, e₂, e₃, e₄, hρ, hσ, hτ]; ring)
  have g₆ : div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 3)
      = α₆ + ρ * α₄ + ρ ^ 2 * α₂ + ρ ^ 3 - ϖ * τ * α₃ - ϖ * τ ^ 2 - ϖ * ρ * τ * α₁ :=
    div_eq_of_eq (pow_ne_zero 3 hϖ) (by rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring)
  refine Cubic.ext rfl ?_ ?_ ?_
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₂ ϖ)
      = mod ϖ (div V.a₂ ϖ) + 3 * 1 * mod ϖ (div r ϖ)
    rw [g₂, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mod_self]
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₄ (ϖ ^ 2))
      = mod ϖ (div V.a₄ (ϖ ^ 2)) + 2 * mod ϖ (div V.a₂ ϖ) * mod ϖ (div r ϖ)
        + 3 * 1 * mod ϖ (div r ϖ) ^ 2
    rw [g₄, d₄, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mod_self]
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ 3))
      = mod ϖ (div V.a₆ (ϖ ^ 3)) + mod ϖ (div V.a₄ (ϖ ^ 2)) * mod ϖ (div r ϖ)
        + mod ϖ (div V.a₂ ϖ) * mod ϖ (div r ϖ) ^ 2 + 1 * mod ϖ (div r ϖ) ^ 3
    rw [g₆, d₆, d₄, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, mod_self]
    ring

open scoped Classical in
/-- Under the hypotheses of `cubic_smul`, Step 6's cubics for `V` and for its image under
`⟨1, r, s, t⟩` have the same number of distinct roots. -/
theorem card_roots_smul [IsDomain R] [(span {ϖ}).IsMaximal] (h2 : IsUnit (2 : R))
    (h3 : IsUnit (3 : R)) (hϖ : ϖ ≠ 0) {V : WeierstrassCurve R} {r s t : R} (ha₁ : ϖ ∣ V.a₁)
    (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ 2 ∣ V.a₃) (ha₄ : ϖ ^ 2 ∣ V.a₄) (ha₆ : ϖ ^ 3 ∣ V.a₆)
    (ha₁' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₁)
    (ha₂' : ϖ ∣ ((VariableChange.mk 1 r s t) • V).a₂)
    (ha₃' : ϖ ^ 2 ∣ ((VariableChange.mk 1 r s t) • V).a₃) :
    (cubic ϖ ((VariableChange.mk 1 r s t) • V) 1 1).toPoly.roots.toFinset.card
      = (cubic ϖ V 1 1).toPoly.roots.toFinset.card := by
  rw [cubic_smul h2 h3 hϖ ha₁ ha₂ ha₃ ha₄ ha₆ ha₁' ha₂' ha₃',
    Cubic.card_toFinset_roots_shiftBy]

end Step6

/-! #### Step 7's subprocedure -/

namespace Step7

/-- Suppose `2` is a unit, `n ≠ 0`, `ϖ ^ n ∣ r`, `ϖ ^ n ∣ a₃`, `ϖ ^ (2n) ∣ a₆`, `ϖ ∣ b₂`,
`ϖ ^ (n + 1) ∣ b₄` for `V`, and `ϖ ^ n ∣ a₃`, `ϖ ^ (2n) ∣ a₆` for its image under `⟨1, r, s, t⟩`.
Then the quadratic `Y² + (a₃/ϖⁿ)Y - a₆/ϖ²ⁿ` for the image is a shift of the one for `V`. -/
theorem quadratic_smul [IsDomain R] (h2 : IsUnit (2 : R)) (hϖ : ϖ ≠ 0) {n : ℕ} (hn : n ≠ 0)
    {V : WeierstrassCurve R} {r s t : R} (hr : ϖ ^ n ∣ r) (ha₃ : ϖ ^ n ∣ V.a₃)
    (ha₆ : ϖ ^ (2 * n) ∣ V.a₆) (hb₂ : ϖ ∣ V.b₂) (hb₄ : ϖ ^ (n + 1) ∣ V.b₄)
    (ha₃' : ϖ ^ n ∣ ((VariableChange.mk 1 r s t) • V).a₃)
    (ha₆' : ϖ ^ (2 * n) ∣ ((VariableChange.mk 1 r s t) • V).a₆) :
    ∃ γ, quadratic ϖ ((VariableChange.mk 1 r s t) • V) n = (quadratic ϖ V n).shiftBy γ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hdiff : ϖ ^ (2 * (k + 1) + 1) ∣ ((VariableChange.mk 1 r s t) • V).b₆ - V.b₆ := by
    obtain ⟨ρ, hρ⟩ := hr
    obtain ⟨u₄, hu₄⟩ := hb₄
    obtain ⟨u₂, hu₂⟩ := hb₂
    refine ⟨2 * ρ * u₄ + ρ ^ 2 * u₂ + 4 * ϖ ^ k * ρ ^ 3, ?_⟩
    rw [smulOne_b₆, hρ, hu₄, hu₂, two_mul]
    ring
  refine Cubic.exists_shiftBy_of_discr_eq ?_ rfl rfl rfl rfl ?_
  · have hu := h2.map (mod ϖ)
    rwa [map_ofNat] at hu
  · rw [quadratic_discr hϖ rfl ha₃' ha₆', quadratic_discr hϖ rfl ha₃ ha₆]
    exact mod_div_eq_of_dvd_sub hϖ (by omega) (dvd_b₆_of rfl ha₃ ha₆) hdiff

/-- Suppose `n ≥ 2`, `ϖ ∣ a₁, a₂`, `ϖⁿ⁺¹ ∣ a₃, a₄`, `ϖ²ⁿ⁺¹ ∣ a₆` for `V`, and `ϖ ∣ s`, `ϖⁿ ∣ r`,
`ϖⁿ⁺¹ ∣ t`. Then the cubic `(a₂/ϖ)X² + (a₄/ϖⁿ⁺¹)X + a₆/ϖ²ⁿ⁺¹` modulo `ϖ` for the image of `V` under
`⟨1, r, s, t⟩` is the shift by `r/ϖⁿ` of the one for `V`. -/
theorem cubic_smul [IsDomain R] (hϖ : ϖ ≠ 0) {n : ℕ} (hn : 2 ≤ n) {V : WeierstrassCurve R}
    {r s t : R} (hs : ϖ ∣ s) (hr : ϖ ^ n ∣ r) (ht : ϖ ^ (n + 1) ∣ t) (ha₁ : ϖ ∣ V.a₁)
    (ha₂ : ϖ ∣ V.a₂) (ha₃ : ϖ ^ (n + 1) ∣ V.a₃) (ha₄ : ϖ ^ (n + 1) ∣ V.a₄)
    (ha₆ : ϖ ^ (2 * n + 1) ∣ V.a₆) :
    cubic ϖ ((VariableChange.mk 1 r s t) • V) 0 n
      = (cubic ϖ V 0 n).shiftBy (mod ϖ (div r (ϖ ^ n))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨α₁, e₁⟩ := ha₁
  obtain ⟨α₂, e₂⟩ := ha₂
  obtain ⟨α₃, e₃⟩ := ha₃
  obtain ⟨α₄, e₄⟩ := ha₄
  obtain ⟨α₆, e₆⟩ := ha₆
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht
  have dr : div r (ϖ ^ (k + 2)) = ρ := div_eq_of_eq (pow_ne_zero _ hϖ) hρ
  have d₂ : div V.a₂ ϖ = α₂ := div_eq_of_eq hϖ e₂
  have d₄ : div V.a₄ (ϖ ^ (k + 2 + 1)) = α₄ := div_eq_of_eq (pow_ne_zero _ hϖ) e₄
  have d₆ : div V.a₆ (ϖ ^ (2 * (k + 2) + 1)) = α₆ := div_eq_of_eq (pow_ne_zero _ hϖ) e₆
  have g₂ : div ((VariableChange.mk 1 r s t) • V).a₂ ϖ
      = α₂ - ϖ * σ * α₁ + 3 * ϖ * ϖ ^ k * ρ - ϖ * σ ^ 2 :=
    div_eq_of_eq hϖ (by rw [smulOne_a₂, e₁, e₂, hρ, hσ]; ring)
  have g₄ : div ((VariableChange.mk 1 r s t) • V).a₄ (ϖ ^ (k + 2 + 1))
      = α₄ + 2 * ρ * α₂ - ϖ * σ * α₃ - ϖ * τ * α₁ - ϖ * ρ * σ * α₁ + 3 * ϖ * ϖ ^ k * ρ ^ 2
        - 2 * ϖ * σ * τ :=
    div_eq_of_eq (pow_ne_zero _ hϖ) (by rw [smulOne_a₄, e₁, e₂, e₃, e₄, hρ, hσ, hτ]; ring)
  have g₆ : div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ (2 * (k + 2) + 1))
      = α₆ + ρ * α₄ + ρ ^ 2 * α₂ + ϖ * ϖ ^ k * ρ ^ 3 - ϖ * τ * α₃ - ϖ * τ ^ 2
        - ϖ * ρ * τ * α₁ :=
    div_eq_of_eq (pow_ne_zero _ hϖ) (by rw [smulOne_a₆, e₁, e₂, e₃, e₄, e₆, hρ, hτ]; ring)
  refine Cubic.ext rfl ?_ ?_ ?_
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₂ ϖ)
      = mod ϖ (div V.a₂ ϖ) + 3 * 0 * mod ϖ (div r (ϖ ^ (k + 2)))
    rw [g₂, d₂]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mod_self]
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₄ (ϖ ^ (k + 2 + 1)))
      = mod ϖ (div V.a₄ (ϖ ^ (k + 2 + 1))) + 2 * mod ϖ (div V.a₂ ϖ)
          * mod ϖ (div r (ϖ ^ (k + 2))) + 3 * 0 * mod ϖ (div r (ϖ ^ (k + 2))) ^ 2
    rw [g₄, d₄, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mod_self]
    ring
  · change mod ϖ (div ((VariableChange.mk 1 r s t) • V).a₆ (ϖ ^ (2 * (k + 2) + 1)))
      = mod ϖ (div V.a₆ (ϖ ^ (2 * (k + 2) + 1)))
          + mod ϖ (div V.a₄ (ϖ ^ (k + 2 + 1))) * mod ϖ (div r (ϖ ^ (k + 2)))
          + mod ϖ (div V.a₂ ϖ) * mod ϖ (div r (ϖ ^ (k + 2))) ^ 2
          + 0 * mod ϖ (div r (ϖ ^ (k + 2))) ^ 3
    rw [g₆, d₆, d₄, d₂, dr]
    simp only [map_add, map_sub, map_mul, map_pow, mod_self]
    ring

end Step7

end WeierstrassCurve.TateAlgorithm
