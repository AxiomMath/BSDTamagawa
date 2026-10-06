/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityIVStar

/-!
# Residue pairs and Step 6 of Tate's algorithm in the deep locus, for `p ≥ 5`

Inside the deep locus `{p² ∣ a₄, p³ ∣ a₆}` of short models, with `a₄ = p²A` and `a₆ = p³B`,
whether the cubic of Step 6 of Tate's algorithm has a double root or three distinct roots depends
only on the residue pair `(Ā, B̄) ∈ 𝔽_p²`, through the depressed cubic `Y³ + ĀY + B̄`. This file
introduces the corresponding sets of residue pairs, counts the pairs giving a double but not a
triple root, computes the mass of the deep locus refined by a set of residue pairs, and shows that
Tate's algorithm answers `(I₀*, 1 + #roots)` when Step 6's cubic is separable. It also shows that,
for a scale-invariant stratification, the non-minimal part of a fibre `{c = t}` is the image of
that fibre under `σ_p`.

## Main definitions

* `WeierstrassCurve.rootPairs`: the pairs `(x, y) ∈ 𝔽_p²` with `x`, `y`, `-x-y` pairwise distinct.
* `WeierstrassCurve.rootPairSym`: the coefficient pair of the depressed cubic with roots `x`, `y`,
  `-x-y`.
* `WeierstrassCurve.threeRootResidues`: the pairs `(A, B)` for which `Y³ + AY + B` has three
  distinct roots in `𝔽_p`.
* `WeierstrassCurve.doubleRootResidues`: the points `(A, B)` of the cuspidal cubic `4A³ + 27B² = 0`
  with `A ≠ 0`.
* `WeierstrassCurve.deepResidueLocus`: the deep locus refined by a set of residue pairs.

## Main results

* `WeierstrassCurve.card_doubleRootResidues`: `|doubleRootResidues p| = p - 1`.
* `WeierstrassCurve.step6_cubic_bridge`: Step 6's cubic of a short model in the deep locus has a
  double root, resp. three distinct roots, exactly when `(Ā, B̄)` lies on the cuspidal cubic, resp.
  in `threeRootResidues p`.
* `WeierstrassCurve.volume_deepResidueLocus`: the refined deep locus over `S` has mass `|S| p⁻⁷`.
* `WeierstrassCurve.run_eq_I0star_of_not_hasDoubleRoot`: on a short model in the deep locus whose
  Step-6 cubic is separable, Tate's algorithm answers `(I₀*, 1 + #roots)`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The `σ_p`-tower above a whole fibre -/

omit [Fact p.Prime] in
private theorem inv_pow_ten_lt_one_of_five_le (hp : 5 ≤ p) : ((p : ℝ≥0∞)⁻¹) ^ 10 < 1 :=
  pow_lt_one₀ zero_le (ENNReal.inv_lt_one.2 (by exact_mod_cast (by omega : 1 < p))) (by norm_num)

/-- **The non-minimal part of the fibre `{c = t}` is its own image under `σ_p`**, for a
scale-invariant stratification. -/
theorem iUnion_stratFibre_inter_range_eq_image (h : StratScaleInvariant p) (t : ℕ) :
    (⋃ κ : KodairaSymbol, stratFibre p (κ, t)) ∩
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = PadicInt.scaleProdByPPow 4 6 '' (⋃ κ : KodairaSymbol, stratFibre p (κ, t)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hyt, x, rfl⟩
    obtain ⟨κ, hyκ⟩ := Set.mem_iUnion.1 hyt
    have hyUp : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p := stratFibre_subset _ hyκ
    have hxUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_scaleProdByPPow_iff.1 hyUp
    exact ⟨x, Set.mem_iUnion.2 ⟨κ, (mem_stratFibre_iff hxUp).2
      ((h x hxUp hyUp).symm.trans ((mem_stratFibre_iff hyUp).1 hyκ))⟩, rfl⟩
  · rintro y ⟨x, hxt, rfl⟩
    obtain ⟨κ, hxκ⟩ := Set.mem_iUnion.1 hxt
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxκ
    have hyUp : PadicInt.scaleProdByPPow 4 6 x ∈ nonsingularLocus p :=
      mem_nonsingularLocus_scaleProdByPPow_iff.2 hxUp
    exact ⟨Set.mem_iUnion.2 ⟨κ, (mem_stratFibre_iff hyUp).2
      ((h x hxUp hyUp).trans ((mem_stratFibre_iff hxUp).1 hxκ))⟩, ⟨x, rfl⟩⟩

/-! ### Depressed cubics over a field, and their root counts

The shift `X ↦ X - b/3` puts a monic cubic in depressed form `Y³ + AY + B` without changing its
discriminant or its number of distinct roots. -/

namespace Cubic

variable {K : Type*} [Field K]

/-- **The shift that depresses a monic cubic.** With `b = 3e`, `A = c - 3e²` and `B = 2e³ - ce + d`
one has `(X + e)³ + A(X + e) + B = X³ + bX² + cX + d`; a polynomial identity, valid in any
commutative ring. -/
theorem eval_depress {R : Type*} [CommRing R] (c d e : R) (x : R) :
    (Cubic.toPoly ⟨1, 0, c - 3 * e ^ 2, 2 * e ^ 3 - c * e + d⟩).eval (x + e)
      = (Cubic.toPoly ⟨1, 3 * e, c, d⟩).eval x := by
  simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The shift does not change the discriminant. -/
theorem discr_depress {R : Type*} [CommRing R] (c d e : R) :
    (⟨1, 0, c - 3 * e ^ 2, 2 * e ^ 3 - c * e + d⟩ : Cubic R).discr
      = (⟨1, 3 * e, c, d⟩ : Cubic R).discr := by
  simp only [Cubic.discr]
  ring

/-- The shift does not change the number of distinct roots in the field. -/
theorem card_roots_depress [DecidableEq K] (c d e : K) :
    (Cubic.toPoly ⟨1, 0, c - 3 * e ^ 2, 2 * e ^ 3 - c * e + d⟩).roots.toFinset.card
      = (Cubic.toPoly ⟨1, 3 * e, c, d⟩).roots.toFinset.card := by
  have hne : ∀ (b' c' d' : K), (Cubic.toPoly ⟨1, b', c', d'⟩ : Polynomial K) ≠ 0 := fun b' c' d' =>
    Cubic.ne_zero_of_a_ne_zero (P := ⟨1, b', c', d'⟩) one_ne_zero
  have himg : (Cubic.toPoly ⟨1, 0, c - 3 * e ^ 2, 2 * e ^ 3 - c * e + d⟩).roots.toFinset
      = (Cubic.toPoly ⟨1, 3 * e, c, d⟩).roots.toFinset.image (fun x => x + e) := by
    ext y
    simp only [Finset.mem_image, Multiset.mem_toFinset, Polynomial.mem_roots', Polynomial.IsRoot]
    constructor
    · intro hy
      refine ⟨y - e, ⟨hne _ _ _, ?_⟩, by ring⟩
      rw [← eval_depress c d e (y - e), show y - e + e = y by ring]
      exact hy.2
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact ⟨hne _ _ _, by rwa [eval_depress c d e x]⟩
  rw [himg, Finset.card_image_of_injective _ (add_left_injective e)]

/-- **A depressed monic cubic has a double root exactly when `4A³ + 27B² = 0`**: its discriminant
is `-(4A³ + 27B²)`. -/
theorem hasDoubleRoot_depressed_iff {R : Type*} [CommRing R] (A B : R) :
    (⟨1, 0, A, B⟩ : Cubic R).HasDoubleRoot ↔ 4 * A ^ 3 + 27 * B ^ 2 = 0 := by
  rw [Cubic.HasDoubleRoot, Cubic.discr]
  exact ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- **A depressed monic cubic has three distinct roots exactly when it is
`(X - x)(X - y)(X + x + y)` for some `x ≠ y` with `x + y` distinct from both `-x` and `-y`.** -/
theorem card_roots_depressed_eq_three_iff [DecidableEq K] (A B : K) :
    (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K).roots.toFinset.card = 3 ↔
      ∃ x y : K, x ≠ y ∧ x ≠ -x - y ∧ y ≠ -x - y ∧ A = -(x ^ 2 + x * y + y ^ 2) ∧
        B = x ^ 2 * y + x * y ^ 2 := by
  set P : Cubic K := ⟨1, 0, A, B⟩ with hP
  have h0 : (P.toPoly : Polynomial K) ≠ 0 := Cubic.ne_zero_of_a_ne_zero (P := P) one_ne_zero
  have hdeg : P.toPoly.natDegree = 3 := Cubic.natDegree_of_a_ne_zero (P := P) one_ne_zero
  have hmap : Cubic.map (RingHom.id K) P = P := rfl
  refine ⟨fun h => ?_, fun ⟨x, y, hxy, hxz, hyz, hA, hB⟩ => ?_⟩
  · have hle : P.toPoly.roots.card ≤ 3 := hdeg ▸ P.toPoly.card_roots'
    have hge : (3 : ℕ) ≤ P.toPoly.roots.card := h ▸ Multiset.toFinset_card_le _
    have hcard : P.toPoly.roots.card = 3 := le_antisymm hle hge
    have hnodup : P.toPoly.roots.Nodup :=
      Multiset.toFinset_card_eq_card_iff_nodup.1 (by rw [h, hcard])
    obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.1 hcard
    have hroots : (Cubic.map (RingHom.id K) P).roots = {x, y, z} := by
      rwa [hmap, Cubic.roots]
    have hnd : ({x, y, z} : Multiset K).Nodup := hxyz ▸ hnodup
    simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, and_true, not_or] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz⟩ := hnd
    have hb := Cubic.b_eq_three_roots (φ := RingHom.id K) (P := P) one_ne_zero hroots
    have hc := Cubic.c_eq_three_roots (φ := RingHom.id K) (P := P) one_ne_zero hroots
    have hd := Cubic.d_eq_three_roots (φ := RingHom.id K) (P := P) one_ne_zero hroots
    simp only [RingHom.id_apply, hP, one_mul] at hb hc hd
    have hsum : z = -x - y := by linear_combination hb
    refine ⟨x, y, hxy, ?_, ?_, ?_, ?_⟩
    · rwa [← hsum]
    · rwa [← hsum]
    · rw [hc, hsum]; ring
    · rw [hd, hsum]; ring
  · have hle : (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K).roots.toFinset.card ≤ 3 := by
      rw [← Cubic.roots]
      exact Cubic.card_roots_le (P := P)
    have hroot : ∀ w : K, w ^ 3 + A * w + B = 0 →
        w ∈ (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K).roots.toFinset := by
      intro w hw
      refine Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨h0, ?_⟩)
      simp only [Polynomial.IsRoot, Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      linear_combination hw
    have hsub : ({x, y, -x - y} : Finset K)
        ⊆ (Cubic.toPoly ⟨1, 0, A, B⟩ : Polynomial K).roots.toFinset := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> exact hroot _ (by rw [hA, hB]; ring)
    have hc3 : ({x, y, -x - y} : Finset K).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    exact le_antisymm hle (hc3 ▸ Finset.card_le_card hsub)

end Cubic

/-! ### The two residue sets of `𝔽_p²`

The plane `𝔽_p²` of residue pairs `(Ā, B̄)` splits into the pairs with `4Ā³ + 27B̄² ≠ 0`, the
points of the cuspidal cubic `4Ā³ + 27B̄² = 0` with `Ā ≠ 0`, and the origin. Among the first,
`threeRootResidues p` is the set where `Y³ + ĀY + B̄` has three distinct roots; the second is
`doubleRootResidues p`, which has `p - 1` points. -/

variable (p) in
/-- The pairs `(x, y) ∈ 𝔽_p²` for which `x`, `y` and `-x-y` are pairwise distinct: the ordered
parametrizations of a three-element subset of `𝔽_p` of sum `0`. -/
def rootPairs : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun q => q.1 ≠ q.2 ∧ q.1 ≠ -q.1 - q.2 ∧ q.2 ≠ -q.1 - q.2

/-- `(x, y) ↦ (e₂, -e₃)` of the triple `x, y, -x-y`: the coefficient pair of the depressed monic
cubic whose roots those three are. -/
def rootPairSym (q : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (-(q.1 ^ 2 + q.1 * q.2 + q.2 ^ 2), q.1 ^ 2 * q.2 + q.1 * q.2 ^ 2)

variable (p) in
/-- The residue pairs `(A, B) ∈ 𝔽_p²` for which `Y³ + AY + B` has **three** distinct roots in
`𝔽_p`, given as the image of `rootPairs p` under `rootPairSym`. -/
def threeRootResidues : Finset (ZMod p × ZMod p) := (rootPairs p).image rootPairSym

variable (p) in
/-- The residue pairs `(A, B) ∈ 𝔽_p²` on the cuspidal cubic `4A³ + 27B² = 0` with `A ≠ 0`, for
which `Y³ + AY + B` has a double but not a triple root. -/
def doubleRootResidues : Finset (ZMod p × ZMod p) :=
  (cuspidalResidues p).filter fun c => c.1 ≠ 0

/-- A pair `(x, y)` lies in `rootPairs p` exactly when `x`, `y` and `-x - y` are pairwise
distinct. -/
theorem mem_rootPairs_iff {q : ZMod p × ZMod p} :
    q ∈ rootPairs p ↔ q.1 ≠ q.2 ∧ q.1 ≠ -q.1 - q.2 ∧ q.2 ≠ -q.1 - q.2 := by
  simp only [rootPairs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A pair `(A, B)` lies in `threeRootResidues p` exactly when `A = -(x² + xy + y²)` and
`B = x²y + xy²` for some `x`, `y` with `x`, `y`, `-x-y` pairwise distinct. -/
theorem mem_threeRootResidues_iff {c : ZMod p × ZMod p} :
    c ∈ threeRootResidues p ↔ ∃ x y : ZMod p, x ≠ y ∧ x ≠ -x - y ∧ y ≠ -x - y ∧
      c.1 = -(x ^ 2 + x * y + y ^ 2) ∧ c.2 = x ^ 2 * y + x * y ^ 2 := by
  simp only [threeRootResidues, Finset.mem_image, mem_rootPairs_iff, Prod.exists, rootPairSym,
    Prod.ext_iff]
  constructor
  · rintro ⟨x, y, ⟨h1, h2, h3⟩, hc1, hc2⟩
    exact ⟨x, y, h1, h2, h3, hc1.symm, hc2.symm⟩
  · rintro ⟨x, y, h1, h2, h3, hc1, hc2⟩
    exact ⟨x, y, ⟨h1, h2, h3⟩, hc1.symm, hc2.symm⟩

/-! #### The roots of the cubic of `rootPairSym` -/

/-- Both members of the pair `(x, y)` are roots of its own depressed cubic — a ring identity. -/
theorem cubic_rootPairSym_eq_zero (x y : ZMod p) :
    x ^ 3 + (rootPairSym (x, y)).1 * x + (rootPairSym (x, y)).2 = 0 ∧
      y ^ 3 + (rootPairSym (x, y)).1 * y + (rootPairSym (x, y)).2 = 0 := by
  simp only [rootPairSym]
  exact ⟨by ring, by ring⟩

/-! #### The count of `doubleRootResidues` -/

/-- **`|doubleRootResidues p| = p - 1`**, for every prime `p ≥ 5`: the cuspidal cubic has `p`
points, exactly one of which, the cusp, has first coordinate `0`. -/
theorem card_doubleRootResidues (hp : 5 ≤ p) : (doubleRootResidues p).card = p - 1 := by
  classical
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
  have himg : doubleRootResidues p
      = (Finset.univ.erase (0 : ZMod p)).image (cuspParam (p := p)) := by
    rw [doubleRootResidues, cuspidalResidues_eq_image hp, Finset.filter_image]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, cuspParam,
      ne_eq, neg_mul, neg_eq_zero, mul_eq_zero, pow_eq_zero_iff two_ne_zero, h3, false_or]
    tauto
  rw [himg, Finset.card_image_of_injective _ (cuspParam_injective hp),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-! ### From the Step-6 cubic to the residue pair `(a₄/p², a₆/p³)`

The discriminant and the root count of Step 6's cubic are shift-invariant, and the coefficients of
its depressed form are, up to the units `-48` and `-864`, the quotients `c₄/p²` and `c₆/p³`. On a
short model in the deep locus these are `a₄/p²` and `a₆/p³`. -/

/-- `3` is a unit of the residue field at `p ≥ 5`. -/
theorem isUnit_mod_three (hp : 5 ≤ p) :
    IsUnit (3 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  simpa only [map_ofNat] using (PadicInt.isUnit_three hp).map (CommRing.mod (p : ℤ_[p]))

/-- **The depressed form of Step 6's cubic, read off `c₄` and `c₆`.** If `c₄ = -48p²u₄` and
`c₆ = -864p³u₆`, then the cubic `X³ + (a₂/p)X² + (a₄/p²)X + a₆/p³` is `⟨1, 3e, c, d⟩` for some `e`,
`c`, `d` in the residue field, with `ū₄ = c - 3e²` and `ū₆ = 2e³ - ce + d`. -/
theorem exists_depressed_residue (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ A₆ u₄ u₆ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 2 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 2 * A₄)
    (h6 : W.a₆ = (p : ℤ_[p]) ^ 3 * A₆) (hc₄ : W.c₄ = -48 * ((p : ℤ_[p]) ^ 2 * u₄))
    (hc₆ : W.c₆ = -864 * ((p : ℤ_[p]) ^ 3 * u₆)) :
    ∃ e c d : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])},
      cubic (p : ℤ_[p]) W 1 1 = ⟨1, 3 * e, c, d⟩ ∧
        CommRing.mod (p : ℤ_[p]) u₄ = c - 3 * e ^ 2 ∧
        CommRing.mod (p : ℤ_[p]) u₆ = 2 * e ^ 3 - c * e + d := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hz : CommRing.mod (p : ℤ_[p]) (p : ℤ_[p]) = 0 := CommRing.mod_self _
  obtain ⟨v, hv⟩ := (isUnit_mod_three hp).exists_left_inv
  have h864u : IsUnit (864 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
    have h : IsUnit (864 : ℤ_[p]) := by simpa using (isUnit_neg_eightSixFour hp).neg
    simpa only [map_ofNat] using h.map (CommRing.mod (p : ℤ_[p]))
  have e₄ : W.c₄ = (p : ℤ_[p]) ^ 2
      * (((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)) := by
    rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h1, h2, h3, h4]; ring
  have hY₄ : ((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)
      = -48 * u₄ := mul_left_cancel₀ (pow_ne_zero 2 hϖ) (by rw [← e₄, hc₄]; ring)
  have hm₄ : (16 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})
        * (CommRing.mod (p : ℤ_[p]) A₂ ^ 2 - 3 * CommRing.mod (p : ℤ_[p]) A₄)
      = -48 * CommRing.mod (p : ℤ_[p]) u₄ := by
    have hthis := congrArg (CommRing.mod (p : ℤ_[p])) hY₄
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, hz] at hthis
    linear_combination hthis
  have key₄ : 3 * CommRing.mod (p : ℤ_[p]) u₄
      = 3 * CommRing.mod (p : ℤ_[p]) A₄ - CommRing.mod (p : ℤ_[p]) A₂ ^ 2 :=
    mul_left_cancel₀ (isUnit_mod_sixteen hp).ne_zero (by linear_combination hm₄)
  have e₆ : W.c₆ = (p : ℤ_[p]) ^ 3 * (-(((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 3)
      + 36 * ((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)
      - 216 * ((p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆)) := by
    rw [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      h1, h2, h3, h4, h6]
    ring
  have hY₆ : -(((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) ^ 3)
      + 36 * ((p : ℤ_[p]) * A₁ ^ 2 + 4 * A₂) * (2 * A₄ + (p : ℤ_[p]) * A₁ * A₃)
      - 216 * ((p : ℤ_[p]) * A₃ ^ 2 + 4 * A₆) = -864 * u₆ :=
    mul_left_cancel₀ (pow_ne_zero 3 hϖ) (by rw [← e₆, hc₆]; ring)
  have key₆ : (864 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) * CommRing.mod (p : ℤ_[p]) u₆
      = 64 * CommRing.mod (p : ℤ_[p]) A₂ ^ 3
        - 288 * CommRing.mod (p : ℤ_[p]) A₂ * CommRing.mod (p : ℤ_[p]) A₄
        + 864 * CommRing.mod (p : ℤ_[p]) A₆ := by
    have hthis := congrArg (CommRing.mod (p : ℤ_[p])) hY₆
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, hz] at hthis
    linear_combination hthis
  refine ⟨v * CommRing.mod (p : ℤ_[p]) A₂, CommRing.mod (p : ℤ_[p]) A₄,
    CommRing.mod (p : ℤ_[p]) A₆, ?_, ?_, ?_⟩
  · rw [cubic_one_one_eq_of_eq_mul hϖ h2 h4 h6, Cubic.ext_iff]
    refine ⟨rfl, ?_, rfl, rfl⟩
    linear_combination (-(CommRing.mod (p : ℤ_[p]) A₂)) * hv
  · refine mul_left_cancel₀ (isUnit_mod_three hp).ne_zero ?_
    rw [key₄]
    linear_combination (CommRing.mod (p : ℤ_[p]) A₂ ^ 2 * (3 * v + 1)) * hv
  · refine mul_left_cancel₀ h864u.ne_zero ?_
    rw [key₆]
    linear_combination (288 * CommRing.mod (p : ℤ_[p]) A₂ * CommRing.mod (p : ℤ_[p]) A₄
      - 64 * CommRing.mod (p : ℤ_[p]) A₂ ^ 3 * (9 * v ^ 2 + 3 * v + 1)) * hv

/-! ### Transporting the residue conditions to `ZMod p` -/

/-- The three-root condition on a coefficient pair transports along any isomorphism of fields. -/
theorem exists_rootPair_congr {K L : Type*} [Field K] [Field L] (E : K ≃+* L) (A B : K) :
    (∃ x y : K, x ≠ y ∧ x ≠ -x - y ∧ y ≠ -x - y ∧ A = -(x ^ 2 + x * y + y ^ 2) ∧
        B = x ^ 2 * y + x * y ^ 2)
      ↔ (∃ x y : L, x ≠ y ∧ x ≠ -x - y ∧ y ≠ -x - y ∧ E A = -(x ^ 2 + x * y + y ^ 2) ∧
        E B = x ^ 2 * y + x * y ^ 2) := by
  constructor
  · rintro ⟨x, y, h1, h2, h3, hA, hB⟩
    refine ⟨E x, E y, fun h => h1 (E.injective h), fun h => h2 (E.injective ?_),
      fun h => h3 (E.injective ?_), ?_, ?_⟩
    · rw [h, map_sub, map_neg]
    · rw [h, map_sub, map_neg]
    · rw [hA]; simp only [map_neg, map_add, map_mul, map_pow]
    · rw [hB]; simp only [map_add, map_mul, map_pow]
  · rintro ⟨x, y, h1, h2, h3, hA, hB⟩
    refine ⟨E.symm x, E.symm y, fun h => h1 (E.symm.injective h),
      fun h => h2 (E.symm.injective ?_), fun h => h3 (E.symm.injective ?_), ?_, ?_⟩
    · rw [h, map_sub, map_neg]
    · rw [h, map_sub, map_neg]
    · have := congrArg E.symm hA
      simpa only [RingEquiv.symm_apply_apply, map_neg, map_add, map_mul, map_pow] using this
    · have := congrArg E.symm hB
      simpa only [RingEquiv.symm_apply_apply, map_add, map_mul, map_pow] using this

open scoped Classical in
/-- **Three distinct roots of the depressed cubic over the residue field is membership in
`threeRootResidues p`.** -/
theorem card_roots_mod_eq_three_iff (A B : ℤ_[p]) :
    (Cubic.toPoly ⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
        Polynomial (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})).roots.toFinset.card = 3
      ↔ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ threeRootResidues p := by
  classical
  rw [Cubic.card_roots_depressed_eq_three_iff, mem_threeRootResidues_iff,
    exists_rootPair_congr (residueEquiv p), residueEquiv_mod, residueEquiv_mod]

/-- **A double root of the depressed cubic over the residue field is membership in
`cuspidalResidues p`.** -/
theorem hasDoubleRoot_mod_iff (A B : ℤ_[p]) :
    (⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
        Cubic (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})).HasDoubleRoot
      ↔ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ cuspidalResidues p := by
  rw [Cubic.hasDoubleRoot_depressed_iff, cuspidalResidues, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have hkey : (4 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) * CommRing.mod (p : ℤ_[p]) A ^ 3
        + 27 * CommRing.mod (p : ℤ_[p]) B ^ 2
      = CommRing.mod (p : ℤ_[p]) (4 * A ^ 3 + 27 * B ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [hkey, ← (residueEquiv p).map_eq_zero_iff, residueEquiv_mod]
  simp only [map_add, map_mul, map_pow, map_ofNat]

/-! ### Step 6 on a short model in the deep locus -/

open scoped Classical in
/-- **The Step-6 branch data of a short model in the deep locus, read off its residue pair.** For
`a₄ = p²A`, `a₆ = p³B` at `p ≥ 5`: Step 6's cubic has a double root exactly when `(Ā, B̄)` lies on
the cuspidal cubic, and it has three distinct roots exactly when
`(Ā, B̄) ∈ threeRootResidues p`. -/
theorem step6_cubic_bridge (hp : 5 ≤ p) {a₄ a₆ A B : ℤ_[p]}
    (h4 : a₄ = (p : ℤ_[p]) ^ 2 * A) (h6 : a₆ = (p : ℤ_[p]) ^ 3 * B)
    {W' : WeierstrassCurve ℤ_[p]}
    (h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok W') :
    ((cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot
        ↔ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ cuspidalResidues p) ∧
      ((cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).toPoly.roots.toFinset.card = 3
        ↔ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ threeRootResidues p) := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hv6 := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ h5)
  obtain ⟨A₁, hA₁⟩ := hv6.a₁
  obtain ⟨A₂, hA₂⟩ := hv6.a₂
  obtain ⟨A₃, hA₃⟩ := hv6.a₃
  obtain ⟨A₄, hA₄⟩ := hv6.a₄
  obtain ⟨A₆, hA₆⟩ := hv6.a₆
  rw [pow_one] at hA₁ hA₂
  have f₄ : (Step6.translate (p : ℤ_[p]) W').c₄ = -48 * ((p : ℤ_[p]) ^ 2 * A) := by
    rw [Step6.translate_c₄, Step5.run_c₄ h5, ofShortNF_c₄, h4]
  have f₆ : (Step6.translate (p : ℤ_[p]) W').c₆ = -864 * ((p : ℤ_[p]) ^ 3 * B) := by
    rw [Step6.translate_c₆, Step5.run_c₆ h5, ofShortNF_c₆, h6]
  obtain ⟨e, c, d, hcub, hu₄, hu₆⟩ :=
    exists_depressed_residue hp hA₁ hA₂ hA₃ hA₄ hA₆ f₄ f₆
  have hdep : (⟨1, 0, CommRing.mod (p : ℤ_[p]) A, CommRing.mod (p : ℤ_[p]) B⟩ :
      Cubic (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}))
      = ⟨1, 0, c - 3 * e ^ 2, 2 * e ^ 3 - c * e + d⟩ := by
    rw [hu₄, hu₆]
  refine ⟨?_, ?_⟩
  · rw [← hasDoubleRoot_mod_iff, hcub, Cubic.HasDoubleRoot, Cubic.HasDoubleRoot, hdep,
      Cubic.discr_depress]
  · rw [← card_roots_mod_eq_three_iff, hcub, hdep, Cubic.card_roots_depress]

/-! ### The congruence locus of a set of residue pairs, and its mass -/

variable (p) in
/-- The **deep locus refined by a set of residue pairs**: `p² ∣ a₄`, `p³ ∣ a₆` and the residue pair
`(a₄/p², a₆/p³)` lies in `S`. -/
noncomputable def deepResidueLocus (S : Finset (ZMod p × ZMod p)) : Set (ℤ_[p] × ℤ_[p]) :=
  PadicInt.scaleProdByPPow 2 3 '' (PadicInt.redPair p ⁻¹' (S : Set (ZMod p × ZMod p)))

/-- A pair `(a₄, a₆)` lies in `deepResidueLocus p S` exactly when `a₄ = p²A` and `a₆ = p³B` with
the residue pair `(Ā, B̄)` in `S`. -/
theorem mem_deepResidueLocus_iff {S : Finset (ZMod p × ZMod p)} {x : ℤ_[p] × ℤ_[p]} :
    x ∈ deepResidueLocus p S ↔ ∃ A B : ℤ_[p], x.1 = (p : ℤ_[p]) ^ 2 * A ∧
      x.2 = (p : ℤ_[p]) ^ 3 * B ∧ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ S := by
  simp only [deepResidueLocus, Set.mem_image, Set.mem_preimage, PadicInt.scaleProdByPPow_apply,
    PadicInt.redPair, Finset.mem_coe, Prod.exists, Prod.ext_iff]
  constructor
  · rintro ⟨A, B, hS, hx1, hx2⟩
    exact ⟨A, B, hx1.symm, hx2.symm, hS⟩
  · rintro ⟨A, B, hx1, hx2, hS⟩
    exact ⟨A, B, hS, hx1.symm, hx2.symm⟩

/-- **The mass of a refined deep locus is `|S| p⁻⁷`.** -/
theorem volume_deepResidueLocus (S : Finset (ZMod p × ZMod p)) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (deepResidueLocus p S)
      = (S.card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 7 := by
  have hz : (p : ℝ≥0∞) ^ (-(((2 : ℕ) : ℤ) + ((3 : ℕ) : ℤ))) = ((p : ℝ≥0∞)⁻¹) ^ 5 := by
    rw [show -(((2 : ℕ) : ℤ) + ((3 : ℕ) : ℤ)) = -((5 : ℕ) : ℤ) by norm_num,
      ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]
  rw [deepResidueLocus, PadicInt.measure_image_scaleProdByPPow, hz,
    PadicInt.volume_preimage_redPair, ENNReal.inv_pow]
  ring

/-! ### Tate's algorithm when Step 6's cubic is separable -/

open scoped Classical in
/-- **Tate's algorithm on a short model in the deep locus whose Step-6 cubic is separable** answers
`(I₀*, 1 + #roots)`. -/
theorem run_eq_I0star_of_not_hasDoubleRoot (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 3 ∣ a₆)
    (hnd : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).HasDoubleRoot) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = 1 + (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
            (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).toPoly.roots.toFinset.card := by
  classical
  have h5 := step5_run_eq_ok_of_dvd hp h4 h6
  set out : Output ℤ_[p] :=
    ⟨Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)),
      KodairaSymbol.I! 0, 1 + (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).toPoly.roots.toFinset.card⟩
    with hout
  have h6run : Step6.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.error out := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_right hnd
  have h7run : Step7.run (W := ofShortNF a₄ a₆) PadicInt.uniformizer_ne_zero hΔ
      = Except.error out := by
    rw [Step7.run.eq_def]
    split
    next out' heq => rw [← Except.error.inj (h6run.symm.trans heq)]
    next W'' heq => exact absurd (heq.symm.trans h6run) (by simp)
  have h8run : Step8.run (W := ofShortNF a₄ a₆) PadicInt.uniformizer_ne_zero hΔ
      = Except.error out := by
    rw [Step8.run.eq_def, h7run]; rfl
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step8 hΔ h8run)]
  exact ⟨rfl, rfl⟩

end WeierstrassCurve
