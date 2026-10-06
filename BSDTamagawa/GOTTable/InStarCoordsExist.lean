/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarParametrisation

/-!
# Every point of the `Iₙ*` family has good coordinates

Let `p ≥ 5` be prime. Given `a₄ = p²A` and `a₆ = p³B` with `A` a unit and `p ∣ 4A³ + 27B²`, there
is a unit `t` and a `C` divisible by `p` with `goodPair p t C = (a₄, a₆)`, where
`goodPair p t C = (-3p²t², p³(2t³ + C))`. Here `t` is the double root of the cubic `T³ + AT + B`:
first `-3A` is a square in `ℤ_p`, since the cuspidal relation exhibits `9B̄/(2Ā)` as a square root
of `-3Ā` in `ZMod p`; dividing a square root by `3` gives `t` with `-3t² = A`. Of the two roots
`±t`, exactly one has `p ∣ B - 2t³`, because the relation forces `p ∣ (2t³ - B)(2t³ + B)`; the
other choice would give a unit `C`. Consequently the entry locus of Step 7's subprocedure is
exactly the set of good pairs.

## Main results

* `two_ne_zero_zmod`: `2 ≠ 0` in `ZMod p` for `p ≥ 5`.
* `isSquare_neg_three_mul`: `-3A` is a square in `ℤ_p`.
* `exists_goodCoords`: there is a unit `t` with `-3t² = A` and `p ∣ B - 2t³`.
* `exists_goodPair`: `(p²A, p³B) = goodPair p t C` for a unit `t` and `p ∣ C`.
* `mem_deepResidueLocus_doubleRootResidues_iff`: the entry locus of Step 7's subprocedure is the
  set of good pairs `goodPair p t C` with `t` a unit and `p ∣ C`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-- `2 ≠ 0` in `ZMod p` for `p ≥ 5`. -/
theorem two_ne_zero_zmod (hp : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  exact_mod_cast h

/-- **`-3A` is a square in `ℤ_p`** whenever `A` is a unit and `p ∣ 4A³ + 27B²`, at every prime
`p ≥ 5`. By Hensel's lemma it suffices to work in `ZMod p`, where `9B̄/(2Ā)` is a square root of
`-3Ā`: squaring it and clearing denominators gives `-3` times the relation `4Ā³ + 27B̄² = 0`. -/
theorem isSquare_neg_three_mul (hp : 5 ≤ p) {A B : ℤ_[p]} (hA : IsUnit A)
    (hcusp : (p : ℤ_[p]) ∣ 4 * A ^ 3 + 27 * B ^ 2) : IsSquare ((-3 : ℤ_[p]) * A) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  refine (PadicInt.isSquare_iff_isSquare_toZMod hodd (h3.neg.mul hA)).2 ?_
  have ha : (PadicInt.toZMod A : ZMod p) ≠ 0 := fun h =>
    PadicInt.dvd_iff_not_isUnit.1 (PadicInt.dvd_iff_toZMod_eq_zero.2 h) hA
  have hrel : 4 * (PadicInt.toZMod A) ^ 3 + 27 * (PadicInt.toZMod B) ^ 2 = 0 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat] using
      PadicInt.dvd_iff_toZMod_eq_zero.1 hcusp
  have h2 := two_ne_zero_zmod hp
  refine ⟨9 * PadicInt.toZMod B * (2 * PadicInt.toZMod A)⁻¹, ?_⟩
  simp only [map_mul, map_neg, map_ofNat]
  field_simp
  linear_combination (-3 : ZMod p) * hrel

/-- **The good coordinates exist.** For `A` a unit with `p ∣ 4A³ + 27B²`, at every prime `p ≥ 5`,
there is a unit `t` with `-3t² = A` and `p ∣ B - 2t³`. -/
theorem exists_goodCoords (hp : 5 ≤ p) {A B : ℤ_[p]} (hA : IsUnit A)
    (hcusp : (p : ℤ_[p]) ∣ 4 * A ^ 3 + 27 * B ^ 2) :
    ∃ t : ℤ_[p], IsUnit t ∧ (-3 : ℤ_[p]) * t ^ 2 = A ∧ (p : ℤ_[p]) ∣ B - 2 * t ^ 3 := by
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  have h27 : IsUnit (27 : ℤ_[p]) := by
    simpa [show (3 : ℤ_[p]) ^ 3 = 27 by norm_num] using h3.pow 3
  obtain ⟨v, hv⟩ := h3.exists_right_inv
  obtain ⟨u, hu⟩ := isSquare_neg_three_mul hp hA hcusp
  have key : (-3 : ℤ_[p]) * (v * u) ^ 2 = A := by
    have hrw : (v * u) ^ 2 = v ^ 2 * (u * u) := by ring
    rw [hrw, ← hu]
    linear_combination (A * (3 * v + 1)) * hv
  have htu : IsUnit (v * u) :=
    (isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_right (key ▸ hA))
  have hfac : (p : ℤ_[p]) ∣ (B - 2 * (v * u) ^ 3) * (B + 2 * (v * u) ^ 3) := by
    rwa [← key, show 4 * ((-3) * (v * u) ^ 2) ^ 3 + 27 * B ^ 2
        = 27 * ((B - 2 * (v * u) ^ 3) * (B + 2 * (v * u) ^ 3)) by ring,
      h27.dvd_mul_left] at hcusp
  rcases PadicInt.prime_p.dvd_mul.1 hfac with h | h
  · exact ⟨v * u, htu, key, h⟩
  · exact ⟨-(v * u), htu.neg, by rwa [neg_sq],
      by rwa [show B - 2 * (-(v * u)) ^ 3 = B + 2 * (v * u) ^ 3 by ring]⟩

/-- **The coordinates are onto the family.** A point `(p²A, p³B)` with `A` a unit and
`p ∣ 4A³ + 27B²` is `goodPair p t C` for a unit `t` and a `C` divisible by `p`. One takes
`C = B - 2t³` for the `t` of `exists_goodCoords`. -/
theorem exists_goodPair (hp : 5 ≤ p) {A B : ℤ_[p]} (hA : IsUnit A)
    (hcusp : (p : ℤ_[p]) ∣ 4 * A ^ 3 + 27 * B ^ 2) :
    ∃ t C : ℤ_[p], IsUnit t ∧ (p : ℤ_[p]) ∣ C ∧
      goodPair p t C = ((p : ℤ_[p]) ^ 2 * A, (p : ℤ_[p]) ^ 3 * B) := by
  obtain ⟨t, ht, hkey, hdvd⟩ := exists_goodCoords hp hA hcusp
  refine ⟨t, B - 2 * t ^ 3, ht, hdvd, ?_⟩
  rw [goodPair, ← hkey, Prod.mk.injEq]
  constructor <;> ring

/-! ### The entry locus, in good coordinates -/

/-- **The entry locus of Step 7's subprocedure is exactly the set of good pairs.**

  `x ∈ deepResidueLocus p (doubleRootResidues p) ↔ ∃ t C, IsUnit t ∧ p ∣ C ∧ goodPair p t C = x`.

`→` is `exists_goodPair`: the deep locus supplies `A` and `B` with `Ā ≠ 0`, so `A` is a unit, and
`4Ā³ + 27B̄² = 0`, which is `p ∣ 4A³ + 27B²`. `←` is the identity
`4(-3t²)³ + 27(2t³ + C)² = 27C(4t³ + C)`, which `p ∣ C` kills modulo `p`, together with
`Ā = -3t̄² ≠ 0`. This lifts the residue-level parametrisation `t ↦ (-3t², 2t³)` of the cuspidal
cubic from `ZMod p` to `ℤ_p`, with the defect `C` of the lift made explicit. -/
theorem mem_deepResidueLocus_doubleRootResidues_iff (hp : 5 ≤ p) {x : ℤ_[p] × ℤ_[p]} :
    x ∈ deepResidueLocus p (doubleRootResidues p) ↔
      ∃ t C : ℤ_[p], IsUnit t ∧ (p : ℤ_[p]) ∣ C ∧ goodPair p t C = x := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    have h : ((3 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
    exact_mod_cast h
  constructor
  · intro hx
    obtain ⟨A, B, hx1, hx2, hmem⟩ := mem_deepResidueLocus_iff.1 hx
    rw [doubleRootResidues, Finset.mem_filter, cuspidalResidues, Finset.mem_filter] at hmem
    obtain ⟨⟨-, hcusp0⟩, hAne⟩ := hmem
    have hA : IsUnit A := by
      by_contra hcon
      exact hAne (PadicInt.dvd_iff_toZMod_eq_zero.1 (PadicInt.dvd_iff_not_isUnit.2 hcon))
    obtain ⟨t, C, ht, hC, hgp⟩ :=
      exists_goodPair (B := B) hp hA <| PadicInt.dvd_iff_toZMod_eq_zero.2 <| by
        simpa only [map_add, map_mul, map_pow, map_ofNat] using hcusp0
    exact ⟨t, C, ht, hC, by rw [hgp, ← hx1, ← hx2]⟩
  · rintro ⟨t, C, ht, hC, rfl⟩
    have htz : PadicInt.toZMod t ≠ 0 := fun h =>
      PadicInt.dvd_iff_not_isUnit.1 (PadicInt.dvd_iff_toZMod_eq_zero.2 h) ht
    have hCz : PadicInt.toZMod C = 0 := PadicInt.dvd_iff_toZMod_eq_zero.1 hC
    refine mem_deepResidueLocus_iff.2 ⟨(-3) * t ^ 2, 2 * t ^ 3 + C, by rw [goodPair]; ring,
      by rw [goodPair], ?_⟩
    rw [doubleRootResidues, Finset.mem_filter, cuspidalResidues, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simp only [map_add, map_mul, map_pow, map_neg, map_ofNat, hCz]
      ring
    · simp only [map_mul, map_pow, map_neg, map_ofNat]
      exact mul_ne_zero (neg_ne_zero.2 h3) (pow_ne_zero 2 htz)

end WeierstrassCurve
