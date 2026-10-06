/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarCoordsExist
public import BSDTamagawa.GOTTable.InStarGoodModel

/-!
# The `Iₘ*` stratum as a region of the `(A, B)` plane

For `t` a unit and `p ∣ C`, the pair `goodPair p t C = (-3p²t², p³(2t³ + C))` is the image of
`(A, B) = (-3t², 2t³ + C)` under the dilation `(A, B) ↦ (p²A, p³B)`. With `C = pᵐc₀` and `c₀` a
unit, Step 7's subprocedure returns `Iₘ*` with Tamagawa number `4` or `2` according as
`goodModelTest t c₀ m` is a square. This file defines the corresponding region of the `(A, B)`
plane.

## Main definitions

* `deepScale`: the dilation `(A, B) ↦ (p²A, p³B)` of `ℤ_[p] × ℤ_[p]`.
* `goodRegion`: the set of `(-3t², 2t³ + pᵐc₀)` with `t`, `c₀` units for which
  `if IsSquare (goodModelTest t c₀ m) then 4 else 2` equals `c`.

## Main results

* `deepScale_ofCoords`: `deepScale p (-3t², 2t³ + C) = goodPair p t C`.
* `mem_goodRegion_iff`: membership in `goodRegion`, unfolded.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm TateAlgorithm.Step7

variable (p) in
/-- The dilation `(A, B) ↦ (p²A, p³B)` of `ℤ_[p] × ℤ_[p]`, that is,
`PadicInt.scaleProdByPPow 2 3`. -/
noncomputable def deepScale : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p] := PadicInt.scaleProdByPPow 2 3

/-- `deepScale p (A, B) = (p²A, p³B)`. -/
theorem deepScale_apply (z : ℤ_[p] × ℤ_[p]) :
    deepScale p z = ((p : ℤ_[p]) ^ 2 * z.1, (p : ℤ_[p]) ^ 3 * z.2) :=
  PadicInt.scaleProdByPPow_apply ..

open scoped Classical in
variable (p) in
/-- The set of pairs `(A, B) = (-3t², 2t³ + pᵐc₀)` with `t` and `c₀` units such that
`if IsSquare (goodModelTest t c₀ m) then 4 else 2` equals `c`. -/
noncomputable def goodRegion (m c : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  {z | ∃ t c₀ : ℤ_[p], IsUnit t ∧ IsUnit c₀ ∧
    z = ((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * c₀) ∧
    (if IsSquare (goodModelTest t c₀ m) then 4 else 2) = c}

/-- For `t, C ∈ ℤ_[p]`, `deepScale p (-3t², 2t³ + C) = goodPair p t C`. -/
theorem deepScale_ofCoords (t C : ℤ_[p]) :
    deepScale p ((-3) * t ^ 2, 2 * t ^ 3 + C) = goodPair p t C := by
  rw [deepScale_apply, goodPair, Prod.mk.injEq]
  constructor
  · ring
  · rfl

open scoped Classical in
/-- `z ∈ goodRegion p m c` if and only if `z = (-3t², 2t³ + pᵐc₀)` for units `t`, `c₀` with
`if IsSquare (goodModelTest t c₀ m) then 4 else 2` equal to `c`. -/
theorem mem_goodRegion_iff {m c : ℕ} {z : ℤ_[p] × ℤ_[p]} :
    z ∈ goodRegion p m c ↔ ∃ t c₀ : ℤ_[p], IsUnit t ∧ IsUnit c₀ ∧
      z = ((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * c₀) ∧
      (if IsSquare (goodModelTest t c₀ m) then 4 else 2) = c := Iff.rfl

end WeierstrassCurve
