/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowLowerBoundThree

/-!
# The quadratic twist by `−1` on the coefficient plane at `p = 3`

`ι(a₄, a₆) = (a₄, −a₆)` is the quadratic twist of the short model `y² = x³ + a₄x + a₆` by the unit
`−1`, which is a non-square in `ℤ_3ˣ`. This file defines `ι` and records the residue-field
arithmetic behind it: Frobenius is the identity on the residue field `𝔽_p` of `ℤ_[p]`, and on
`𝔽₃` negation exchanges the two square classes of nonzero elements. The latter is the arithmetic
by which `ι` exchanges the Tamagawa numbers at those exits of Tate's algorithm whose square test
is linear in `a₆`.

## Main definitions

* `WeierstrassCurve.twistThree`: the map, as `twistPlane (−1)`.
* `WeierstrassCurve.residueRingEquiv`: the residue ring `ℤ_[p] ⧸ (p)` as `ZMod p`.

## Main results

* `WeierstrassCurve.twistThree_apply`: `ι(a₄, a₆) = (a₄, −a₆)`.
* `WeierstrassCurve.residue_pow_self`, `…residue_root_self`: Frobenius, and hence the `p`-th root,
  is the identity on the residue field of `ℤ_[p]`.
* `WeierstrassCurve.isSquare_neg_iff_three`: negation flips the square class on the residue field
  of `ℤ_3`.

## Implementation notes

The twist does not exchange Tamagawa numbers uniformly across the `Iₘ*` family. On a short model
the odd exit (`m` odd) tests `IsSquare (4d)` with `d` linear in `a₆`, so `ι` flips it, whereas the
even exit (`m` even) tests `B² − 4AC` with `A` independent of `a₆` and `B`, `C` odd in `a₆`, so the
test is even in `a₆` and `ι` does not move it.
-/

open scoped ENNReal
open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### The map -/

variable (p) in
/-- **The quadratic twist by `−1` on the coefficient plane**: `ι(a₄, a₆) = (a₄, −a₆)`. This is
`twistPlane (−1)`, and `−1` is a non-square in `ℤ_3ˣ`, so `ι` is the non-trivial unramified
quadratic twist at `p = 3`. -/
noncomputable def twistThree : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p] := twistPlane (-1 : ℤ_[p])

/-- `ι` negates the second coordinate and fixes the first. -/
theorem twistThree_apply (x : ℤ_[p] × ℤ_[p]) : twistThree p x = (x.1, -x.2) := by
  simp [twistThree, twistPlane, Prod.map, show ((-1 : ℤ_[p])) ^ 3 = -1 by ring]

/-- `ι` fixes the first coordinate. -/
@[simp]
theorem twistThree_fst (x : ℤ_[p] × ℤ_[p]) : (twistThree p x).1 = x.1 := by
  rw [twistThree_apply]

/-- `ι` negates the second coordinate. -/
@[simp]
theorem twistThree_snd (x : ℤ_[p] × ℤ_[p]) : (twistThree p x).2 = -x.2 := by
  rw [twistThree_apply]

/-! ### Frobenius is the identity on the residue field -/

/-- The ring isomorphism `ℤ_[p] ⧸ (p) ≃+* ZMod p`. -/
noncomputable def residueRingEquiv (p : ℕ) [Fact p.Prime] :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq PadicInt.maximalIdeal_eq_span_p.symm).trans PadicInt.residueField

/-- **Frobenius is the identity on the residue field of `ℤ_[p]`.** The residue field is `ZMod p`,
so this is `ZMod.pow_card` transported along `residueRingEquiv`. -/
theorem residue_pow_self (x : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) : x ^ p = x :=
  (residueRingEquiv p).injective (by rw [map_pow, ZMod.pow_card])

/-- **The `p`-th root on the residue field of `ℤ_[p]` is the identity.** Since `x ↦ x ^ p` is the
identity there (`residue_pow_self`), the `p`-th root of `x` is `x`. -/
theorem residue_root_self [ExpChar (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) p]
    [PerfectRing (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) p]
    (x : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) : CharP.root p x = x := by
  conv_lhs => rw [← residue_pow_self x]
  rw [CharP.root_pow]

/-! ### The flip on the residue field of `ℤ_[3]` -/

/-- Square-ness transports along `residueRingEquiv`, both ways. -/
theorem isSquare_residueRingEquiv_iff (x : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) :
    IsSquare x ↔ IsSquare (residueRingEquiv p x) :=
  ⟨fun h => h.map (residueRingEquiv p), fun h => by simpa using h.map (residueRingEquiv p).symm⟩

private theorem zmod_three_isSquare_neg_iff :
    ∀ z : ZMod 3, z ≠ 0 → (IsSquare (-z) ↔ ¬ IsSquare z) := by decide

/-- **Negation flips the square class on the residue field of `ℤ_3`**: for `d ≠ 0`, `-d` is a
square exactly when `d` is not, since `−1` is a non-residue mod `3`. -/
theorem isSquare_neg_iff_three (hp3 : p = 3) {d : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}} (hd : d ≠ 0) :
    IsSquare (-d) ↔ ¬ IsSquare d := by
  subst hp3
  rw [isSquare_residueRingEquiv_iff, isSquare_residueRingEquiv_iff d, map_neg]
  exact zmod_three_isSquare_neg_iff _ fun h =>
    hd ((residueRingEquiv 3).injective (h.trans (map_zero _).symm))

end WeierstrassCurve

end
