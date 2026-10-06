/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.PadicHaar

/-!
# Square level sets with a non-unit centre, and the `9 ∣ a₄` slices at `p = 3`

For a centre `c ∈ ℤ_[p]`, this file studies the square level sets
`sqLevelSet c m = {x | v(x² - c) = m}`:

* when `v(x²) < v(c)` the centre is invisible: `v(x² - c) = v(x²)`;
* when `v(c) = 2r` is even, writing `c = p^{2r} c'` with `c'` a unit, the level set at `2r + n`
  is the dilate `p^r · sqLevelSet c' n`.

At `p = 3`, on the plane `a₄ = 9β`, the discriminant is `Δ = -16 · 27 · (a₆² - (-108β³))`, so the
`a₆`-slice at level `v₃(Δ) = m + 3` is `sqLevelSet (-108β³) m`.

## Main results

* `PadicInt.emultiplicity_sq_sub_eq_left`: the ultrametric identity `v(x² - c) = v(x²)` when
  `v(x²) < v(c)`.
* `PadicInt.sqLevelSet_pPow_mul_eq_image`: at and above an even `v(c) = 2r`, the level set is the
  `p^r`-dilate of a unit-centre one, for every `n ≥ 0`.
* `WeierstrassCurve.setOf_emultiplicity_Δ_nine_mul_eq_sqLevelSet`: at `p = 3`, the slice at level
  `m + 3` is `PadicInt.sqLevelSet (-108β³) m`.

## Implementation notes

The prime is carried as `p` with `hp3 : p = 3`, so that the lemmas about `(p : ℤ_[p])` with
`[Fact p.Prime]` apply verbatim; for the same reason the coefficient is written
`(p : ℤ_[p]) ^ 2 * β` rather than `9 * β` in the `p`-adic statements. Levels are written `m + 3`
or `2 * r + n` so that no truncated natural subtraction occurs.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ## `ℕ∞` bookkeeping for the valuation of a square

`v(y²) = v(y) + v(y)`, so `2r ≤ v(y²)` forces `r ≤ v(y)`. -/

/-- The valuation of a square is twice the valuation. -/
private theorem emultiplicity_sq (y : ℤ_[p]) :
    emultiplicity (p : ℤ_[p]) (y ^ 2)
      = emultiplicity (p : ℤ_[p]) y + emultiplicity (p : ℤ_[p]) y := by
  rw [sq, emultiplicity_mul prime_p]

/-- In `ℕ∞`, `2r ≤ a + a` forces `r ≤ a`. -/
private theorem le_of_two_mul_le_add_self {a : ℕ∞} {r : ℕ}
    (h : ((2 * r : ℕ) : ℕ∞) ≤ a + a) : (r : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with htop | hne
  · simp [htop]
  · obtain ⟨l, rfl⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← Nat.cast_add, Nat.cast_le] at h
    exact_mod_cast (by omega : r ≤ l)

/-- A `p`-adic integer not divisible by `p` is a unit. -/
private theorem isUnit_of_not_dvd_uniformizer {y : ℤ_[p]} (hy : ¬ (p : ℤ_[p]) ∣ y) : IsUnit y :=
  isUnit_iff.2 (le_antisymm (norm_le_one y)
    (le_of_not_gt fun h => hy ((norm_lt_one_iff_dvd y).1 h)))

/-- An element of valuation exactly `w` is `p^w` times a unit. -/
theorem exists_isUnit_of_emultiplicity_eq_natCast {y : ℤ_[p]} {w : ℕ}
    (hy : emultiplicity (p : ℤ_[p]) y = (w : ℕ∞)) :
    ∃ u : ℤ_[p], IsUnit u ∧ y = (p : ℤ_[p]) ^ w * u := by
  obtain ⟨hdvd, hndvd⟩ := (emultiplicity_eq_coe (n := w)).1 hy
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, isUnit_of_not_dvd_uniformizer fun ⟨t, ht⟩ => hndvd ⟨t, ?_⟩, hu⟩
  rw [hu, ht]; ring

/-! ## The ultrametric identity for `x² - c`

For an arbitrary centre `c`, the valuation of `x² - c` is `v(x²)` whenever `v(x²) < v(c)`. -/

/-- If `v(x²) < v(c)` then `v(x² - c) = v(x²)`: the centre is invisible. -/
theorem emultiplicity_sq_sub_eq_left {c x : ℤ_[p]}
    (h : emultiplicity (p : ℤ_[p]) (x ^ 2) < emultiplicity (p : ℤ_[p]) c) :
    emultiplicity (p : ℤ_[p]) (x ^ 2 - c) = emultiplicity (p : ℤ_[p]) (x ^ 2) := by
  rw [sub_eq_add_neg, add_comm]
  exact emultiplicity_add_of_gt (by rwa [emultiplicity_neg])

/-! ## An even `v(c)`: the two-ball count reappears, dilated -/

/-- For `c'` a unit and every `r` and `n`,

  `sqLevelSet (p^{2r} c') (2r + n) = p^r · sqLevelSet c' n`. -/
theorem sqLevelSet_pPow_mul_eq_image {c' : ℤ_[p]} (hc' : IsUnit c') (r n : ℕ) :
    sqLevelSet ((p : ℤ_[p]) ^ (2 * r) * c') (2 * r + n)
      = scaleByPPow r '' sqLevelSet c' n := by
  have hcval : emultiplicity (p : ℤ_[p]) ((p : ℤ_[p]) ^ (2 * r) * c') = ((2 * r : ℕ) : ℕ∞) := by
    rw [emultiplicity_mul prime_p, emultiplicity_pow_self_of_prime prime_p,
      emultiplicity_eq_zero_of_isUnit hc', add_zero]
  have hshift : ∀ z : ℤ_[p], emultiplicity (p : ℤ_[p]) ((p : ℤ_[p]) ^ (2 * r) * z)
      = ((2 * r : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) z := fun z => by
    rw [emultiplicity_mul prime_p, emultiplicity_pow_self_of_prime prime_p]
  have hcancel : ∀ a b : ℕ∞, ((2 * r : ℕ) : ℕ∞) + a = ((2 * r : ℕ) : ℕ∞) + b → a = b :=
    fun _ _ h =>
      ENat.add_right_injective_of_ne_top (n := ((2 * r : ℕ) : ℕ∞)) (ENat.natCast_ne_top _) h
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · rw [mem_sqLevelSet] at hx
    have hnlt : ¬ emultiplicity (p : ℤ_[p]) (x ^ 2)
        < emultiplicity (p : ℤ_[p]) ((p : ℤ_[p]) ^ (2 * r) * c') := by
      intro h
      rw [emultiplicity_sq_sub_eq_left h] at hx
      rw [hcval, hx] at h
      exact absurd (by exact_mod_cast h : 2 * r + n < 2 * r) (by omega)
    have hge : ((2 * r : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ_[p]) x + emultiplicity (p : ℤ_[p]) x := by
      rw [← emultiplicity_sq, ← hcval]
      exact not_lt.1 hnlt
    obtain ⟨u, hu⟩ := pow_dvd_of_le_emultiplicity (le_of_two_mul_le_add_self hge)
    refine ⟨u, ?_, ?_⟩
    · rw [mem_sqLevelSet]
      refine hcancel _ _ ?_
      rw [← hshift, show (p : ℤ_[p]) ^ (2 * r) * (u ^ 2 - c') = x ^ 2 - (p : ℤ_[p]) ^ (2 * r) * c'
        by rw [hu]; ring, hx]
      push_cast
      ring
    · rw [scaleByPPow, hu]
  · rintro x ⟨u, hu, rfl⟩
    rw [mem_sqLevelSet] at hu
    rw [mem_sqLevelSet, scaleByPPow,
      show ((p : ℤ_[p]) ^ r * u) ^ 2 - (p : ℤ_[p]) ^ (2 * r) * c'
        = (p : ℤ_[p]) ^ (2 * r) * (u ^ 2 - c') by ring, hshift, hu]
    push_cast
    ring

end PadicInt

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ## The plane `a₄ = 9β` at `p = 3` -/

/-- `-4` is a unit of `ℤ_[3]`. -/
private theorem isUnit_neg_four_of_eq_three (hp3 : p = 3) : IsUnit (-4 : ℤ_[p]) := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two (hp3 ▸ (by decide : Odd 3))
  simpa [show (2 : ℤ_[p]) * 2 = 4 by norm_num] using (h2.mul h2).neg

/-- `-16` is a unit of `ℤ_[3]`. -/
private theorem isUnit_neg_sixteen_of_eq_three (hp3 : p = 3) : IsUnit (-16 : ℤ_[p]) := by
  have h4 : IsUnit (4 : ℤ_[p]) := by simpa using (isUnit_neg_four_of_eq_three hp3).neg
  simpa [show (4 : ℤ_[p]) * 4 = 16 by norm_num] using (h4.mul h4).neg

/-- For a short model with `a₄ = 3²β` over `ℤ_[3]`,

  `v₃(Δ) = 3 + v₃(a₆² - (-108β³))`. -/
theorem emultiplicity_Δ_nine_mul (hp3 : p = 3) (β a₆ : ℤ_[p]) :
    emultiplicity (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * β) a₆).Δ
      = 3 + emultiplicity (p : ℤ_[p]) (a₆ ^ 2 - (-108 * β ^ 3)) := by
  have h16 : IsUnit (-16 : ℤ_[p]) := isUnit_neg_sixteen_of_eq_three hp3
  have hΔ : (ofShortNF ((p : ℤ_[p]) ^ 2 * β) a₆).Δ
      = -16 * ((p : ℤ_[p]) ^ 3 * (a₆ ^ 2 - (-108 * β ^ 3))) := by
    subst hp3
    rw [ofShortNF_Δ]
    push_cast
    ring
  rw [hΔ, emultiplicity_mul PadicInt.prime_p, PadicInt.emultiplicity_eq_zero_of_isUnit h16,
    zero_add, emultiplicity_mul PadicInt.prime_p,
    emultiplicity_pow_self_of_prime PadicInt.prime_p]
  norm_num

/-- For `a₄ = 3²β` over `ℤ_[3]`,

  `{a₆ : v₃(Δ) = m + 3} = sqLevelSet (-108β³) m`. -/
theorem setOf_emultiplicity_Δ_nine_mul_eq_sqLevelSet (hp3 : p = 3) (β : ℤ_[p]) (m : ℕ) :
    {a₆ : ℤ_[p] | emultiplicity (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 2 * β) a₆).Δ
        = ((m + 3 : ℕ) : ℕ∞)} = PadicInt.sqLevelSet (-108 * β ^ 3) m := by
  ext a₆
  rw [Set.mem_ofPred_eq, PadicInt.mem_sqLevelSet, emultiplicity_Δ_nine_mul hp3,
    show ((m + 3 : ℕ) : ℕ∞) = 3 + (m : ℕ∞) by push_cast; ring]
  exact (ENat.add_right_injective_of_ne_top (n := (3 : ℕ∞)) (by simp)).eq_iff

end WeierstrassCurve
