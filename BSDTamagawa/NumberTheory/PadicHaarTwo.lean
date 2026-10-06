/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.PadicHaar

/-!
# The square level sets of `ℤ_[2]`

For a unit `c` and an odd prime `p`, the square level set
`sqLevelSet c n = {x : ℤ_[p] | v_p(x² - c) = n}` has mass `2(1 - p⁻¹)p⁻ⁿ` when `c` is a square and
`0` otherwise, for every `n ≥ 1`. At `p = 2` the shape of these sets changes, and this file
describes them. Writing `c = s²` with `s` a unit, the factors of `x² - c = (x - s)(x + s)` are both
non-units, and exactly one of them has valuation `1`. Hence for `m ≥ 2` the level set at level
`m + 1` is the disjoint union of the two valuation level sets `{x | v₂(x ∓ s) = m}`. The squares
among the units of `ℤ_[2]` are those congruent to `1` mod `8`, and for a unit non-square `c` the
level set is empty at every level `n ≥ 3`.

## Main results

* `PadicInt.emultiplicity_sub_or_add_eq_one_of_eq_two`: for units `x` and `s` of `ℤ_[2]`, exactly
  one of `x - s`, `x + s` has valuation `1`, the other having valuation `> 1`.
* `PadicInt.isSquare_iff_three_le_emultiplicity_sub_one_of_eq_two`: a unit `c` of `ℤ_[2]` is a
  square iff `v₂(c - 1) ≥ 3`, i.e. iff `c ≡ 1 mod 8`.
* `PadicInt.sqLevelSet_eq_union_of_eq_two`: for `c = s²` a unit and `m ≥ 2`, the level set at
  level `m + 1` is the disjoint union of the two valuation level sets `{x | v₂(x ∓ s) = m}`.
* `PadicInt.sqLevelSet_eq_empty_of_not_isSquare_of_eq_two`: for a unit non-square `c`, the level
  set is empty for every `n ≥ 3`.

## Implementation notes

The prime is carried as `p` together with `hp2 : p = 2` rather than as the numeral `2`, so that
the lemmas about `(p : ℤ_[p])` with `[Fact p.Prime]` apply verbatim.

For a unit non-square `c` the bound `n ≥ 3` cannot be weakened to `n ≥ 1`: if `c ≢ 1 mod 8` then
`v₂(x² - c) = v₂(c - 1) ∈ {1, 2}` for every unit `x`, so the level set at that one level is the
whole unit group.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ## Units, divisibility and the valuation -/

/-- A non-unit of `ℤ_[p]` is divisible by `p`. -/
private theorem dvd_of_not_isUnit {y : ℤ_[p]} (hy : ¬ IsUnit y) : (p : ℤ_[p]) ∣ y :=
  (norm_lt_one_iff_dvd y).1 (lt_of_le_of_ne (norm_le_one y) fun h => hy (isUnit_iff.2 h))

/-- A `p`-adic integer not divisible by `p` is a unit. -/
private theorem isUnit_of_not_dvd {y : ℤ_[p]} (hy : ¬ (p : ℤ_[p]) ∣ y) : IsUnit y :=
  not_not.1 fun h => hy (dvd_of_not_isUnit h)

/-- A unit of `ℤ_[p]` is not divisible by `p`. -/
private theorem not_dvd_of_isUnit {y : ℤ_[p]} (hy : IsUnit y) : ¬ (p : ℤ_[p]) ∣ y :=
  fun h => p_nonunit (isUnit_of_dvd_unit h hy)

/-- `1 ≤ v y` iff `p ∣ y`, for the `ℕ∞`-valued valuation `v = emultiplicity (p : ℤ_[p])`. -/
theorem one_le_emultiplicity_iff_dvd {y : ℤ_[p]} :
    1 ≤ emultiplicity (p : ℤ_[p]) y ↔ (p : ℤ_[p]) ∣ y := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ← pow_dvd_iff_le_emultiplicity, pow_one]

/-- `ZMod 2` has a single nonzero element. -/
private theorem eq_one_of_ne_zero_zmod_two : ∀ u : ZMod 2, u ≠ 0 → u = 1 := by decide

/-- `3 ≤ 1 + a` in `ℕ∞` whenever `1 < a`. -/
private theorem three_le_one_add {a : ℕ∞} (ha : 1 < a) : (3 : ℕ∞) ≤ 1 + a := by
  have h2 : (1 : ℕ∞) + 1 ≤ a := Order.add_one_le_of_lt ha
  calc (3 : ℕ∞) = 1 + (1 + 1) := by norm_num
    _ ≤ 1 + a := by gcongr

/-- The valuation of the uniformizer is `1`. -/
theorem emultiplicity_uniformizer : emultiplicity (p : ℤ_[p]) (p : ℤ_[p]) = 1 := by
  have h := emultiplicity_pow_self_of_prime (prime_p (p := p)) 1
  rwa [pow_one, Nat.cast_one] at h

/-- An element of valuation exactly `1` is `p` times a unit. -/
theorem exists_isUnit_of_emultiplicity_eq_one {y : ℤ_[p]} (hy : emultiplicity (p : ℤ_[p]) y = 1) :
    ∃ u : ℤ_[p], IsUnit u ∧ y = (p : ℤ_[p]) * u := by
  obtain ⟨hdvd, hndvd⟩ := (emultiplicity_eq_coe (n := 1)).1 (by rw [hy]; rfl)
  rw [pow_one] at hdvd
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, isUnit_of_not_dvd fun ⟨v, hv⟩ => hndvd ⟨v, ?_⟩, hu⟩
  rw [hu, hv]; ring

/-- If `x - s` is divisible by `p` and `s` is a unit then so is `x`. -/
theorem isUnit_of_dvd_sub {x s : ℤ_[p]} (hs : IsUnit s) (h : (p : ℤ_[p]) ∣ x - s) : IsUnit x :=
  isUnit_of_not_dvd fun hx => not_dvd_of_isUnit hs
    (by simpa using dvd_sub hx h)

/-! ## The even prime: units differ by exactly one factor of `2` -/

/-- At `p = 2` every unit of `ℤ_[2]` is `≡ 1 mod 2`. -/
theorem dvd_sub_one_of_isUnit_of_eq_two (hp2 : p = 2) {a : ℤ_[p]} (ha : IsUnit a) :
    (p : ℤ_[p]) ∣ a - 1 := by
  subst hp2
  have hres : toZMod a = 1 :=
    eq_one_of_ne_zero_zmod_two _ (ha.map (toZMod : ℤ_[2] →+* ZMod 2)).ne_zero
  have hmem : a - 1 ∈ RingHom.ker (toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [RingHom.mem_ker, map_sub, map_one, hres, sub_self]
  rwa [ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem

/-- At `p = 2` the sum of two units is a non-unit. -/
theorem dvd_add_of_isUnit_of_eq_two (hp2 : p = 2) {a b : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b) :
    (p : ℤ_[p]) ∣ a + b := by
  have hd : (p : ℤ_[p]) ∣ 2 := by subst hp2; exact ⟨1, by push_cast; ring⟩
  have h := dvd_add (dvd_add (dvd_sub_one_of_isUnit_of_eq_two hp2 ha)
    (dvd_sub_one_of_isUnit_of_eq_two hp2 hb)) hd
  rwa [show a - 1 + (b - 1) + 2 = a + b by ring] at h

/-- At `p = 2` the difference of two units is a non-unit. -/
theorem dvd_sub_of_isUnit_of_eq_two (hp2 : p = 2) {a b : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b) :
    (p : ℤ_[p]) ∣ a - b := by
  have h := dvd_add_of_isUnit_of_eq_two hp2 ha hb.neg
  rwa [show a + -b = a - b by ring] at h

/-- For units `x` and `s` of `ℤ_[2]`, exactly one of `x - s`, `x + s` has valuation `1`; the other
has valuation `> 1`. -/
theorem emultiplicity_sub_or_add_eq_one_of_eq_two (hp2 : p = 2) {x s : ℤ_[p]} (hx : IsUnit x)
    (hs : IsUnit s) :
    (emultiplicity (p : ℤ_[p]) (x - s) = 1 ∧ 1 < emultiplicity (p : ℤ_[p]) (x + s)) ∨
      (emultiplicity (p : ℤ_[p]) (x + s) = 1 ∧ 1 < emultiplicity (p : ℤ_[p]) (x - s)) := by
  have hc : (2 : ℤ_[p]) = (p : ℤ_[p]) := by subst hp2; push_cast; ring
  have hsub : 1 ≤ emultiplicity (p : ℤ_[p]) (x - s) :=
    one_le_emultiplicity_iff_dvd.2 (dvd_sub_of_isUnit_of_eq_two hp2 hx hs)
  have hadd : 1 ≤ emultiplicity (p : ℤ_[p]) (x + s) :=
    one_le_emultiplicity_iff_dvd.2 (dvd_add_of_isUnit_of_eq_two hp2 hx hs)
  have hmin : min (emultiplicity (p : ℤ_[p]) (x - s)) (emultiplicity (p : ℤ_[p]) (x + s)) ≤ 1 := by
    have h := min_le_emultiplicity_add (p := (p : ℤ_[p])) (a := x - s) (b := x + s)
    rw [show x - s + (x + s) = (p : ℤ_[p]) * x by linear_combination x * hc,
      emultiplicity_mul prime_p, emultiplicity_uniformizer,
      emultiplicity_eq_zero_of_isUnit hx, add_zero] at h
    exact h
  have hnotboth : ¬(emultiplicity (p : ℤ_[p]) (x - s) = 1 ∧
      emultiplicity (p : ℤ_[p]) (x + s) = 1) := by
    rintro ⟨hA, hB⟩
    obtain ⟨u, hu, hxu⟩ := exists_isUnit_of_emultiplicity_eq_one hA
    obtain ⟨w, hw, hxw⟩ := exists_isUnit_of_emultiplicity_eq_one hB
    have hxsum : x = u + w :=
      mul_left_cancel₀ uniformizer_ne_zero
        (by linear_combination hxu + hxw - x * hc : (p : ℤ_[p]) * x = (p : ℤ_[p]) * (u + w))
    exact not_dvd_of_isUnit hx (hxsum ▸ dvd_add_of_isUnit_of_eq_two hp2 hu hw)
  rcases le_total (emultiplicity (p : ℤ_[p]) (x - s)) (emultiplicity (p : ℤ_[p]) (x + s)) with
    hle | hle
  · rw [min_eq_left hle] at hmin
    have hA : emultiplicity (p : ℤ_[p]) (x - s) = 1 := le_antisymm hmin hsub
    exact Or.inl ⟨hA, lt_of_le_of_ne hadd fun h => hnotboth ⟨hA, h.symm⟩⟩
  · rw [min_eq_right hle] at hmin
    have hB : emultiplicity (p : ℤ_[p]) (x + s) = 1 := le_antisymm hmin hadd
    exact Or.inr ⟨hB, lt_of_le_of_ne hsub fun h => hnotboth ⟨h.symm, hB⟩⟩

/-! ## The `p = 2` square criterion: `c` is a square iff `c ≡ 1 mod 8` -/

/-- An odd square is `≡ 1 mod 8`: for a unit `s` of `ℤ_[2]`, `v₂(s² - 1) ≥ 3`. -/
theorem three_le_emultiplicity_sq_sub_one_of_eq_two (hp2 : p = 2) {s : ℤ_[p]} (hs : IsUnit s) :
    3 ≤ emultiplicity (p : ℤ_[p]) (s ^ 2 - 1) := by
  have hsplit : emultiplicity (p : ℤ_[p]) (s ^ 2 - 1)
      = emultiplicity (p : ℤ_[p]) (s - 1) + emultiplicity (p : ℤ_[p]) (s + 1) := by
    rw [show s ^ 2 - 1 = (s - 1) * (s + 1) by ring, emultiplicity_mul prime_p]
  rw [hsplit]
  rcases emultiplicity_sub_or_add_eq_one_of_eq_two hp2 hs isUnit_one with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · rw [hA]
    exact three_le_one_add hB
  · rw [hB, add_comm]
    exact three_le_one_add hA

/-- A unit `c` of `ℤ_[2]` is a square iff `v₂(c - 1) ≥ 3`, i.e. iff `c ≡ 1 mod 8`. -/
theorem isSquare_iff_three_le_emultiplicity_sub_one_of_eq_two (hp2 : p = 2) {c : ℤ_[p]}
    (hc : IsUnit c) : IsSquare c ↔ 3 ≤ emultiplicity (p : ℤ_[p]) (c - 1) := by
  refine ⟨fun ⟨s, hs⟩ => ?_, fun hv => ?_⟩
  · have hsunit : IsUnit s := (IsUnit.mul_iff.mp (hs ▸ hc)).1
    have := three_le_emultiplicity_sq_sub_one_of_eq_two hp2 hsunit
    rwa [show s ^ 2 - 1 = c - 1 by rw [hs]; ring] at this
  · subst hp2
    have hdvd : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ c - 1 := pow_dvd_of_le_emultiplicity (by
      refine le_trans ?_ hv
      norm_num)
    have hnorm : ‖c - 1‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) :=
      (norm_le_pow_iff_mem_span_pow (c - 1) 3).2 (Ideal.mem_span_singleton.2 (by
        simpa using hdvd))
    set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C c with hF
    have haevalF : (Polynomial.aeval (1 : ℤ_[2])) F = 1 - c := by simp [hF]
    have hderiv : Polynomial.derivative F = 2 * Polynomial.X := by
      simp [hF]; ring
    have haevalD : (Polynomial.aeval (1 : ℤ_[2])) (Polynomial.derivative F) = 2 := by
      rw [hderiv]; simp
    have hnormD : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by push_cast; ring, norm_p]
      norm_num
    have hcond : ‖(Polynomial.aeval (1 : ℤ_[2])) F‖
        < ‖(Polynomial.aeval (1 : ℤ_[2])) (Polynomial.derivative F)‖ ^ 2 := by
      rw [haevalF, haevalD, hnormD, show (1 : ℤ_[2]) - c = -(c - 1) by ring, norm_neg]
      refine lt_of_le_of_lt hnorm ?_
      norm_num
    obtain ⟨z, hz, _⟩ := hensels_lemma hcond
    rw [show (Polynomial.aeval z) F = z ^ 2 - c by simp [hF]] at hz
    exact ⟨z, by rw [← sub_eq_zero.mp hz]; ring⟩

/-! ## The square level sets at `p = 2` -/

/-- If `c` is a unit and `x` lies in the square level set `sqLevelSet c n` with `n ≥ 1`, then `x`
is a unit. -/
theorem isUnit_of_mem_sqLevelSet {c : ℤ_[p]} (hc : IsUnit c) {n : ℕ} (hn : 1 ≤ n) {x : ℤ_[p]}
    (hx : x ∈ sqLevelSet c n) : IsUnit x := by
  refine isUnit_of_not_dvd fun hdx => not_dvd_of_isUnit hc ?_
  have hdiff : (p : ℤ_[p]) ∣ x ^ 2 - c :=
    one_le_emultiplicity_iff_dvd.1 (by rw [mem_sqLevelSet.1 hx]; exact_mod_cast hn)
  have h := dvd_sub (dvd_pow hdx two_ne_zero) hdiff
  rwa [show x ^ 2 - (x ^ 2 - c) = c by ring] at h

/-- For `c = s²` in `ℤ_[2]` with `s` a unit and `m ≥ 2`,

  `{x | v₂(x² - c) = m + 1} = {x | v₂(x - s) = m} ∪ {x | v₂(x + s) = m}`,

the union being disjoint. -/
theorem sqLevelSet_eq_union_of_eq_two (hp2 : p = 2) {c : ℤ_[p]} (hc : IsUnit c) {s : ℤ_[p]}
    (hs : c = s * s) {m : ℕ} (hm : 2 ≤ m) :
    sqLevelSet c (m + 1) = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - s) = (m : ℕ∞)}
      ∪ {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (m : ℕ∞)} := by
  have hsunit : IsUnit s := (IsUnit.mul_iff.mp (hs ▸ hc)).1
  have hcancel : ∀ a b : ℕ∞, (1 : ℕ∞) + a = 1 + b → a = b := fun _ _ h =>
    ENat.add_right_injective_of_ne_top (n := (1 : ℕ∞)) (by simp) h
  have hsplit : ∀ x : ℤ_[p], emultiplicity (p : ℤ_[p]) (x ^ 2 - c)
      = emultiplicity (p : ℤ_[p]) (x - s) + emultiplicity (p : ℤ_[p]) (x + s) := fun x => by
    rw [show x ^ 2 - c = (x - s) * (x + s) by rw [hs]; ring, emultiplicity_mul prime_p]
  have hlev : ((m + 1 : ℕ) : ℕ∞) = 1 + (m : ℕ∞) := by push_cast; ring
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, mem_sqLevelSet]
  constructor
  · intro hxmem
    have hxunit : IsUnit x := isUnit_of_mem_sqLevelSet hc (by omega) hxmem
    rw [hsplit x, hlev] at hxmem
    rcases emultiplicity_sub_or_add_eq_one_of_eq_two hp2 hxunit hsunit with ⟨hA, _⟩ | ⟨hB, _⟩
    · rw [hA] at hxmem
      exact Or.inr (hcancel _ _ hxmem)
    · rw [hB, add_comm] at hxmem
      exact Or.inl (hcancel _ _ hxmem)
  · have key : ∀ y : ℤ_[p], emultiplicity (p : ℤ_[p]) (y - s) = (m : ℕ∞) →
        emultiplicity (p : ℤ_[p]) (y ^ 2 - c) = ((m + 1 : ℕ) : ℕ∞) := by
      intro y hy
      have hyunit : IsUnit y := isUnit_of_dvd_sub hsunit
        (one_le_emultiplicity_iff_dvd.1 (by rw [hy]; exact_mod_cast Nat.one_le_of_lt hm))
      rcases emultiplicity_sub_or_add_eq_one_of_eq_two hp2 hyunit hsunit with ⟨hA, _⟩ | ⟨hB, _⟩
      · rw [hy] at hA
        exact absurd (by exact_mod_cast hA.symm : (1 : ℕ) = m) (by omega)
      · rw [hsplit y, hy, hB, hlev, add_comm]
    rintro (hy | hy)
    · exact key x hy
    · simpa using key (-x) (by rwa [show -x - s = -(x + s) by ring, emultiplicity_neg])

/-- For `c` a unit of `ℤ_[2]` that is not a square, `sqLevelSet c n = ∅` for every `n ≥ 3`. -/
theorem sqLevelSet_eq_empty_of_not_isSquare_of_eq_two (hp2 : p = 2) {c : ℤ_[p]} (hc : IsUnit c)
    (hns : ¬IsSquare c) {n : ℕ} (hn : 3 ≤ n) : sqLevelSet c n = (∅ : Set ℤ_[p]) := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => hns ?_
  have hxunit : IsUnit x := isUnit_of_mem_sqLevelSet hc (by omega) hx
  have h1 : (p : ℤ_[p]) ^ 3 ∣ x ^ 2 - c :=
    pow_dvd_of_le_emultiplicity (by rw [mem_sqLevelSet.1 hx]; exact_mod_cast hn)
  have h2 : (p : ℤ_[p]) ^ 3 ∣ x ^ 2 - 1 :=
    pow_dvd_of_le_emultiplicity (three_le_emultiplicity_sq_sub_one_of_eq_two hp2 hxunit)
  rw [isSquare_iff_three_le_emultiplicity_sub_one_of_eq_two hp2 hc,
    show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) from rfl, ← pow_dvd_iff_le_emultiplicity]
  have h := dvd_sub h2 h1
  rwa [show x ^ 2 - 1 - (x ^ 2 - c) = c - 1 by ring] at h

end PadicInt
