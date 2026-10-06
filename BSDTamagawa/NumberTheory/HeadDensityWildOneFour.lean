/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.SmallPrimeHeadBound

/-!
# Tate's algorithm on residue classes at the wild primes `q ∈ {2, 3}`

This file reads off the reduction data of short models `ofShortNF a₄ a₆` over `ℤ_q`, for
`q ∈ {2, 3}`, from the residues of `(a₄, a₆)` modulo `q²`. These are the loci behind the head
densities `δ_q(1)` and `δ_q(2)` at the wild primes; the values of Griffin–Ono–Tsai are
`δ_2(1) = 241/396 ≈ 0.6086` and `δ_3(1) = 1924841/2125728 ≈ 0.9055`.

At `q ∈ {2, 3}` the invariant `c₄ = -48a₄` of a short model is always divisible by `q`, so the
reduction is never multiplicative. Tate's algorithm reports the additive type `II`, with Tamagawa
number `1`, when Step 3's test `ϖ² ∣ a₆(V)` fails. Writing `V` for the Step-2 translate of
`ofShortNF a₄ a₆` and `r`, `t` for the lifts of the singular point,
`a₆(V) = a₆ + r(a₄ + r²) - t²`, and the condition `ϖ² ∤ a₆(V)` is decided by the residues of
`(a₄, a₆)` modulo `q²` for every pair of lifts with `ϖ ∣ a₄(V)` and `ϖ ∣ a₆(V)`.

* At `q = 2` eight of the sixteen classes modulo `4` are type `II`, and four further classes are
  type `III` with Tamagawa number `2`; the type-`III` locus has mass `1/4`.
* At `q = 3` the locus `{3 ∤ a₄}` has good reduction, and on `3 ∣ a₄` eighteen of the eighty-one
  classes modulo `9` are type `II`; on their union the Tamagawa number is `1`.

## Main definitions

* `WeierstrassCurve.iii2LocusFull`: the type-`III` locus at `2`.

## Main results

* `WeierstrassCurve.run_eq_II_two`, `WeierstrassCurve.run_eq_III_two_full`,
  `WeierstrassCurve.run_eq_II_three`: the reduction data on these loci.
* `WeierstrassCurve.run_tamagawaNumber_eq_one_three`: Tamagawa number `1` at `3` when `3 ∤ a₄` or
  the pair is of type `II`.
* `WeierstrassCurve.volume_iii2LocusFull`: the type-`III` locus at `2` has mass `1/4`.

## Implementation notes

The equality `δ_p(I_t^{sp}) = δ_p(I_t^{ns})` of split and non-split multiplicative densities is
false at `p = 2`: the map exchanging the two shells at odd `p` is multiplication by a quadratic
non-residue, and there is none modulo `2`. No argument here uses it; every mass is a point count
over `ℤ/q^k`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Lemma 3.1.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

/-! ### Reading `p ∣ y` off the residue modulo `p²` -/

/-- `p ∣ y` exactly when the image of `y mod p²` under `ℤ/p² → ℤ/p` vanishes. -/
theorem dvd_iff_cast_toZModPow_two_eq_zero {p : ℕ} [Fact p.Prime] {y : ℤ_[p]} :
    ((p : ℤ_[p]) ∣ y) ↔ (ZMod.cast (PadicInt.toZModPow 2 y) : ZMod (p ^ 1)) = 0 := by
  rw [← pow_one (p : ℤ_[p]), PadicInt.pow_dvd_iff_toZModPow_eq_zero,
    ← PadicInt.cast_toZModPow 1 2 (by norm_num) y]

/-! ### Cross-multiplication for `ℝ≥0∞` fractions -/

/-- `a/b = c/d` from `a·d = c·b`, for finite nonzero `b`, `d`. -/
theorem enn_div_eq_div {a b c d : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ⊤) (hd : d ≠ 0) (hd' : d ≠ ⊤)
    (h : a * d = c * b) : a / b = c / d :=
  (ENNReal.div_eq_div_iff hd hd' hb hb').2 (by rw [mul_comm, h, mul_comm])

/-! ## Type `II` at the prime `2`

The residue condition is exactly "Step 3 fails", read modulo `4`. -/

/-- The residue condition cutting out the type-`II` locus at `2`: the eight classes
`(a₄, a₆) ≡ (0, 2), (0, 3), (1, 0), (1, 1), (2, 2), (2, 3), (3, 2), (3, 3)` modulo `4`. -/
abbrev HeadResIITwo (A E : ZMod (2 ^ 2)) : Prop :=
  (A = 0 ∧ E = 2) ∨ (A = 0 ∧ E = 3) ∨ (A = 1 ∧ E = 0) ∨ (A = 1 ∧ E = 1) ∨
    (A = 2 ∧ E = 2) ∨ (A = 2 ∧ E = 3) ∨ (A = 3 ∧ E = 2) ∨ (A = 3 ∧ E = 3)

/-- Let `A`, `E` modulo `4` satisfy `HeadResIITwo`, and let `R`, `T` be such that `A + 3R²` and
`a₆(V) = E + R(A + R²) - T²` are even. Then `a₆(V)` is nonzero modulo `4`. -/
theorem headResIITwo_key : ∀ A E R T : ZMod (2 ^ 2), HeadResIITwo A E →
    (ZMod.cast (A + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (E + R * (A + R ^ 2) - T ^ 2) : ZMod (2 ^ 1)) = 0 →
    E + R * (A + R ^ 2) - T ^ 2 ≠ 0 := by decide

/-- On the type-`II` locus at `2`, `4a₄³ + 27a₆²` is nonzero modulo `16`. -/
theorem headResIITwo_disc : ∀ A E : ZMod (2 ^ 4),
    HeadResIITwo (ZMod.cast A) (ZMod.cast E) → 4 * A ^ 3 + 27 * E ^ 2 ≠ 0 := by decide

/-- A short model over `ℤ_2` whose coefficient pair reduces into `HeadResIITwo` modulo `4` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_II_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResIITwo (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[2]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left neg_sixteen_ne_zero_two
  refine headResIITwo_disc (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 a₆) ?_ ?_
  · rw [PadicInt.cast_toZModPow 2 4 (by norm_num), PadicInt.cast_toZModPow 2 4 (by norm_num)]
    exact hA
  · have h := congrArg (PadicInt.toZModPow 4) hD
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat, map_zero] at h
    exact h

open TateAlgorithm in
/-- A short model over `ℤ_2` whose coefficient pair reduces into `HeadResIITwo` modulo `4` has
reduction datum `(II, 1)`. -/
theorem run_eq_II_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResIITwo (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hcast]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  have hm4 : (ZMod.cast (PadicInt.toZModPow 2 a₄ +
      3 * PadicInt.toZModPow 2 r ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 2 a₄ + 3 * PadicInt.toZModPow 2 r ^ 2
        = PadicInt.toZModPow 2 (a₄ + 3 * r ^ 2) by rw [map_add, map_mul, map_pow, map_ofNat],
      PadicInt.cast_toZModPow 1 2 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h := hval.a₄; rw [e4, pow_one] at h; exact h
  have hm6 : (ZMod.cast (PadicInt.toZModPow 2 a₆ + PadicInt.toZModPow 2 r *
      (PadicInt.toZModPow 2 a₄ + PadicInt.toZModPow 2 r ^ 2)
        - PadicInt.toZModPow 2 t ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 2 a₆ + PadicInt.toZModPow 2 r *
          (PadicInt.toZModPow 2 a₄ + PadicInt.toZModPow 2 r ^ 2) - PadicInt.toZModPow 2 t ^ 2
        = PadicInt.toZModPow 2 (a₆ + r * (a₄ + r ^ 2) - t ^ 2) by
      rw [map_sub, map_add, map_mul, map_add, map_pow, map_pow],
      PadicInt.cast_toZModPow 1 2 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h := hval.a₆; rw [e6, pow_one] at h; exact h
  have k := headResIITwo_key _ _ (PadicInt.toZModPow 2 r) (PadicInt.toZModPow 2 t) hA hm4 hm6
  have hn4 : ¬ ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ (a₆ + r * (a₄ + r ^ 2) - t ^ 2) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_add, map_mul, map_add, map_pow,
      map_pow]
    exact k
  have hs3 : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆),
          KodairaSymbol.II, 1⟩ := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_right (by rw [e6]; exact hn4)
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step3 hΔ hs3)]
  exact ⟨rfl, rfl⟩

/-! ### The type-`II` residue pairs at `2` -/

/-- The eight residue pairs of `HeadResIITwo`, as a `Finset`. -/
def headResiduesIITwo : Finset (ZMod (2 ^ 2) × ZMod (2 ^ 2)) :=
  Finset.univ.filter fun c => HeadResIITwo c.1 c.2

/-! ## The full type-`III` locus at the prime `2`

Type `III` is "Step 3 succeeds, Step 4 fails": `4 ∣ a₆(V)` and `8 ∤ b₈(V)`. On a short model
`b₈(V) = 12r·a₆(V) + 12rt² - (a₄ + 3r²)²`, and the verdict depends only on `(a₄, a₆) mod 4`: the
type-`III` locus is four of the sixteen classes modulo `4`, of mass `1/4`, with Tamagawa number
`2`. -/

/-- The residue condition cutting out the type-`III` locus at `2`: the four classes
`(a₄, a₆) ≡ (1, 3), (2, 0), (2, 1), (3, 0)` modulo `4`. -/
abbrev HeadResIIITwo (A E : ZMod (2 ^ 2)) : Prop :=
  (A = 1 ∧ E = 3) ∨ (A = 2 ∧ E = 0) ∨ (A = 2 ∧ E = 1) ∨ (A = 3 ∧ E = 0)

/-- Let `A`, `E` modulo `8` reduce into `HeadResIIITwo` modulo `4`, and let `R`, `T` be such that
`A + 3R²` and `a₆(V) = E + R(A + R²) - T²` are even. Then, modulo `8`, `4 ∣ a₆(V)` and
`b₈(V) ≠ 0`. -/
theorem headResIIITwo_key : ∀ A E R T : ZMod (2 ^ 3),
    HeadResIIITwo (ZMod.cast A) (ZMod.cast E) →
    (ZMod.cast (A + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (E + R * (A + R ^ 2) - T ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (E + R * (A + R ^ 2) - T ^ 2) : ZMod (2 ^ 2)) = 0 ∧
      12 * R * (E + R * (A + R ^ 2) - T ^ 2) + 12 * R * T ^ 2
        - (A + 3 * R ^ 2) ^ 2 ≠ 0 := by decide

set_option maxRecDepth 40000 in
/-- On the type-`III` locus at `2`, `4a₄³ + 27a₆²` is nonzero modulo `64`. -/
theorem headResIIITwo_disc : ∀ A E : ZMod (2 ^ 6),
    HeadResIIITwo (ZMod.cast A) (ZMod.cast E) → 4 * A ^ 3 + 27 * E ^ 2 ≠ 0 := by decide

/-- A short model over `ℤ_2` whose coefficient pair reduces into `HeadResIIITwo` modulo `4` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_III_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResIIITwo (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[2]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left neg_sixteen_ne_zero_two
  refine headResIIITwo_disc (PadicInt.toZModPow 6 a₄) (PadicInt.toZModPow 6 a₆) ?_ ?_
  · rw [PadicInt.cast_toZModPow 2 6 (by norm_num), PadicInt.cast_toZModPow 2 6 (by norm_num)]
    exact hA
  · have h := congrArg (PadicInt.toZModPow 6) hD
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat, map_zero] at h
    exact h

open TateAlgorithm in
/-- A short model over `ℤ_2` whose coefficient pair reduces into `HeadResIIITwo` modulo `4` has
reduction datum `(III, 2)`. -/
theorem run_eq_III_two_full {a₄ a₆ : ℤ_[2]}
    (hA : HeadResIIITwo (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.III ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hΔdvd : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hcast]; ring⟩
  have hc₄ : ((2 : ℕ) : ℤ_[2]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-24 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  have hm4 : (ZMod.cast (PadicInt.toZModPow 3 a₄ +
      3 * PadicInt.toZModPow 3 r ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 3 a₄ + 3 * PadicInt.toZModPow 3 r ^ 2
        = PadicInt.toZModPow 3 (a₄ + 3 * r ^ 2) by rw [map_add, map_mul, map_pow, map_ofNat],
      PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h := hval.a₄; rw [e4, pow_one] at h; exact h
  have hm6 : (ZMod.cast (PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
      (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2)
        - PadicInt.toZModPow 3 t ^ 2) : ZMod (2 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
          (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2) - PadicInt.toZModPow 3 t ^ 2
        = PadicInt.toZModPow 3 (a₆ + r * (a₄ + r ^ 2) - t ^ 2) by
      rw [map_sub, map_add, map_mul, map_add, map_pow, map_pow],
      PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h := hval.a₆; rw [e6, pow_one] at h; exact h
  have hAc : HeadResIIITwo (ZMod.cast (PadicInt.toZModPow 3 a₄))
      (ZMod.cast (PadicInt.toZModPow 3 a₆)) := by
    rw [PadicInt.cast_toZModPow 2 3 (by norm_num), PadicInt.cast_toZModPow 2 3 (by norm_num)]
    exact hA
  obtain ⟨k1, k2⟩ := headResIIITwo_key _ _ (PadicInt.toZModPow 3 r)
    (PadicInt.toZModPow 3 t) hAc hm4 hm6
  have h4a₆ : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ (a₆ + r * (a₄ + r ^ 2) - t ^ 2) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero,
      ← PadicInt.cast_toZModPow 2 3 (by norm_num), map_sub, map_add, map_mul, map_add, map_pow,
      map_pow]
    exact k1
  have hs3 : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left (by rw [e6]; exact h4a₆)
  have hb₈ : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈
      = 12 * r * (a₆ + r * (a₄ + r ^ 2) - t ^ 2) + 12 * r * t ^ 2 - (a₄ + 3 * r ^ 2) ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, e6]; ring
  have hnb₈ : ¬ ((2 : ℕ) : ℤ_[2]) ^ 3 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hb₈, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    exact k2
  have hs4 : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆),
          KodairaSymbol.III, 2⟩ := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_right hnb₈
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step4 hΔ hs4)]
  exact ⟨rfl, rfl⟩

/-- The four residue pairs of `HeadResIIITwo`, as a `Finset`. -/
def headResiduesIIITwo : Finset (ZMod (2 ^ 2) × ZMod (2 ^ 2)) :=
  Finset.univ.filter fun c => HeadResIIITwo c.1 c.2

/-- There are exactly four residue pairs modulo `4` satisfying `HeadResIIITwo`. -/
theorem card_headResiduesIIITwo : headResiduesIIITwo.card = 4 := by decide

/-- A residue pair lies in `headResiduesIIITwo` if and only if it satisfies `HeadResIIITwo`. -/
theorem mem_headResiduesIIITwo_iff {c : ZMod (2 ^ 2) × ZMod (2 ^ 2)} :
    c ∈ headResiduesIIITwo ↔ HeadResIIITwo c.1 c.2 := by
  simp [headResiduesIIITwo]

/-- The type-`III` locus of the coefficient plane at `2`: the pairs whose reduction modulo `4`
satisfies `HeadResIIITwo`. -/
noncomputable def iii2LocusFull : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 2 ⁻¹' (headResiduesIIITwo : Set (ZMod (2 ^ 2) × ZMod (2 ^ 2)))

/-- A pair of `2`-adic integers lies in `iii2LocusFull` if and only if its reduction modulo `4`
satisfies `HeadResIIITwo`. -/
theorem mem_iii2LocusFull_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ iii2LocusFull ↔ HeadResIIITwo (PadicInt.toZModPow 2 x.1) (PadicInt.toZModPow 2 x.2) := by
  rw [iii2LocusFull, mem_preimage, Finset.mem_coe, mem_headResiduesIIITwo_iff,
    PadicInt.redPairPow]

/-- `4 · 2⁻⁴ = 4/16 = 1/4`. -/
theorem four_mul_inv_pow_four_eq :
    ((4 : ℕ) : ℝ≥0∞) * ((((2 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 2) = 1 / 4 := by
  rw [show ((4 : ℕ) : ℝ≥0∞) = 4 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 2) = 16 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The type-`III` locus at `2` has mass `1/4`. -/
theorem volume_iii2LocusFull :
    (volume : Measure (ℤ_[2] × ℤ_[2])) iii2LocusFull = 1 / 4 := by
  rw [iii2LocusFull, PadicInt.volume_preimage_redPairPow, card_headResiduesIIITwo,
    four_mul_inv_pow_four_eq]

/-- The type-`III` locus at `2` lies in the union of the strata with Tamagawa number `2`. -/
theorem iii2LocusFull_subset_iUnion_stratFibre :
    iii2LocusFull ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2) := by
  intro x hx
  have hA := mem_iii2LocusFull_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_III_two hA
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_III_two_full hA hΔ
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.III, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-! ## Good reduction and type `II` at the prime `3`

At `q = 3` the locus `{3 ∤ a₄}` has `3 ∤ Δ`, hence good reduction and the datum `(I₀, 1)`; on
`3 ∣ a₄` the type-`II` condition is `9 ∤ a₆ + r(a₄ + r²)`, the lift `t` dropping out because
`3 ∣ a₃(V) = 2t` and `2` is a unit, so `9 ∣ t²`. Both are conditions on `(a₄, a₆) mod 9`. -/

/-- `3 ∤ 16` in `ℤ_3`. -/
theorem not_three_dvd_sixteen : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (16 : ℤ_[3]) := by
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_ofNat]
  decide

/-- `-16` is a unit in `ℤ_3`. -/
theorem isUnit_neg_sixteen_three : IsUnit (-16 : ℤ_[3]) :=
  (not_not.mp fun hc => not_three_dvd_sixteen (PadicInt.dvd_iff_not_isUnit.mpr hc)).neg

/-- The residue condition cutting out the type-`II` locus at `3`: eighteen classes modulo `9`,
all with `3 ∣ a₄` and none with `9 ∣ a₆`. -/
abbrev HeadResIIThree (A E : ZMod (3 ^ 2)) : Prop :=
  (A = 0 ∧ (E = 2 ∨ E = 3 ∨ E = 4 ∨ E = 5 ∨ E = 6 ∨ E = 7)) ∨
    (A = 3 ∧ (E = 1 ∨ E = 2 ∨ E = 3 ∨ E = 6 ∨ E = 7 ∨ E = 8)) ∨
      (A = 6 ∧ (E = 1 ∨ E = 3 ∨ E = 4 ∨ E = 5 ∨ E = 6 ∨ E = 8))

/-- The residue condition for `t = 1` at `3`: either `a₄` is a unit, or the pair is one of the
eighteen type-`II` classes modulo `9`. -/
abbrev HeadResOneThree (A E : ZMod (3 ^ 2)) : Prop :=
  (ZMod.cast A : ZMod (3 ^ 1)) ≠ 0 ∨ HeadResIIThree A E

/-- On the type-`II` locus at `3`, `3 ∣ a₄`, read modulo `9`. -/
theorem headResIIThree_cast : ∀ A E : ZMod (3 ^ 2), HeadResIIThree A E →
    (ZMod.cast A : ZMod (3 ^ 1)) = 0 := by decide

/-- On the type-`II` locus at `3`, `9 ∤ a₆`. -/
theorem headResIIThree_snd_ne : ∀ A E : ZMod (3 ^ 2), HeadResIIThree A E → E ≠ 0 := by decide

/-- Let `A`, `E` modulo `9` satisfy `HeadResIIThree`, and let `R` be such that
`X = E + R(A + R²)` is divisible by `3`. Then `X` is nonzero modulo `9`. -/
theorem headResIIThree_key : ∀ A E R : ZMod (3 ^ 2), HeadResIIThree A E →
    (ZMod.cast (E + R * (A + R ^ 2)) : ZMod (3 ^ 1)) = 0 → E + R * (A + R ^ 2) ≠ 0 := by decide

/-- On the type-`II` locus at `3` with `3 ∤ a₆`, no `u` with `a₄ = 3u` satisfies
`4u³ + a₆² = 0` modulo `9`. -/
theorem headResIIThree_disc : ∀ A E U : ZMod (3 ^ 2), HeadResIIThree A E → A = 3 * U →
    (ZMod.cast E : ZMod (3 ^ 1)) ≠ 0 → 4 * U ^ 3 + E ^ 2 ≠ 0 := by decide

/-- `4u³ + 9w² ≠ 0` in `ℤ_3` for `w` a unit. -/
theorem four_mul_cube_add_nine_mul_sq_ne_zero {u w : ℤ_[3]} (hw : ¬ ((3 : ℕ) : ℤ_[3]) ∣ w) :
    (4 : ℤ_[3]) * u ^ 3 + 9 * w ^ 2 ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h9 : (9 : ℤ_[3]) ≠ 0 := by
    rw [show (9 : ℤ_[3]) = 3 ^ 2 by norm_num]; exact pow_ne_zero 2 h3
  intro h
  by_cases hu : ((3 : ℕ) : ℤ_[3]) ∣ u
  · obtain ⟨z, hz⟩ := hu
    rw [hcast] at hz
    have e : (9 : ℤ_[3]) * (12 * z ^ 3 + w ^ 2) = 0 := by rw [hz] at h; linear_combination h
    have e' : (12 : ℤ_[3]) * z ^ 3 + w ^ 2 = 0 := (mul_eq_zero.mp e).resolve_left h9
    exact hw (PadicInt.prime_p.dvd_of_dvd_pow (n := 2) ⟨-(4 * z ^ 3), by
      rw [hcast]; linear_combination e'⟩)
  · refine hu (PadicInt.prime_p.dvd_of_dvd_pow (n := 3) ?_)
    refine (PadicInt.prime_p.dvd_or_dvd (a := (4 : ℤ_[3])) (b := u ^ 3) ?_).resolve_left
      not_three_dvd_four
    exact ⟨-(3 * w ^ 2), by rw [hcast]; linear_combination h⟩

/-- A short model over `ℤ_3` whose coefficient pair reduces into `HeadResIIThree` modulo `9` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_II_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResIIThree (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h27 : (27 : ℤ_[3]) ≠ 0 := by
    rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]; exact pow_ne_zero 3 h3
  obtain ⟨u, hu⟩ : ((3 : ℕ) : ℤ_[3]) ∣ a₄ :=
    dvd_of_cast_toZModPow_eq_zero (headResIIThree_cast _ _ hA)
  rw [hcast] at hu
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[3]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left isUnit_neg_sixteen_three.ne_zero
  have hE : (27 : ℤ_[3]) * (4 * u ^ 3 + a₆ ^ 2) = 0 := by rw [hu] at hD; linear_combination hD
  have hE' : (4 : ℤ_[3]) * u ^ 3 + a₆ ^ 2 = 0 := (mul_eq_zero.mp hE).resolve_left h27
  by_cases h6 : ((3 : ℕ) : ℤ_[3]) ∣ a₆
  · obtain ⟨w, hw⟩ := h6
    rw [hcast] at hw
    have hwu : ¬ ((3 : ℕ) : ℤ_[3]) ∣ w := by
      intro hc
      obtain ⟨d, hd⟩ := hc
      refine headResIIThree_snd_ne _ _ hA ?_
      exact PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp ⟨d, by rw [hw, hd, hcast]; ring⟩
    refine four_mul_cube_add_nine_mul_sq_ne_zero (u := u) hwu ?_
    rw [hw] at hE'
    linear_combination hE'
  · refine headResIIThree_disc _ _ (PadicInt.toZModPow 2 u) hA ?_ ?_ ?_
    · rw [hu, map_mul, map_ofNat]
    · rw [Ne, ← dvd_iff_cast_toZModPow_two_eq_zero]; exact h6
    · have h := congrArg (PadicInt.toZModPow 2) hE'
      rw [map_add, map_mul, map_pow, map_pow, map_ofNat, map_zero] at h
      linear_combination h

/-- If `3 ∤ a₄` in `ℤ_3`, then `3 ∤ Δ`. -/
theorem not_three_dvd_Δ_of_not_dvd_fst {a₄ a₆ : ℤ_[3]} (h4 : ¬ ((3 : ℕ) : ℤ_[3]) ∣ a₄) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).Δ := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  intro h
  rw [ofShortNF_Δ, isUnit_neg_sixteen_three.dvd_mul_left] at h
  have h27 : ((3 : ℕ) : ℤ_[3]) ∣ 27 * a₆ ^ 2 := ⟨9 * a₆ ^ 2, by rw [hcast]; ring⟩
  have h4a : ((3 : ℕ) : ℤ_[3]) ∣ 4 * a₄ ^ 3 := by
    have hs := dvd_sub h h27
    rwa [show 4 * a₄ ^ 3 + 27 * a₆ ^ 2 - 27 * a₆ ^ 2 = 4 * a₄ ^ 3 from by ring] at hs
  exact h4 (PadicInt.prime_p.dvd_of_dvd_pow (n := 3)
    ((PadicInt.prime_p.dvd_or_dvd h4a).resolve_left not_three_dvd_four))

open TateAlgorithm in
/-- A short model over `ℤ_3` whose coefficient pair reduces into `HeadResIIThree` modulo `9` has
reduction datum `(II, 1)`. -/
theorem run_eq_II_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResIIThree (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨u, hu⟩ : ((3 : ℕ) : ℤ_[3]) ∣ a₄ :=
    dvd_of_cast_toZModPow_eq_zero (headResIIThree_cast _ _ hA)
  rw [hcast] at hu
  have hΔdvd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-144 * (4 * u ^ 3 + a₆ ^ 2), by rw [ofShortNF_Δ, hu, hcast]; ring⟩
  have hc₄ : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).c₄ :=
    ⟨-16 * a₄, by rw [ofShortNF_c₄, hcast]; ring⟩
  have hs2 : Step2.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔdvd hc₄
  obtain ⟨r, t, e1, e2, e3, e4, e6⟩ := Step2.exists_translate_ofShortNF hΔdvd
  have hval := Step2.hasValuation_translate hΔdvd
  obtain ⟨τ, hτ⟩ : ((3 : ℕ) : ℤ_[3]) ∣ t := by
    have h := hval.a₃
    rw [e3, pow_one] at h
    exact (PadicInt.prime_p.dvd_or_dvd h).resolve_left not_three_dvd_two
  rw [hcast] at hτ
  have hX3 : ((3 : ℕ) : ℤ_[3]) ∣ a₆ + r * (a₄ + r ^ 2) := by
    have h := hval.a₆
    rw [e6, pow_one, hcast] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w + 3 * τ ^ 2, by rw [hcast]; linear_combination hw + (t + 3 * τ) * hτ⟩
  have hXcast : (ZMod.cast (PadicInt.toZModPow 2 a₆ + PadicInt.toZModPow 2 r *
      (PadicInt.toZModPow 2 a₄ + PadicInt.toZModPow 2 r ^ 2)) : ZMod (3 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 2 a₆ + PadicInt.toZModPow 2 r *
          (PadicInt.toZModPow 2 a₄ + PadicInt.toZModPow 2 r ^ 2)
        = PadicInt.toZModPow 2 (a₆ + r * (a₄ + r ^ 2)) by rw [map_add, map_mul, map_add, map_pow],
      PadicInt.cast_toZModPow 1 2 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact hX3
  have k := headResIIThree_key _ _ (PadicInt.toZModPow 2 r) hA hXcast
  have hn9X : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ (a₆ + r * (a₄ + r ^ 2)) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_add, map_pow]
    exact k
  have hn9 : ¬ ((3 : ℕ) : ℤ_[3]) ^ 2 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆ := by
    rw [e6, hτ]
    intro hc
    obtain ⟨w, hw⟩ := hc
    exact hn9X ⟨w + τ ^ 2, by rw [hcast] at hw ⊢; linear_combination hw⟩
  have hs3 : Step3.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆),
          KodairaSymbol.II, 1⟩ := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_right hn9
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step3 hΔ hs3)]
  exact ⟨rfl, rfl⟩

/-! ### Tamagawa number `1` at `3` -/

/-- A short model over `ℤ_3` whose coefficient pair satisfies `HeadResOneThree` modulo `9` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_One_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResOneThree (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  rcases hA with hunit | hII
  · intro hz
    refine not_three_dvd_Δ_of_not_dvd_fst (a₄ := a₄) (a₆ := a₆) ?_ ?_
    · rw [dvd_iff_cast_toZModPow_two_eq_zero]; exact hunit
    · rw [hz]; exact dvd_zero _
  · exact ofShortNF_Δ_ne_zero_II_three hII

/-- A short model over `ℤ_3` whose coefficient pair satisfies `HeadResOneThree` modulo `9` has
Tamagawa number `1`. -/
theorem run_tamagawaNumber_eq_one_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResOneThree (PadicInt.toZModPow 2 a₄) (PadicInt.toZModPow 2 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  rcases hA with hunit | hII
  · have h4 : ¬ ((3 : ℕ) : ℤ_[3]) ∣ a₄ := by
      rw [dvd_iff_cast_toZModPow_two_eq_zero]; exact hunit
    rw [run_eq_of_not_dvd_Δ hΔ (not_three_dvd_Δ_of_not_dvd_fst h4)]
  · exact (run_eq_II_three hII hΔ).2

/-! ## Two mass identities

`4 · 2⁻⁶ = 1/16` is the mass of the split-`IV` locus at `2`, and `6 · 3⁻⁴ = 2/27` is the mass of
the `III` locus at `3`. -/

/-- `4 · 2⁻⁶ = 4/64 = 1/16`. -/
theorem four_mul_inv_pow_six_eq : (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 6 = 1 / 16 := by
  rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 6 = 64 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `6 · 3⁻⁴ = 6/81 = 2/27`. -/
theorem six_mul_inv_pow_four_eq : (6 : ℝ≥0∞) * ((3 : ℝ≥0∞)⁻¹) ^ 4 = 2 / 27 := by
  rw [← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ 4 = 81 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

variable {p : ℕ} [Fact p.Prime]

end WeierstrassCurve
