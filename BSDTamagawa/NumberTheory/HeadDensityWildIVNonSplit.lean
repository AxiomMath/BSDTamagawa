/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityWildOneFour
public import BSDTamagawa.NumberTheory.HeadDensityLargePrime

/-!
# The non-split `IV` cell at the wild primes, and the enlarged `t = 1` loci

At the wild primes `q ∈ {2, 3}` this file identifies the short models whose reduction datum is
`(IV, 1)`, i.e. those on which Step 5 of Tate's algorithm answers `IV` and its split test fails,
and adds them to the `t = 1` locus.

Step 5 answers `⟨V, IV, if (quadratic ϖ V 1).toPoly.Splits then 3 else 1⟩`, where
`quadratic ϖ V 1` is `Y² + cY - d` with `c = a₃(V)/ϖ mod ϖ` and `d = a₆(V)/ϖ² mod ϖ`. Write
`X = a₆ + r(a₄ + r²)` for the data of the Step-2 translate.

* **At `q = 2`** every element of the residue field `𝔽₂` is idempotent, so `Y² + cY - d` has a
  root unless `c = d = 1`. The non-split cell is the four classes
  `(a₄, a₆) ≡ (0, 5), (3, 1), (4, 5), (7, 5)` modulo `8`, of mass `4 · 2⁻⁶ = 1/16`.
* **At `q = 3`** the split test is completing the square. On a short model `b₆(V) = 4X`; writing
  `X = 9M`, the discriminant is `b₆(V)/9 = 4M`, and the non-split cell is `M ≡ 2 (mod 3)`, where
  `4M ≡ 2` is not a square in `𝔽₃`. That is nine classes modulo `27`, of mass `9 · 3⁻⁶ = 1/81`.

Both cells carry Tamagawa number `1`, so they enlarge the `t = 1` locus, which becomes `36` of the
`64` classes modulo `8` at `q = 2` and `657` of the `729` classes modulo `27` at `q = 3`.

## Main definitions

* `WeierstrassCurve.HeadResIVNSTwo`, `WeierstrassCurve.HeadResIVNSThree`: the residue conditions
  cutting out the non-split `IV` loci at `2` and at `3`.
* `WeierstrassCurve.one2Locus`, `WeierstrassCurve.one3LocusFull`: the enlarged `t = 1` loci, of
  mass `9/16` and `73/81`.

## Main results

* `WeierstrassCurve.run_eq_IVns_two`, `WeierstrassCurve.run_eq_IVns_three`: on the non-split `IV`
  loci the reduction datum is `(IV, 1)`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Lemma 3.1.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadSumThree TateAlgorithm

/-! ### A monic quadratic with no root does not split -/

/-- A monic quadratic with no root in the field does not split. -/
theorem not_splits_quadratic_of_forall_ne {K : Type*} [Field K] (c d : K)
    (h : ∀ y : K, y ^ 2 + c * y + d ≠ 0) :
    ¬ (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X
      + Polynomial.C d).Splits := by
  intro hs
  obtain ⟨y, hy⟩ := hs.exists_eval_eq_zero (by
    rw [Polynomial.degree_quadratic (one_ne_zero (α := K))]; decide)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X] at hy
  exact h y (by linear_combination hy)

/-- If `x` and `z` are both odd, `Y² + xY - z` has no root in the residue field of `ℤ_2`. -/
theorem no_root_quadratic_two {x z : ℤ_[2]} (hx : ¬ ((2 : ℕ) : ℤ_[2]) ∣ x)
    (hz : ¬ ((2 : ℕ) : ℤ_[2]) ∣ z) (y : ℤ_[2] ⧸ Ideal.span {((2 : ℕ) : ℤ_[2])}) :
    y ^ 2 + CommRing.mod ((2 : ℕ) : ℤ_[2]) x * y
      + -CommRing.mod ((2 : ℕ) : ℤ_[2]) z ≠ 0 := by
  intro h
  have hx' : PadicInt.toZMod x ≠ 0 := by rwa [Ne, ← PadicInt.dvd_iff_toZMod_eq_zero]
  have hz' : PadicInt.toZMod z ≠ 0 := by rwa [Ne, ← PadicInt.dvd_iff_toZMod_eq_zero]
  have hh := congrArg (residueEquiv 2) h
  rw [map_add, map_add, map_mul, map_pow, map_neg, residueEquiv_mod, residueEquiv_mod,
    map_zero] at hh
  have key : ∀ Y X Z : ZMod 2, X ≠ 0 → Z ≠ 0 → Y ^ 2 + X * Y + -Z ≠ 0 := by decide
  exact key _ _ _ hx' hz' hh

/-! ## The non-split `IV` cell at the prime `2`

`8 ∤ b₆(V) = 4X` forces `X` odd, hence `t` odd, hence `c = 1`; then `4 ∣ a₆(V)` with `8 ∤ a₆(V)`
is `d = 1`, and the split test fails. -/

/-- The residue condition cutting out the non-split `IV` locus at `2`: the four classes
`(a₄, a₆) ≡ (0, 5), (3, 1), (4, 5), (7, 5)` modulo `8`. -/
abbrev HeadResIVNSTwo (A E : ZMod (2 ^ 3)) : Prop :=
  (A = 0 ∧ E = 5) ∨ (A = 3 ∧ E = 1) ∨ (A = 4 ∧ E = 5) ∨ (A = 7 ∧ E = 5)

/-- On the non-split `IV` locus at `2` the coefficient `a₆` is odd. -/
theorem headResIVNSTwo_odd : ∀ A E : ZMod (2 ^ 3), HeadResIVNSTwo A E →
    (ZMod.cast E : ZMod (2 ^ 1)) ≠ 0 := by decide

/-- Let `A`, `E` modulo `8` satisfy `HeadResIVNSTwo`, and let `R`, `T` be such that
`a₄(V) = A + 3R²` and `a₆(V) = E + R(A + R²) - T²` are even. Then, modulo `8`, `4 ∣ a₆(V)`,
`b₈(V) = 0`, `b₆(V) ≠ 0`, `a₆(V) ≠ 0`, and `T` is odd. -/
theorem headResIVNSTwo_key : ∀ A E R T : ZMod (2 ^ 3), HeadResIVNSTwo A E →
    (ZMod.cast (A + 3 * R ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (E + R * (A + R ^ 2) - T ^ 2) : ZMod (2 ^ 1)) = 0 →
    (ZMod.cast (E + R * (A + R ^ 2) - T ^ 2) : ZMod (2 ^ 2)) = 0 ∧
      12 * R * (E + R * (A + R ^ 2) - T ^ 2) + 12 * R * T ^ 2
          - (A + 3 * R ^ 2) ^ 2 = 0 ∧
      4 * T ^ 2 + 4 * (E + R * (A + R ^ 2) - T ^ 2) ≠ 0 ∧
      E + R * (A + R ^ 2) - T ^ 2 ≠ 0 ∧ (ZMod.cast T : ZMod (2 ^ 1)) ≠ 0 := by decide

open TateAlgorithm in
/-- A short model over `ℤ_2` whose coefficient pair reduces into `HeadResIVNSTwo` modulo `8` has
reduction datum `(IV, 1)`. -/
theorem run_eq_IVns_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResIVNSTwo (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hϖ : ((2 : ℕ) : ℤ_[2]) ≠ 0 := PadicInt.uniformizer_ne_zero
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
  obtain ⟨k1, k2, k3, k4, k5⟩ := headResIVNSTwo_key _ _ (PadicInt.toZModPow 3 r)
    (PadicInt.toZModPow 3 t) hA hm4 hm6
  have h4a₆ : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ a₆ + r * (a₄ + r ^ 2) - t ^ 2 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero,
      ← PadicInt.cast_toZModPow 2 3 (by norm_num), map_sub, map_add, map_mul, map_add, map_pow,
      map_pow]
    exact k1
  have h4a₆V : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆ := by rw [e6]; exact h4a₆
  have hs3 : Step3.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left h4a₆V
  have hb₈ : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈
      = 12 * r * (a₆ + r * (a₄ + r ^ 2) - t ^ 2) + 12 * r * t ^ 2 - (a₄ + 3 * r ^ 2) ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, e6]; ring
  have h8b₈ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hb₈, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    exact k2
  have hs4 : Step4.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left h8b₈
  have hb₆ : (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₆
      = 4 * t ^ 2 + 4 * (a₆ + r * (a₄ + r ^ 2) - t ^ 2) := by
    rw [WeierstrassCurve.b₆, e3, e6]; ring
  have hnb₆ : ¬ ((2 : ℕ) : ℤ_[2]) ^ 3 ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).b₆ := by
    rw [hb₆, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    exact k3
  have ht2 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ t := by
    intro hc
    refine k5 ?_
    rw [PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact hc
  have ha₃dvd : ((2 : ℕ) : ℤ_[2]) ∣
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₃ := by
    have h := hval.a₃; rwa [pow_one] at h
  have hdiva₃ : CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₃
      ((2 : ℕ) : ℤ_[2]) = t := by
    refine mul_left_cancel₀ hϖ ?_
    calc ((2 : ℕ) : ℤ_[2]) *
          CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₃
            ((2 : ℕ) : ℤ_[2])
        = (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₃ :=
          CommRing.mul_div hϖ ha₃dvd
      _ = 2 * t := e3
      _ = ((2 : ℕ) : ℤ_[2]) * t := by rw [hcast]
  obtain ⟨w, hw⟩ := h4a₆
  have hw2 : ¬ ((2 : ℕ) : ℤ_[2]) ∣ w := by
    intro hcw
    obtain ⟨z, hz⟩ := hcw
    refine k4 ?_
    have hd3 : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ a₆ + r * (a₄ + r ^ 2) - t ^ 2 :=
      ⟨z, by rw [hw, hz]; ring⟩
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_add, map_mul, map_add, map_pow,
      map_pow] at hd3
    exact hd3
  have hdiva₆ : CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
      (((2 : ℕ) : ℤ_[2]) ^ 2) = w := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_
    calc ((2 : ℕ) : ℤ_[2]) ^ 2 *
          CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
            (((2 : ℕ) : ℤ_[2]) ^ 2)
        = (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆ :=
          CommRing.mul_div (pow_ne_zero 2 hϖ) h4a₆V
      _ = ((2 : ℕ) : ℤ_[2]) ^ 2 * w := by rw [e6, hw]
  have hnsplit : ¬ (quadratic ((2 : ℕ) : ℤ_[2])
      (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).toPoly.Splits := by
    have hb : (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).b = 1 := by
      norm_num [quadratic]
    have hcq : (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).c
        = CommRing.mod ((2 : ℕ) : ℤ_[2])
            (CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₃
              ((2 : ℕ) : ℤ_[2])) := by norm_num [quadratic]
    have hdq : (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).d
        = -CommRing.mod ((2 : ℕ) : ℤ_[2])
            (CommRing.div (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)).a₆
              (((2 : ℕ) : ℤ_[2]) ^ 2)) := by norm_num [quadratic]
    rw [Cubic.of_a_eq_zero (by norm_num [quadratic] :
      (quadratic ((2 : ℕ) : ℤ_[2])
        (Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)) 1).a = 0), hb, hcq, hdq,
      hdiva₃, hdiva₆]
    exact not_splits_quadratic_of_forall_ne _ _ (no_root_quadratic_two ht2 hw2)
  have hs5 : Step5.run ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((2 : ℕ) : ℤ_[2]) (ofShortNF a₄ a₆),
          KodairaSymbol.IV, 1⟩ := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    rw [ite_eq_right hnb₆, ite_eq_right hnsplit]
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step5 hΔ hs5)]
  exact ⟨rfl, rfl⟩

/-! ### The `t = 1` locus at `2`, modulo `8`

The type-`II` locus is eight classes modulo `4`, that is thirty-two classes modulo `8`; with the
four non-split `IV` classes the `t = 1` locus is thirty-six of the sixty-four, of mass `9/16`. -/

/-- The residue condition for `t = 1` at `2`, modulo `8`: the type-`II` classes of
`HeadResIITwo`, read modulo `8`, together with the four non-split `IV` classes. -/
abbrev HeadResOneTwo (A E : ZMod (2 ^ 3)) : Prop :=
  HeadResIITwo (ZMod.cast A) (ZMod.cast E) ∨ HeadResIVNSTwo A E

/-- A short model over `ℤ_2` whose coefficient pair satisfies `HeadResOneTwo` modulo `8` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_One_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResOneTwo (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  rcases hA with hII | hIV
  · refine ofShortNF_Δ_ne_zero_II_two ?_
    rwa [PadicInt.cast_toZModPow 2 3 (by norm_num),
      PadicInt.cast_toZModPow 2 3 (by norm_num)] at hII
  · refine ofShortNF_Δ_ne_zero_of_not_dvd_snd ?_
    intro hc
    refine headResIVNSTwo_odd _ _ hIV ?_
    rw [PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact hc

/-- A short model over `ℤ_2` whose coefficient pair satisfies `HeadResOneTwo` modulo `8` has
Tamagawa number `1`. -/
theorem run_tamagawaNumber_eq_one_two {a₄ a₆ : ℤ_[2]}
    (hA : HeadResOneTwo (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  rcases hA with hII | hIV
  · refine (run_eq_II_two ?_ hΔ).2
    rwa [PadicInt.cast_toZModPow 2 3 (by norm_num),
      PadicInt.cast_toZModPow 2 3 (by norm_num)] at hII
  · exact (run_eq_IVns_two hIV hΔ).2

/-- The thirty-six residue pairs of `HeadResOneTwo`, as a `Finset`. -/
def headResiduesOneTwo : Finset (ZMod (2 ^ 3) × ZMod (2 ^ 3)) :=
  Finset.univ.filter fun c => HeadResOneTwo c.1 c.2

set_option maxRecDepth 40000 in
/-- Exactly thirty-six residue pairs modulo `8` satisfy `HeadResOneTwo`. -/
theorem card_headResiduesOneTwo : headResiduesOneTwo.card = 36 := by decide

/-- A residue pair lies in `headResiduesOneTwo` if and only if it satisfies `HeadResOneTwo`. -/
theorem mem_headResiduesOneTwo_iff {c : ZMod (2 ^ 3) × ZMod (2 ^ 3)} :
    c ∈ headResiduesOneTwo ↔ HeadResOneTwo c.1 c.2 := by
  simp [headResiduesOneTwo]

/-- The `t = 1` locus of the coefficient plane at `2`: the pairs whose reduction modulo `8`
satisfies `HeadResOneTwo`, thirty-six of the sixty-four residue classes. -/
noncomputable def one2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 3 ⁻¹' (headResiduesOneTwo : Set (ZMod (2 ^ 3) × ZMod (2 ^ 3)))

/-- A coefficient pair lies in `one2Locus` if and only if its reduction modulo `8` satisfies
`HeadResOneTwo`. -/
theorem mem_one2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ one2Locus ↔ HeadResOneTwo (PadicInt.toZModPow 3 x.1) (PadicInt.toZModPow 3 x.2) := by
  rw [one2Locus, mem_preimage, Finset.mem_coe, mem_headResiduesOneTwo_iff, PadicInt.redPairPow]

/-- `36 · 2⁻⁶ = 36/64 = 9/16`. -/
theorem thirtySix_mul_inv_pow_six_eq :
    ((36 : ℕ) : ℝ≥0∞) * ((((2 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 3) = 9 / 16 := by
  rw [show ((36 : ℕ) : ℝ≥0∞) = 36 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 3) = 64 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The `t = 1` locus at `2` has mass `9/16`. -/
theorem volume_one2Locus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) one2Locus = 9 / 16 := by
  rw [one2Locus, PadicInt.volume_preimage_redPairPow, card_headResiduesOneTwo,
    thirtySix_mul_inv_pow_six_eq]

/-- The `t = 1` locus at `2` lies in the union of the strata with Tamagawa number `1`. -/
theorem one2Locus_subset_iUnion_stratFibre :
    one2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) := by
  intro x hx
  have hA := mem_one2Locus_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_One_two hA
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  have ht := run_tamagawaNumber_eq_one_two hA hΔ
  refine Set.mem_iUnion.2 ⟨(TateAlgorithm.run (W := ofShortNF x.1 x.2)
    PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol, (mem_stratFibre_iff hUp).2 ?_⟩
  rw [strat]
  exact Prod.ext rfl ht

/-! ## The non-split `IV` cell at the prime `3`

Nine residue classes modulo `27`, cut out by `X ≡ 18 (mod 27)` together with `27 ∣ b₈(V)`. Writing
`X = 9M`, the discriminant `b₆(V)/9 = 4M` of Step 5's quadratic is `8 ≡ 2`, not a square in `𝔽₃`.
-/

/-- `8` is not a square in the residue field `𝔽₃` of `ℤ_3`. -/
theorem not_isSquare_eight_three :
    ¬ IsSquare (8 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])}) := by
  rw [show (8 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])})
      = CommRing.mod ((3 : ℕ) : ℤ_[3]) 8 from by simp only [map_ofNat],
    isSquare_mod_iff_isSquare_toZMod, map_ofNat]
  rintro ⟨s, hs⟩
  have key : ∀ s : ZMod 3, (8 : ZMod 3) ≠ s * s := by decide
  exact key s hs

/-- The residue condition cutting out the non-split `IV` locus at `3`: the nine classes
`(a₄, a₆) ≡ (0, 18), (6, 11), (6, 25), (9, 18), (15, 2), (15, 7), (18, 18), (24, 16), (24, 20)`
modulo `27`. -/
abbrev HeadResIVNSThree (A E : ZMod (3 ^ 3)) : Prop :=
  (A = 0 ∧ E = 18) ∨ (A = 6 ∧ E = 11) ∨ (A = 6 ∧ E = 25) ∨ (A = 9 ∧ E = 18) ∨
    (A = 15 ∧ E = 2) ∨ (A = 15 ∧ E = 7) ∨ (A = 18 ∧ E = 18) ∨ (A = 24 ∧ E = 16) ∨
    (A = 24 ∧ E = 20)

/-- For a residue pair satisfying `HeadResIVNSThree` and any `R` with `3 ∣ X = a₆ + R(a₄ + R²)`:
`X ≡ 18 (mod 27)` and `27 ∣ 12RX - (a₄ + 3R²)²`. -/
theorem headResIVNSThree_key : ∀ A E R : ZMod (3 ^ 3), HeadResIVNSThree A E →
    (ZMod.cast (E + R * (A + R ^ 2)) : ZMod (3 ^ 1)) = 0 →
    E + R * (A + R ^ 2) = 18 ∧
      12 * R * (E + R * (A + R ^ 2)) - (A + 3 * R ^ 2) ^ 2 = 0 := by decide

/-- On the non-split `IV` locus at `3`, `a₆` is either a unit or `≡ 18 (mod 27)`. -/
theorem headResIVNSThree_snd : ∀ A E : ZMod (3 ^ 3), HeadResIVNSThree A E →
    (ZMod.cast E : ZMod (3 ^ 1)) ≠ 0 ∨ E = 18 := by decide

/-- On the non-split `IV` locus at `3` with `3 ∤ a₆`, no `u` with `a₄ = 3u` satisfies
`a₆² = -4u³` modulo `27`. -/
theorem headResIVNSThree_ne : ∀ A E U : ZMod (3 ^ 3), HeadResIVNSThree A E →
    (ZMod.cast E : ZMod (3 ^ 1)) ≠ 0 → A = 3 * U → E ^ 2 ≠ -4 * U ^ 3 := by decide

/-- On the non-split `IV` locus at `3`, `3 ∣ a₄` modulo `27`. -/
theorem headResIVNSThree_cast : ∀ A E : ZMod (3 ^ 3), HeadResIVNSThree A E →
    (ZMod.cast A : ZMod (3 ^ 1)) = 0 := by decide

/-- A short model over `ℤ_3` whose coefficient pair reduces into `HeadResIVNSThree` modulo `27` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_IVns_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResIVNSThree (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have h3 : (3 : ℤ_[3]) ≠ 0 := by rw [← hcast]; exact PadicInt.uniformizer_ne_zero
  have h27 : (27 : ℤ_[3]) ≠ 0 := by
    rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]; exact pow_ne_zero 3 h3
  intro hzero
  rw [ofShortNF_Δ] at hzero
  have hD : (4 : ℤ_[3]) * a₄ ^ 3 + 27 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left isUnit_neg_sixteen_three.ne_zero
  rcases headResIVNSThree_snd _ _ hA with hunit | hbig
  · have hd4 : ((3 : ℕ) : ℤ_[3]) ∣ a₄ := by
      have h := pow_dvd_of_cast_toZModPow_eq_zero (p := 3) (m := 1) (n := 3) (by norm_num)
        (y := a₄) (headResIVNSThree_cast _ _ hA)
      rwa [pow_one] at h
    obtain ⟨u, hu⟩ := hd4
    rw [hcast] at hu
    have hE : (27 : ℤ_[3]) * (4 * u ^ 3 + a₆ ^ 2) = 0 := by rw [hu] at hD; linear_combination hD
    have hE' : (4 : ℤ_[3]) * u ^ 3 + a₆ ^ 2 = 0 := (mul_eq_zero.mp hE).resolve_left h27
    refine headResIVNSThree_ne _ _ (PadicInt.toZModPow 3 u) hA hunit ?_ ?_
    · rw [hu, map_mul, map_ofNat]
    · have h := congrArg (PadicInt.toZModPow 3) hE'
      rw [map_add, map_mul, map_pow, map_pow, map_ofNat, map_zero] at h
      linear_combination h
  · obtain ⟨c, hc⟩ : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ a₆ := by
      refine pow_dvd_of_cast_toZModPow_eq_zero (m := 2) (n := 3) (by norm_num) ?_
      rw [hbig]; decide
    rw [hcast] at hc
    refine no_singular_of_emultiplicity_snd_eq_two (a₄ := a₄) (c := c) ?_ ?_
    · intro hdc
      obtain ⟨d, hd⟩ := hdc
      have h27a₆ : PadicInt.toZModPow 3 a₆ = 0 :=
        PadicInt.pow_dvd_iff_toZModPow_eq_zero.mp ⟨d, by rw [hc, hd, hcast]; ring⟩
      rw [hbig] at h27a₆
      exact absurd h27a₆ (by decide)
    · rw [hc] at hD; linear_combination hD

open TateAlgorithm in
/-- A short model over `ℤ_3` whose coefficient pair reduces into `HeadResIVNSThree` modulo `27` has
reduction datum `(IV, 1)`. -/
theorem run_eq_IVns_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResIVNSThree (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h9 : (9 : ℤ_[3]) ≠ 0 := by
    rw [show (9 : ℤ_[3]) = 3 ^ 2 by norm_num, ← hcast]
    exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  obtain ⟨u, hu⟩ : ((3 : ℕ) : ℤ_[3]) ∣ a₄ := by
    have h := pow_dvd_of_cast_toZModPow_eq_zero (p := 3) (m := 1) (n := 3) (by norm_num)
      (y := a₄) (headResIVNSThree_cast _ _ hA)
    rwa [pow_one] at h
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
  have hXcast : (ZMod.cast (PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
      (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2)) : ZMod (3 ^ 1)) = 0 := by
    rw [show PadicInt.toZModPow 3 a₆ + PadicInt.toZModPow 3 r *
          (PadicInt.toZModPow 3 a₄ + PadicInt.toZModPow 3 r ^ 2)
        = PadicInt.toZModPow 3 (a₆ + r * (a₄ + r ^ 2)) by rw [map_add, map_mul, map_add, map_pow],
      PadicInt.cast_toZModPow 1 3 (by norm_num),
      ← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact hX3
  obtain ⟨k1, k2⟩ := headResIVNSThree_key _ _ (PadicInt.toZModPow 3 r) hA hXcast
  obtain ⟨m, hm⟩ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ (a₆ + r * (a₄ + r ^ 2) - 18) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [k1, sub_self]
  rw [hcast] at hm
  have hXM : a₆ + r * (a₄ + r ^ 2) = 9 * (2 + 3 * m) := by linear_combination hm
  have hM3 : ¬ ((3 : ℕ) : ℤ_[3]) ∣ (2 + 3 * m) := by
    intro hcm
    obtain ⟨v, hv⟩ := hcm
    rw [hcast] at hv
    exact not_three_dvd_two ⟨v - m, by rw [hcast]; linear_combination hv⟩
  have ha₆V : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
      = 9 * (2 + 3 * m - τ ^ 2) := by rw [e6, hXM, hτ]; ring
  have h9a₆V : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆ :=
    ⟨2 + 3 * m - τ ^ 2, by rw [ha₆V, hcast]; ring⟩
  have hs3 : Step3.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_left h9a₆V
  have hb₈ : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₈
      = 12 * r * (a₆ + r * (a₄ + r ^ 2)) - (a₄ + 3 * r ^ 2) ^ 2 := by
    rw [WeierstrassCurve.b₈, e1, e2, e3, e4, e6]; ring
  have h27b₈ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₈ := by
    rw [hb₈, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    exact k2
  have hs4 : Step4.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left h27b₈
  have hb₆ : (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
      = 9 * (4 * (2 + 3 * m)) := by rw [WeierstrassCurve.b₆, e3, e6, hXM]; ring
  have hnb₆ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 3 ∣
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆ := by
    rw [hb₆]
    intro hcb
    obtain ⟨w, hw⟩ := hcb
    refine hM3 ((PadicInt.prime_p.dvd_or_dvd (a := (4 : ℤ_[3])) (b := 2 + 3 * m)
      ⟨w, ?_⟩).resolve_left not_three_dvd_four)
    rw [hcast] at hw ⊢
    refine mul_left_cancel₀ h9 ?_
    linear_combination hw
  have hv3 := Step3.run_hasValuation hs3
  have ea₃ : ((3 : ℕ) : ℤ_[3]) *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃ ((3 : ℕ) : ℤ_[3])
        = (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃ :=
    CommRing.mul_div hϖ (by simpa using hv3.a₃)
  have ea₆ : ((3 : ℕ) : ℤ_[3]) ^ 2 *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
        (((3 : ℕ) : ℤ_[3]) ^ 2)
        = (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ) hv3.a₆
  have eb₆ : ((3 : ℕ) : ℤ_[3]) ^ 2 *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
        (((3 : ℕ) : ℤ_[3]) ^ 2)
        = (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ) hv3.b₆
  have hdisc : CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
        ((3 : ℕ) : ℤ_[3]) ^ 2
      + 4 * CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
        (((3 : ℕ) : ℤ_[3]) ^ 2)
      = CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
        (((3 : ℕ) : ℤ_[3]) ^ 2) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_
    rw [eb₆, WeierstrassCurve.b₆]
    linear_combination (((3 : ℕ) : ℤ_[3]) *
      CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃ ((3 : ℕ) : ℤ_[3])
        + (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃) * ea₃ + 4 * ea₆
  have edivb₆ : CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).b₆
      (((3 : ℕ) : ℤ_[3]) ^ 2) = 4 * (2 + 3 * m) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ) ?_
    rw [eb₆, hb₆, hcast]; ring
  have hmod8M : CommRing.mod ((3 : ℕ) : ℤ_[3]) (4 * (2 + 3 * m))
      = (8 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])}) := by
    have hd : ((3 : ℕ) : ℤ_[3]) ∣ (4 * (2 + 3 * m) - 8) := ⟨4 * m, by rw [hcast]; ring⟩
    have h0 := (CommRing.mod_eq_zero ((3 : ℕ) : ℤ_[3]) (4 * (2 + 3 * m) - 8)).2 hd
    rw [map_sub, map_ofNat, sub_eq_zero] at h0
    exact h0
  have h2' : (2 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])}) ≠ 0 := by
    rw [show (2 : ℤ_[3] ⧸ Ideal.span {((3 : ℕ) : ℤ_[3])})
        = CommRing.mod ((3 : ℕ) : ℤ_[3]) 2 from by simp only [map_ofNat], Ne,
      CommRing.mod_eq_zero]
    exact not_three_dvd_two
  have hnsq : ¬ IsSquare (CommRing.mod ((3 : ℕ) : ℤ_[3])
      (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
        ((3 : ℕ) : ℤ_[3])) ^ 2
      + 4 * CommRing.mod ((3 : ℕ) : ℤ_[3])
        (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
          (((3 : ℕ) : ℤ_[3]) ^ 2))) := by
    rw [show CommRing.mod ((3 : ℕ) : ℤ_[3])
          (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
            ((3 : ℕ) : ℤ_[3])) ^ 2
          + 4 * CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
              (((3 : ℕ) : ℤ_[3]) ^ 2))
        = CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
              ((3 : ℕ) : ℤ_[3]) ^ 2
              + 4 * CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
                (((3 : ℕ) : ℤ_[3]) ^ 2)) from by
      simp only [map_add, map_mul, map_pow, map_ofNat], hdisc, edivb₆, hmod8M]
    exact not_isSquare_eight_three
  have hnsplit : ¬ (quadratic ((3 : ℕ) : ℤ_[3])
      (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).toPoly.Splits := by
    have hb : (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).b = 1 := by
      norm_num [quadratic]
    have hcq : (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).c
        = CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₃
              ((3 : ℕ) : ℤ_[3])) := by norm_num [quadratic]
    have hdq : (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).d
        = -CommRing.mod ((3 : ℕ) : ℤ_[3])
            (CommRing.div (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)).a₆
              (((3 : ℕ) : ℤ_[3]) ^ 2)) := by norm_num [quadratic]
    rw [Cubic.of_a_eq_zero (by norm_num [quadratic] :
      (quadratic ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)) 1).a = 0), hb, hcq, hdq]
    exact fun hsp => hnsq (isSquare_of_splits_quadratic h2' hsp)
  have hs5 : Step5.run ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF a₄ a₆),
          KodairaSymbol.IV, 1⟩ := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    rw [ite_eq_right hnb₆, ite_eq_right hnsplit]
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step5 hΔ hs5)]
  exact ⟨rfl, rfl⟩

/-! ### The `t = 1` locus at `3`, modulo `27`

Good reduction together with type `II` is seventy-two classes modulo `9`, that is six hundred
forty-eight modulo `27`; with the nine non-split `IV` classes the `t = 1` locus is six hundred
fifty-seven of the seven hundred twenty-nine, of mass `657/729 = 73/81`. -/

/-- The residue condition for `t = 1` at `3`, modulo `27`: good reduction or type `II`
(`HeadResOneThree`, read modulo `27`) together with the nine non-split `IV` classes. -/
abbrev HeadResOneThreeFull (A E : ZMod (3 ^ 3)) : Prop :=
  HeadResOneThree (ZMod.cast A) (ZMod.cast E) ∨ HeadResIVNSThree A E

/-- A short model over `ℤ_3` whose coefficient pair satisfies `HeadResOneThreeFull` modulo `27` is
nonsingular. -/
theorem ofShortNF_Δ_ne_zero_OneFull_three {a₄ a₆ : ℤ_[3]}
    (hA : HeadResOneThreeFull (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆)) :
    (ofShortNF a₄ a₆).Δ ≠ 0 := by
  rcases hA with hone | hIV
  · refine ofShortNF_Δ_ne_zero_One_three ?_
    rwa [PadicInt.cast_toZModPow 2 3 (by norm_num),
      PadicInt.cast_toZModPow 2 3 (by norm_num)] at hone
  · exact ofShortNF_Δ_ne_zero_IVns_three hIV

/-- A short model over `ℤ_3` whose coefficient pair satisfies `HeadResOneThreeFull` modulo `27` has
Tamagawa number `1`. -/
theorem run_tamagawaNumber_eq_one_three_full {a₄ a₆ : ℤ_[3]}
    (hA : HeadResOneThreeFull (PadicInt.toZModPow 3 a₄) (PadicInt.toZModPow 3 a₆))
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  rcases hA with hone | hIV
  · refine run_tamagawaNumber_eq_one_three ?_ hΔ
    rwa [PadicInt.cast_toZModPow 2 3 (by norm_num),
      PadicInt.cast_toZModPow 2 3 (by norm_num)] at hone
  · exact (run_eq_IVns_three hIV hΔ).2

/-- The six hundred fifty-seven residue pairs of `HeadResOneThreeFull`, as a `Finset`. -/
def headResiduesOneThreeFull : Finset (ZMod (3 ^ 3) × ZMod (3 ^ 3)) :=
  Finset.univ.filter fun c => HeadResOneThreeFull c.1 c.2

set_option maxRecDepth 100000 in
/-- Exactly six hundred fifty-seven residue pairs modulo `27` satisfy `HeadResOneThreeFull`. -/
theorem card_headResiduesOneThreeFull : headResiduesOneThreeFull.card = 657 := by decide

/-- A residue pair lies in `headResiduesOneThreeFull` if and only if it satisfies
`HeadResOneThreeFull`. -/
theorem mem_headResiduesOneThreeFull_iff {c : ZMod (3 ^ 3) × ZMod (3 ^ 3)} :
    c ∈ headResiduesOneThreeFull ↔ HeadResOneThreeFull c.1 c.2 := by
  simp [headResiduesOneThreeFull]

/-- The `t = 1` locus of the coefficient plane at `3`: the pairs whose reduction modulo `27`
satisfies `HeadResOneThreeFull`, six hundred fifty-seven of the seven hundred twenty-nine residue
classes. -/
noncomputable def one3LocusFull : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.redPairPow 3 3 ⁻¹' (headResiduesOneThreeFull : Set (ZMod (3 ^ 3) × ZMod (3 ^ 3)))

/-- A coefficient pair lies in `one3LocusFull` if and only if its reduction modulo `27` satisfies
`HeadResOneThreeFull`. -/
theorem mem_one3LocusFull_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ one3LocusFull ↔
      HeadResOneThreeFull (PadicInt.toZModPow 3 x.1) (PadicInt.toZModPow 3 x.2) := by
  rw [one3LocusFull, mem_preimage, Finset.mem_coe, mem_headResiduesOneThreeFull_iff,
    PadicInt.redPairPow]

/-- `657 · 3⁻⁶ = 657/729 = 73/81`. -/
theorem sixHundredFiftySeven_mul_inv_pow_six_eq :
    ((657 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 3) = 73 / 81 := by
  rw [show ((657 : ℕ) : ℝ≥0∞) = 657 by norm_num, show (((3 : ℕ)) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 3) = 729 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The `t = 1` locus at `3` has mass `73/81`. -/
theorem volume_one3LocusFull :
    (volume : Measure (ℤ_[3] × ℤ_[3])) one3LocusFull = 73 / 81 := by
  rw [one3LocusFull, PadicInt.volume_preimage_redPairPow, card_headResiduesOneThreeFull,
    sixHundredFiftySeven_mul_inv_pow_six_eq]

/-- The `t = 1` locus at `3` lies in the union of the strata with Tamagawa number `1`. -/
theorem one3LocusFull_subset_iUnion_stratFibre :
    one3LocusFull ⊆ ⋃ κ : KodairaSymbol, stratFibre 3 (κ, 1) := by
  intro x hx
  have hA := mem_one3LocusFull_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := ofShortNF_Δ_ne_zero_OneFull_three hA
  have hUp : x ∈ nonsingularLocus 3 := hΔ
  have ht := run_tamagawaNumber_eq_one_three_full hA hΔ
  refine Set.mem_iUnion.2 ⟨(TateAlgorithm.run (W := ofShortNF x.1 x.2)
    PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol, (mem_stratFibre_iff hUp).2 ?_⟩
  rw [strat]
  exact Prod.ext rfl ht

end WeierstrassCurve
