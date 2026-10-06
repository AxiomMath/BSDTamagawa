/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.SmallPrimeSigns
public import BSDTamagawa.NumberTheory.RatioLawAtThree
public import BSDTamagawa.NumberTheory.TailConstantTwo

/-!
# Uniform bounds on `α_p`

For every prime `p`, the tail constant `α_p = p⁵ δ_p(5)` satisfies `α_p < 1/2` and `α_p ≥ 1/88572`.
At `p = 3` the lower bound is an equality, `α_3 = 1/88572`, so the constant cannot be improved. The
upper bound holds at every prime and the lower bound at every odd prime; at `p = 2` the lower bound
follows either from the Haar bound `δ_2(5) ≥ 1/2834304` or from the descent of Tate's algorithm on
the split locus, `HasSplitStoreyDescent 2`, which gives `δ_2(t) ≥ 2^{-(t+11)}` for `t ≥ 5`.

## Main definitions

* `WeierstrassCurve.HasSplitStoreyDescent`: on a short model over `ℤ_p` with `a₄` a unit,
  `a₆ = pb` with `b ∈ splitSetTwo p` and `p¹⁴ ∣ Δ`, Tate's algorithm reaches Step 11 and succeeds.

## Main results

* `WeierstrassCurve.α_lt_half`: `α_p < 1/2` for every prime `p`.
* `WeierstrassCurve.inv_88572_le_α_of_ne_two`: `α_p ≥ 1/88572` for every odd prime `p`.
* `WeierstrassCurve.α_eq_inv_88572_of_eq_three`: `α_3 = 1/88572`.
* `WeierstrassCurve.inv_pow_le_δ_two`: `δ_2(t) ≥ 2^{-(t+11)}` for `t ≥ 5`, given
  `HasSplitStoreyDescent 2`.
* `WeierstrassCurve.α_bounds_of_splitStoreyDescent`: both bounds at every prime, given
  `HasSplitStoreyDescent 2`.

## Implementation notes

The split congruence in `HasSplitStoreyDescent` cannot be dropped. Write `a₆ = 2b` on the locus
where `a₄` is a unit and `2¹⁴ ∣ Δ`; then `b` is a unit and `a₄ ≡ 5 mod 8`. Checking the
non-minimality criterion over the residue classes of `(a₄, b)` modulo `2¹¹` gives:

| `a₄ mod 16` | classes of `b mod 8` on the locus | Step 11 fires |
| --- | --- | --- |
| `5` | `3`, `5` | `b ≡ 3` only |
| `13` | `1`, `7` | `b ≡ 7` only |

So the descent holds on exactly half of the locus. The split condition `27b ≡ 1 mod 8`, i.e.
`b ≡ 3 mod 8`, together with `2¹⁴ ∣ Δ` forces `a₄ ≡ 5 mod 16`, and there Step 11 fires.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### Numeral identities in `ℝ≥0∞` -/

/-- `a ^ m · (a ^ (m + n))⁻¹ = (a ^ n)⁻¹` for `a` neither `0` nor `∞`. -/
theorem _root_.ENNReal.pow_mul_inv_pow_add {a : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (m n : ℕ) :
    a ^ m * (a ^ (m + n))⁻¹ = (a ^ n)⁻¹ := by
  rw [pow_add, ENNReal.mul_inv (Or.inl (pow_ne_zero m ha0)) (Or.inl (by simp [hat])),
    ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero m ha0) (by simp [hat]), one_mul]

/-- `2⁵ · (2 · (2⁻¹)⁹) = 1/8`. -/
theorem pow_five_mul_two_mul_inv_pow_nine : (2 : ℝ≥0∞) ^ 5 * (2 * ((2 : ℝ≥0∞)⁻¹) ^ 9) = 1 / 8 := by
  rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞) ^ 5 * (2 * ((2 : ℝ≥0∞) ^ 9)⁻¹)
      = 2 ^ 6 * ((2 : ℝ≥0∞) ^ (6 + 3))⁻¹ by norm_num; ring,
    ENNReal.pow_mul_inv_pow_add (by norm_num) (by norm_num) 6 3, one_div]
  norm_num

/-- `2⁵ · (1/2834304) = 1/88572`, since `2834304 = 2⁵ · 88572`. -/
theorem pow_five_mul_inv_2834304 : (2 : ℝ≥0∞) ^ 5 * (1 / 2834304) = 1 / 88572 := by
  rw [one_div, one_div, show (2834304 : ℝ≥0∞) = 2 ^ 5 * 88572 by norm_num,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-! ### The even prime: the upper bound, unconditionally -/

/-- **`α_2 ≤ 1/8`.** The small-prime decay `δ_2(t) ≤ 2 · 2^{-(t+4)}` at `t = 5` gives
`δ_2(5) ≤ 2⁻⁸`, and `α_2 = 2⁵ δ_2(5)`. -/
theorem α_le_inv_eight_of_eq_two (hp2 : p = 2) : α p ≤ 1 / 8 := by
  calc α p = (p : ℝ≥0∞) ^ 5 * δ p 5 := rfl
    _ ≤ (p : ℝ≥0∞) ^ 5 * (2 * ((p : ℝ≥0∞)⁻¹) ^ (5 + 4)) :=
        mul_le_mul le_rfl (δ_le_two_mul_inv_pow_add_four_at_two hp2 le_rfl) zero_le zero_le
    _ = 1 / 8 := by
        subst hp2
        rw [show ((2 : ℕ) : ℝ≥0∞) = 2 by norm_num, show 5 + 4 = 9 from rfl]
        exact pow_five_mul_two_mul_inv_pow_nine

/-- `α_2 < 1/2`. -/
theorem α_lt_half_of_eq_two (hp2 : p = 2) : α p < 1 / 2 :=
  (α_le_inv_eight_of_eq_two hp2).trans_lt (by rw [one_div, one_div, ENNReal.inv_lt_inv]; norm_num)

/-! ### The prime `3`: both bounds, the lower one with equality -/

/-- **`α_3 = 1/88572`**, the value `1/(3 · 29524)`. This is the case of equality in the lower bound
`α_p ≥ 1/88572`. -/
theorem α_eq_inv_88572_of_eq_three (hp3 : p = 3) : α p = 1 / 88572 := by
  rw [α_eq_ofReal_three_of_eq_three hp3, show (1 : ℝ) / (3 * 29524) = 1 / 88572 by norm_num,
    ofReal_one_div_88572]

/-- `α_3 ≥ 1/88572`, with equality. -/
theorem inv_88572_le_α_of_eq_three (hp3 : p = 3) : 1 / 88572 ≤ α p :=
  (α_eq_inv_88572_of_eq_three hp3).ge

/-- `α_3 = 1/88572 < 1/2`. -/
theorem α_lt_half_of_eq_three (hp3 : p = 3) : α p < 1 / 2 := by
  rw [α_eq_inv_88572_of_eq_three hp3, one_div, one_div, ENNReal.inv_lt_inv]
  norm_num

/-! ### The primes `p ≥ 5`: both bounds -/

/-- `α_p < 1/2` at every prime `p ≥ 5`. -/
theorem α_lt_half_of_five_le (hp : 5 ≤ p) : α p < 1 / 2 :=
  α_lt_half_of_stratScaleInvariant hp (stratScaleInvariant_of_five_le hp)

/-- `α_p ≥ 1/88572` at every prime `p ≥ 5`. -/
theorem inv_88572_le_α_of_five_le (hp : 5 ≤ p) : 1 / 88572 ≤ α p :=
  inv_88572_le_α_of_stratScaleInvariant hp (stratScaleInvariant_of_five_le hp)

/-! ### The upper bound at every prime -/

/-- **`α_p < 1/2` for every prime `p`.** -/
theorem α_lt_half : α p < 1 / 2 := by
  rcases eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with h | h | h
  · exact α_lt_half_of_eq_two h
  · exact α_lt_half_of_eq_three h
  · exact α_lt_half_of_five_le h

/-! ### The lower bound -/

/-- **`α_p ≥ 1/88572` for every odd prime `p`**, with equality at `p = 3`. -/
theorem inv_88572_le_α_of_ne_two (hp2 : p ≠ 2) : 1 / 88572 ≤ α p := by
  rcases eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with h | h | h
  · exact absurd h hp2
  · exact inv_88572_le_α_of_eq_three h
  · exact inv_88572_le_α_of_five_le h

/-- **The lower bound at `p = 2` from a lower bound on `δ_2(5)`.** Since `α_2 = 2⁵ δ_2(5)` and
`2834304 = 2⁵ · 88572`, `δ_2(5) ≥ 1/2834304` implies `α_2 ≥ 1/88572`. -/
theorem inv_88572_le_α_of_eq_two (hp2 : p = 2) (hδ : 1 / 2834304 ≤ δ p 5) : 1 / 88572 ≤ α p := by
  calc (1 : ℝ≥0∞) / 88572 = (p : ℝ≥0∞) ^ 5 * (1 / 2834304) := by
        subst hp2
        rw [show ((2 : ℕ) : ℝ≥0∞) = 2 by norm_num]
        exact pow_five_mul_inv_2834304.symm
    _ ≤ (p : ℝ≥0∞) ^ 5 * δ p 5 := mul_le_mul le_rfl hδ zero_le zero_le
    _ = α p := rfl

/-! ### The lower bound at `p = 2`, from the descent on the split locus -/

variable (p) in
/-- **The `p = 2` minimal-storey descent, restricted to the split locus.** On a short model over
`ℤ_2` with `a₄` a unit, `a₆ = 2b` with `27b ≡ 1 mod 8`, and `2¹⁴ ∣ Δ`, Steps 1–10 of Tate's
algorithm all pass, so Step 11 fires.

The congruence `27b ≡ 1 mod 8` says that `-c₆ = 27b` of the descended curve is a square, so this is
the locus producing split multiplicative reduction `I_t`. Without it the statement is false: for
`a₄ ≡ 5 mod 16` the locus also contains `b ≡ 5 mod 8`, where the model is `2`-minimal. -/
def HasSplitStoreyDescent : Prop :=
  ∀ (a₄ b : ℤ_[p]) (hΔ0 : (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ ≠ 0), IsUnit a₄ →
    b ∈ splitSetTwo p → (p : ℤ_[p]) ^ 14 ∣ (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ →
      ∃ V, TateAlgorithm.Step11.run PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V

/-- **The split locus lies inside the stratum**, granted the descent: for `p = 2`, `t ≥ 5` and `a₄`
a unit, every `a₆` in `splitLevelSet p t a₄` gives a point of the stratum of `(I_t, t)`. -/
theorem splitLevelSet_subset_preimage_stratFibre_two (hp2 : p = 2)
    (hdesc : HasSplitStoreyDescent p) {t : ℕ} (ht : 5 ≤ t) {a₄ : ℤ_[p]} (ha₄ : IsUnit a₄) :
    splitLevelSet p t a₄ ⊆ Prod.mk a₄ ⁻¹' stratFibre p (KodairaSymbol.I t, t) := by
  rintro a₆ ⟨⟨b, rfl, hsplit⟩, hd⟩
  have hΔ0 : (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero_right] at hd
    exact (ENat.natCast_ne_top (t + 12)) hd.symm
  have h14 : (p : ℤ_[p]) ^ 14 ∣ (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ :=
    pow_dvd_of_le_emultiplicity (by rw [hd]; exact_mod_cast (by omega : 14 ≤ t + 12))
  have hbu : IsUnit b := by
    refine not_not.1 fun hnu => ?_
    obtain ⟨k, hk⟩ := PadicInt.dvd_iff_not_isUnit.2 hnu
    have hd1 : (p : ℤ_[p]) ∣ 27 * b - 1 :=
      (dvd_pow_self _ three_ne_zero).trans (hsplit : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 1)
    exact PadicInt.prime_p.not_isUnit <| isUnit_of_dvd_one <| by
      simpa using dvd_sub (⟨27 * k, by rw [hk]; ring⟩ : (p : ℤ_[p]) ∣ 27 * b) hd1
  exact (mem_stratFibre_iff_isSquare_two hp2 ht ha₄ hd hΔ0 (hdesc a₄ b hΔ0 ha₄ hsplit h14)).2
    ((mem_splitSetTwo_iff_isSquare hp2 hbu).1 hsplit)

/-- **The `a₆`-slice of the stratum, bounded below at every `a₄`**, granted the descent: it is at
least the mass of the split locus, which vanishes unless `a₄ ∈ minimalFstTwo p`. -/
theorem indicator_le_volume_preimage_stratFibre_two (hp2 : p = 2)
    (hdesc : HasSplitStoreyDescent p) {t : ℕ} (ht : 5 ≤ t) (a₄ : ℤ_[p]) :
    (minimalFstTwo p).indicator
        (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 5))) a₄
      ≤ (volume : Measure ℤ_[p]) (Prod.mk a₄ ⁻¹' stratFibre p (KodairaSymbol.I t, t)) := by
  by_cases hm : a₄ ∈ minimalFstTwo p
  · have ha₄ : IsUnit a₄ := isUnit_of_mem_minimalFstTwo hp2 hm
    calc (minimalFstTwo p).indicator
            (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 5))) a₄
        = (volume : Measure ℤ_[p]) (splitLevelSet p t a₄) :=
          (volume_splitLevelSet_two hp2 ht ha₄).symm
      _ ≤ (volume : Measure ℤ_[p]) (Prod.mk a₄ ⁻¹' stratFibre p (KodairaSymbol.I t, t)) :=
          measure_mono (splitLevelSet_subset_preimage_stratFibre_two hp2 hdesc ht ha₄)
  · rw [Set.indicator_of_notMem hm]
    exact zero_le

/-- `1 - p⁻¹ = p⁻¹` in `ℝ≥0∞` at `p = 2`. -/
theorem one_sub_inv_eq_inv_of_eq_two (hp2 : p = 2) :
    (1 : ℝ≥0∞) - (p : ℝ≥0∞)⁻¹ = (p : ℝ≥0∞)⁻¹ := by
  subst hp2
  simp

/-- **The `p = 2` stratum weighs at least `2^{-(t+11)}`** for every `t ≥ 5`, granted the descent on
the split locus. The four powers of `2` are `2⁻⁴` for the class of `a₄`, `2⁻¹` for the rescaling
`a₆ = 2b`, `2⁻¹` for the surviving shell, and `2^{-(t+5)}` for its level. -/
theorem inv_pow_le_volume_stratFibre_two (hp2 : p = 2) (hdesc : HasSplitStoreyDescent p) {t : ℕ}
    (ht : 5 ≤ t) :
    ((p : ℝ≥0∞)⁻¹) ^ (t + 11)
      ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I t, t)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (isOpen_stratFibre _).measurableSet]
  refine le_trans ?_ (lintegral_mono (indicator_le_volume_preimage_stratFibre_two hp2 hdesc ht))
  rw [lintegral_indicator_const measurableSet_minimalFstTwo, volume_minimalFstTwo,
    one_sub_inv_eq_inv_of_eq_two hp2, ENNReal.inv_pow,
    show t + 11 = 1 + (1 + (t + 5)) + 4 by omega, pow_add, pow_add, pow_add]
  ring_nf
  exact le_rfl

/-- **`δ_2(t) ≥ 2^{-(t+11)}` for every `t ≥ 5`**, granted the descent on the split locus. -/
theorem inv_pow_le_δ_two (hp2 : p = 2) (hdesc : HasSplitStoreyDescent p) {t : ℕ} (ht : 5 ≤ t) :
    ((p : ℝ≥0∞)⁻¹) ^ (t + 11) ≤ δ p t := by
  rw [δ_eq_deltaP_I ht, ← volume_stratFibre]
  exact inv_pow_le_volume_stratFibre_two hp2 hdesc ht

/-- **`α_2 ≥ 1/88572`, granted the descent on the split locus**, as `δ_2(5) ≥ 2⁻¹⁶ ≥ 1/2834304`. -/
theorem inv_88572_le_α_of_splitStoreyDescent (hp2 : p = 2) (hdesc : HasSplitStoreyDescent p) :
    1 / 88572 ≤ α p := by
  refine inv_88572_le_α_of_eq_two hp2 (le_trans ?_ (inv_pow_le_δ_two hp2 hdesc (le_refl 5)))
  subst hp2
  rw [show ((2 : ℕ) : ℝ≥0∞) = 2 by norm_num, show (5 : ℕ) + 11 = 16 from rfl,
    ← ENNReal.inv_pow, one_div, ENNReal.inv_le_inv]
  norm_num

/-- **For every prime `p`, `α_p < 1/2` and `α_p ≥ 1/88572`**, given `HasSplitStoreyDescent 2`. The
hypothesis is vacuous at every odd prime. -/
theorem α_bounds_of_splitStoreyDescent (hdesc : p = 2 → HasSplitStoreyDescent p) :
    α p < 1 / 2 ∧ 1 / 88572 ≤ α p := by
  refine ⟨α_lt_half, ?_⟩
  by_cases hp2 : p = 2
  · exact inv_88572_le_α_of_splitStoreyDescent hp2 (hdesc hp2)
  · exact inv_88572_le_α_of_ne_two hp2

end WeierstrassCurve
