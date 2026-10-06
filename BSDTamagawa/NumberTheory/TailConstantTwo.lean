/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.SplitTestAtTwo
public import BSDTamagawa.NumberTheory.PadicHaarThreeSlices

/-!
# The split locus on the minimal storey at `p = 2`

On the plane `a₆ = 2b` over `ℤ_2` the discriminant is `Δ = 2⁶ · (-27) · (b² - γ)` with
`γ = -a₄³/27`, so each `a₆`-slice of a discriminant level set is a rescaled unit-centre square
level set. The split test at `2` on the minimal storey of the split-multiplicative stratum is the
congruence `27b ≡ 1 mod 8`, and the resulting locus has Haar mass `2^{-(t+7)}` over the single
class `a₄ ≡ 5 mod 16` and `0` over every other unit `a₄`. The `a₆`-slice of the minimal storey
lies inside this locus.

## Main definitions

* `WeierstrassCurve.splitSetTwo`: the set `{b | 8 ∣ 27b - 1}`.
* `WeierstrassCurve.splitLevelSet`: the `a₆ = 2b` with `27b ≡ 1 mod 8` and
  `v₂(Δ(a₄, a₆)) = t + 12`.
* `WeierstrassCurve.minimalFstTwo`: the residue class `a₄ ≡ 5 mod 16`.

## Main results

* `WeierstrassCurve.ofShortNF_Δ_two_mul`, `WeierstrassCurve.emultiplicity_Δ_two_mul`: on the plane
  `a₆ = 2b`, `Δ = 2⁶ · (-27) · (b² - γ)` and `v₂(Δ) = 6 + v₂(b² - γ)`.
* `WeierstrassCurve.mem_splitSetTwo_iff_isSquare`: for a unit `b` of `ℤ_2`, `b ∈ splitSetTwo 2` iff
  `27b` is a square.
* `WeierstrassCurve.exists_step11_ok_of_mem_stratFibre_two`: Step 11 fires at every point of the
  `p = 2` stratum.
* `WeierstrassCurve.mem_stratFibre_iff_isSquare_two`: the level-`t` dictionary on the minimal
  storey, for a model on which Step 11 fires.
* `WeierstrassCurve.volume_splitLevelSet_two`: for `a₄` a unit and `t ≥ 5`,
  `μ₂(splitLevelSet 2 t a₄) = 1_{a₄ ≡ 5 mod 16}(a₄) · 2⁻¹ · (1 - 2⁻¹) · 2^{-(t+5)}`.
* `WeierstrassCurve.setOf_mem_stratFibre_subset_splitLevelSet_two`: for `t ≥ 5` and `a₄` a unit,
  the `a₆`-slice of the stratum lies inside `splitLevelSet 2 t a₄`.

## Implementation notes

The minimal storey of the `p = 2` stratum is its part `{v₂(a₄) = 0}` outside the `σ_2`-dilates
`σ_2(ℤ_2²)`. On the discriminant level set `{v₂(a₄) = 0, v₂(Δ) = t + 12}` the split test keeps
one of the two Hensel shells over the class `a₄ ≡ 5 mod 16`, and neither over the other unit
classes modulo `16`; this cannot happen at an odd prime, where the quadratic twist exchanges the
two shells.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### Units of `ℤ_2`, and the two `ZMod 16` decisions -/

/-- `-3` is a unit of `ℤ_2`. -/
private theorem isUnit_neg_three_two (hp2 : p = 2) : IsUnit (-3 : ℤ_[p]) := by
  have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 3) (by rw [hp2]; norm_num)
  simpa using h.neg

/-- `27` is a unit of `ℤ_2`. -/
private theorem isUnit_twentySeven_two (hp2 : p = 2) : IsUnit (27 : ℤ_[p]) := by
  have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 27) (by rw [hp2]; norm_num)
  simpa using h

/-- `-27` is a unit of `ℤ_2`. -/
private theorem isUnit_neg_twentySeven_two (hp2 : p = 2) : IsUnit (-27 : ℤ_[p]) := by
  have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 27) (by rw [hp2]; norm_num)
  simpa using h.neg

/-- **The split count in `ZMod 16`.** If `27W = 1` and `S² = -A³W`, then `2(27S - 1) = 0` holds for
exactly one of `S`, `-S` when `A = 5`, and for neither when `A ≠ 5`. -/
private theorem zmod_split_two (hp2 : p = 2) :
    ∀ A S W : ZMod (p ^ 4), 27 * W = 1 → S ^ 2 = -(A ^ 3) * W →
      ((A = 5 → ((2 * (27 * S - 1) = 0 ∧ 2 * (27 * (-S) - 1) ≠ 0) ∨
            (2 * (27 * S - 1) ≠ 0 ∧ 2 * (27 * (-S) - 1) = 0))) ∧
        (A ≠ 5 → (2 * (27 * S - 1) ≠ (0 : ZMod (p ^ 4)) ∧
          2 * (27 * (-S) - 1) ≠ (0 : ZMod (p ^ 4))))) := by
  subst hp2
  decide

/-- **The centre is a square on the class `A = 5`.** For `27W = 1` and `A = 5` in `ZMod 16`,
`2(-A³W - 1) = 0`. -/
private theorem zmod_isSquare_gamma_two (hp2 : p = 2) :
    ∀ A W : ZMod (p ^ 4), 27 * W = 1 → A = 5 → 2 * (-(A ^ 3) * W - 1) = (0 : ZMod (p ^ 4)) := by
  subst hp2
  decide

/-! ### Step 11 fires on the whole `p = 2` stratum -/

/-- **Step 11 fires at every point of the `p = 2` stratum** `τ₂⁻¹((I_t, t))`, `t ≥ 1`. -/
theorem exists_step11_ok_of_mem_stratFibre_two (hp2 : p = 2) {t : ℕ} (ht : 1 ≤ t)
    {a₄ a₆ : ℤ_[p]} (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0)
    (hx : ((a₄, a₆) : ℤ_[p] × ℤ_[p]) ∈ stratFibre p (KodairaSymbol.I t, t)) :
    ∃ V, TateAlgorithm.Step11.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V := by
  have hUp : ((a₄, a₆) : ℤ_[p] × ℤ_[p]) ∈ nonsingularLocus p := hΔ0
  rcases he : TateAlgorithm.Step11.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ0 with out | V
  · exfalso
    have hk := run_kodairaSymbol_of_mem_stratFibre hUp hx
    rw [TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ0 he] at hk
    exact (TateAlgorithm.Step11.nodal_of_kodairaSymbol_eq_I PadicInt.uniformizer_ne_zero
      hΔ0 he hk ht).1 (dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inl hp2) a₄ a₆)
  · exact ⟨V, rfl⟩

/-! ### The discriminant on the plane `a₆ = 2b` -/

/-- **The discriminant on the plane `a₆ = 2b` at `p = 2`:** for `27w = 1`,

  `Δ(a₄, 2b) = 2⁶ · (-27) · (b² - (-a₄³w))`. -/
theorem ofShortNF_Δ_two_mul (hp2 : p = 2) {w : ℤ_[p]} (hw : (27 : ℤ_[p]) * w = 1) (a₄ b : ℤ_[p]) :
    (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ
      = (p : ℤ_[p]) ^ 6 * ((-27) * (b ^ 2 - (-(a₄ ^ 3) * w))) := by
  rw [ofShortNF_Δ]
  subst hp2
  push_cast
  linear_combination (64 * a₄ ^ 3) * hw

/-- **`v₂(Δ(a₄, 2b)) = 6 + v₂(b² - γ)`** with `γ = -a₄³w`, `27w = 1`. -/
theorem emultiplicity_Δ_two_mul (hp2 : p = 2) {w : ℤ_[p]} (hw : (27 : ℤ_[p]) * w = 1)
    (a₄ b : ℤ_[p]) :
    emultiplicity (p : ℤ_[p]) (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ
      = ((6 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) (b ^ 2 - (-(a₄ ^ 3) * w)) := by
  rw [ofShortNF_Δ_two_mul hp2 hw,
    PadicInt.emultiplicity_pow_mul_unit_mul 6 (isUnit_neg_twentySeven_two hp2)]

/-! ### The split test as a congruence modulo `8` -/

variable (p) in
/-- **The split condition at `p = 2`**: `27 b ≡ 1 mod 8`, equivalently `b ≡ 3 mod 8`. -/
def splitSetTwo : Set ℤ_[p] := {b : ℤ_[p] | (p : ℤ_[p]) ^ 3 ∣ 27 * b - 1}

/-- `splitSetTwo p` is a union of residue classes modulo `p³`. -/
theorem mem_splitSetTwo_congr {y z : ℤ_[p]} (h : (p : ℤ_[p]) ^ 3 ∣ y - z) :
    y ∈ splitSetTwo p ↔ z ∈ splitSetTwo p := by
  have hd : (p : ℤ_[p]) ^ 3 ∣ (27 * y - 1) - (27 * z - 1) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨27 * k, by linear_combination 27 * hk⟩
  exact ⟨fun hy => by
      have h1 := dvd_sub hy hd
      rwa [show 27 * y - 1 - (27 * y - 1 - (27 * z - 1)) = 27 * z - 1 from by ring] at h1,
    fun hz => by
      have h1 := dvd_add hz hd
      rwa [show 27 * z - 1 + (27 * y - 1 - (27 * z - 1)) = 27 * y - 1 from by ring] at h1⟩

/-- On the units of `ℤ_2`, `splitSetTwo 2` is the split test `IsSquare (27 b)`. -/
theorem mem_splitSetTwo_iff_isSquare (hp2 : p = 2) {b : ℤ_[p]} (hb : IsUnit b) :
    b ∈ splitSetTwo p ↔ IsSquare (27 * b) :=
  (PadicInt.isSquare_iff_pow_three_dvd_sub_one_of_eq_two hp2
    ((isUnit_twentySeven_two hp2).mul hb)).symm

private theorem mem_splitSetTwo_iff_zmod (hp2 : p = 2) (y : ℤ_[p]) :
    y ∈ splitSetTwo p ↔ (2 : ZMod (p ^ 4)) * (27 * PadicInt.toZModPow 4 y - 1) = 0 := by
  rw [splitSetTwo, Set.mem_ofPred_eq,
    PadicInt.pow_three_dvd_iff_two_mul_toZModPow_four_of_eq_two hp2, map_sub, map_mul, map_ofNat,
    map_one]

/-! ### The minimal storey is the `a₄`-unit part of the stratum -/

/-- **Every point of `τ₂⁻¹((I_t, t))` outside `σ₂(ℤ₂²)` has `a₄` a unit**, for `t ≥ 5`. -/
theorem isUnit_fst_of_mem_diff_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I t, t))
    (hxr : x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :
    IsUnit x.1 := by
  obtain ⟨s, h4, h6, -⟩ := exists_emultiplicity_of_mem_stratFibre_two hp2 ht hx
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine not_not.1 fun hnu => ?_
    have hdvd : (p : ℤ_[p]) ∣ x.1 := PadicInt.dvd_iff_not_isUnit.2 hnu
    have h0 : emultiplicity (p : ℤ_[p]) x.1 = 0 := by simpa using h4
    exact (emultiplicity_eq_zero.1 h0) hdvd
  · exact absurd (PadicInt.mem_range_scaleProdByPPow_iff.2
      ⟨pow_dvd_of_le_emultiplicity (by rw [h4]; exact_mod_cast (by omega : 4 ≤ 4 * s)),
        pow_dvd_of_le_emultiplicity (by rw [h6]; exact_mod_cast (by omega : 6 ≤ 6 * s + 1))⟩) hxr

/-- **A point whose `a₄` is a unit is not a `σ₂`-dilate**, a dilate having `2⁴ ∣ a₄`. -/
theorem notMem_range_of_isUnit_fst_two {x : ℤ_[p] × ℤ_[p]} (ha₄ : IsUnit x.1) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := fun hxr =>
  PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit
    ((dvd_pow_self (p : ℤ_[p]) (by norm_num : (4 : ℕ) ≠ 0)).trans
      (PadicInt.mem_range_scaleProdByPPow_iff.1 hxr).1) ha₄)

/-- **On the minimal storey `v₂(a₆) = 1` and `v₂(Δ) = t + 12`**, for `t ≥ 5`. -/
theorem emultiplicity_snd_Δ_of_isUnit_fst_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I t, t)) (ha₄ : IsUnit x.1) :
    emultiplicity (p : ℤ_[p]) x.2 = ((1 : ℕ) : ℕ∞) ∧
      emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((t + 12 : ℕ) : ℕ∞) := by
  obtain ⟨s, h4, h6, hd⟩ := exists_emultiplicity_of_mem_stratFibre_two hp2 ht hx
  have hs0 : s = 0 := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rfl
    · refine absurd ha₄ (PadicInt.dvd_iff_not_isUnit.1 ?_)
      have h1 : (p : ℤ_[p]) ^ 1 ∣ x.1 :=
        pow_dvd_of_le_emultiplicity (by rw [h4]; exact_mod_cast (by omega : 1 ≤ 4 * s))
      rwa [pow_one] at h1
  subst hs0
  exact ⟨by simpa using h6, by simpa using hd⟩

/-! ### The level-`t` dictionary at `p = 2`, on the minimal storey -/

/-- **The level-`t` dictionary at `p = 2`, on the minimal storey.** For `t ≥ 5`, a short model over
`ℤ_2` with `a₄` a unit, `a₆ = 2b` and `v₂(Δ) = t + 12`, on which Step 11 fires, lies in
`τ₂⁻¹((I_t, t))` **iff** `27b` is a square in `ℤ_2`. -/
theorem mem_stratFibre_iff_isSquare_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) {a₄ b : ℤ_[p]}
    (ha₄ : IsUnit a₄)
    (hΔ : emultiplicity (p : ℤ_[p]) (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ = ((t + 12 : ℕ) : ℕ∞))
    (hΔ0 : (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ ≠ 0)
    (hV : ∃ V, TateAlgorithm.Step11.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
      PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V) :
    (a₄, (p : ℤ_[p]) * b) ∈ stratFibre p (KodairaSymbol.I t, t) ↔ IsSquare (27 * b) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨V, hVe⟩ := hV
  have hVΔ0 : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔ0 hVe
  have hc₄V : V.c₄ = -3 * a₄ := by
    have h := TateAlgorithm.Step11.run_c₄ hϖ hΔ0 hVe
    rw [ofShortNF_c₄] at h
    refine mul_left_cancel₀ (pow_ne_zero 4 hϖ) ?_
    rw [h]; subst hp2; push_cast; ring
  have hc₄ : ¬ (p : ℤ_[p]) ∣ V.c₄ := by
    rw [hc₄V]
    exact fun hd => PadicInt.prime_p.not_isUnit
      (isUnit_of_dvd_unit hd ((isUnit_neg_three_two hp2).mul ha₄))
  have hΔV : emultiplicity (p : ℤ_[p]) V.Δ = ((t : ℕ) : ℕ∞) := by
    have h := TateAlgorithm.Step11.run_Δ hϖ hΔ0 hVe
    have h12 : ((12 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) V.Δ = ((t + 12 : ℕ) : ℕ∞) := by
      rw [← hΔ, ← h, show (p : ℤ_[p]) ^ 12 * V.Δ = (p : ℤ_[p]) ^ 12 * (1 * V.Δ) from by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 12 isUnit_one]
    obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 12) (n := t + 12) h12
    rw [hj, show j = t by omega]
  have hc₆V : -V.c₆ = 27 * b := by
    have h := TateAlgorithm.Step11.run_c₆ hϖ hΔ0 hVe
    rw [ofShortNF_c₆] at h
    have hV6 : V.c₆ = -27 * b := by
      refine mul_left_cancel₀ (pow_ne_zero 6 hϖ) ?_
      rw [h]; subst hp2; push_cast; ring
    rw [hV6]; ring
  have hUp : ((a₄, (p : ℤ_[p]) * b) : ℤ_[p] × ℤ_[p]) ∈ nonsingularLocus p := hΔ0
  rw [mem_stratFibre_iff hUp, strat, Prod.mk.injEq,
    TateAlgorithm.run_eq_of_step11_ok hϖ hΔ0 hVe hVΔ0,
    run_kodaira_tamagawa_eq_iff_isSquare_of_eq_two hp2 hVΔ0 hc₄ (by omega : 3 ≤ t), hΔV, hc₆V]
  simp only [true_and]

/-! ### The exact Haar computation -/

variable (p) in
/-- **The `a₆`-locus cut out by the split test**, at level `t` over `a₄`: the `a₆ = 2b` with
`27b ≡ 1 mod 8` and `v₂(Δ(a₄, a₆)) = t + 12`. -/
def splitLevelSet (t : ℕ) (a₄ : ℤ_[p]) : Set ℤ_[p] :=
  {a₆ : ℤ_[p] | (∃ b, a₆ = (p : ℤ_[p]) * b ∧ b ∈ splitSetTwo p) ∧
    emultiplicity (p : ℤ_[p]) (ofShortNF a₄ a₆).Δ = ((t + 12 : ℕ) : ℕ∞)}

/-- **The split locus is a rescaled unit-centre level set cut by a congruence modulo `8`.** For
`27w = 1` and every `a₄`,

  `splitLevelSet 2 t a₄ = 2 · (sqLevelSet (-a₄³w) (t+6) ∩ splitSetTwo 2)`. -/
theorem splitLevelSet_eq_image (hp2 : p = 2) {w : ℤ_[p]} (hw : (27 : ℤ_[p]) * w = 1) (t : ℕ)
    (a₄ : ℤ_[p]) :
    splitLevelSet p t a₄
      = PadicInt.scaleByPPow 1 ''
          (PadicInt.sqLevelSet (-(a₄ ^ 3) * w) (t + 6) ∩ splitSetTwo p) := by
  have hval : ∀ b : ℤ_[p],
      emultiplicity (p : ℤ_[p]) (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ = ((t + 12 : ℕ) : ℕ∞) ↔
        b ∈ PadicInt.sqLevelSet (-(a₄ ^ 3) * w) (t + 6) := by
    intro b
    rw [emultiplicity_Δ_two_mul hp2 hw, PadicInt.mem_sqLevelSet]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 6) (n := t + 12) h
      rw [hj, show j = t + 6 by omega]
    · rw [h]; push_cast; ring
  ext a₆
  simp only [splitLevelSet, Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨b, rfl, hsplit⟩, hd⟩
    exact ⟨b, ⟨(hval b).1 hd, hsplit⟩, by rw [PadicInt.scaleByPPow, pow_one]⟩
  · rintro ⟨b, ⟨hlev, hsplit⟩, rfl⟩
    rw [PadicInt.scaleByPPow, pow_one]
    exact ⟨⟨b, rfl, hsplit⟩, (hval b).2 hlev⟩

variable (p) in
/-- **The `a₄`-locus carrying the `p = 2` minimal storey**: `a₄ ≡ 5 mod 16`. -/
def minimalFstTwo : Set ℤ_[p] := PadicInt.toZModPow 4 ⁻¹' {(5 : ZMod (p ^ 4))}

/-- `minimalFstTwo p` is measurable. -/
theorem measurableSet_minimalFstTwo : MeasurableSet (minimalFstTwo p) :=
  PadicInt.measurableSet_preimage_toZModPow 4 (5 : ZMod (p ^ 4))

/-- **The mass of the `a₄`-locus is `2⁻⁴`.** -/
theorem volume_minimalFstTwo :
    (volume : Measure ℤ_[p]) (minimalFstTwo p) = ((p : ℝ≥0∞) ^ 4)⁻¹ :=
  PadicInt.volume_preimage_toZModPow 4 (5 : ZMod (p ^ 4))

/-- Membership of `minimalFstTwo p`, unfolded. -/
theorem mem_minimalFstTwo_iff {a₄ : ℤ_[p]} :
    a₄ ∈ minimalFstTwo p ↔ PadicInt.toZModPow 4 a₄ = (5 : ZMod (p ^ 4)) := Iff.rfl

/-- Every point of `minimalFstTwo 2` is a unit. -/
theorem isUnit_of_mem_minimalFstTwo (hp2 : p = 2) {a₄ : ℤ_[p]}
    (h : a₄ ∈ minimalFstTwo p) : IsUnit a₄ := by
  refine not_not.1 fun hnu => ?_
  obtain ⟨k, hk⟩ := PadicInt.dvd_iff_not_isUnit.2 hnu
  have h5 : PadicInt.toZModPow 4 a₄ = (5 : ZMod (p ^ 4)) := h
  rw [hk, map_mul, map_natCast] at h5
  subst hp2
  revert h5
  have hdec : ∀ K : ZMod (2 ^ 4), ((2 : ℕ) : ZMod (2 ^ 4)) * K ≠ 5 := by decide
  exact hdec _

/-- **The exact Haar mass of the `p = 2` split locus.** For `a₄` a unit and `t ≥ 5`,

  `μ₂(splitLevelSet 2 t a₄) = 1_{a₄ ≡ 5 mod 16}(a₄) · 2⁻¹ · (1 - 2⁻¹) · 2^{-(t+5)}`,

which is `2^{-(t+7)}` on the single class `a₄ ≡ 5 mod 16` and `0` on every other unit `a₄`. -/
theorem volume_splitLevelSet_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) {a₄ : ℤ_[p]}
    (ha₄ : IsUnit a₄) :
    (volume : Measure ℤ_[p]) (splitLevelSet p t a₄)
      = (minimalFstTwo p).indicator
          (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 5))) a₄ := by
  obtain ⟨w, hw⟩ := (isUnit_twentySeven_two hp2).exists_right_inv
  have hwu : IsUnit w := ⟨⟨w, 27, by rw [mul_comm]; exact hw, hw⟩, rfl⟩
  have hγu : IsUnit (-(a₄ ^ 3) * w : ℤ_[p]) := ((ha₄.pow 3).neg).mul hwu
  have hW : (27 : ZMod (p ^ 4)) * PadicInt.toZModPow 4 w = 1 := by
    rw [← map_ofNat (PadicInt.toZModPow 4) 27, ← map_mul, hw, map_one]
  have hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z →
      (y ∈ splitSetTwo p ↔ z ∈ splitSetTwo p) := fun _ _ h => mem_splitSetTwo_congr h
  rw [splitLevelSet_eq_image hp2 hw, PadicInt.measure_image_scaleByPPow,
    PadicInt.zpow_neg_natCast_eq_inv_pow_two, pow_one, show t + 6 = t + 5 + 1 by omega]
  by_cases hA : PadicInt.toZModPow 4 a₄ = (5 : ZMod (p ^ 4))
  · rw [Set.indicator_of_mem (mem_minimalFstTwo_iff.2 hA)]
    have hsq : IsSquare (-(a₄ ^ 3) * w : ℤ_[p]) := by
      rw [PadicInt.isSquare_iff_two_mul_toZModPow_four_of_eq_two hp2 hγu, map_mul, map_neg, map_pow]
      exact zmod_isSquare_gamma_two hp2 _ _ hW hA
    obtain ⟨s, hs⟩ := hsq
    have hSrel : (PadicInt.toZModPow 4 s) ^ 2
        = -((PadicInt.toZModPow 4 a₄) ^ 3) * PadicInt.toZModPow 4 w := by
      have h := congrArg (PadicInt.toZModPow (p := p) 4) hs
      rw [map_mul, map_neg, map_pow, map_mul] at h
      rw [h]; ring
    have hone := (zmod_split_two hp2 (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 s)
      (PadicInt.toZModPow 4 w) hW hSrel).1 hA
    have hmem_s : s ∈ splitSetTwo p ↔
        (2 : ZMod (p ^ 4)) * (27 * PadicInt.toZModPow 4 s - 1) = 0 :=
      mem_splitSetTwo_iff_zmod hp2 s
    have hmem_ns : -s ∈ splitSetTwo p ↔
        (2 : ZMod (p ^ 4)) * (27 * (-(PadicInt.toZModPow 4 s)) - 1) = 0 := by
      rw [mem_splitSetTwo_iff_zmod hp2, map_neg]
    rw [PadicInt.volume_sqLevelSet_inter_of_unique_root_of_eq_two hp2 hγu hs hQ ?_
      (by omega : 3 ≤ t + 5)]
    rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmem_s.2 h1, fun hc => h2 (hmem_ns.1 hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hmem_s.1 hc), hmem_ns.2 h2⟩
  · rw [Set.indicator_of_notMem (fun hc => hA (mem_minimalFstTwo_iff.1 hc))]
    by_cases hsq : IsSquare (-(a₄ ^ 3) * w : ℤ_[p])
    · obtain ⟨s, hs⟩ := hsq
      have hSrel : (PadicInt.toZModPow 4 s) ^ 2
          = -((PadicInt.toZModPow 4 a₄) ^ 3) * PadicInt.toZModPow 4 w := by
        have h := congrArg (PadicInt.toZModPow (p := p) 4) hs
        rw [map_mul, map_neg, map_pow, map_mul] at h
        rw [h]; ring
      have hnone := (zmod_split_two hp2 (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 s)
        (PadicInt.toZModPow 4 w) hW hSrel).2 hA
      rw [PadicInt.volume_sqLevelSet_inter_of_no_root_of_eq_two hp2 hγu hs hQ
        ⟨fun hc => hnone.1 ((mem_splitSetTwo_iff_zmod hp2 s).1 hc),
          fun hc => hnone.2 (by
            have h := (mem_splitSetTwo_iff_zmod hp2 (-s)).1 hc
            rwa [map_neg] at h)⟩ (by omega : 3 ≤ t + 5), mul_zero]
    · rw [PadicInt.sqLevelSet_eq_empty_of_not_isSquare_of_eq_two hp2 hγu hsq
        (by omega : 3 ≤ t + 5 + 1), Set.empty_inter, measure_empty, mul_zero]

/-! ### The `a₆`-slice of the minimal storey -/

/-- **The `a₆`-slice of the minimal storey lies inside the split locus**, for `t ≥ 5` and `a₄` a
unit. -/
theorem setOf_mem_stratFibre_subset_splitLevelSet_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t)
    {a₄ : ℤ_[p]} (ha₄ : IsUnit a₄) :
    {a₆ : ℤ_[p] | (a₄, a₆) ∈ stratFibre p (KodairaSymbol.I t, t)} ⊆ splitLevelSet p t a₄ := by
  intro a₆ hmem
  obtain ⟨h6, hd⟩ := emultiplicity_snd_Δ_of_isUnit_fst_two hp2 ht hmem ha₄
  obtain ⟨b, hbu, hb⟩ := PadicInt.exists_isUnit_of_emultiplicity_eq_natCast h6
  rw [pow_one] at hb
  subst hb
  have hΔ0 : (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero_right] at hd
    exact (ENat.natCast_ne_top (t + 12)) hd.symm
  have hV := exists_step11_ok_of_mem_stratFibre_two hp2 (by omega : 1 ≤ t) hΔ0 hmem
  exact ⟨⟨b, rfl, (mem_splitSetTwo_iff_isSquare hp2 hbu).2
    ((mem_stratFibre_iff_isSquare_two hp2 ht ha₄ hd hΔ0 hV).1 hmem)⟩, hd⟩

end WeierstrassCurve
