/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.Step11AtThree
public import BSDTamagawa.NumberTheory.PadicHaarThreeSlices

/-!
# The minimal storey of the split-multiplicative stratum at `p = 3`

At `p = 3`, every point of the split-multiplicative stratum `τ₃⁻¹((I_t, t))` with `t ≥ 5` outside
the image of the dilation `σ₃(a₄, a₆) = (3⁴a₄, 3⁶a₆)` lies on the minimal storey `v₃(a₄) = 3`. On
that storey the stratum is described by a congruence on `a₆ = 27u` modulo `3`: `32u` must be a
square in the residue field. This file proves this description and computes the `a₆`-slices of the
stratum through points of the minimal storey. It also records the masses of translated valuation
shells and the decomposition of a square level set into two Hensel balls at an odd prime.

## Main definitions

* `WeierstrassCurve.splitResidueSet`: the `p`-adic integers `u` for which `32u` is a square modulo
  `p`.

## Main results

* `WeierstrassCurve.mem_stratFibre_iff_splitResidue_three`: for `t ≥ 5`, a short model over `ℤ_3`
  with `v₃(a₄) = 3` and `v₃(Δ) = t + 12` lies in `τ₃⁻¹((I_t, t))` iff `a₆ = 27u` with `32u` a
  square in the residue field.
* `WeierstrassCurve.setOf_mem_stratFibre_three_eq_image`: the `a₆`-slice of that stratum through
  `a₄ = 27α` is `27 · (sqLevelSet (-4α³) (t+3) ∩ splitResidueSet 3)`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

/-! ### Valuation shells, and the two Hensel balls of a square level set -/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- A translated valuation shell `{y | v_p(y + c) = n}` is a translate of `{y | v_p(y) = n}`. -/
theorem setOf_emultiplicity_add_eq_preimage (c : ℤ_[p]) (n : ℕ) :
    {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) (y + c) = (n : ℕ∞)}
      = (fun z => c + z) ⁻¹' {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (n : ℕ∞)} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [show c + y = y + c by ring]

/-- **The mass of a translated valuation shell** is that of the shell itself, `(1 - p⁻¹)p⁻ⁿ`. -/
theorem volume_setOf_emultiplicity_add_eq (c : ℤ_[p]) (n : ℕ) :
    (volume : Measure ℤ_[p]) {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) (y + c) = (n : ℕ∞)}
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ n := by
  rw [setOf_emultiplicity_add_eq_preimage, measure_preimage_add, volume_setOf_emultiplicity_eq]

/-- **The two Hensel balls.** At an odd prime, for a unit `c = s²` and `n ≥ 1`,

  `sqLevelSet c n = {x | v(x + (-s)) = n} ∪ {x | v(x + s) = n}`. -/
theorem sqLevelSet_eq_union_shell (hp : Odd p) {c s : ℤ_[p]} (hc : IsUnit c) (hs : c = s * s)
    {n : ℕ} (hn : 1 ≤ n) :
    sqLevelSet c n = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + -s) = (n : ℕ∞)}
      ∪ {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (n : ℕ∞)} := by
  have hsunit : IsUnit s := by rw [hs] at hc; exact (IsUnit.mul_iff.mp hc).1
  have hn0 : (n : ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  ext x
  have hsplit : emultiplicity (p : ℤ_[p]) (x ^ 2 - c)
      = emultiplicity (p : ℤ_[p]) (x + -s) + emultiplicity (p : ℤ_[p]) (x + s) := by
    rw [show x ^ 2 - c = (x + -s) * (x + s) by rw [hs]; ring, emultiplicity_mul prime_p]
  rw [Set.mem_union, mem_sqLevelSet, hsplit]
  simp only [Set.mem_ofPred_eq]
  rcases isUnit_sub_or_isUnit_add hp hsunit x with hu | hu
  · rw [emultiplicity_eq_zero_of_isUnit (show IsUnit (x + -s) by rwa [← sub_eq_add_neg]), zero_add]
    exact ⟨Or.inr, fun h => h.resolve_left fun h0 => hn0 h0.symm⟩
  · rw [emultiplicity_eq_zero_of_isUnit hu, add_zero]
    exact ⟨Or.inl, fun h => h.resolve_right fun h0 => hn0 h0.symm⟩

end PadicInt

/-! ### The minimal storey of the `p = 3` split-multiplicative stratum -/

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The `p`-adic integers `u` for which the residue of `32u` modulo `p` is a square. At `p = 3` and
`a₆ = 27u` on the storey `v₃(a₄) = 3`, this is the split test of the multiplicative stratum. -/
def splitResidueSet : Set ℤ_[p] :=
  {u : ℤ_[p] | IsSquare (CommRing.mod (p : ℤ_[p]) (32 * u))}

/-- A `p`-adic integer `u` lies in `splitResidueSet p` exactly when the residue of `32u` modulo
`p` is a square. -/
@[simp] theorem mem_splitResidueSet_iff {u : ℤ_[p]} :
    u ∈ splitResidueSet p ↔ IsSquare (CommRing.mod (p : ℤ_[p]) (32 * u)) := Iff.rfl

/-- `splitResidueSet` is a union of residue classes modulo `p`. -/
theorem mem_splitResidueSet_congr {y z : ℤ_[p]} (h : (p : ℤ_[p]) ∣ y - z) :
    y ∈ splitResidueSet p ↔ z ∈ splitResidueSet p := by
  have hmod : CommRing.mod (p : ℤ_[p]) (32 * y) = CommRing.mod (p : ℤ_[p]) (32 * z) := by
    rw [← sub_eq_zero, ← map_sub, show (32 : ℤ_[p]) * y - 32 * z = 32 * (y - z) by ring,
      CommRing.mod_eq_zero]
    exact h.mul_left 32
  simp only [mem_splitResidueSet_iff, hmod]

/-- **On the minimal storey the `a₆`-valuation is forced to be `3`.** For `t ≥ 5`, a short model
over `ℤ_3` with `v₃(a₄) = 3` and `v₃(Δ) = t + 12` has `v₃(a₆) = 3`. -/
theorem emultiplicity_snd_eq_three_of_emultiplicity_fst_eq_three (hp3 : p = 3) {t : ℕ}
    (ht : 5 ≤ t) {a₄ a₆ : ℤ_[p]}
    (ha₄ : emultiplicity (p : ℤ_[p]) a₄ = ((3 : ℕ) : ℕ∞))
    (hΔ : emultiplicity (p : ℤ_[p]) (ofShortNF a₄ a₆).Δ = ((t + 12 : ℕ) : ℕ∞)) :
    emultiplicity (p : ℤ_[p]) a₆ = ((3 : ℕ) : ℕ∞) := by
  have hodd : Odd p := hp3 ▸ (by decide : Odd 3)
  have h16 : IsUnit (-16 : ℤ_[p]) := PadicInt.isUnit_neg_sixteen hodd
  have h4u : IsUnit (4 : ℤ_[p]) := by simpa using (PadicInt.isUnit_neg_four hodd).neg
  have hsum : emultiplicity (p : ℤ_[p]) (4 * a₄ ^ 3 + 27 * a₆ ^ 2) = ((t + 12 : ℕ) : ℕ∞) := by
    rw [← hΔ, ofShortNF_Δ,
      show (-16 : ℤ_[p]) * (4 * a₄ ^ 3 + 27 * a₆ ^ 2)
        = (p : ℤ_[p]) ^ 0 * (-16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2)) by ring,
      PadicInt.emultiplicity_pow_mul_unit_mul 0 h16]
    norm_num
  have hcube : emultiplicity (p : ℤ_[p]) (4 * a₄ ^ 3) = ((9 : ℕ) : ℕ∞) := by
    rw [show (4 : ℤ_[p]) * a₄ ^ 3 = (p : ℤ_[p]) ^ 0 * (4 * a₄ ^ 3) by ring,
      PadicInt.emultiplicity_pow_mul_unit_mul 0 h4u, emultiplicity_pow PadicInt.prime_p, ha₄]
    push_cast
    ring
  have h27 : emultiplicity (p : ℤ_[p]) (27 * a₆ ^ 2) = ((9 : ℕ) : ℕ∞) :=
    PadicInt.emultiplicity_eq_of_lt_of_add_eq hcube hsum (by omega)
  have h27' : emultiplicity (p : ℤ_[p]) (27 * a₆ ^ 2)
      = ((3 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) * emultiplicity (p : ℤ_[p]) a₆ := by
    rw [show (27 : ℤ_[p]) * a₆ ^ 2 = (p : ℤ_[p]) ^ 3 * (1 * a₆ ^ 2) by subst hp3; push_cast; ring,
      PadicInt.emultiplicity_pow_mul_unit_mul 3 isUnit_one, emultiplicity_pow PadicInt.prime_p]
  obtain ⟨i, hi, hir⟩ := ENat.exists_natCast_of_add_mul_eq (k := 3) (b := 2) (n := 9)
    two_ne_zero (h27'.symm.trans h27)
  rw [hi, show i = 3 by omega]

/-- **The level-`t` dictionary at `p = 3`, on the minimal storey.** For `t ≥ 5`, a short model over
`ℤ_3` with `v₃(a₄) = 3` and `v₃(Δ) = t + 12` lies in `τ₃⁻¹((I_t, t))` **iff** `a₆ = 27u` with `32u`
a square in the residue field. -/
theorem mem_stratFibre_iff_splitResidue_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) {a₄ a₆ : ℤ_[p]}
    (ha₄ : emultiplicity (p : ℤ_[p]) a₄ = ((3 : ℕ) : ℕ∞))
    (hΔ : emultiplicity (p : ℤ_[p]) (ofShortNF a₄ a₆).Δ = ((t + 12 : ℕ) : ℕ∞)) :
    (a₄, a₆) ∈ stratFibre p (KodairaSymbol.I t, t) ↔
      ∃ u : ℤ_[p], a₆ = (p : ℤ_[p]) ^ 3 * u ∧ u ∈ splitResidueSet p := by
  have hodd : Odd p := hp3 ▸ (by decide : Odd 3)
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have ha₆ := emultiplicity_snd_eq_three_of_emultiplicity_fst_eq_three hp3 ht ha₄ hΔ
  obtain ⟨α, hαu, hα⟩ := PadicInt.exists_isUnit_of_emultiplicity_eq_natCast ha₄
  obtain ⟨u, huu, hu⟩ := PadicInt.exists_isUnit_of_emultiplicity_eq_natCast ha₆
  have hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero_right] at hΔ
    exact (ENat.natCast_ne_top (t + 12)) hΔ.symm
  have hUp : ((a₄, a₆) : ℤ_[p] × ℤ_[p]) ∈ nonsingularLocus p := hΔ0
  obtain ⟨V, hV⟩ := TateAlgorithm.Step11.run_eq_ok_of_three hp3 hΔ0
    (pow_dvd_of_le_emultiplicity (by rw [ha₄]))
    (pow_dvd_of_le_emultiplicity (by rw [ha₆]))
    (pow_dvd_of_le_emultiplicity (by rw [hΔ]; exact_mod_cast (by omega : 14 ≤ t + 12)))
  have hVΔ0 : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔ0 hV
  have hc₄V : V.c₄ = -16 * α := by
    have h := TateAlgorithm.Step11.run_c₄ hϖ hΔ0 hV
    rw [ofShortNF_c₄, hα] at h
    refine mul_left_cancel₀ (pow_ne_zero 4 hϖ) ?_
    rw [h]
    subst hp3
    push_cast
    ring
  have hc₄ : ¬ (p : ℤ_[p]) ∣ V.c₄ := by
    rw [hc₄V]
    exact fun hd => PadicInt.prime_p.not_isUnit
      (isUnit_of_dvd_unit hd ((PadicInt.isUnit_neg_sixteen hodd).mul hαu))
  have hΔV : emultiplicity (p : ℤ_[p]) V.Δ = ((t : ℕ) : ℕ∞) := by
    have h := TateAlgorithm.Step11.run_Δ hϖ hΔ0 hV
    have h12 : ((12 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) V.Δ = ((t + 12 : ℕ) : ℕ∞) := by
      rw [← hΔ, ← h, show (p : ℤ_[p]) ^ 12 * V.Δ = (p : ℤ_[p]) ^ 12 * (1 * V.Δ) by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 12 isUnit_one]
    obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 12) (n := t + 12) h12
    rw [hj, show j = t by omega]
  have hc₆V : -V.c₆ = 32 * u := by
    have h := TateAlgorithm.Step11.run_c₆ hϖ hΔ0 hV
    rw [ofShortNF_c₆, hu] at h
    have hV6 : V.c₆ = -32 * u := by
      refine mul_left_cancel₀ (pow_ne_zero 6 hϖ) ?_
      rw [h]
      subst hp3
      push_cast
      ring
    rw [hV6]
    ring
  rw [mem_stratFibre_iff hUp, strat, Prod.mk.injEq,
    TateAlgorithm.run_eq_of_step11_ok hϖ hΔ0 hV hVΔ0,
    run_kodaira_tamagawa_eq_iff_isSquare hodd hVΔ0 hc₄ (by omega : 3 ≤ t), hΔV, hc₆V]
  simp only [true_and]
  refine ⟨fun hs => ⟨u, hu, hs⟩, ?_⟩
  rintro ⟨u', hu', hs⟩
  obtain rfl : u' = u := mul_left_cancel₀ (pow_ne_zero 3 hϖ) (hu'.symm.trans hu)
  exact hs

/-! ### The minimal storey is the complement of the dilate -/

/-- **Every point of `τ₃⁻¹((I_t, t))` outside `σ₃(ℤ₃²)` has `v₃(a₄) = 3`**, for `t ≥ 5`. -/
theorem emultiplicity_fst_eq_three_of_mem_diff (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I t, t))
    (hxr : x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) :
    emultiplicity (p : ℤ_[p]) x.1 = ((3 : ℕ) : ℕ∞) := by
  obtain ⟨s, h4, h6, -⟩ := exists_emultiplicity_of_mem_stratFibre_three hp3 ht hx
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [h4]
  · exact absurd (PadicInt.mem_range_scaleProdByPPow_iff.2
      ⟨pow_dvd_of_le_emultiplicity (by rw [h4]; exact_mod_cast (by omega : 4 ≤ 4 * s + 3)),
        pow_dvd_of_le_emultiplicity (by rw [h6]; exact_mod_cast (by omega : 6 ≤ 6 * s + 3))⟩) hxr

/-- **A point with `v₃(a₄) = 3` is not a dilate**, since a dilate has `3⁴ ∣ a₄`. -/
theorem notMem_range_of_emultiplicity_fst_eq_three {x : ℤ_[p] × ℤ_[p]}
    (ha₄ : emultiplicity (p : ℤ_[p]) x.1 = ((3 : ℕ) : ℕ∞)) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  intro hxr
  obtain ⟨h4, -⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hxr
  have hle : ((4 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ_[p]) x.1 :=
    PadicInt.mem_span_pPow_iff_le_emultiplicity.1 (Ideal.mem_span_singleton.2 h4)
  rw [ha₄] at hle
  exact absurd (by exact_mod_cast hle : (4 : ℕ) ≤ 3) (by omega)

/-! ### The `a₆`-slice of the minimal storey -/

/-- **The `a₆`-slice through a minimal-storey point.** For `α` a unit of `ℤ_3` and `t ≥ 5`,

  `{a₆ | (27α, a₆) ∈ τ₃⁻¹((I_t, t))} = 27 · (sqLevelSet (-4α³) (t+3) ∩ splitResidueSet)`. -/
theorem setOf_mem_stratFibre_three_eq_image (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) {α : ℤ_[p]}
    (hαu : IsUnit α) :
    {a₆ : ℤ_[p] | ((p : ℤ_[p]) ^ 3 * α, a₆) ∈ stratFibre p (KodairaSymbol.I t, t)}
      = PadicInt.scaleByPPow 3 ''
          (PadicInt.sqLevelSet (-4 * α ^ 3) (t + 3) ∩ splitResidueSet p) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hodd : Odd p := hp3 ▸ (by decide : Odd 3)
  have ha₄ : emultiplicity (p : ℤ_[p]) ((p : ℤ_[p]) ^ 3 * α) = ((3 : ℕ) : ℕ∞) :=
    PadicInt.emultiplicity_pow_mul_unit 3 hαu
  have hunit : IsUnit (-4 * α ^ 3 : ℤ_[p]) :=
    (PadicInt.isUnit_neg_four hodd).mul (hαu.pow 3)
  have hlevel : {a₆ : ℤ_[p] |
      emultiplicity (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 3 * α) a₆).Δ = ((t + 12 : ℕ) : ℕ∞)}
      = PadicInt.scaleByPPow 3 '' PadicInt.sqLevelSet (-4 * α ^ 3) (t + 3) := by
    have hβ : ((p : ℤ_[p]) ^ 3 * α) = (p : ℤ_[p]) ^ 2 * ((p : ℤ_[p]) * α) := by ring
    have hc : (-108 : ℤ_[p]) * ((p : ℤ_[p]) * α) ^ 3
        = (p : ℤ_[p]) ^ (2 * 3) * (-4 * α ^ 3) := by subst hp3; push_cast; ring
    rw [hβ, show t + 12 = (t + 9) + 3 by omega,
      setOf_emultiplicity_Δ_nine_mul_eq_sqLevelSet hp3, hc, show t + 9 = 2 * 3 + (t + 3) by omega,
      PadicInt.sqLevelSet_pPow_mul_eq_image hunit 3 (t + 3)]
  ext a₆
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
  constructor
  · intro hmem
    have hΔ : emultiplicity (p : ℤ_[p]) (ofShortNF ((p : ℤ_[p]) ^ 3 * α) a₆).Δ
        = ((t + 12 : ℕ) : ℕ∞) := by
      obtain ⟨s, h4, -, hd⟩ := exists_emultiplicity_of_mem_stratFibre_three hp3 ht hmem
      rw [ha₄] at h4
      obtain rfl : s = 0 := by
        have : (3 : ℕ) = 4 * s + 3 := mod_cast h4
        omega
      rw [hd]
    obtain ⟨u, hu, hsplit⟩ := (mem_stratFibre_iff_splitResidue_three hp3 ht ha₄ hΔ).1 hmem
    obtain ⟨u', hu'lev, hu'eq⟩ : a₆ ∈ PadicInt.scaleByPPow 3 ''
        PadicInt.sqLevelSet (-4 * α ^ 3) (t + 3) := hlevel ▸ hΔ
    have heq : u' = u := by
      refine mul_left_cancel₀ (pow_ne_zero 3 hϖ) ?_
      rw [show (p : ℤ_[p]) ^ 3 * u' = PadicInt.scaleByPPow 3 u' from rfl, hu'eq, hu]
    subst heq
    exact ⟨u', ⟨hu'lev, hsplit⟩, by rw [PadicInt.scaleByPPow, hu]⟩
  · rintro ⟨u, ⟨hlev, hsplit⟩, rfl⟩
    have hΔ : emultiplicity (p : ℤ_[p])
        (ofShortNF ((p : ℤ_[p]) ^ 3 * α) (PadicInt.scaleByPPow 3 u)).Δ
        = ((t + 12 : ℕ) : ℕ∞) := (Set.ext_iff.1 hlevel _).2 ⟨u, hlev, rfl⟩
    exact (mem_stratFibre_iff_splitResidue_three hp3 ht ha₄ hΔ).2
      ⟨u, by rw [PadicInt.scaleByPPow], hsplit⟩

/-! ### Slices off the minimal storey -/

/-- The `a₆`-slice of `τ₃⁻¹((I_t, t)) ∖ σ₃(ℤ₃²)` is empty unless `v₃(a₄) = 3`. -/
theorem setOf_mem_stratFibre_diff_eq_empty_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) {a₄ : ℤ_[p]}
    (ha₄ : emultiplicity (p : ℤ_[p]) a₄ ≠ ((3 : ℕ) : ℕ∞)) :
    {a₆ : ℤ_[p] | (a₄, a₆) ∈ stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])}
      = (∅ : Set ℤ_[p]) :=
  Set.eq_empty_iff_forall_notMem.2 fun _a₆ hx =>
    ha₄ (emultiplicity_fst_eq_three_of_mem_diff hp3 ht hx.1 hx.2)

end WeierstrassCurve
