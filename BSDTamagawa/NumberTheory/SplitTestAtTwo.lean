/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.PadicHaarTwo
public import BSDTamagawa.NumberTheory.SmallPrimeStratum

/-!
# The split-multiplicative test at the even prime

At an odd prime the tangent quadratic of a nodal model splits iff `-c₆` is a square in the residue
field. At `p = 2` every element of the residue field `𝔽_2` is a square, and the criterion becomes:
for a nodal model over `ℤ_2`, the tangent quadratic splits iff `-c₆` is a square in `ℤ_2`, i.e.
`-c₆ ≡ 1 mod 8`. This file proves that criterion, the resulting description of the level-`t`
split-multiplicative stratum at `p = 2`, and the masses of a `2`-adic square level set cut by a
constraint that is constant on residue classes modulo `8`.

## Main results

* `PadicInt.isSquare_iff_pow_three_dvd_sub_one_of_eq_two`,
  `PadicInt.isSquare_iff_two_mul_toZModPow_four_of_eq_two`: a unit `c` of `ℤ_2` is a square iff
  `8 ∣ c - 1`, iff `2(c - 1) = 0` in `ZMod 16`.
* `PadicInt.volume_sqLevelSet_inter_of_unique_root_of_eq_two`,
  `PadicInt.volume_sqLevelSet_inter_of_no_root_of_eq_two`: the mass of a `2`-adic square level set
  with unit square centre, cut by a constraint constant on residue classes modulo `8`.
* `WeierstrassCurve.TateAlgorithm.Step2.residue_eq_zero_or_one_of_eq_two`: every element of the
  residue field of `ℤ_2` is `0` or `1`.
* `WeierstrassCurve.TateAlgorithm.Step2.tangentSplits_iff_dvd_translate_a₂_of_eq_two`: at a node,
  the tangent quadratic splits iff `2` divides the `a₂` of the Step-2 translate.
* `WeierstrassCurve.TateAlgorithm.Step2.tangentSplits_iff_isSquare_neg_c₆_of_eq_two`: for a nodal
  model over `ℤ_2`, the tangent quadratic splits iff `-c₆` is a square in `ℤ_2`.
* `WeierstrassCurve.run_kodaira_tamagawa_eq_iff_isSquare_of_eq_two`: for a nodal model over `ℤ_2`
  and `t ≥ 3`, `τ_2(W) = (I_t, t)` iff `v₂(Δ) = t` and `-c₆` is a square in `ℤ_2`.
-/

@[expose] public section

open CommRing Ideal

namespace PadicInt

open MeasureTheory

open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ### The `p = 2` square criterion, in divisibility and in `ZMod 16` -/

/-- **The `p = 2` square criterion as a divisibility:** a unit `c` of `ℤ_2` is a square iff
`8 ∣ c - 1`. -/
theorem isSquare_iff_pow_three_dvd_sub_one_of_eq_two (hp2 : p = 2) {c : ℤ_[p]} (hc : IsUnit c) :
    IsSquare c ↔ (p : ℤ_[p]) ^ 3 ∣ c - 1 := by
  rw [isSquare_iff_three_le_emultiplicity_sub_one_of_eq_two hp2 hc,
    show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) from rfl, ← pow_dvd_iff_le_emultiplicity]

/-- **An odd square is `≡ 1 mod 8`**, as a divisibility. -/
theorem pow_three_dvd_sq_sub_one_of_eq_two (hp2 : p = 2) {s : ℤ_[p]} (hs : IsUnit s) :
    (p : ℤ_[p]) ^ 3 ∣ s ^ 2 - 1 :=
  pow_dvd_of_le_emultiplicity (by
    refine le_trans ?_ (three_le_emultiplicity_sq_sub_one_of_eq_two hp2 hs); norm_num)

/-- **`8 ∣ x` read in `ZMod 16`.** At `p = 2`, `8 ∣ x` iff `2 x = 0` in `ZMod 16`. -/
theorem pow_three_dvd_iff_two_mul_toZModPow_four_of_eq_two (hp2 : p = 2) (x : ℤ_[p]) :
    (p : ℤ_[p]) ^ 3 ∣ x ↔ (2 : ZMod (p ^ 4)) * toZModPow 4 x = 0 := by
  have hcast : ((p : ℤ_[p]) * x) = ((p : ℕ) : ℤ_[p]) * x := by norm_num
  have h1 : (p : ℤ_[p]) ^ 3 ∣ x ↔ (p : ℤ_[p]) ^ 4 ∣ (p : ℤ_[p]) * x := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, by rw [hk]; ring⟩
    · obtain ⟨k, hk⟩ := h
      refine ⟨k, mul_left_cancel₀ (PadicInt.uniformizer_ne_zero (p := p)) ?_⟩
      rw [hk]; ring
  rw [h1, pow_dvd_iff_toZModPow_eq_zero, hcast, map_mul, map_natCast]
  subst hp2
  norm_num

/-- **The `p = 2` square criterion in `ZMod 16`:** a unit `c` of `ℤ_2` is a square iff
`2 (c - 1) = 0` in `ZMod 16`. -/
theorem isSquare_iff_two_mul_toZModPow_four_of_eq_two (hp2 : p = 2) {c : ℤ_[p]} (hc : IsUnit c) :
    IsSquare c ↔ (2 : ZMod (p ^ 4)) * (toZModPow 4 c - 1) = 0 := by
  rw [isSquare_iff_pow_three_dvd_sub_one_of_eq_two hp2 hc,
    pow_three_dvd_iff_two_mul_toZModPow_four_of_eq_two hp2, map_sub, map_one]

/-! ### `p^{-m}` as a power of `p⁻¹` -/

/-- `p^{-m} = (p⁻¹)^m` in `ℝ≥0∞`. -/
theorem zpow_neg_natCast_eq_inv_pow_two (m : ℕ) :
    (p : ℝ≥0∞) ^ (-(m : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ m :=
  (measure_span_pPow (p := p) m).symm.trans (measure_span_pPow' m)

/-! ### The two shells of a `p = 2` square level set, cut by a residue constraint -/

private theorem setOf_emultiplicity_sub_eq_preimage (s : ℤ_[p]) (m : ℕ) :
    {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - s) = (m : ℕ∞)}
      = (fun h => (-s) + h) ⁻¹' {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = (m : ℕ∞)} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [show (-s) + x = x - s from by ring]

/-- **The mass of the shell `{x | v_p(x - s) = m}`** is that of `{y | v_p(y) = m}`, namely
`(1 - p⁻¹)p^{-m}`. -/
theorem volume_setOf_emultiplicity_sub_eq (s : ℤ_[p]) (m : ℕ) :
    (volume : Measure ℤ_[p]) {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - s) = (m : ℕ∞)}
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ m := by
  rw [setOf_emultiplicity_sub_eq_preimage, measure_preimage_add, volume_setOf_emultiplicity_eq]

variable {Q : Set ℤ_[p]}

private theorem shell_subset_of_mem (hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z →
    (y ∈ Q ↔ z ∈ Q)) {d : ℤ_[p]} {m : ℕ} (hm : 3 ≤ m) (hd : d ∈ Q) :
    {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - d) = (m : ℕ∞)} ∩ Q
      = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - d) = (m : ℕ∞)} :=
  Set.inter_eq_left.2 fun x hx => (hQ x d (pow_dvd_of_le_emultiplicity (by
    rw [(hx : _ = (m : ℕ∞))]; exact_mod_cast hm))).2 hd

private theorem shell_inter_eq_empty_of_notMem (hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z →
    (y ∈ Q ↔ z ∈ Q)) {d : ℤ_[p]} {m : ℕ} (hm : 3 ≤ m) (hd : d ∉ Q) :
    {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - d) = (m : ℕ∞)} ∩ Q = (∅ : Set ℤ_[p]) :=
  Set.eq_empty_iff_forall_notMem.2 fun x hx => hd ((hQ x d (pow_dvd_of_le_emultiplicity (by
    rw [(hx.1 : _ = (m : ℕ∞))]; exact_mod_cast hm))).1 hx.2)

private theorem shell_add_eq_shell_sub_neg (s : ℤ_[p]) (m : ℕ) :
    {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x + s) = (m : ℕ∞)}
      = {x : ℤ_[p] | emultiplicity (p : ℤ_[p]) (x - -s) = (m : ℕ∞)} := by
  ext x; simp only [Set.mem_ofPred_eq, sub_neg_eq_add]

/-- **One of the two `p = 2` shells kept.** For a unit `c = s²`, a constraint `Q` constant on
residue classes modulo `8`, and `m ≥ 3`, if exactly one of `s`, `-s` lies in `Q` then

  `μ₂(sqLevelSet c (m + 1) ∩ Q) = (1 - 2⁻¹) 2^{-m}`. -/
theorem volume_sqLevelSet_inter_of_unique_root_of_eq_two (hp2 : p = 2) {c s : ℤ_[p]}
    (hc : IsUnit c) (hs : c = s * s)
    (hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z → (y ∈ Q ↔ z ∈ Q))
    (hone : (s ∈ Q ∧ -s ∉ Q) ∨ (s ∉ Q ∧ -s ∈ Q)) {m : ℕ} (hm : 3 ≤ m) :
    (volume : Measure ℤ_[p]) (sqLevelSet c (m + 1) ∩ Q)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ m := by
  rw [sqLevelSet_eq_union_of_eq_two hp2 hc hs (by omega : 2 ≤ m), Set.union_inter_distrib_right,
    shell_add_eq_shell_sub_neg]
  rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [shell_subset_of_mem hQ hm h1, shell_inter_eq_empty_of_notMem hQ hm h2, Set.union_empty,
      volume_setOf_emultiplicity_sub_eq]
  · rw [shell_inter_eq_empty_of_notMem hQ hm h1, shell_subset_of_mem hQ hm h2, Set.empty_union,
      volume_setOf_emultiplicity_sub_eq]

/-- **Neither of the two `p = 2` shells kept.** For a unit `c = s²`, a constraint `Q` constant on
residue classes modulo `8` containing neither `s` nor `-s`, and `m ≥ 3`, the intersection
`sqLevelSet c (m + 1) ∩ Q` has mass `0`. -/
theorem volume_sqLevelSet_inter_of_no_root_of_eq_two (hp2 : p = 2) {c s : ℤ_[p]}
    (hc : IsUnit c) (hs : c = s * s)
    (hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z → (y ∈ Q ↔ z ∈ Q))
    (hnone : s ∉ Q ∧ -s ∉ Q) {m : ℕ} (hm : 3 ≤ m) :
    (volume : Measure ℤ_[p]) (sqLevelSet c (m + 1) ∩ Q) = 0 := by
  rw [sqLevelSet_eq_union_of_eq_two hp2 hc hs (by omega : 2 ≤ m), Set.union_inter_distrib_right,
    shell_add_eq_shell_sub_neg, shell_inter_eq_empty_of_notMem hQ hm hnone.1,
    shell_inter_eq_empty_of_notMem hQ hm hnone.2, Set.union_empty, measure_empty]

end PadicInt

/-! ### The split test at `p = 2` -/

namespace WeierstrassCurve.TateAlgorithm.Step2

variable {p : ℕ} [Fact p.Prime]

/-- **The residue field of `ℤ_2` is `𝔽_2`:** every element is `0` or `1`. -/
theorem residue_eq_zero_or_one_of_eq_two (hp2 : p = 2)
    (y : ℤ_[p] ⧸ span {(p : ℤ_[p])}) : y = 0 ∨ y = 1 := by
  rw [← mod_out y]
  by_cases h : (p : ℤ_[p]) ∣ y.out
  · exact Or.inl ((mod_eq_zero _ _).2 h)
  · refine Or.inr ?_
    have hu : IsUnit y.out :=
      not_not.1 fun hnu => h (PadicInt.dvd_iff_not_isUnit.2 hnu)
    have h8 := PadicInt.dvd_sub_one_of_isUnit_of_eq_two hp2 hu
    rw [← sub_eq_zero, ← map_one (mod (p : ℤ_[p])), ← map_sub, mod_eq_zero]
    exact h8

/-- `2 = 0` in the residue field at `p = 2`. -/
theorem residue_two_eq_zero_of_eq_two (hp2 : p = 2) :
    (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
  rw [← map_ofNat (mod (p : ℤ_[p])) 2, mod_eq_zero]
  exact ⟨1, by subst hp2; push_cast; ring⟩

variable {W : WeierstrassCurve ℤ_[p]}

/-- **The split test at `p = 2` is the parity of the translate's `a₂`.** On a model whose Step-2
translate has `b₂` a unit, the tangent quadratic splits exactly when `2` divides the translate's
`a₂`. -/
theorem tangentSplits_iff_dvd_translate_a₂_of_eq_two (hp2 : p = 2)
    (hb₂ : ¬ (p : ℤ_[p]) ∣ (translate (p : ℤ_[p]) W).b₂) :
    TangentSplits (p : ℤ_[p]) W ↔ (p : ℤ_[p]) ∣ (translate (p : ℤ_[p]) W).a₂ := by
  have h2 : (2 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := residue_two_eq_zero_of_eq_two hp2
  have h4 : (4 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
    rw [show (4 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 2 * 2 from by norm_num, h2, mul_zero]
  set A := mod (p : ℤ_[p]) (translate (p : ℤ_[p]) W).a₁ with hA
  set B := mod (p : ℤ_[p]) (translate (p : ℤ_[p]) W).a₂ with hB
  have hb₂' : A ^ 2 ≠ 0 := by
    intro h0
    refine hb₂ ((mod_eq_zero _ _).1 ?_)
    rw [WeierstrassCurve.b₂]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    rw [← hA, ← hB, h0, h4, zero_mul, add_zero]
  have hA1 : A = 1 := by
    rcases residue_eq_zero_or_one_of_eq_two hp2 A with h | h
    · exact absurd (by rw [h]; ring) hb₂'
    · exact h
  rw [tangentSplits_iff_exists_root, ← hA, ← hB, hA1, ← mod_eq_zero, ← hB]
  refine ⟨fun ⟨y, hy⟩ => ?_, fun h0 => ⟨0, by rw [h0]; ring⟩⟩
  rcases residue_eq_zero_or_one_of_eq_two hp2 y with h | h
  · rw [h] at hy
    rw [← neg_eq_zero]
    linear_combination hy
  · rw [h] at hy
    rw [← neg_eq_zero]
    linear_combination hy - h2

/-- **The invariant split criterion at `p = 2`.** At a nodal model over `ℤ_2` (`2 ∣ Δ`, `2 ∤ c₄`)
the tangent quadratic splits exactly when `-c₆` is a square in `ℤ_2`. -/
theorem tangentSplits_iff_isSquare_neg_c₆_of_eq_two (hp2 : p = 2)
    (hΔ : (p : ℤ_[p]) ∣ W.Δ) (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) :
    TangentSplits (p : ℤ_[p]) W ↔ IsSquare (-W.c₆) := by
  have hv := hasValuation_translate hΔ
  have hb₄ : (p : ℤ_[p]) ∣ (translate (p : ℤ_[p]) W).b₄ := by simpa using hv.b₄
  have hb₆ : (p : ℤ_[p]) ∣ (translate (p : ℤ_[p]) W).b₆ := by simpa using hv.b₆
  have hb₂ : ¬ (p : ℤ_[p]) ∣ (translate (p : ℤ_[p]) W).b₂ := not_dvd_translate_b₂ hΔ hc₄
  have hb₂u : IsUnit (translate (p : ℤ_[p]) W).b₂ :=
    not_not.1 fun h => hb₂ (PadicInt.dvd_iff_not_isUnit.2 h)
  have ha₁u : IsUnit (translate (p : ℤ_[p]) W).a₁ := by
    refine not_not.1 fun hnu => hb₂ ?_
    obtain ⟨j, hj⟩ := PadicInt.dvd_iff_not_isUnit.2 hnu
    refine ⟨(p : ℤ_[p]) * j ^ 2 + 2 * (translate (p : ℤ_[p]) W).a₂, ?_⟩
    rw [WeierstrassCurve.b₂, hj]
    subst hp2
    push_cast
    ring
  have hkey : (p : ℤ_[p]) ^ 3 ∣ (-W.c₆) - (translate (p : ℤ_[p]) W).b₂ := by
    obtain ⟨u, hu⟩ := PadicInt.pow_three_dvd_sq_sub_one_of_eq_two hp2 hb₂u
    obtain ⟨k, hk⟩ := hb₄
    obtain ⟨l, hl⟩ := hb₆
    refine ⟨(translate (p : ℤ_[p]) W).b₂ * u - 9 * (translate (p : ℤ_[p]) W).b₂ * k + 54 * l, ?_⟩
    rw [← translate_c₆ (p : ℤ_[p]) W, WeierstrassCurve.c₆]
    subst hp2
    push_cast at hu hk hl ⊢
    linear_combination (translate ((2 : ℕ) : ℤ_[2]) W).b₂ * hu
      - 36 * (translate ((2 : ℕ) : ℤ_[2]) W).b₂ * hk + 216 * hl
  have hc₆u : IsUnit (-W.c₆) :=
    PadicInt.isUnit_of_dvd_sub hb₂u ((dvd_pow_self _ three_ne_zero).trans hkey)
  obtain ⟨u, hu⟩ := PadicInt.pow_three_dvd_sq_sub_one_of_eq_two hp2 ha₁u
  rw [tangentSplits_iff_dvd_translate_a₂_of_eq_two hp2 hb₂,
    PadicInt.isSquare_iff_pow_three_dvd_sub_one_of_eq_two hp2 hc₆u]
  constructor
  · rintro ⟨j, hj⟩
    have h1 : (p : ℤ_[p]) ^ 3 ∣ (translate (p : ℤ_[p]) W).b₂ - 1 := by
      refine ⟨u + j, ?_⟩
      rw [WeierstrassCurve.b₂, hj]
      subst hp2
      push_cast at hu ⊢
      linear_combination hu
    convert dvd_add hkey h1 using 1
    ring
  · intro h
    obtain ⟨v, hv⟩ : (p : ℤ_[p]) ^ 3 ∣ (translate (p : ℤ_[p]) W).b₂ - 1 := by
      convert dvd_sub h hkey using 1
      ring
    rw [WeierstrassCurve.b₂] at hv
    refine ⟨v - u, mul_left_cancel₀ (pow_ne_zero 2 (PadicInt.uniformizer_ne_zero (p := p))) ?_⟩
    subst hp2
    push_cast at hu hv ⊢
    linear_combination hv - hu

end WeierstrassCurve.TateAlgorithm.Step2

/-! ### The level-`t` split-multiplicative stratum at `p = 2` -/

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- **The level-`t` split-multiplicative stratum at `p = 2`, in invariant form.** For a nodal model
over `ℤ_2` and `t ≥ 3`,

  `τ_2(W) = (I_t, t)  ↔  v₂(Δ) = t` and `-c₆` is a square in `ℤ_2`. -/
theorem run_kodaira_tamagawa_eq_iff_isSquare_of_eq_two (hp2 : p = 2) {W : WeierstrassCurve ℤ_[p]}
    (hΔ : W.Δ ≠ 0) (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) {t : ℕ} (ht : 3 ≤ t) :
    ((TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I t ∧
        (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = t) ↔
      emultiplicity (p : ℤ_[p]) W.Δ = (t : ℕ∞) ∧ IsSquare (-W.c₆) := by
  rw [run_kodaira_tamagawa_eq_iff_of_nodal hΔ hc₄ ht]
  refine and_congr_right fun hn => ?_
  exact TateAlgorithm.Step2.tangentSplits_iff_isSquare_neg_c₆_of_eq_two hp2
    (dvd_Δ_of_emultiplicity_eq (by omega) hn) hc₄

end WeierstrassCurve
