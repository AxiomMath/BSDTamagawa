/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildIZeroStarAtThree
public import BSDTamagawa.GOTTable.InStarFlipRunAtTwo
public import BSDTamagawa.GOTTable.InStarTamagawaTwoFour

/-!
# Family A at `p = 3`: the `Iₘ*` strata with `m ≥ 1`

The `Iₘ*` strata with `m ≥ 1` at `p = 3` lie in the cell `v₃(a₄) = 1`, `v₃(a₆) = 0`. Writing
`a₄ = 3α` with `α` a unit, the discriminant is

  `Δ = −16(4a₄³ + 27a₆²) = −16 · 27 · (4α³ + a₆²)`,

and the level is `m = v₃(4α³ + a₆²) − 3`, so the level-`m` stratum is a cylinder whose depth grows
linearly in `m`. The union over all `m ≥ 1` is nevertheless cut out by the bounded condition

  `3 ∤ α`  and  `3⁴ ∣ 4α³ + a₆²`,

that is, by fifty-four of the `6561` residue classes of `(α, a₆)` modulo `81`. Pushed onto the
coefficient plane by `a₄ = 3α` this is a set of mass `3⁻¹ · 54 · 3⁻⁸ = 2/729`.

Over `ℤ₃` the quantity `4α³ + a₆²` factors as `(a₆ − ν)(a₆ + ν)` with `ν` a square root of `−4α³`,
which exists exactly when `α ≡ 2 (mod 3)`. Since `2ν` is a unit, at most one of the two factors is
divisible by `3`, so each admissible `α` has precisely two classes of `a₆` modulo `81`.

On every nonsingular point of the locus, Steps 1 to 6 of Tate's algorithm pass, the Step-6 cubic
has a double but no triple root, and Step 7 answers `Iₘ*` with `m ≥ 1` and Tamagawa number `2` or
`4`, without the level being determined.

## Main definitions

* `WeierstrassCurve.FamilyAThree.Res`: the residue condition on `(α, a₆)` modulo `81`.
* `WeierstrassCurve.FamilyAThree.residues`: the fifty-four classes satisfying it.
* `WeierstrassCurve.FamilyAThree.locus`: the Family A locus of the coefficient plane.

## Main results

* `WeierstrassCurve.FamilyAThree.card_residues`: there are fifty-four classes.
* `WeierstrassCurve.FamilyAThree.volume_locus`: the locus has mass `2/729`.
* `WeierstrassCurve.FamilyAThree.exists_form_of_mem_locus`: a point of the locus has `a₄ = 3α` with
  `3 ∤ α`, `3 ∤ a₆` and `3⁴ ∣ 4α³ + a₆²`.
* `WeierstrassCurve.FamilyAThree.locus_subset_notMem_range`: the locus contains no
  `(3⁴, 3⁶)`-dilate.
* `WeierstrassCurve.FamilyAThree.dvd_add_of_step2_at_three`: the Step-2 shift satisfies
  `r ≡ −a₆ (mod 3)`.
* `WeierstrassCurve.FamilyAThree.step2_data`: the Step-2 translate of a point of the locus, with
  `(α + r²)/3` and `(a₆ + 3rα + r³)/27` exact divisions.
* `WeierstrassCurve.FamilyAThree.three_dvd_cubic_combo`: the double-root congruence
  `3 ∣ r²C² − C³ − r³D`.
* `WeierstrassCurve.FamilyAThree.step6_ok_of_mem_locus`: Step 6 returns `ok` and the Step-6 cubic
  has no triple root.
* `WeierstrassCurve.FamilyAThree.exists_kodairaSymbol_eq_Istar_of_mem_locus`: on a nonsingular
  point of the locus the Kodaira symbol is `Iₘ*` with `m ≥ 1`.
* `WeierstrassCurve.FamilyAThree.tamagawaNumber_eq_two_or_four_of_mem_locus`: there the Tamagawa
  number is `2` or `4`.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction
open CommRing Ideal TateAlgorithm

namespace FamilyAThree

/-! ### The fifty-four residue classes modulo `81`

The pair reduced is `(α, a₆)` with `a₄ = 3α`: the condition `3⁴ ∣ 4α³ + a₆²` reads `α` to depth
`4`, hence `a₄` to depth `5`. -/

/-- **The residue condition cutting out Family A at `3`**, on the pair `(α, a₆)` where `a₄ = 3α`:
`3 ∤ α`, and `4α³ + a₆² = 0` in `ZMod 81`, which is `3⁴ ∣ 4α³ + a₆²` for any lift.

It implies `3 ∤ a₆` (`res_cast_snd`) and `α ≡ 2 (mod 3)`: if `3 ∣ a₆` then
`4α³ + a₆² ≡ 4α³ ≡ α (mod 3)` is a unit, and if `α ≡ 1` then `−4α³ ≡ 2` is a non-square so
`4α³ + a₆²` is again a unit. -/
abbrev Res (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) : Prop :=
  (ZMod.cast c.1 : ZMod 3) ≠ 0 ∧ 4 * c.1 ^ 3 + c.2 ^ 2 = 0

/-- **The classes of `(α, a₆)` modulo `81` cutting out Family A at `3`**: those satisfying
`Res`. -/
noncomputable def residues : Finset (ZMod (3 ^ 4) × ZMod (3 ^ 4)) :=
  Finset.univ.filter Res

/-- A class lies in `residues` exactly when it satisfies `Res`. -/
theorem mem_residues_iff (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) : c ∈ residues ↔ Res c := by
  simp [residues]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` ranges over all `6561` pairs modulo `81`, evaluating a cube in `ZMod 81` in each.
/-- **There are fifty-four classes**: twenty-seven admissible `α`, those with `α ≡ 2 (mod 3)`, each
with exactly two `a₆`, because `4α³ + a₆²` factors as `(a₆ − ν)(a₆ + ν)` with `2ν` a unit. -/
theorem card_residues : residues.card = 54 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` ranges over all `6561` pairs modulo `81`.
/-- **`3 ∤ a₆` on the locus**: `a₆` is a unit, so `v₃(a₆) = 0` and the cell is `C(1, 0)`. -/
theorem res_cast_snd (c : ZMod (3 ^ 4) × ZMod (3 ^ 4)) (h : Res c) :
    (ZMod.cast c.2 : ZMod 3) ≠ 0 := by
  revert c; decide

/-! ### The locus, its measurability and its mass -/

/-- **The Family A locus of the coefficient plane at `3`**: the image under `(α, a₆) ↦ (3α, a₆)` of
the fifty-four-class cylinder modulo `81`. -/
noncomputable def locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.scaleProdByPPow 1 0 ''
    (PadicInt.redPairPow 3 4 ⁻¹' (residues : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4))))

/-- The Family A locus at `3` is measurable. -/
theorem measurableSet_locus : MeasurableSet locus :=
  (PadicInt.measurableEmbedding_scaleProdByPPow 1 0).measurableSet_image.2
    (PadicInt.measurableSet_preimage_redPairPow 4 residues)

/-- `54 · 3⁻⁸ = 54/6561 = 2/243`, in the shape `PadicInt.volume_preimage_redPairPow` produces. -/
theorem fiftyFour_mul_inv_pow_eight_eq :
    ((54 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 4) = 2 / 243 := by
  rw [show ((54 : ℕ) : ℝ≥0∞) = 54 by norm_num, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 4) = 6561 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the Family A locus at `3` is `2/729`**: the dilation `(α, a₆) ↦ (3α, a₆)` costs a
factor `3⁻¹` on top of the cylinder's `54 · 3⁻⁸ = 2/243`. -/
theorem volume_locus : (volume : Measure (ℤ_[3] × ℤ_[3])) locus = 2 / 729 := by
  rw [locus, PadicInt.measure_image_scaleProdByPPow, PadicInt.volume_preimage_redPairPow,
    card_residues, fiftyFour_mul_inv_pow_eight_eq,
    show ((1 : ℕ) + (0 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) by norm_num,
    PadicInt.zpow_neg_natCast_eq_inv_pow, pow_one,
    show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num]
  rw [show (3 : ℝ≥0∞)⁻¹ = 1 / 3 from by rw [one_div], enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Membership, the algebraic shape, and minimality -/

set_option maxRecDepth 100000 in
/-- Membership of `locus`, with the dilation `a₄ = 3α` made explicit and the residue condition read
on `(α, a₆)`. -/
theorem mem_locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ locus ↔ ∃ α : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) * α ∧
      Res (PadicInt.toZModPow 4 α, PadicInt.toZModPow 4 x.2) := by
  have hcoe : ∀ c : ZMod (3 ^ 4) × ZMod (3 ^ 4),
      c ∈ (residues : Set (ZMod (3 ^ 4) × ZMod (3 ^ 4))) ↔ Res c :=
    fun c => (Finset.mem_coe).trans (mem_residues_iff c)
  constructor
  · rintro ⟨⟨α, e⟩, hmem, rfl⟩
    refine ⟨α, ?_, ?_⟩
    · rw [PadicInt.scaleProdByPPow, Prod.map_fst, PadicInt.scaleByPPow, pow_one]
    · rw [PadicInt.scaleProdByPPow, Prod.map_snd, PadicInt.scaleByPPow, pow_zero, one_mul]
      exact (hcoe _).1 hmem
  · rintro ⟨α, h1, hres⟩
    refine ⟨(α, x.2), (hcoe _).2 hres, Prod.ext ?_ ?_⟩
    · rw [PadicInt.scaleProdByPPow, Prod.map_fst, PadicInt.scaleByPPow, pow_one]
      exact h1.symm
    · rw [PadicInt.scaleProdByPPow, Prod.map_snd, PadicInt.scaleByPPow, pow_zero, one_mul]

/-- **The algebraic shape of a point of the locus**: `a₄ = 3α` with `α` a unit, `a₆` a unit, and
`3⁴ ∣ 4α³ + a₆²`, the last being exactly `v₃(Δ) ≥ 7`. -/
theorem exists_form_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) :
    ∃ α : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) * α ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ x.2 ∧ ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ 4 * α ^ 3 + x.2 ^ 2 := by
  obtain ⟨α, h1, hres⟩ := mem_locus_iff.1 hx
  have key : ∀ y : ℤ_[3], (ZMod.cast (PadicInt.toZModPow 4 y) : ZMod 3) ≠ 0 →
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ y := by
    intro y hy hdvd
    have h2 : PadicInt.toZModPow 1 y = 0 := by
      rwa [← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    exact hy (by simpa using (PadicInt.cast_toZModPow 1 4 (by norm_num) y).trans h2)
  refine ⟨α, h1, key α hres.1, key x.2 (res_cast_snd _ hres), ?_⟩
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_pow, map_ofNat]
  exact hres.2

/-- **The whole locus lies in the minimal storey.** `v₃(a₄) = 1`, so `3⁴ ∤ a₄` and no point is a
`(3⁴, 3⁶)`-dilate. -/
theorem locus_subset_notMem_range :
    ∀ x ∈ locus, x ∉ Set.range
      (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  intro x hx
  obtain ⟨α, h1, hα, -, -⟩ := exists_form_of_mem_locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => hα ?_
  rw [h1] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨((3 : ℕ) : ℤ_[3]) ^ 2 * c, mul_left_cancel₀ PadicInt.uniformizer_ne_zero ?_⟩
  rw [hc]
  ring

/-! ### The Step-2 translate: where the singular point sits

The shift `(r, t)` chosen by `Step2.translate` is determined only through the two divisibilities
`Step2.hasValuation_translate` records. On this family these determine its residues, by the
Frobenius identity of `𝔽₃`. -/

variable {p : ℕ} [Fact p.Prime]

/-- The `a₁`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₁ (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
  simp [variableChange_a₁]

/-- The `a₂`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₂ (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
  simp [variableChange_a₂]

/-- The `a₃`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₃ (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = 2 * t := by
  simp [variableChange_a₃]

/-- The `a₄`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₄ (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = a₄ + 3 * r ^ 2 := by
  simp [variableChange_a₄]

/-- The `a₆`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_a₆ (a₄ a₆ r t : ℤ_[p]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
  simp [variableChange_a₆]

/-- **The Step-2 shift is `r ≡ −a₆ (mod 3)`.** On `ofShortNF a₄ a₆` at `p = 3` with `3 ∣ a₄`, an
integral translate `⟨1, r, 0, t⟩ • W` whose `a₃` and `a₆` are divisible by `3` has `3 ∣ r + a₆` and
`3 ∣ t`. -/
theorem dvd_add_of_step2_at_three (hp3 : p = 3) {a₄ a₆ r t : ℤ_[p]} (h₄ : (p : ℤ_[p]) ∣ a₄)
    (ha₃ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃)
    (ha₆ : (p : ℤ_[p]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆) :
    (p : ℤ_[p]) ∣ r + a₆ ∧ (p : ℤ_[p]) ∣ t := by
  rw [smulOne_a₃] at ha₃
  rw [smulOne_a₆] at ha₆
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two (hp3 ▸ (by decide : Odd 3))
  have ht : (p : ℤ_[p]) ∣ t := h2.dvd_mul_left.mp ha₃
  refine ⟨?_, ht⟩
  have ht2 : (p : ℤ_[p]) ∣ t ^ 2 := ht.trans (dvd_pow_self t two_ne_zero)
  have hsum : (p : ℤ_[p]) ∣ a₆ + r ^ 3 := by
    have h := dvd_add (dvd_sub ha₆ (h₄.mul_left r)) ht2
    have e : a₆ + r * a₄ + r ^ 3 - t ^ 2 - r * a₄ + t ^ 2 = a₆ + r ^ 3 := by ring
    rwa [e] at h
  have hd : (p : ℤ_[p]) ∣ (a₆ + r ^ 3) - (r ^ 3 - r) :=
    dvd_sub hsum (three_dvd_cube_sub_self hp3 r)
  have e2 : (a₆ + r ^ 3) - (r ^ 3 - r) = r + a₆ := by ring
  rwa [e2] at hd

/-- **`α ≡ −1 (mod 3)` on the locus**: if `3 ∤ e` and `3 ∣ 4α³ + e²` then `α = −1 + 3n` for some
`n`. -/
theorem alpha_eq_neg_one_add {α e : ℤ_[3]} (he : ¬ ((3 : ℕ) : ℤ_[3]) ∣ e)
    (h : ((3 : ℕ) : ℤ_[3]) ∣ 4 * α ^ 3 + e ^ 2) :
    ∃ n : ℤ_[3], α = -1 + ((3 : ℕ) : ℤ_[3]) * n := by
  suffices hd : ((3 : ℕ) : ℤ_[3]) ∣ α + 1 by
    obtain ⟨n, hn⟩ := hd
    exact ⟨n, by linear_combination hn⟩
  rw [PadicInt.dvd_iff_toZMod_eq_zero] at he h ⊢
  rw [map_add, map_mul, map_pow, map_pow, map_ofNat] at h
  rw [map_add, map_one]
  revert h he
  generalize PadicInt.toZMod (α : ℤ_[3]) = A
  generalize PadicInt.toZMod (e : ℤ_[3]) = E
  revert A E
  decide

/-- The `b₂`-coefficient of an integral translate with `s = 0` of a short model. -/
private theorem smulOne_b₂ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₂ = 12 * r := by
  simp [WeierstrassCurve.b₂, variableChange_a₁, variableChange_a₂]
  ring

/-- The `b₆`-coefficient of an integral translate with `s = 0` of a short model: `t²` cancels. -/
private theorem smulOne_b₆ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₆ = 4 * (a₆ + r * a₄ + r ^ 3) := by
  simp [WeierstrassCurve.b₆, variableChange_a₃, variableChange_a₆]
  ring

/-- The `b₈`-coefficient of an integral translate with `s = 0` of a short model: again the `t²`
cancels, leaving `12r(a₆ + ra₄ + r³) − (a₄ + 3r²)²`. -/
private theorem smulOne_b₈ (a₄ a₆ r t : ℤ_[3]) :
    ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).b₈
      = 12 * r * (a₆ + r * a₄ + r ^ 3) - (a₄ + 3 * r ^ 2) ^ 2 := by
  simp [WeierstrassCurve.b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring

/-! ### The Step-2 translate on the locus, in full

The translate `Step2.translate 3 (ofShortNF 3α a₆)` is described in the parameters `α = −1 + 3n`,
`a₆² = −4α³ + 81K`, `r = −a₆ + 3ρ`, `t = 3τ`. The quantities `C = (α + r²)/3` and
`D = (a₆ + 3rα + r³)/27` are exact divisions: `3 ∣ α + r²` because `r ≡ −a₆` and `a₆² ≡ −4α³ ≡ −α`,
while `27 ∣ a₆ + 3rα + r³` uses all of `81 ∣ 4α³ + a₆²` and `α ≡ −1`. -/

/-- **The Step-2 translate of a Family A point at `p = 3`, in full.** It is `⟨1, r, 0, t⟩ • W` with
`r = −a₆ + 3ρ`, `t = 3τ`, `a₄ = 3(−1 + 3n)`, `a₆² = −4(−1 + 3n)³ + 81K`, and the divisions
`C = (α + r²)/3` and `D = (a₆ + ra₄ + r³)/27` exact, with the explicit witnesses

  `C = 1 + 27K − 11n + 3ρ² + 36n² − 2a₆ρ − 36n³`,
  `D = a₆n(1 − 2n)² − 3Ka₆ + ρ(1 + 27K − 11n + 36n² − 36n³) − a₆ρ² + ρ³`. -/
theorem step2_data {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) :
    ∃ r t ρ τ n K C D : ℤ_[3],
      Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
          = (VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2 ∧
        r = -x.2 + 3 * ρ ∧ t = 3 * τ ∧ x.1 = 3 * (-1 + 3 * n) ∧
        x.2 ^ 2 = -4 * (-1 + 3 * n) ^ 3 + 81 * K ∧
        (-1 + 3 * n) + r ^ 2 = 3 * C ∧ x.2 + r * x.1 + r ^ 3 = 27 * D := by
  classical
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨α, h1, hα, he, hdeep⟩ := exists_form_of_mem_locus hx
  obtain ⟨n, hn⟩ := alpha_eq_neg_one_add he
    (dvd_trans (dvd_pow_self _ (by norm_num : 4 ≠ 0)) hdeep)
  obtain ⟨K, hK⟩ := hdeep
  rw [hcast] at h1 hn hK
  have hΔd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF x.1 x.2).Δ := by
    refine ⟨-16 * (36 * α ^ 3 + 9 * x.2 ^ 2), ?_⟩
    rw [ofShortNF_Δ, h1, hcast]; ring
  obtain ⟨r, t, hT⟩ : ∃ r t : ℤ_[3], Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
      = (VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2 := ⟨_, _, dite_eq_left hΔd⟩
  have hval := Step2.hasValuation_translate hΔd
  have ha₃ : ((3 : ℕ) : ℤ_[3]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2).a₃ := by
    rw [← hT]; simpa using hval.a₃
  have ha₆ : ((3 : ℕ) : ℤ_[3]) ∣ ((VariableChange.mk 1 r 0 t) • ofShortNF x.1 x.2).a₆ := by
    rw [← hT]; simpa using hval.a₆
  obtain ⟨hre, ht⟩ := dvd_add_of_step2_at_three (p := 3) rfl ⟨α, h1⟩ ha₃ ha₆
  obtain ⟨ρ, hρ⟩ := hre
  obtain ⟨τ, hτ⟩ := ht
  rw [hcast] at hρ hτ
  have hr : r = -x.2 + 3 * ρ := by linear_combination hρ
  have hK' : x.2 ^ 2 = -4 * (-1 + 3 * n) ^ 3 + 81 * K := by
    rw [← hn]; linear_combination hK
  refine ⟨r, t, ρ, τ, n, K,
    1 + 27 * K - 11 * n + 3 * ρ ^ 2 + 36 * n ^ 2 - 2 * x.2 * ρ - 36 * n ^ 3,
    x.2 * n * (1 - 2 * n) ^ 2 - 3 * K * x.2
      + ρ * (1 + 27 * K - 11 * n + 36 * n ^ 2 - 36 * n ^ 3) - x.2 * ρ ^ 2 + ρ ^ 3,
    hT, hr, by linear_combination hτ, by rw [h1, hn], hK', ?_, ?_⟩
  · rw [hr]; linear_combination hK'
  · rw [hr, h1, hn]; linear_combination (9 * ρ - x.2) * hK'

/-! ### Steps 1 to 5 traverse

On the Step-2 translate, `3 ∣ b₂`, `9 ∣ a₆`, `27 ∣ b₈` and `27 ∣ b₆`, since `b₂ = 12r`,
`a₆ = 27D − 9τ²`, `b₆ = 4·27D` and `b₈ = 12r·27D − 81C²`. -/

/-- **Steps 1 to 5 all pass on a Family A point at `p = 3`**, and the curve they hand on is the
Step-2 translate of the input. -/
theorem step5_run_eq_ok_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) :
    Step5.run ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
      = Except.ok (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨r, t, ρ, τ, n, K, C, D, hT, hr, ht, h1, hK, hC, hD⟩ := step2_data hx
  have hΔd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF x.1 x.2).Δ := by
    refine ⟨-16 * (36 * (-1 + 3 * n) ^ 3 + 9 * x.2 ^ 2), ?_⟩
    rw [ofShortNF_Δ, h1, hcast]; ring
  refine FlipRun.step5_run_eq_ok_of_tests hΔd ?_ ?_ ?_ ?_
  · rw [hT, smulOne_b₂, hcast]; exact ⟨4 * r, by ring⟩
  · rw [hT, smulOne_a₆, ht, hcast]
    exact ⟨3 * D - τ ^ 2, by linear_combination hD⟩
  · have hx1 : x.1 + 3 * r ^ 2 = 9 * C := by rw [h1]; linear_combination 3 * hC
    rw [hT, smulOne_b₈, hcast]
    refine ⟨12 * r * D - 3 * C ^ 2, ?_⟩
    linear_combination 12 * r * hD - (x.1 + 3 * r ^ 2 + 9 * C) * hx1
  · rw [hT, smulOne_b₆, hcast]
    exact ⟨4 * D, by linear_combination 4 * hD⟩

/-! ### The double-root condition, reduced to two exact identities

Step 6's cubic on the Step-2 translate is `⟨1, b, c, d⟩` with `b = r̄`, `c = C̄`, `d = D̄` — the
residues of `r`, `C = (α + r²)/3` and `D = (a₆ + 3rα + r³)/27`. In characteristic `3`
`hasDoubleRoot_of_a_eq_one` loses its `27d²` and `18bcd` terms and `4 = 1`, so the test is
`b²c² = c³ + b³d`, i.e. `3 ∣ r²C² − C³ − r³D`.

This divisibility follows from the deep congruence through two polynomial identities, valid in any
commutative ring:

  `3r²P² − P³ − r³S = r⁶ − r³a₆ − α³`   where `P = α + r²`, `S = a₆ + 3rα + r³`,
  `4(r⁶ − r³a₆ − α³) = (2r³ − a₆)² − (a₆² + 4α³)`,

together with `9 ∣ 2r³ − a₆`, which also requires `81 ∣ 4α³ + a₆²`. -/

/-- **The double-root congruence**, as pure arithmetic in `ℤ_3`: from the deep condition
`a₆² = −4α³ + 81K` with `α = −1 + 3n`, `r = −a₆ + 3ρ`, and the two exact divisions `3C = α + r²`
and `27D = a₆ + 3rα + r³`, one gets `3 ∣ r²C² − C³ − r³D`. -/
theorem three_dvd_cubic_combo {e n K r ρ C D : ℤ_[3]}
    (hr : r = -e + 3 * ρ) (hK : e ^ 2 = -4 * (-1 + 3 * n) ^ 3 + 81 * K)
    (hC : (-1 + 3 * n) + r ^ 2 = 3 * C)
    (hD : e + r * (3 * (-1 + 3 * n)) + r ^ 3 = 27 * D) :
    (3 : ℤ_[3]) ∣ r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D := by
  have hZ : 2 * r ^ 3 - e = 9 * (8 * ρ - e + 162 * ρ * K - 72 * n * ρ - 18 * e * K + 8 * e * n
      + 6 * ρ ^ 3 + 216 * n ^ 2 * ρ - 6 * e * ρ ^ 2 - 24 * e * n ^ 2 - 216 * n ^ 3 * ρ
      + 24 * e * n ^ 3) := by
    rw [hr]; linear_combination (18 * ρ - 2 * e) * hK
  obtain ⟨Z, hZ'⟩ : ∃ Z : ℤ_[3], 2 * r ^ 3 - e = 9 * Z := ⟨_, hZ⟩
  have hmain : (4 : ℤ_[3]) * (r ^ 6 - r ^ 3 * e - (-1 + 3 * n) ^ 3) = 81 * (Z ^ 2 - K) := by
    linear_combination (2 * r ^ 3 - e + 9 * Z) * hZ' - hK
  have h27 : (27 : ℤ_[3]) * (r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D)
      = r ^ 6 - r ^ 3 * e - (-1 + 3 * n) ^ 3 := by
    linear_combination (1 - 3 * C - 6 * n + r ^ 2 + 9 * C ^ 2 + 9 * n * C + 9 * n ^ 2
      - 6 * C * r ^ 2 - 3 * n * r ^ 2 - 2 * r ^ 4) * hC + r ^ 3 * hD
  have h4 : (4 : ℤ_[3]) * (r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D) = 3 * (Z ^ 2 - K) := by
    have h := hmain
    rw [← h27] at h
    have h27ne : (27 : ℤ_[3]) ≠ 0 := by
      rw [show (27 : ℤ_[3]) = 3 ^ 3 by norm_num]
      refine pow_ne_zero 3 ?_
      rw [show (3 : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) by norm_num]
      exact PadicInt.uniformizer_ne_zero
    refine mul_left_cancel₀ h27ne ?_
    linear_combination h
  have hu : IsUnit (4 : ℤ_[3]) := by
    have h := (PadicInt.isUnit_two (p := 3) (by decide)).pow 2
    simpa [show (2 : ℤ_[3]) ^ 2 = 4 by norm_num] using h
  refine hu.dvd_mul_left.mp ⟨Z ^ 2 - K, ?_⟩
  linear_combination h4

/-! ### The cubic's coefficients, through the Step-6 lifts

`cubic ϖ W 1 1` is `⟨1, (a₂/ϖ)‾, (a₄/ϖ²)‾, (a₆/ϖ³)‾⟩`. On the Step-6 translate of the Step-2
translate these three residues are `r̄`, `C̄`, `D̄`, independently of the lifts `Step6.s` and
`Step6.t`: `3 ∣ s`, and `9 ∣ a₃` on the translate forces `τ + t = 3y`, so the contributions of `s`
and `t` to `a₄` and `a₆` carry the factors `6σy` and `3y²`. Hence `b = r̄ ≠ 0`, which excludes a
triple root since `b² = 3c` reads `b² = 0` at `p = 3`. -/

/-- Dividing `3ᵏa` by `3ᵏ` gives `a`. -/
private theorem div_pow_mul' (k : ℕ) (a : ℤ_[3]) :
    div ((((3 : ℕ) : ℤ_[3])) ^ k * a) ((((3 : ℕ) : ℤ_[3])) ^ k) = a :=
  mul_left_cancel₀ (pow_ne_zero k PadicInt.uniformizer_ne_zero)
    (CommRing.mul_div (pow_ne_zero k PadicInt.uniformizer_ne_zero) (Dvd.intro a rfl))

/-- **The cubic's `b` is the residue of `a₂/ϖ`**, whenever that division is exact. -/
theorem cubic_b_eq {V : WeierstrassCurve ℤ_[3]} {X : ℤ_[3]}
    (h : V.a₂ = ((3 : ℕ) : ℤ_[3]) * X) (a : ℤ_[3]) (m : ℕ) :
    (cubic ((3 : ℕ) : ℤ_[3]) V a m).b = mod ((3 : ℕ) : ℤ_[3]) X := by
  rw [cubic, show div V.a₂ ((3 : ℕ) : ℤ_[3]) = X from by
    rw [h, show ((3 : ℕ) : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) ^ 1 from by rw [pow_one]]
    exact div_pow_mul' 1 X]

/-- **The cubic's `c` is the residue of `a₄/ϖ²`**, whenever that division is exact. -/
theorem cubic_c_eq {V : WeierstrassCurve ℤ_[3]} {X : ℤ_[3]}
    (h : V.a₄ = ((3 : ℕ) : ℤ_[3]) ^ 2 * X) (a : ℤ_[3]) :
    (cubic ((3 : ℕ) : ℤ_[3]) V a 1).c = mod ((3 : ℕ) : ℤ_[3]) X := by
  rw [cubic, show div V.a₄ (((3 : ℕ) : ℤ_[3]) ^ 2) = X from by rw [h]; exact div_pow_mul' 2 X]

/-- **The cubic's `d` is the residue of `a₆/ϖ³`**, whenever that division is exact. -/
theorem cubic_d_eq {V : WeierstrassCurve ℤ_[3]} {X : ℤ_[3]}
    (h : V.a₆ = ((3 : ℕ) : ℤ_[3]) ^ 3 * X) (a : ℤ_[3]) :
    (cubic ((3 : ℕ) : ℤ_[3]) V a 1).d = mod ((3 : ℕ) : ℤ_[3]) X := by
  rw [cubic, show div V.a₆ (((3 : ℕ) : ℤ_[3]) ^ 3) = X from by rw [h]; exact div_pow_mul' 3 X]

/-- **The Step-6 translate's coefficients.** If `a₁ = 0`, `a₂ = 3r`, `a₃ = 2·3τ`, `a₄ = 3²C` and
`a₆ = 3³D − 3²τ²`, then the Step-6 translate has `a₂ = 3(r − 3σ²)`, `a₄ = 3²(C − 6σy)` and
`a₆ = 3³(D − 3y²)` for some `σ`, `y`. -/
theorem step6_coeffs {V : WeierstrassCurve ℤ_[3]} {r τ C D : ℤ_[3]}
    (ha₁ : V.a₁ = 0) (ha₂ : V.a₂ = ((3 : ℕ) : ℤ_[3]) * r)
    (ha₃ : V.a₃ = 2 * (((3 : ℕ) : ℤ_[3]) * τ))
    (ha₄ : V.a₄ = ((3 : ℕ) : ℤ_[3]) ^ 2 * C)
    (ha₆ : V.a₆ = ((3 : ℕ) : ℤ_[3]) ^ 3 * D - ((3 : ℕ) : ℤ_[3]) ^ 2 * τ ^ 2) :
    ∃ σ y : ℤ_[3],
      (Step6.translate ((3 : ℕ) : ℤ_[3]) V).a₂
          = ((3 : ℕ) : ℤ_[3]) * (r - ((3 : ℕ) : ℤ_[3]) * σ ^ 2) ∧
      (Step6.translate ((3 : ℕ) : ℤ_[3]) V).a₄
          = ((3 : ℕ) : ℤ_[3]) ^ 2 * (C - 6 * σ * y) ∧
      (Step6.translate ((3 : ℕ) : ℤ_[3]) V).a₆
          = ((3 : ℕ) : ℤ_[3]) ^ 3 * (D - 3 * y ^ 2) := by
  obtain ⟨σ, hσ⟩ := dvd_step6_s (p := 3) rfl ha₁
  set s6 := Step6.s ((3 : ℕ) : ℤ_[3]) V with hs6
  set t6 := Step6.t ((3 : ℕ) : ℤ_[3]) V with ht6
  have h9 : (((3 : ℕ) : ℤ_[3])) ^ 2 ∣ (Step6.translate ((3 : ℕ) : ℤ_[3]) V).a₃ :=
    sq_dvd_step6_translate_a₃_at_three (p := 3) rfl ⟨2 * τ, by rw [ha₃]; ring⟩
  have ha₃W : (Step6.translate ((3 : ℕ) : ℤ_[3]) V).a₃
      = 2 * ((3 : ℕ) : ℤ_[3]) * (τ + t6) := by
    rw [show (Step6.translate ((3 : ℕ) : ℤ_[3]) V).a₃
        = V.a₃ + 2 * (((3 : ℕ) : ℤ_[3]) * t6) from by
      simp [Step6.translate, variableChange_a₃, ha₁, ht6], ha₃]
    ring
  have hy : ((3 : ℕ) : ℤ_[3]) ∣ τ + t6 := by
    obtain ⟨w, hw⟩ := h9
    refine (PadicInt.isUnit_two (p := 3) (by decide)).dvd_mul_left.mp ⟨w, ?_⟩
    refine mul_left_cancel₀ (PadicInt.uniformizer_ne_zero (p := 3)) ?_
    rw [show ((3 : ℕ) : ℤ_[3]) * (2 * (τ + t6)) = 2 * ((3 : ℕ) : ℤ_[3]) * (τ + t6) from by ring,
      ← ha₃W, hw]
    ring
  obtain ⟨y, hyy⟩ := hy
  refine ⟨σ, y, ?_, ?_, ?_⟩
  · rw [step6_translate_a₂ (p := 3) V ha₁, ha₂, ← hs6, hσ]; ring
  · rw [step6_translate_a₄ (p := 3) V ha₁, ha₄, ha₃W, ← hs6, hσ]
    have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
    rw [hcast] at hyy ⊢
    linear_combination (-18 * σ) * hyy
  · rw [step6_translate_a₆ (p := 3) ha₁, ha₆, ha₃, ← ht6]
    have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
    rw [hcast] at hyy ⊢
    linear_combination (-9 * (τ + t6) - 27 * y) * hyy

/-! ### The two cubic tests -/

/-- **The Step-6 cubic has a double but no triple root.** Under the hypotheses of `step6_coeffs`,
with `3 ∤ r` and `3 ∣ r²C² − C³ − r³D`, the cubic of the Step-6 translate has a double root and no
triple root. -/
theorem cubic_tests {V : WeierstrassCurve ℤ_[3]} {r τ C D : ℤ_[3]}
    (hru : ¬ ((3 : ℕ) : ℤ_[3]) ∣ r)
    (hdbl : ((3 : ℕ) : ℤ_[3]) ∣ r ^ 2 * C ^ 2 - C ^ 3 - r ^ 3 * D)
    (ha₁ : V.a₁ = 0) (ha₂ : V.a₂ = ((3 : ℕ) : ℤ_[3]) * r)
    (ha₃ : V.a₃ = 2 * (((3 : ℕ) : ℤ_[3]) * τ))
    (ha₄ : V.a₄ = ((3 : ℕ) : ℤ_[3]) ^ 2 * C)
    (ha₆ : V.a₆ = ((3 : ℕ) : ℤ_[3]) ^ 3 * D - ((3 : ℕ) : ℤ_[3]) ^ 2 * τ ^ 2) :
    (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).HasDoubleRoot ∧
      ¬ (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) V) 1 1).HasTripleRoot := by
  obtain ⟨σ, y, h2, h4, h6⟩ := step6_coeffs ha₁ ha₂ ha₃ ha₄ ha₆
  set W := Step6.translate ((3 : ℕ) : ℤ_[3]) V with hW
  have hb : (cubic ((3 : ℕ) : ℤ_[3]) W 1 1).b = mod ((3 : ℕ) : ℤ_[3]) r := by
    rw [cubic_b_eq h2 1 1]
    rw [show mod ((3 : ℕ) : ℤ_[3]) (r - ((3 : ℕ) : ℤ_[3]) * σ ^ 2)
        = mod ((3 : ℕ) : ℤ_[3]) r from by
      rw [map_sub, map_mul, show mod ((3 : ℕ) : ℤ_[3]) ((3 : ℕ) : ℤ_[3]) = 0 from by
        rw [mod_eq_zero], zero_mul, sub_zero]]
  have hc : (cubic ((3 : ℕ) : ℤ_[3]) W 1 1).c = mod ((3 : ℕ) : ℤ_[3]) C := by
    rw [cubic_c_eq h4 1, map_sub, map_mul, map_mul,
      show mod ((3 : ℕ) : ℤ_[3]) 6 = 0 from by
        rw [mod_eq_zero]; exact ⟨2, by norm_num⟩,
      zero_mul, zero_mul, sub_zero]
  have hd : (cubic ((3 : ℕ) : ℤ_[3]) W 1 1).d = mod ((3 : ℕ) : ℤ_[3]) D := by
    rw [cubic_d_eq h6 1, map_sub, map_mul,
      show mod ((3 : ℕ) : ℤ_[3]) 3 = 0 from by
        rw [mod_eq_zero]; exact ⟨1, by norm_num⟩,
      zero_mul, sub_zero]
  have hbne : (cubic ((3 : ℕ) : ℤ_[3]) W 1 1).b ≠ 0 := by
    rw [hb, ← mod_eq_zero] at *
    exact hru
  refine ⟨?_, ?_⟩
  · rw [Cubic.hasDoubleRoot_of_a_eq_one (by simp [cubic]), hb, hc, hd]
    have h27 : (27 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 0 := by
      rw [← map_ofNat (mod ((3 : ℕ) : ℤ_[3])) 27, mod_eq_zero]; exact ⟨9, by norm_num⟩
    have h18 : (18 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 0 := by
      rw [← map_ofNat (mod ((3 : ℕ) : ℤ_[3])) 18, mod_eq_zero]; exact ⟨6, by norm_num⟩
    have h3 : (3 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 0 := by
      rw [← map_ofNat (mod ((3 : ℕ) : ℤ_[3])) 3, mod_eq_zero]; exact ⟨1, by norm_num⟩
    have hkey : mod ((3 : ℕ) : ℤ_[3]) r ^ 2 * mod ((3 : ℕ) : ℤ_[3]) C ^ 2
        - mod ((3 : ℕ) : ℤ_[3]) C ^ 3
        - mod ((3 : ℕ) : ℤ_[3]) r ^ 3 * mod ((3 : ℕ) : ℤ_[3]) D = 0 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_pow, ← map_pow, ← map_mul, ← map_sub, ← map_sub,
        mod_eq_zero]
      exact hdbl
    linear_combination hkey - mod ((3 : ℕ) : ℤ_[3]) C ^ 3 * h3
      - (mod ((3 : ℕ) : ℤ_[3]) r ^ 3 * mod ((3 : ℕ) : ℤ_[3]) D) * h3
      - mod ((3 : ℕ) : ℤ_[3]) D ^ 2 * h27
      + (mod ((3 : ℕ) : ℤ_[3]) r * mod ((3 : ℕ) : ℤ_[3]) C * mod ((3 : ℕ) : ℤ_[3]) D) * h18
  · rw [Cubic.HasTripleRoot]
    intro h
    refine hbne ?_
    have h3 : (3 : ℤ_[3] ⧸ span {((3 : ℕ) : ℤ_[3])}) = 0 := by
      rw [← map_ofNat (mod ((3 : ℕ) : ℤ_[3])) 3, mod_eq_zero]; exact ⟨1, by norm_num⟩
    have hsq : (cubic ((3 : ℕ) : ℤ_[3]) W 1 1).b ^ 2 = 0 := by
      rw [h]; linear_combination (cubic ((3 : ℕ) : ℤ_[3]) W 1 1).c * h3
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hsq

/-! ### Step 6 returns ok -/

open scoped Classical in
/-- **Step 6 passes on the Family A locus at `p = 3`**: it returns the Step-6 translate of the
Step-2 translate, whose cubic has no triple root. -/
theorem step6_ok_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) :
    Step6.run ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2)
        = Except.ok (Step6.translate ((3 : ℕ) : ℤ_[3])
            (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2))) ∧
      ¬ (cubic ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3])
        (Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2))) 1 1).HasTripleRoot := by
  classical
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  obtain ⟨α, hα1, hαu, he, -⟩ := exists_form_of_mem_locus hx
  obtain ⟨r, t, ρ, τ, n, K, C, D, hT, hr, ht, h1, hK, hC, hD⟩ := step2_data hx
  set V := Step2.translate ((3 : ℕ) : ℤ_[3]) (ofShortNF x.1 x.2) with hV
  have hru : ¬ ((3 : ℕ) : ℤ_[3]) ∣ r := by
    intro hd
    refine he ?_
    obtain ⟨w, hw⟩ := hd
    exact ⟨ρ - w, by rw [hcast]; linear_combination -hw + hr⟩
  have ha₁ : V.a₁ = 0 := by rw [hT, smulOne_a₁]
  have ha₂ : V.a₂ = ((3 : ℕ) : ℤ_[3]) * r := by rw [hT, smulOne_a₂, hcast]
  have ha₃ : V.a₃ = 2 * (((3 : ℕ) : ℤ_[3]) * τ) := by
    rw [hT, smulOne_a₃, ht, hcast]
  have ha₄ : V.a₄ = ((3 : ℕ) : ℤ_[3]) ^ 2 * C := by
    rw [hT, smulOne_a₄, h1, hcast]; linear_combination 3 * hC
  have ha₆ : V.a₆ = ((3 : ℕ) : ℤ_[3]) ^ 3 * D - ((3 : ℕ) : ℤ_[3]) ^ 2 * τ ^ 2 := by
    rw [hT, smulOne_a₆, ht, hcast]; linear_combination hD
  obtain ⟨hdbl, hntr⟩ := cubic_tests hru
    (three_dvd_cubic_combo hr hK hC (by linear_combination hD - r * h1)) ha₁ ha₂ ha₃ ha₄ ha₆
  refine ⟨?_, hntr⟩
  rw [Step6.run.eq_def, step5_run_eq_ok_of_mem_locus hx]
  simp only [except_ok_bind]
  exact ite_eq_left hdbl

/-! ### The two conclusions

Once Step 6 returns `ok` and the cubic has no triple root, Step 7 reports `Iₘ*` with `m ≥ 1` and
Tamagawa number `2` or `4`, for every number of turns of its subprocedure. -/

/-- **On the Family A locus at `p = 3`, Tate's algorithm answers `Iₘ*` with `m ≥ 1`.** Here `m` is
`2n − 2` or `2n − 3` for the stage `n` at which Step 7's subprocedure exits, and varies over the
locus. -/
theorem exists_kodairaSymbol_eq_Istar_of_mem_locus {x : ℤ_[3] × ℤ_[3]}
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) (hx : x ∈ locus) :
    ∃ m, m ≠ 0 ∧ (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m := by
  obtain ⟨h6, hntr⟩ := step6_ok_of_mem_locus hx
  obtain ⟨out, h7, m, hm, hout⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hntr
  refine ⟨m, hm, ?_⟩
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step7 hΔ h7)]
  exact hout

/-- **On the Family A locus at `p = 3`, the Tamagawa number is `2` or `4`.** Both exits of Step 7's
subprocedure report `4` if the relevant quadratic has a root and `2` otherwise. -/
theorem tamagawaNumber_eq_two_or_four_of_mem_locus {x : ℤ_[3] × ℤ_[3]}
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) (hx : x ∈ locus) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 ∨
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 4 := by
  obtain ⟨h6, hntr⟩ := step6_ok_of_mem_locus hx
  obtain ⟨out, h7, -⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hntr
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step7 hΔ h7)]
  exact Step7.run_error_tamagawaNumber_eq_two_or_four hΔ h6 hntr h7

end FamilyAThree

end WeierstrassCurve

end
