/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FamilyAThreeAtThree

/-!
# Family B at `p = 3`: the multiplicative family behind one non-minimal descent

The short models `y² = x³ + a₄x + a₆` over `ℤ_3` with `a₄ = 27α`, `a₆ = 27β`, `3 ∤ α` and
`27 ∣ 4α³ + β²` — which forces `3 ∤ β` and `α ≡ 2 (mod 3)` — form a single cylinder of eighteen
classes of `(α, β)` modulo `27`, of mass `18 · 3⁻⁶ · 3⁻⁶ = 2/59049`. On it

  `Δ = −16(4a₄³ + 27a₆²) = −16 · 3⁹ · (4α³ + β²)`,   `c₄ = −16 · 3⁴ · α`,   `c₆ = −32 · 3⁶ · β`,

so `v₃(Δ) = 12 + n` where `n := v₃(4α³ + β²) − 3 ≥ 0` is the *level* of the point. Tate's algorithm
traverses Steps 1–10 without answering, Step 11 rescales by `u = 3`, and the descended curve `V`
has `c₄(V) = −16α` (a unit, so `V` is nodal), `c₆(V) = −32β` and `27 · Δ(V) = −16(4α³ + β²)`, i.e.
`v₃(Δ(V)) = n`. The answer is therefore the multiplicative one on `V`: `(I₀, 1)` at level `0`; at
level `n ≥ 1` it is `(Iₙ, n)` when the tangent quadratic splits, which by the classical criterion
is "`−c₆(V) = 32β` is a square in `𝔽₃`", i.e. `β ≡ 2 (mod 3)`; and `(Iₙ, 1)` or `(Iₙ, 2)` according
to the parity of `n` when `β ≡ 1 (mod 3)`.

## Main definitions

* `WeierstrassCurve.FamilyBThree.Res`: the residue condition on `(α, β)` modulo `27`.
* `WeierstrassCurve.FamilyBThree.residues`: the eighteen classes satisfying it.
* `WeierstrassCurve.FamilyBThree.locus`: the Family B locus of the coefficient plane.

## Main results

* `WeierstrassCurve.FamilyBThree.card_residues`: there are eighteen classes modulo `27`.
* `WeierstrassCurve.FamilyBThree.volume_locus`: the locus has mass `2/59049`.
* `WeierstrassCurve.FamilyBThree.exists_form_of_mem_locus`: a point of the locus has `a₄ = 27α`,
  `a₆ = 27β`, `3 ∤ α`, `3 ∤ β` and `3³ ∣ 4α³ + β²`.
* `WeierstrassCurve.FamilyBThree.locus_subset_notMem_range`: the locus contains no
  `(3⁴, 3⁶)`-dilate.
* `WeierstrassCurve.FamilyBThree.pow_six_dvd_a₆_of_not_dvd_c₆`: Step 10's branch condition
  `3⁶ ∣ a₆`, read off `c₆`.
* `WeierstrassCurve.FamilyBThree.step11_run_eq_ok`: Step 11 fires on a short model with `3³ ∣ a₄`,
  `3³ ∣ a₆`, `3¹² ∣ Δ` and `3⁷ ∤ c₆`.
* `WeierstrassCurve.FamilyBThree.exists_descent_of_mem_locus`,
  `WeierstrassCurve.FamilyBThree.exists_descent_of_level`: the descended curve's `c₄`, `c₆` and
  `Δ`, and `v₃(Δ(V)) = n` at level `n`.
* `WeierstrassCurve.FamilyBThree.run_eq_I_zero_of_level_zero`,
  `WeierstrassCurve.FamilyBThree.run_eq_I_of_split`,
  `WeierstrassCurve.FamilyBThree.run_eq_I_of_nonsplit`: `(I₀, 1)` at level `0`, and at level
  `n ≥ 1` the datum `(Iₙ, n)` when `β ≡ 2 (mod 3)` and `(Iₙ, if Odd n then 1 else 2)` when
  `β ≡ 1 (mod 3)`.

## Implementation notes

Step 10's branch condition `3⁶ ∣ a₆` on the Step-9 translate is read off `c₆` rather than `Δ`.
Writing `b₂ = 9B₂`, `b₄ = 81B₄`, `b₆ = 3⁵B₆`, `b₈ = 3⁷B₈` there,

  `c₆ = 3⁶(−B₂³ + 36B₂B₄ − 72B₆)`,   `Δ = 3¹¹(−B₂²B₈ − 24B₄³ + 9(⋯))`,   `4B₈ = B₂B₆ − 3B₄²`,

and `c₆ = −32 · 3⁶ · β` with `β` a unit, so the descent holds at every level `n ≥ 0` under
`3¹² ∣ Δ` and `3⁷ ∤ c₆`.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open CommRing Ideal TateAlgorithm

namespace FamilyBThree

/-! ### The eighteen residue classes modulo `27`

The pair being reduced is `(α, β)` with `a₄ = 27α`, `a₆ = 27β`: the condition `3³ ∣ 4α³ + β²` reads
both to depth `3`, and the dilation `(α, β) ↦ (27α, 27β)` carries the other three digits of each
coordinate. -/

/-- **The residue condition cutting out Family B at `3`**, on the pair `(α, β)` where `a₄ = 27α`
and `a₆ = 27β`: `3 ∤ α`, and `4α³ + β² = 0` in `ZMod 27`.

`3 ∤ β` is a consequence rather than a clause (`res_cast_snd`): if `3 ∣ β` then
`4α³ + β² ≡ α (mod 3)` is a unit. -/
abbrev Res (c : ZMod (3 ^ 3) × ZMod (3 ^ 3)) : Prop :=
  (ZMod.cast c.1 : ZMod 3) ≠ 0 ∧ 4 * c.1 ^ 3 + c.2 ^ 2 = 0

/-- **The classes of `(α, β)` modulo `27` cutting out Family B at `3`**: those satisfying `Res`. -/
noncomputable def residues : Finset (ZMod (3 ^ 3) × ZMod (3 ^ 3)) :=
  Finset.univ.filter Res

/-- A pair of residues modulo `27` lies in `residues` if and only if it satisfies `Res`. -/
theorem mem_residues_iff (c : ZMod (3 ^ 3) × ZMod (3 ^ 3)) : c ∈ residues ↔ Res c := by
  simp [residues]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` ranges over all `729` pairs modulo `27`, evaluating a cube in `ZMod 27` in each.
/-- **There are eighteen classes**: nine admissible `α` (those with `α ≡ 2 (mod 3)`), each with
exactly two `β`, because `4α³ + β²` factors as `(β − ν)(β + ν)` with `2ν` a unit, so exactly one
factor can be deep. -/
theorem card_residues : residues.card = 18 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- `decide` ranges over all `729` pairs modulo `27`.
/-- **`3 ∤ β` on the locus**: if `3 ∣ β` then `4α³ + β² ≡ α (mod 3)` is a unit. -/
theorem res_cast_snd (c : ZMod (3 ^ 3) × ZMod (3 ^ 3)) (h : Res c) :
    (ZMod.cast c.2 : ZMod 3) ≠ 0 := by
  revert c; decide

/-! ### The locus, its measurability and its mass -/

/-- **The Family B locus of the coefficient plane at `3`**: the image under `(α, β) ↦ (27α, 27β)`
of the eighteen-class cylinder modulo `27`. -/
noncomputable def locus : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.scaleProdByPPow 3 3 ''
    (PadicInt.redPairPow 3 3 ⁻¹' (residues : Set (ZMod (3 ^ 3) × ZMod (3 ^ 3))))

/-- The Family B locus at `3` is a measurable subset of `ℤ_[3] × ℤ_[3]`. -/
theorem measurableSet_locus : MeasurableSet locus :=
  (PadicInt.measurableEmbedding_scaleProdByPPow 3 3).measurableSet_image.2
    (PadicInt.measurableSet_preimage_redPairPow 3 residues)

/-- `18 · 3⁻⁶ = 18/729 = 2/81`, in the shape `PadicInt.volume_preimage_redPairPow` produces. -/
theorem eighteen_mul_inv_pow_six_eq :
    ((18 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 3) = 2 / 81 := by
  rw [show ((18 : ℕ) : ℝ≥0∞) = 18 by norm_num, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 3) = 729 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the Family B locus at `3` is `2/59049`** — the dilation `(α, β) ↦ (27α, 27β)`
costs a factor `3⁻⁶` on top of the cylinder's `18 · 3⁻⁶ = 2/81`. -/
theorem volume_locus : (volume : Measure (ℤ_[3] × ℤ_[3])) locus = 2 / 59049 := by
  rw [locus, PadicInt.measure_image_scaleProdByPPow, PadicInt.volume_preimage_redPairPow,
    card_residues, eighteen_mul_inv_pow_six_eq,
    show ((3 : ℕ) + (3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num,
    PadicInt.zpow_neg_natCast_eq_inv_pow, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num]
  rw [show (3 : ℝ≥0∞)⁻¹ ^ 6 = 1 / 729 from by rw [← ENNReal.inv_pow, one_div]; norm_num,
    enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Membership, the algebraic shape, and minimality -/

set_option maxRecDepth 100000 in
/-- Membership of `locus`, with the dilation `(a₄, a₆) = (27α, 27β)` made explicit and the residue
condition read on `(α, β)`. -/
theorem mem_locus_iff {x : ℤ_[3] × ℤ_[3]} :
    x ∈ locus ↔ ∃ α β : ℤ_[3], x.1 = ((3 : ℕ) : ℤ_[3]) ^ 3 * α ∧
      x.2 = ((3 : ℕ) : ℤ_[3]) ^ 3 * β ∧ Res (PadicInt.toZModPow 3 α, PadicInt.toZModPow 3 β) := by
  have hcoe : ∀ c : ZMod (3 ^ 3) × ZMod (3 ^ 3),
      c ∈ (residues : Set (ZMod (3 ^ 3) × ZMod (3 ^ 3))) ↔ Res c :=
    fun c => (Finset.mem_coe).trans (mem_residues_iff c)
  constructor
  · rintro ⟨⟨α, β⟩, hmem, rfl⟩
    exact ⟨α, β, rfl, rfl, (hcoe _).1 hmem⟩
  · rintro ⟨α, β, h1, h2, hres⟩
    exact ⟨(α, β), (hcoe _).2 hres, Prod.ext h1.symm h2.symm⟩

/-- **The algebraic shape of a point of the locus**: `a₄ = 27α`, `a₆ = 27β` with `α`, `β` units,
and `3³ ∣ 4α³ + β²`, the last being exactly `v₃(Δ) ≥ 12`. -/
theorem exists_form_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) :
    ∃ α β : ℤ_[3], x.1 = 27 * α ∧ x.2 = 27 * β ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ β ∧ ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ 4 * α ^ 3 + β ^ 2 := by
  obtain ⟨α, β, h1, h2, hres⟩ := mem_locus_iff.1 hx
  have hcast : ((3 : ℕ) : ℤ_[3]) ^ 3 = 27 := by norm_num
  have key : ∀ y : ℤ_[3], (ZMod.cast (PadicInt.toZModPow 3 y) : ZMod 3) ≠ 0 →
      ¬ ((3 : ℕ) : ℤ_[3]) ∣ y := by
    intro y hy hdvd
    refine hy ?_
    have h1 : (ZMod.cast (PadicInt.toZModPow 3 y) : ZMod (3 ^ 1)) = PadicInt.toZModPow 1 y :=
      PadicInt.cast_toZModPow 1 3 (by norm_num) y
    have h2 : PadicInt.toZModPow 1 y = 0 := by
      rwa [← PadicInt.pow_dvd_iff_toZModPow_eq_zero, pow_one]
    have h3 : (ZMod.cast (PadicInt.toZModPow 3 y) : ZMod (3 ^ 1)) = 0 := h1.trans h2
    simpa using h3
  refine ⟨α, β, by rw [h1, hcast], by rw [h2, hcast], key α hres.1,
    key β (res_cast_snd _ hres), ?_⟩
  rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_pow, map_ofNat]
  exact hres.2

/-- **The whole locus lies in the minimal storey.** `v₃(a₄) = 3`, so `3⁴ ∤ a₄` and no point is a
`(3⁴, 3⁶)`-dilate. -/
theorem locus_subset_notMem_range :
    ∀ x ∈ locus, x ∉ Set.range
      (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  intro x hx
  obtain ⟨α, β, h1, -, hα, -, -⟩ := exists_form_of_mem_locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => hα ?_
  rw [h1] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  rw [hcast] at hc ⊢
  refine ⟨c, mul_left_cancel₀ (by norm_num : (27 : ℤ_[3]) ≠ 0) ?_⟩
  rw [hc]
  ring

/-- If `x ∈ locus` and `x = (27α, 27β)` then `3 ∤ α`, `3 ∤ β` and `3³ ∣ 4α³ + β²`. -/
theorem not_dvd_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ locus) {α β : ℤ_[3]}
    (h₄ : x.1 = 27 * α) (h₆ : x.2 = 27 * β) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ β ∧
      ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ 4 * α ^ 3 + β ^ 2 := by
  obtain ⟨α', β', h₄', h₆', hα, hβ, h27⟩ := exists_form_of_mem_locus hx
  have h27ne : (27 : ℤ_[3]) ≠ 0 := by norm_num
  obtain rfl : α' = α := mul_left_cancel₀ h27ne (h₄'.symm.trans h₄)
  obtain rfl : β' = β := mul_left_cancel₀ h27ne (h₆'.symm.trans h₆)
  exact ⟨hα, hβ, h27⟩

/-! ### The descent at every level -/

private theorem three_ne_zero' : (3 : ℤ_[3]) ≠ 0 := by
  rw [show (3 : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) by norm_num]; exact PadicInt.uniformizer_ne_zero

private theorem three_prime : Prime (3 : ℤ_[3]) := by
  rw [show (3 : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) by norm_num]; exact PadicInt.prime_p

private theorem isUnit_four : IsUnit (4 : ℤ_[3]) := by
  have h := (PadicInt.isUnit_two (p := 3) (by decide)).pow 2
  simpa [show (2 : ℤ_[3]) ^ 2 = 4 by norm_num] using h

private theorem isUnit_sixteen : IsUnit (16 : ℤ_[3]) := by
  have h := (PadicInt.isUnit_two (p := 3) (by decide)).pow 4
  simpa [show (2 : ℤ_[3]) ^ 4 = 16 by norm_num] using h

private theorem isUnit_thirtyTwo : IsUnit (32 : ℤ_[3]) := by
  have h := (PadicInt.isUnit_two (p := 3) (by decide)).pow 5
  simpa [show (2 : ℤ_[3]) ^ 5 = 32 by norm_num] using h

/-- Cancel a common power of `3` from a divisibility. -/
private theorem dvd_of_pow_dvd_pow_mul {k j : ℕ} {x : ℤ_[3]}
    (h : (3 : ℤ_[3]) ^ (k + j) ∣ 3 ^ k * x) : (3 : ℤ_[3]) ^ j ∣ x := by
  rwa [pow_add, mul_dvd_mul_iff_left (pow_ne_zero k three_ne_zero')] at h

/-- **Step 10's branch condition at `p = 3`, read off `c₆` instead of `Δ`: `3⁶ ∣ a₆`.** At the
stage `Step9.run_hasValuation` records — `3² ∣ b₂`, `3⁴ ∣ b₄`, `3⁷ ∣ b₈`, `3³ ∣ a₃`, `3⁵ ∣ a₆` — if
`3¹² ∣ Δ` and `3⁷ ∤ c₆`, then `3⁶ ∣ a₆`. -/
theorem pow_six_dvd_a₆_of_not_dvd_c₆ {V : WeierstrassCurve ℤ_[3]} {B₂ B₄ B₈ A₃ A₆ : ℤ_[3]}
    (hb₂ : V.b₂ = ((3 : ℕ) : ℤ_[3]) ^ 2 * B₂) (hb₄ : V.b₄ = ((3 : ℕ) : ℤ_[3]) ^ 4 * B₄)
    (hb₈ : V.b₈ = ((3 : ℕ) : ℤ_[3]) ^ 7 * B₈) (ha₃ : V.a₃ = ((3 : ℕ) : ℤ_[3]) ^ 3 * A₃)
    (ha₆ : V.a₆ = ((3 : ℕ) : ℤ_[3]) ^ 5 * A₆) (hΔ : ((3 : ℕ) : ℤ_[3]) ^ 12 ∣ V.Δ)
    (hc₆ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 7 ∣ V.c₆) :
    ((3 : ℕ) : ℤ_[3]) ^ 6 ∣ V.a₆ := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  rw [hcast] at hb₂ hb₄ hb₈ ha₃ ha₆ hΔ hc₆ ⊢
  obtain ⟨B₆, hB₆def⟩ : ∃ B₆ : ℤ_[3], B₆ = 3 * A₃ ^ 2 + 4 * A₆ := ⟨_, rfl⟩
  have hb₆ : V.b₆ = 3 ^ 5 * B₆ := by rw [WeierstrassCurve.b₆, ha₃, ha₆, hB₆def]; ring
  have hc₆' : V.c₆ = 3 ^ 6 * (-B₂ ^ 3 + 36 * B₂ * B₄ - 72 * B₆) := by
    rw [WeierstrassCurve.c₆, hb₂, hb₄, hb₆]; ring
  have hB₂ : ¬ (3 : ℤ_[3]) ∣ B₂ := by
    rintro ⟨y, hy⟩
    refine hc₆ ⟨-9 * y ^ 3 + 36 * y * B₄ - 24 * B₆, ?_⟩
    rw [hc₆', hy]; ring
  have key : V.Δ = 3 ^ 11 * (-(B₂ ^ 2 * B₈) - 3 * (8 * B₄ ^ 3)
      + 3 ^ 2 * (-(B₆ ^ 2) + B₂ * B₄ * B₆)) := by
    rw [WeierstrassCurve.Δ, hb₂, hb₄, hb₆, hb₈]; ring
  obtain ⟨y, hy⟩ := dvd_of_pow_dvd_pow_mul (k := 11) (j := 1) (by rw [← key]; exact hΔ)
  rw [pow_one] at hy
  have hB₂₈ : (3 : ℤ_[3]) ∣ B₂ ^ 2 * B₈ :=
    ⟨-y - 8 * B₄ ^ 3 + 3 * (-(B₆ ^ 2) + B₂ * B₄ * B₆), by linear_combination -hy⟩
  have hB₈ : (3 : ℤ_[3]) ∣ B₈ := by
    rcases three_prime.dvd_mul.mp hB₂₈ with h | h
    · exact absurd (three_prime.dvd_of_dvd_pow h) hB₂
    · exact h
  obtain ⟨F₈, hF₈⟩ := hB₈
  have hrel : 4 * B₈ = B₂ * B₆ - 3 * B₄ ^ 2 := by
    have h := V.b_relation
    rw [hb₂, hb₄, hb₆, hb₈] at h
    refine mul_left_cancel₀ (pow_ne_zero 7 three_ne_zero') ?_
    linear_combination h
  have hB₂₆ : (3 : ℤ_[3]) ∣ B₂ * B₆ :=
    ⟨4 * F₈ + B₄ ^ 2, by linear_combination -hrel + 4 * hF₈⟩
  have hB₆ : (3 : ℤ_[3]) ∣ B₆ := by
    rcases three_prime.dvd_mul.mp hB₂₆ with h | h
    · exact absurd h hB₂
    · exact h
  obtain ⟨G, hG⟩ := hB₆
  have h4A₆ : (3 : ℤ_[3]) ∣ 4 * A₆ := ⟨G - A₃ ^ 2, by linear_combination hG - hB₆def⟩
  obtain ⟨H, hH⟩ := isUnit_four.dvd_mul_left.mp h4A₆
  exact ⟨H, by rw [ha₆, hH]; ring⟩

/-- **Steps 6–10 traverse, from the Step-5 output, at `p = 3`, given `3¹² ∣ Δ` and `3⁷ ∤ c₆`**,
when the curve `W₂` handed on by Step 5 has `a₁ = 0`, `3² ∣ a₂` and `3³ ∣ a₄`. -/
theorem step11_run_eq_ok_of_step5 {W W₂ : WeierstrassCurve ℤ_[3]} (hΔ0 : W.Δ ≠ 0)
    (h5 : Step5.run ((3 : ℕ) : ℤ_[3]) W = Except.ok W₂) (ha₁ : W₂.a₁ = 0) {A₂ A₄ : ℤ_[3]}
    (hA₂ : W₂.a₂ = ((3 : ℕ) : ℤ_[3]) ^ 2 * A₂) (hA₄ : W₂.a₄ = ((3 : ℕ) : ℤ_[3]) ^ 3 * A₄)
    (hΔ12 : ((3 : ℕ) : ℤ_[3]) ^ 12 ∣ W.Δ) (hc₆ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 7 ∣ W.c₆) :
    ∃ V, Step11.run (W := W) PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V := by
  have hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hval5 := Step5.run_hasValuation hϖ h5
  have hval6 := Step6.hasValuation_translate hϖ hval5
  obtain ⟨σ, hσ⟩ := dvd_step6_s (p := 3) rfl ha₁
  obtain ⟨A₃', hA₃'⟩ := hval6.a₃
  have hW6a₂ : (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂).a₂
      = ((3 : ℕ) : ℤ_[3]) ^ 2 * (A₂ - σ ^ 2) := by
    rw [step6_translate_a₂ _ ha₁, hA₂, hσ]; ring
  have hW6a₄ : (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂).a₄
      = ((3 : ℕ) : ℤ_[3]) ^ 3 * (A₄ - σ * A₃') := by
    rw [step6_translate_a₄ _ ha₁, hA₄, hσ, hA₃']; ring
  have hdouble := hasDoubleRoot_of_three (p := 3) rfl hW6a₂ hW6a₄
  have htriple := hasTripleRoot_of_three (p := 3) rfl hW6a₂
  have h6 : Step6.run ((3 : ℕ) : ℤ_[3]) W
      = Except.ok (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂) := by
    rw [Step6.run.eq_def, h5]; simp only [except_ok_bind]; exact ite_eq_left hdouble
  have h7 : Step7.run hϖ hΔ0 = Except.ok (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = Step6.translate ((3 : ℕ) : ℤ_[3]) W₂ :=
          Except.ok.inj (heq.symm.trans h6)
        exact dite_eq_left htriple
  have hval7 := Step7.run_hasValuation hϖ hΔ0 h7
  have hval8 := Step8.hasValuation_translate hϖ hval7 hdouble htriple
  obtain ⟨B₂, hB₂⟩ := hval8.b₂
  obtain ⟨B₄, hB₄⟩ := hval8.b₄
  obtain ⟨B₈, hB₈⟩ := hval8.b₈
  obtain ⟨A₃₈, hA₃₈⟩ := hval8.a₃
  obtain ⟨A₆₈, hA₆₈⟩ := hval8.a₆
  have hΔ8 : (Step8.translate ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂)).Δ
      = W.Δ := by
    rw [Step8.translate_Δ, Step7.run_Δ hϖ hΔ0 h7]
  have hq := quadratic_hasDoubleRoot_of_three (p := 3) rfl hB₂ hB₄ hB₈ hA₃₈ hA₆₈
    (by rw [hΔ8]; exact hΔ12)
  have h8 : Step8.run hϖ hΔ0 = Except.ok (Step8.translate ((3 : ℕ) : ℤ_[3])
      (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂)) := by
    rw [Step8.run.eq_def, h7]; simp only [except_ok_bind]; exact ite_eq_left hq
  have hval9 := Step9.hasValuation_translate hϖ hval8 hq
  obtain ⟨C₂, hC₂⟩ := hval9.b₂
  obtain ⟨C₄, hC₄⟩ := hval9.b₄
  obtain ⟨C₆, hC₆⟩ := hval9.b₆
  obtain ⟨C₈, hC₈⟩ := hval9.b₈
  have hΔ9 : (Step9.translate ((3 : ℕ) : ℤ_[3]) (Step8.translate ((3 : ℕ) : ℤ_[3])
      (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂))).Δ = W.Δ := by
    rw [Step9.translate, Step7.translateY_Δ, Step8.run_Δ hϖ hΔ0 h8]
  have h9cond := pow_four_dvd_a₄_of_three (p := 3) rfl hC₂ hC₄ hC₆ hC₈
    (by simpa using hval9.a₁) hval9.a₃
    (by rw [hΔ9]; exact (pow_dvd_pow _ (by norm_num : 10 ≤ 12)).trans hΔ12)
  have h9 : Step9.run hϖ hΔ0 = Except.ok (Step9.translate ((3 : ℕ) : ℤ_[3])
      (Step8.translate ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂))) := by
    rw [Step9.run.eq_def, h8]; simp only [except_ok_bind]; exact ite_eq_left h9cond
  have hval9' := Step9.run_hasValuation hϖ hΔ0 h9
  obtain ⟨D₂, hD₂⟩ := hval9'.b₂
  obtain ⟨D₄, hD₄⟩ := hval9'.b₄
  obtain ⟨D₈, hD₈⟩ := hval9'.b₈
  obtain ⟨E₃, hE₃⟩ := hval9'.a₃
  obtain ⟨E₆, hE₆⟩ := hval9'.a₆
  have h10cond := pow_six_dvd_a₆_of_not_dvd_c₆ hD₂ hD₄ hD₈ hE₃ hE₆
    (by rw [Step9.run_Δ hϖ hΔ0 h9]; exact hΔ12) (by rw [Step9.run_c₆ hϖ hΔ0 h9]; exact hc₆)
  have h10 : Step10.run hϖ hΔ0 = Except.ok (Step9.translate ((3 : ℕ) : ℤ_[3])
      (Step8.translate ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂))) := by
    rw [Step10.run.eq_def, h9]; simp only [except_ok_bind]; exact ite_eq_left h10cond
  exact ⟨Step11.translate ((3 : ℕ) : ℤ_[3]) (Step9.translate ((3 : ℕ) : ℤ_[3])
    (Step8.translate ((3 : ℕ) : ℤ_[3]) (Step6.translate ((3 : ℕ) : ℤ_[3]) W₂))),
    by rw [Step11.run.eq_def, h10]; rfl⟩

/-- **Step 11 fires on a short model over `ℤ_3` with `3³ ∣ a₄`, `3³ ∣ a₆`, `3¹² ∣ Δ` and
`3⁷ ∤ c₆`.** -/
theorem step11_run_eq_ok {a₄ a₆ : ℤ_[3]} (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0)
    (h₄ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ a₄) (h₆ : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ a₆)
    (hΔ12 : ((3 : ℕ) : ℤ_[3]) ^ 12 ∣ (ofShortNF a₄ a₆).Δ)
    (hc₆ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 7 ∣ (ofShortNF a₄ a₆).c₆) :
    ∃ V, Step11.run (W := ofShortNF a₄ a₆) PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V := by
  have hΔd : ((3 : ℕ) : ℤ_[3]) ∣ (ofShortNF a₄ a₆).Δ :=
    (dvd_pow_self _ (by norm_num : (12 : ℕ) ≠ 0)).trans hΔ12
  obtain ⟨ha₁, ⟨A₂, hA₂⟩, ⟨A₄, hA₄⟩, -, -, -⟩ :=
    step2_translate_data_three (p := 3) rfl h₄ h₆ hΔd
  exact step11_run_eq_ok_of_step5 hΔ0 (Step5.run_eq_ok_of_cb_dvd_three (p := 3) rfl h₄ h₆) ha₁
    hA₂ hA₄ hΔ12 hc₆

/-! ### The descended curve

From `Step11.run = ok V` the algorithm records `3⁴ · c₄(V) = c₄`, `3⁶ · c₆(V) = c₆` and
`3¹² · Δ(V) = Δ`; on Family B these read `c₄(V) = −16α`, `c₆(V) = −32β` and
`27 · Δ(V) = −16(4α³ + β²)`. -/

/-- **The descent fires on a nonsingular point of the locus, and the descended curve's invariants
are `c₄(V) = −16α`, `c₆(V) = −32β`, `27 · Δ(V) = −16(4α³ + β²)`.** -/
theorem exists_descent_of_mem_locus {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0)
    (hx : x ∈ locus) {α β : ℤ_[3]} (h₄ : x.1 = 27 * α) (h₆ : x.2 = 27 * β) :
    ∃ V : WeierstrassCurve ℤ_[3],
      Step11.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ = Except.ok V ∧
        V.c₄ = -16 * α ∧ V.c₆ = -32 * β ∧ 27 * V.Δ = -16 * (4 * α ^ 3 + β ^ 2) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨-, hβ, h27⟩ := not_dvd_of_mem_locus hx h₄ h₆
  rw [hcast] at hβ h27
  obtain ⟨D, hD⟩ := h27
  have hc₆ : ¬ ((3 : ℕ) : ℤ_[3]) ^ 7 ∣ (ofShortNF x.1 x.2).c₆ := by
    rintro ⟨y, hy⟩
    rw [ofShortNF_c₆, h₆, hcast] at hy
    refine hβ (isUnit_thirtyTwo.dvd_mul_left.mp ⟨-y, ?_⟩)
    refine mul_left_cancel₀ (pow_ne_zero 6 three_ne_zero') ?_
    linear_combination -hy
  obtain ⟨V, hV⟩ := step11_run_eq_ok hΔ ⟨α, by rw [h₄, hcast]; ring⟩ ⟨β, by rw [h₆, hcast]; ring⟩
    ⟨-16 * D, by rw [ofShortNF_Δ, h₄, h₆, hcast]; linear_combination (-16 * 3 ^ 9) * hD⟩ hc₆
  have hVc₄ := Step11.run_c₄ hϖ hΔ hV
  have hVc₆ := Step11.run_c₆ hϖ hΔ hV
  have hVΔ := Step11.run_Δ hϖ hΔ hV
  rw [ofShortNF_c₄, h₄, hcast] at hVc₄
  rw [ofShortNF_c₆, h₆, hcast] at hVc₆
  rw [ofShortNF_Δ, h₄, h₆, hcast] at hVΔ
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · exact mul_left_cancel₀ (pow_ne_zero 4 three_ne_zero') (by rw [hVc₄]; ring)
  · exact mul_left_cancel₀ (pow_ne_zero 6 three_ne_zero') (by rw [hVc₆]; ring)
  · exact mul_left_cancel₀ (pow_ne_zero 9 three_ne_zero') (by linear_combination hVΔ)

/-- **At level `n` the descended curve is nodal with `v₃(Δ(V)) = n`.** `c₄(V) = −16α` is a unit;
and `27 · Δ(V) = −16(4α³ + β²)` with `3^(n+3) ∥ 4α³ + β²` gives `3ⁿ ∥ Δ(V)`. -/
theorem exists_descent_of_level {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0)
    (hx : x ∈ locus) {α β : ℤ_[3]} (h₄ : x.1 = 27 * α) (h₆ : x.2 = 27 * β) {n : ℕ}
    (hlev : ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2)
    (hlev' : ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2) :
    ∃ V : WeierstrassCurve ℤ_[3],
      Step11.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ = Except.ok V ∧
        V.Δ ≠ 0 ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ V.c₄ ∧ V.c₆ = -32 * β ∧
        emultiplicity ((3 : ℕ) : ℤ_[3]) V.Δ = (n : ℕ∞) := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨hα, -, -⟩ := not_dvd_of_mem_locus hx h₄ h₆
  obtain ⟨V, hV, hc₄, hc₆, hΔV⟩ := exists_descent_of_mem_locus hΔ hx h₄ h₆
  refine ⟨V, hV, Δ_ne_zero_of_step11_ok hϖ hΔ hV, ?_, hc₆, ?_⟩
  · rw [hc₄]
    exact fun h => hα (isUnit_sixteen.neg.dvd_mul_left.mp h)
  · rw [hcast] at hlev hlev' ⊢
    obtain ⟨D, hD⟩ := hlev
    refine emultiplicity_eq_coe.2 ⟨⟨-16 * D, ?_⟩, ?_⟩
    · refine mul_left_cancel₀ (by norm_num : (27 : ℤ_[3]) ≠ 0) ?_
      rw [hΔV, hD]; ring
    · rintro ⟨y, hy⟩
      refine hlev' (isUnit_sixteen.dvd_mul_left.mp ⟨-y, ?_⟩)
      linear_combination hΔV - 27 * hy

/-! ### The forward run

On the descended curve the answer is multiplicative, and the tangent quadratic splits exactly when
`−c₆(V) = 32β` is a square in `𝔽₃`: `32 · 2 = 1` is a square and `32 · 1 = 2` is not. -/

/-- **Level `0` of Family B answers `(I₀, 1)`.** After the descent `3 ∤ Δ(V)`, so Step 1 exits. -/
theorem run_eq_I_zero_of_level_zero {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0)
    (hx : x ∈ locus) {α β : ℤ_[3]} (h₄ : x.1 = 27 * α) (h₆ : x.2 = 27 * β)
    (hlev : ¬ ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ 4 * α ^ 3 + β ^ 2) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I 0 ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = 1 := by
  have hcast : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
  have hϖ : ((3 : ℕ) : ℤ_[3]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨V, hV, -, -, hΔV⟩ := exists_descent_of_mem_locus hΔ hx h₄ h₆
  have hVΔ0 : V.Δ ≠ 0 := Δ_ne_zero_of_step11_ok hϖ hΔ hV
  have hnd : ¬ ((3 : ℕ) : ℤ_[3]) ∣ V.Δ := by
    rintro ⟨y, hy⟩
    rw [hcast] at hy hlev
    refine hlev (isUnit_sixteen.dvd_mul_left.mp ⟨-y, ?_⟩)
    linear_combination hΔV - 27 * hy
  rw [run_eq_of_step11_ok hϖ hΔ hV hVΔ0, run_eq_of_not_dvd_Δ hVΔ0 hnd]
  exact ⟨rfl, rfl⟩

/-- **The split half of Family B at level `n ≥ 1` answers `(Iₙ, n)`.** `β ≡ 2 (mod 3)` makes
`−c₆(V) = 32β ≡ 1` a square in `𝔽₃`, so the tangent quadratic of the descended curve splits. -/
theorem run_eq_I_of_split {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) (hx : x ∈ locus)
    {α β : ℤ_[3]} (h₄ : x.1 = 27 * α) (h₆ : x.2 = 27 * β) {n : ℕ} (hn : 1 ≤ n)
    (hlev : ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2)
    (hlev' : ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2)
    (hsplit : PadicInt.toZMod β = 2) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = n := by
  obtain ⟨V, hV, hVΔ0, hc₄, hc₆, hem⟩ := exists_descent_of_level hΔ hx h₄ h₆ hlev hlev'
  have hsq : Step2.TangentSplits ((3 : ℕ) : ℤ_[3]) V := by
    rw [Step2.tangentSplits_iff_isSquare_neg_c₆ (dvd_Δ_of_emultiplicity_eq hn hem) hc₄
      (not_dvd_two_of_odd (by decide)), hc₆,
      BSDTamagawa.HeadSumThree.isSquare_mod_iff_isSquare_toZMod]
    simp only [map_neg, map_mul, map_ofNat, hsplit]
    exact ⟨1, by decide⟩
  rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ hV hVΔ0]
  exact run_kodaira_tamagawa_of_tangentSplits hVΔ0 hc₄ hn hem hsq

/-- **The non-split half of Family B at level `n ≥ 1` answers `(Iₙ, if Odd n then 1 else 2)`.**
`β ≡ 1 (mod 3)` makes `−c₆(V) = 32β ≡ 2` a non-square in `𝔽₃`, so Step 2 of the restarted run takes
its non-split branch. -/
theorem run_eq_I_of_nonsplit {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0)
    (hx : x ∈ locus) {α β : ℤ_[3]} (h₄ : x.1 = 27 * α) (h₆ : x.2 = 27 * β) {n : ℕ} (hn : 1 ≤ n)
    (hlev : ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2)
    (hlev' : ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2)
    (hns : PadicInt.toZMod β = 1) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = if Odd n then 1 else 2 := by
  obtain ⟨V, hV, hVΔ0, hc₄, hc₆, hem⟩ := exists_descent_of_level hΔ hx h₄ h₆ hlev hlev'
  have h3Δ : ((3 : ℕ) : ℤ_[3]) ∣ V.Δ := dvd_Δ_of_emultiplicity_eq hn hem
  have hnsplit : ¬ Step2.TangentSplits ((3 : ℕ) : ℤ_[3]) V := by
    rw [Step2.tangentSplits_iff_isSquare_neg_c₆ h3Δ hc₄ (not_dvd_two_of_odd (by decide)), hc₆,
      BSDTamagawa.HeadSumThree.isSquare_mod_iff_isSquare_toZMod]
    simp only [map_neg, map_mul, map_ofNat, hns]
    rintro ⟨r, hr⟩
    revert r
    decide
  have hnt : (emultiplicity ((3 : ℕ) : ℤ_[3]) V.Δ).toNat = n :=
    (toNat_emultiplicity_Δ_eq_iff hVΔ0 n).2 hem
  rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ hV hVΔ0]
  refine ⟨?_, ?_⟩
  · rw [run_kodairaSymbol_of_nodal hVΔ0 h3Δ hc₄, hnt]
  · rw [run_tamagawaNumber_of_nodal hVΔ0 h3Δ hc₄, hnt, ite_eq_right hnsplit]

end FamilyBThree

end WeierstrassCurve

end
