/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.FiberwiseAffine
public import BSDTamagawa.GOTTable.InStarGoodRegion

/-!
# The unit twist exchanging `goodRegion p m 2` and `goodRegion p m 4`

For `p ≥ 5` and `m ≥ 1`, the two regions `goodRegion p m 2` and `goodRegion p m 4` of the
`(A, B)` plane carry the same Haar mass.

`goodRegion p m c` consists of the pairs `(A, B) = (-3t², 2t³ + pᵐc₀)` with `t` and `c₀` units and
`c` the value `if IsSquare (goodModelTest t c₀ m) then 4 else 2`. Fix a unit `ν` of `ℤ_[p]` whose
residue is a quadratic non-residue. The map

  `planeTwist ν (A, B) = (A, ν B + (1 - ν) · √(radicand A))`,

where `radicand A = -4A³/27` and `√` is the Hensel branch `PadicInt.sqrtBranch` chosen by the
residue of `B`, sends `(-3t², 2t³ + pᵐc₀)` to `(-3t², 2t³ + pᵐ(νc₀))`, since
`radicand (-3t²) = (2t³)²` and `2t³ ≡ B (mod p)`. As `goodModelTest t (νc₀) m` is
`ν · goodModelTest t c₀ m`, the square test flips, so `planeTwist ν` carries `goodRegion p m 2`
onto `goodRegion p m 4`. On each piece of the plane where `B` has a fixed residue, `planeTwist ν`
is affine of slope `ν` in `B` with an additive constant depending only on `A`, so it preserves Haar
measure.

## Main definitions

* `PadicInt.radicand`: the function `A ↦ -4A³/27` on `ℤ_[p]`.
* `PadicInt.planeTwist`: the map `(A, B) ↦ (A, ν B + (1 - ν) · √(radicand A))`.

## Main results

* `PadicInt.volume_image_planeTwist`: for a unit `ν`, `planeTwist ν` preserves Haar mass on
  measurable sets on which the residue of `B` is nonzero and the branch is congruent to `B`.
* `WeierstrassCurve.planeTwist_image_goodRegion_two`: `planeTwist ν` maps `goodRegion p m 2` onto
  `goodRegion p m 4`.
* `WeierstrassCurve.volume_goodRegion_two_eq_four`: for `5 ≤ p`, `1 ≤ m` and `goodRegion p m 2`
  measurable, `volume (goodRegion p m 2) = volume (goodRegion p m 4)`.
-/

open MeasureTheory Set CommRing Ideal

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ## The radicand and its Hensel branch -/

/-- **The radicand of the branch**, `-4A³/27`. It is `B² - D/27` for `D = 4A³ + 27B²`, hence a
function of `A` alone. -/
noncomputable def radicand (A : ℤ_[p]) : ℤ_[p] := (27 : ℤ_[p]).inv * (-4 * A ^ 3)

/-- `radicand` is continuous, being a constant multiple of a polynomial. -/
theorem continuous_radicand : Continuous (radicand : ℤ_[p] → ℤ_[p]) :=
  continuous_const.mul (continuous_const.mul (continuous_id.pow 3))

/-- `radicand` is measurable, being continuous. -/
theorem measurable_radicand : Measurable (radicand : ℤ_[p] → ℤ_[p]) :=
  continuous_radicand.measurable

/-- `27` is a unit of `ℤ_[p]` for `p ≥ 5`, being the cube of `3`. -/
theorem isUnit_twentySeven (hp : 5 ≤ p) : IsUnit (27 : ℤ_[p]) := by
  have h : ((3 : ℤ_[p])) ^ 3 = 27 := by norm_num
  exact h ▸ (isUnit_three hp).pow 3

/-- **The radicand at `A = -3t²` is `4t⁶`**: for `p ≥ 5`, `-4(-3t²)³/27 = 4t⁶`. -/
theorem radicand_neg_three_mul_sq (hp : 5 ≤ p) (t : ℤ_[p]) :
    radicand ((-3) * t ^ 2) = 4 * t ^ 6 := by
  have h27 : (27 : ℤ_[p]).inv * 27 = 1 := inv_mul (isUnit_iff.mp (isUnit_twentySeven hp))
  calc radicand ((-3) * t ^ 2 : ℤ_[p])
      = (27 : ℤ_[p]).inv * 27 * (4 * t ^ 6) := by rw [radicand]; ring
    _ = 4 * t ^ 6 := by rw [h27, one_mul]

/-- **A unit of `ℤ_[p]` has nonzero residue.** -/
theorem toZMod_ne_zero_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) : toZMod x ≠ 0 := fun h =>
  ((norm_lt_one_iff_dvd x).2 (dvd_iff_toZMod_eq_zero.2 h)).ne (isUnit_iff.mp hx)

/-- **`2t³` is a unit** when `t` is and `p` is odd. -/
theorem isUnit_two_mul_cube (hp : Odd p) {t : ℤ_[p]} (ht : IsUnit t) : IsUnit (2 * t ^ 3 : ℤ_[p]) :=
  (isUnit_two hp).mul (ht.pow 3)

/-- **Adding a multiple of `pᵐ` does not change the residue** when `m ≥ 1`. -/
theorem toZMod_add_pow_mul (x c : ℤ_[p]) {m : ℕ} (hm : 1 ≤ m) :
    toZMod (x + (p : ℤ_[p]) ^ m * c) = toZMod x := by
  rw [map_add, dvd_iff_toZMod_eq_zero.mp (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) c),
    add_zero]

/-- **The branch at a point of the good region.** For `p ≥ 5`, `t` a unit and `m ≥ 1`, the Hensel
square root of `radicand (-3t²)` in the branch labelled by the residue of `B = 2t³ + pᵐc₀` is
`2t³`: indeed `radicand (-3t²) = (2t³)²` and `B ≡ 2t³ (mod p)`. -/
theorem sqrtBranch_radicand_neg_three_mul_sq (hp : 5 ≤ p) {t : ℤ_[p]} (ht : IsUnit t) {m : ℕ}
    (hm : 1 ≤ m) (c₀ : ℤ_[p]) :
    sqrtBranch (toZMod (2 * t ^ 3 + (p : ℤ_[p]) ^ m * c₀)) (radicand ((-3) * t ^ 2))
      = 2 * t ^ 3 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [toZMod_add_pow_mul _ _ hm]
  refine (eq_sqrtBranch hodd (toZMod_ne_zero_of_isUnit (isUnit_two_mul_cube hodd ht)) ?_ rfl).symm
  rw [radicand_neg_three_mul_sq hp]
  ring

/-! ## The twist of the plane -/

/-- **The twist of the `(A, B)` plane by a unit `ν`.** `planeTwist ν (A, B)` is
`(A, ν B + (1 - ν) √(radicand A))`, where `√` is the Hensel branch `PadicInt.sqrtBranch` labelled
by the residue of `B`. It fixes `A` and is affine of slope `ν` in `B`, but only after the plane is
cut along the residue of `B`, which is what fixes the branch. -/
noncomputable def planeTwist (ν : ℤ_[p]) (z : ℤ_[p] × ℤ_[p]) : ℤ_[p] × ℤ_[p] :=
  (z.1, ν * z.2 + (1 - ν) * sqrtBranch (toZMod z.2) (radicand z.1))

/-- `planeTwist ν (A, B) = (A, ν B + (1 - ν) · sqrtBranch (B mod p) (radicand A))`. -/
@[simp]
theorem planeTwist_apply (ν : ℤ_[p]) (z : ℤ_[p] × ℤ_[p]) :
    planeTwist ν z = (z.1, ν * z.2 + (1 - ν) * sqrtBranch (toZMod z.2) (radicand z.1)) := rfl

/-- **On the piece where `B ≡ j`, the twist is fibrewise affine.** `planeTwist ν` agrees there with
`PadicInt.fibreAffine ν (fun A ↦ (1 - ν) · sqrtBranch j (radicand A))`, whose additive constant
depends on the point only through `A`. -/
theorem planeTwist_eq_fibreAffine (ν : ℤ_[p]) {j : ZMod p} {z : ℤ_[p] × ℤ_[p]}
    (hz : toZMod z.2 = j) :
    planeTwist ν z = fibreAffine ν (fun A => (1 - ν) * sqrtBranch j (radicand A)) z := by
  rw [planeTwist, fibreAffine_apply, hz]

/-- **The mass of an image under `planeTwist`.** For a unit `ν` and a measurable set `S` on which
the residue of `B` is nonzero and the Hensel branch it labels is congruent to it,
`μ_p(planeTwist ν (S)) = μ_p(S)`. -/
theorem volume_image_planeTwist (hp : Odd p) {ν : ℤ_[p]} (hν : IsUnit ν)
    {S : Set (ℤ_[p] × ℤ_[p])} (hS : MeasurableSet S) (hS0 : ∀ z ∈ S, toZMod z.2 ≠ 0)
    (hbr : ∀ z ∈ S, toZMod (sqrtBranch (toZMod z.2) (radicand z.1)) = toZMod z.2) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (planeTwist ν '' S) = volume S := by
  classical
  set U : {j : ZMod p // j ≠ 0} → Set (ℤ_[p] × ℤ_[p]) := fun i =>
    {z | toZMod z.2 = i.1 ∧ toZMod (sqrtBranch i.1 (radicand z.1)) = i.1}
  have hUmeas : ∀ i, MeasurableSet (U i) := by
    intro i
    have hopen : MeasurableSet (toZMod ⁻¹' {i.1} : Set ℤ_[p]) :=
      (isOpen_preimage_toZMod {i.1}).measurableSet
    have h1 : MeasurableSet {z : ℤ_[p] × ℤ_[p] | toZMod z.2 = i.1} := measurable_snd hopen
    have h2 : MeasurableSet {z : ℤ_[p] × ℤ_[p] | toZMod (sqrtBranch i.1 (radicand z.1)) = i.1} :=
      (((measurable_sqrtBranch hp i.2).comp measurable_radicand).comp measurable_fst) hopen
    exact h1.inter h2
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro i k hik
    refine Set.disjoint_left.2 fun z hz hz' => hik (Subtype.ext ?_)
    rw [← hz.1, ← hz'.1]
  have hstab : ∀ i,
      fibreAffine ν (fun A => (1 - ν) * sqrtBranch i.1 (radicand A)) '' U i ⊆ U i := by
    rintro i _ ⟨z, hz, rfl⟩
    refine ⟨?_, hz.2⟩
    rw [fibreAffine_snd, map_add, map_mul, map_mul, map_sub, map_one, hz.1, hz.2]
    ring
  have hcover : S ⊆ ⋃ i, U i := by
    intro z hz
    exact Set.mem_iUnion.2 ⟨⟨toZMod z.2, hS0 z hz⟩, rfl, hbr z hz⟩
  refine volume_image_eq_of_piecewise_fibreAffine hν
    (fun i => ((measurable_sqrtBranch hp i.2).comp measurable_radicand).const_mul (1 - ν))
    hUmeas hdisj hstab hS hcover fun i z hz => ?_
  exact planeTwist_eq_fibreAffine ν hz.2.1

end PadicInt

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open PadicInt BSDTamagawa.HeadSumThree

/-! ## The square test flips -/

/-- **Multiplying by a non-residue flips squareness** in `ZMod p`: for `ν` of quadratic character
`-1` and `x ≠ 0`, `νx` is a square exactly when `x` is not. -/
private theorem isSquare_mul_iff_not_isSquare {ν : ZMod p} (hν : quadraticChar (ZMod p) ν = -1)
    {x : ZMod p} (hx : x ≠ 0) : IsSquare (ν * x) ↔ ¬ IsSquare x := by
  have hν0 : ν ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hν; norm_num at hν
  have hne : ν * x ≠ 0 := mul_ne_zero hν0 hx
  rw [← quadraticChar_one_iff_isSquare hne, ← quadraticChar_neg_one_iff_not_isSquare, map_mul, hν]
  constructor
  · intro h; linear_combination -h
  · intro h; rw [h]; ring

/-- **The test value is a unit** for `p ≥ 5` and `t`, `c₀` units: it is `4c₀` or `-12tc₀`, and `4`
and `-12` are units because `p ∤ 2` and `p ∤ 3`. -/
theorem isUnit_goodModelTestValue (hp : 5 ≤ p) {t c₀ : ℤ_[p]} (ht : IsUnit t) (hc₀ : IsUnit c₀)
    (m : ℕ) : IsUnit (if Odd m then 4 * c₀ else -12 * t * c₀ : ℤ_[p]) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2 : IsUnit (2 : ℤ_[p]) := isUnit_two hodd
  have h3 : IsUnit (3 : ℤ_[p]) := isUnit_three hp
  have h4 : IsUnit (4 : ℤ_[p]) := by
    have : ((2 : ℤ_[p])) ^ 2 = 4 := by norm_num
    exact this ▸ h2.pow 2
  have h12 : IsUnit (-12 : ℤ_[p]) := by
    have : (-1 : ℤ_[p]) * (4 * 3) = -12 := by ring
    exact this ▸ (isUnit_one.neg.mul (h4.mul h3))
  split_ifs with h
  · exact h4.mul hc₀
  · exact (h12.mul ht).mul hc₀

/-- **The test in `ZMod p`.** `goodModelTest t c₀ m` is a square exactly when the residue of
`4c₀` (for `m` odd) or of `-12tc₀` (for `m` even) is a square in `ZMod p`. -/
theorem isSquare_goodModelTest_iff_toZMod (t c₀ : ℤ_[p]) (m : ℕ) :
    IsSquare (goodModelTest t c₀ m) ↔
      IsSquare (toZMod (if Odd m then 4 * c₀ else -12 * t * c₀ : ℤ_[p])) := by
  rw [goodModelTest]
  split_ifs <;> exact isSquare_mod_iff_isSquare_toZMod _

/-- **The square test flips under `c₀ ↦ νc₀`.** For `p ≥ 5`, `t` and `c₀` units and `ν` a unit
whose residue is a quadratic non-residue, `goodModelTest t (νc₀) m` is a square exactly when
`goodModelTest t c₀ m` is not — in both parities at once, since `ν` scales the test either way. -/
theorem isSquare_goodModelTest_mul_iff (hp : 5 ≤ p) {ν : ℤ_[p]}
    (hns : quadraticChar (ZMod p) (toZMod ν) = -1) {t c₀ : ℤ_[p]} (ht : IsUnit t)
    (hc₀ : IsUnit c₀) (m : ℕ) :
    IsSquare (goodModelTest t (ν * c₀) m) ↔ ¬ IsSquare (goodModelTest t c₀ m) := by
  have hx : toZMod (if Odd m then 4 * c₀ else -12 * t * c₀ : ℤ_[p]) ≠ 0 :=
    toZMod_ne_zero_of_isUnit (isUnit_goodModelTestValue hp ht hc₀ m)
  rw [isSquare_goodModelTest_iff_toZMod, isSquare_goodModelTest_iff_toZMod,
    show (if Odd m then 4 * (ν * c₀) else -12 * t * (ν * c₀) : ℤ_[p])
        = ν * (if Odd m then 4 * c₀ else -12 * t * c₀ : ℤ_[p]) by split_ifs <;> ring,
    map_mul]
  exact isSquare_mul_iff_not_isSquare hns hx

/-! ## Membership in the two regions -/

open scoped Classical in
/-- **Membership in `goodRegion p m 2`**: the test is *not* a square. -/
theorem mem_goodRegion_two_iff {m : ℕ} {z : ℤ_[p] × ℤ_[p]} :
    z ∈ goodRegion p m 2 ↔ ∃ t c₀ : ℤ_[p], IsUnit t ∧ IsUnit c₀ ∧
      z = ((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * c₀) ∧
      ¬ IsSquare (goodModelTest t c₀ m) := by
  rw [mem_goodRegion_iff]
  refine exists_congr fun t => exists_congr fun c₀ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  split_ifs with h <;> simp [h]

open scoped Classical in
/-- **Membership in `goodRegion p m 4`**: the test *is* a square. -/
theorem mem_goodRegion_four_iff {m : ℕ} {z : ℤ_[p] × ℤ_[p]} :
    z ∈ goodRegion p m 4 ↔ ∃ t c₀ : ℤ_[p], IsUnit t ∧ IsUnit c₀ ∧
      z = ((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * c₀) ∧
      IsSquare (goodModelTest t c₀ m) := by
  rw [mem_goodRegion_iff]
  refine exists_congr fun t => exists_congr fun c₀ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  split_ifs with h <;> simp [h]

/-! ## The set identity -/

/-- **The twist in coordinates.** `planeTwist ν` sends the point `(-3t², 2t³ + pᵐc₀)` to
`(-3t², 2t³ + pᵐ(νc₀))`: the branch it reads is `2t³`
(`PadicInt.sqrtBranch_radicand_neg_three_mul_sq`), and
`ν(2t³ + pᵐc₀) + (1 - ν)2t³ = 2t³ + pᵐ(νc₀)`. -/
theorem planeTwist_goodPoint (hp : 5 ≤ p) {ν t : ℤ_[p]} (ht : IsUnit t) {m : ℕ} (hm : 1 ≤ m)
    (c₀ : ℤ_[p]) :
    planeTwist ν ((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * c₀)
      = ((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * (ν * c₀)) := by
  rw [planeTwist_apply, sqrtBranch_radicand_neg_three_mul_sq hp ht hm, Prod.mk.injEq]
  exact ⟨rfl, by ring⟩

/-- **The set identity.** For `5 ≤ p`, `1 ≤ m` and a unit `ν` whose residue is a quadratic
non-residue, `planeTwist ν` carries `goodRegion p m 2` onto `goodRegion p m 4`. -/
theorem planeTwist_image_goodRegion_two (hp : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m) {ν : ℤ_[p]}
    (hν : IsUnit ν) (hns : quadraticChar (ZMod p) (toZMod ν) = -1) :
    planeTwist ν '' goodRegion p m 2 = goodRegion p m 4 := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, c₀, ht, hc₀, rfl, hsq⟩ := mem_goodRegion_two_iff.mp hy
    rw [planeTwist_goodPoint hp ht hm, mem_goodRegion_four_iff]
    exact ⟨t, ν * c₀, ht, hν.mul hc₀, rfl,
      (isSquare_goodModelTest_mul_iff hp hns ht hc₀ m).mpr hsq⟩
  · intro hz
    obtain ⟨t, c₀, ht, hc₀, rfl, hsq⟩ := mem_goodRegion_four_iff.mp hz
    obtain ⟨w, hw⟩ := hν.exists_left_inv
    have hwu : IsUnit w := IsUnit.of_mul_eq_one ν hw
    have hνw : ν * (w * c₀) = c₀ := by rw [← mul_assoc, mul_comm ν w, hw, one_mul]
    refine ⟨((-3) * t ^ 2, 2 * t ^ 3 + (p : ℤ_[p]) ^ m * (w * c₀)), ?_, ?_⟩
    · refine mem_goodRegion_two_iff.mpr ⟨t, w * c₀, ht, hwu.mul hc₀, rfl, ?_⟩
      exact (isSquare_goodModelTest_mul_iff hp hns ht (hwu.mul hc₀) m).mp (by rwa [hνw])
    · rw [planeTwist_goodPoint hp ht hm, hνw]

/-! ## The masses agree -/

/-- **The residue of `B` on `goodRegion`** is that of `2t³`, hence nonzero. -/
theorem toZMod_snd_ne_zero_of_mem_goodRegion (hp : 5 ≤ p) {m c : ℕ} (hm : 1 ≤ m)
    {z : ℤ_[p] × ℤ_[p]} (hz : z ∈ goodRegion p m c) : toZMod z.2 ≠ 0 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨t, c₀, ht, -, rfl, -⟩ := hz
  rw [toZMod_add_pow_mul _ _ hm]
  exact toZMod_ne_zero_of_isUnit (isUnit_two_mul_cube hodd ht)

/-- **The branch is congruent to `B` on `goodRegion`**, since it equals `2t³` there. -/
theorem toZMod_sqrtBranch_radicand_of_mem_goodRegion (hp : 5 ≤ p) {m c : ℕ} (hm : 1 ≤ m)
    {z : ℤ_[p] × ℤ_[p]} (hz : z ∈ goodRegion p m c) :
    toZMod (sqrtBranch (toZMod z.2) (radicand z.1)) = toZMod z.2 := by
  obtain ⟨t, c₀, ht, -, rfl, -⟩ := hz
  rw [sqrtBranch_radicand_neg_three_mul_sq hp ht hm, toZMod_add_pow_mul _ _ hm]

/-- **The two regions have the same mass.** For `5 ≤ p`, `1 ≤ m` and `goodRegion p m 2`
measurable, `volume (goodRegion p m 2) = volume (goodRegion p m 4)`: the twist
`PadicInt.planeTwist ν` by a unit `ν` of non-residue character maps the first region onto the
second and preserves Haar mass. -/
theorem volume_goodRegion_two_eq_four (hp : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m)
    (hmeas : MeasurableSet (goodRegion p m 2)) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (goodRegion p m 2) = volume (goodRegion p m 4) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨ν, hν, hns⟩ := exists_isUnit_quadraticChar_eq_neg_one hp
  rw [← planeTwist_image_goodRegion_two hp hm hν hns,
    volume_image_planeTwist hodd hν hmeas
      (fun z hz => toZMod_snd_ne_zero_of_mem_goodRegion hp hm hz)
      (fun z hz => toZMod_sqrtBranch_radicand_of_mem_goodRegion hp hm hz)]

end WeierstrassCurve
