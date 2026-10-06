/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.HeadSumThree

/-!
# Fibrewise affine maps of the coefficient plane, and the Hensel square root

For a unit `ν : ℤ_[p]` and a measurable `g : ℤ_[p] → ℤ_[p]`, the fibrewise affine map
`Φ(x, y) = (x, ν y + g x)` of `ℤ_[p] × ℤ_[p]` preserves Haar measure, and carries every set, not
necessarily measurable, to a set of the same mass. For odd `p`, a nonzero residue `j` and
`c ≡ j² (mod p)`, Hensel's lemma gives a unique square root of `c` congruent to `j`, and this
branch is a continuous function of `c`. The map `(a₄, a₆) ↦ (a₄, ν a₆ + (1 - ν) p³ h(a₄))`, meant
for `h` a Hensel square-root branch, is defined as a fibrewise affine map.

## Main definitions

* `PadicInt.fibreAffine`: the map `Φ_{ν,g}(x, y) = (x, ν y + g x)`.
* `PadicInt.sqrtBranch`: the Hensel square-root branch, extended by `0`.
* `PadicInt.involutionPlane`: the map `(a₄, a₆) ↦ (a₄, ν a₆ + (1 - ν) p³ h(a₄))`.

## Main results

* `PadicInt.measurePreserving_fibreAffine`: `Φ_{ν,g}` preserves `volume` on `ℤ_[p] × ℤ_[p]`.
* `PadicInt.volume_preimage_fibreAffine`, `PadicInt.volume_image_fibreAffine`:
  `μ_p(Φ⁻¹(S)) = μ_p(S)` and `μ_p(Φ(S)) = μ_p(S)` for an arbitrary `S`.
* `PadicInt.volume_image_eq_of_piecewise_fibreAffine`: the same conclusion for a map that agrees
  with a fibrewise affine map only piecewise, over a countable measurable family of pairwise
  disjoint pieces each of which is preserved.
* `PadicInt.existsUnique_sq_eq_of_toZMod_eq`: for odd `p`, a nonzero residue `j : ZMod p` and
  `c ≡ j² (mod p)`, there is a unique `h : ℤ_[p]` with `h² = c` and `h ≡ j (mod p)`.
* `PadicInt.norm_sqrtBranch_sub`, `PadicInt.continuous_sqrtBranch`,
  `PadicInt.measurable_sqrtBranch`: the branch is an isometry of the residue class `{c ≡ j²}`, and
  is continuous and measurable.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ## Fibrewise affine maps of the plane -/

/-- **The fibrewise affine map.** `Φ_{ν,g}(x, y) = (x, ν y + g x)`: the identity on the first
coordinate, and an affine map of slope `ν` on each fibre of the first projection, the additive
constant depending on the point only through its first coordinate. -/
noncomputable def fibreAffine (ν : ℤ_[p]) (g : ℤ_[p] → ℤ_[p]) :
    ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p] := fun z => (z.1, ν * z.2 + g z.1)

/-- `Φ_{ν,g}(z) = (z₁, ν z₂ + g z₁)`. -/
theorem fibreAffine_apply (ν : ℤ_[p]) (g : ℤ_[p] → ℤ_[p]) (z : ℤ_[p] × ℤ_[p]) :
    fibreAffine ν g z = (z.1, ν * z.2 + g z.1) := rfl

/-- `Φ_{ν,g}` fixes the first coordinate. -/
@[simp]
theorem fibreAffine_fst (ν : ℤ_[p]) (g : ℤ_[p] → ℤ_[p]) (z : ℤ_[p] × ℤ_[p]) :
    (fibreAffine ν g z).1 = z.1 := rfl

/-- The second coordinate of `Φ_{ν,g}(z)` is `ν z₂ + g z₁`. -/
@[simp]
theorem fibreAffine_snd (ν : ℤ_[p]) (g : ℤ_[p] → ℤ_[p]) (z : ℤ_[p] × ℤ_[p]) :
    (fibreAffine ν g z).2 = ν * z.2 + g z.1 := rfl

/-- `Φ_{ν,g}` is measurable as soon as `g` is. -/
@[fun_prop]
theorem measurable_fibreAffine (ν : ℤ_[p]) {g : ℤ_[p] → ℤ_[p]} (hg : Measurable g) :
    Measurable (fibreAffine ν g) :=
  measurable_fst.prodMk
    ((measurable_const.mul measurable_snd).add (hg.comp measurable_fst))

/-- **The inverse of a fibrewise affine map is fibrewise affine.** If `w ν = 1` then
`Φ_{w, -w g} ∘ Φ_{ν, g} = id`; `PadicInt.fibreAffine_fibreAffine'` is the composite in the other
order. -/
theorem fibreAffine_fibreAffine {ν w : ℤ_[p]} (h : w * ν = 1) (g : ℤ_[p] → ℤ_[p])
    (z : ℤ_[p] × ℤ_[p]) :
    fibreAffine w (fun x => -(w * g x)) (fibreAffine ν g z) = z := by
  have hsnd : w * (ν * z.2 + g z.1) + -(w * g z.1) = z.2 := by
    have : w * (ν * z.2 + g z.1) + -(w * g z.1) = (w * ν) * z.2 := by ring
    rw [this, h, one_mul]
  simp only [fibreAffine_apply]
  rw [hsnd]

/-- **Fibrewise affine maps preserve Haar measure.** For a unit `ν : ℤ_[p]` and a measurable
`g : ℤ_[p] → ℤ_[p]`, the map `Φ_{ν,g}(x, y) = (x, ν y + g x)` is measure preserving for the Haar
probability measure `volume` on `ℤ_[p] × ℤ_[p]`. -/
theorem measurePreserving_fibreAffine {ν : ℤ_[p]} (hν : IsUnit ν) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) :
    MeasurePreserving (fibreAffine ν g) (volume : Measure (ℤ_[p] × ℤ_[p])) volume := by
  have hfibre : ∀ x : ℤ_[p],
      MeasurePreserving (fun y : ℤ_[p] => ν * y + g x) (volume : Measure ℤ_[p]) volume := fun x =>
    (measurePreserving_add_right (volume : Measure ℤ_[p]) (g x)).comp
      (measurePreserving_mul_of_isUnit hν)
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (volume : Measure ℤ_[p])).skew_product
    ((measurable_const.mul measurable_snd).add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => (hfibre x).map_eq)

/-- The composite in the other order: `Φ_{ν,g} ∘ Φ_{w, -w g} = id` when `w ν = 1`. -/
theorem fibreAffine_fibreAffine' {ν w : ℤ_[p]} (h : w * ν = 1) (g : ℤ_[p] → ℤ_[p])
    (z : ℤ_[p] × ℤ_[p]) :
    fibreAffine ν g (fibreAffine w (fun x => -(w * g x)) z) = z := by
  have hνw : ν * w = 1 := by rw [mul_comm]; exact h
  have hsnd : ν * (w * z.2 + -(w * g z.1)) + g z.1
      = (ν * w) * z.2 - (ν * w) * g z.1 + g z.1 := by ring
  simp only [fibreAffine_apply, hsnd, hνw, one_mul, sub_add_cancel]

/-- **The image of a set under `Φ_{ν,g}` is the preimage under its inverse.** -/
theorem image_fibreAffine {ν w : ℤ_[p]} (h : w * ν = 1) (g : ℤ_[p] → ℤ_[p])
    (S : Set (ℤ_[p] × ℤ_[p])) :
    fibreAffine ν g '' S = fibreAffine w (fun x => -(w * g x)) ⁻¹' S := by
  ext y
  simp only [Set.mem_image, Set.mem_preimage]
  refine ⟨?_, fun hy => ⟨_, hy, fibreAffine_fibreAffine' h g y⟩⟩
  rintro ⟨x, hx, rfl⟩
  rwa [fibreAffine_fibreAffine h g x]

/-- **`Φ_{ν,g}` is a measurable embedding** whenever `ν` has an inverse `w` and `g` is
measurable. -/
theorem measurableEmbedding_fibreAffine {ν w : ℤ_[p]} (h : w * ν = 1) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) : MeasurableEmbedding (fibreAffine ν g) where
  injective := Function.LeftInverse.injective (fibreAffine_fibreAffine h g)
  measurable := measurable_fibreAffine ν hg
  measurableSet_image' := fun _ hA => by
    rw [image_fibreAffine h g _]
    exact measurable_fibreAffine w ((hg.const_mul w).neg) hA

/-- **`Φ_{ν,g}` as a measurable equivalence of the plane.** Its inverse is the fibrewise affine map
`Φ_{w, -w g}`, where `w ν = 1`. -/
noncomputable def fibreAffineEquiv {ν w : ℤ_[p]} (h : w * ν = 1) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) : (ℤ_[p] × ℤ_[p]) ≃ᵐ (ℤ_[p] × ℤ_[p]) :=
  { toEquiv :=
      { toFun := fibreAffine ν g
        invFun := fibreAffine w (fun x => -(w * g x))
        left_inv := fibreAffine_fibreAffine h g
        right_inv := fibreAffine_fibreAffine' h g }
    measurable_toFun := measurable_fibreAffine ν hg
    measurable_invFun := measurable_fibreAffine w ((hg.const_mul w).neg) }

/-- The measurable equivalence `fibreAffineEquiv h hg` acts as `Φ_{ν,g}`. -/
@[simp]
theorem fibreAffineEquiv_apply {ν w : ℤ_[p]} (h : w * ν = 1) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) (z : ℤ_[p] × ℤ_[p]) :
    fibreAffineEquiv h hg z = fibreAffine ν g z := rfl

/-- The inverse of `fibreAffineEquiv h hg` acts as `Φ_{w, -w g}`. -/
@[simp]
theorem fibreAffineEquiv_symm_apply {ν w : ℤ_[p]} (h : w * ν = 1) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) (z : ℤ_[p] × ℤ_[p]) :
    (fibreAffineEquiv h hg).symm z = fibreAffine w (fun x => -(w * g x)) z := rfl

/-- **Preimages under `Φ_{ν,g}` have the same mass.** For an *arbitrary* `S ⊆ ℤ_[p] × ℤ_[p]`,
`μ_p(Φ_{ν,g}⁻¹(S)) = μ_p(S)`. -/
theorem volume_preimage_fibreAffine {ν : ℤ_[p]} (hν : IsUnit ν) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) (S : Set (ℤ_[p] × ℤ_[p])) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (fibreAffine ν g ⁻¹' S) = volume S := by
  obtain ⟨w, hw⟩ := hν.exists_left_inv
  rw [← (measurableEmbedding_fibreAffine hw hg).map_apply,
    (measurePreserving_fibreAffine hν hg).map_eq]

/-- **Images under `Φ_{ν,g}` have the same mass.** For an *arbitrary* `S ⊆ ℤ_[p] × ℤ_[p]`,
`μ_p(Φ_{ν,g}(S)) = μ_p(S)`. -/
theorem volume_image_fibreAffine {ν : ℤ_[p]} (hν : IsUnit ν) {g : ℤ_[p] → ℤ_[p]}
    (hg : Measurable g) (S : Set (ℤ_[p] × ℤ_[p])) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (fibreAffine ν g '' S) = volume S := by
  obtain ⟨w, hw⟩ := hν.exists_left_inv
  have hwu : IsUnit w := IsUnit.of_mul_eq_one ν hw
  rw [image_fibreAffine hw g S]
  exact volume_preimage_fibreAffine hwu ((hg.const_mul w).neg) S

/-- **The piecewise form.** Let `U : ι → Set (ℤ_p²)` be a countable family of pairwise disjoint
measurable sets covering the measurable set `S`, let `ν` be a unit, and for each `i` let
`g i : ℤ_[p] → ℤ_[p]` be measurable with `Φ_{ν, g i}` mapping `U i` into itself. If `Ψ` agrees with
`Φ_{ν, g i}` on `S ∩ U i` for every `i`, then `μ_p(Ψ(S)) = μ_p(S)`. -/
theorem volume_image_eq_of_piecewise_fibreAffine {ι : Type*} [Countable ι] {ν : ℤ_[p]}
    (hν : IsUnit ν) {g : ι → ℤ_[p] → ℤ_[p]} (hg : ∀ i, Measurable (g i))
    {U : ι → Set (ℤ_[p] × ℤ_[p])} (hU : ∀ i, MeasurableSet (U i))
    (hdisj : Pairwise (Function.onFun Disjoint U)) (hstab : ∀ i, fibreAffine ν (g i) '' U i ⊆ U i)
    {Ψ : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]} {S : Set (ℤ_[p] × ℤ_[p])} (hS : MeasurableSet S)
    (hcover : S ⊆ ⋃ i, U i) (hΨ : ∀ i, Set.EqOn Ψ (fibreAffine ν (g i)) (S ∩ U i)) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (Ψ '' S) = volume S := by
  obtain ⟨w, hw⟩ := hν.exists_left_inv
  have hSdecomp : S = ⋃ i, S ∩ U i := by
    rw [← Set.inter_iUnion, Set.inter_eq_self_of_subset_left hcover]
  have hsub : ∀ i, fibreAffine ν (g i) '' (S ∩ U i) ⊆ U i := fun i =>
    (Set.image_mono Set.inter_subset_right).trans (hstab i)
  have hmeasimg : ∀ i, MeasurableSet (fibreAffine ν (g i) '' (S ∩ U i)) := fun i =>
    (measurableEmbedding_fibreAffine hw (hg i)).measurableSet_image.2 (hS.inter (hU i))
  have hdisjimg :
      Pairwise (Function.onFun Disjoint fun i => fibreAffine ν (g i) '' (S ∩ U i)) :=
    fun i k hik => (hdisj hik).mono (hsub i) (hsub k)
  have hdisjS : Pairwise (Function.onFun Disjoint fun i => S ∩ U i) :=
    fun i k hik => (hdisj hik).mono Set.inter_subset_right Set.inter_subset_right
  have himg : Ψ '' S = ⋃ i, fibreAffine ν (g i) '' (S ∩ U i) := by
    conv_lhs => rw [hSdecomp]
    rw [Set.image_iUnion]
    exact Set.iUnion_congr fun i => (hΨ i).image_eq
  calc (volume : Measure (ℤ_[p] × ℤ_[p])) (Ψ '' S)
      = ∑' i, volume (fibreAffine ν (g i) '' (S ∩ U i)) := by
        rw [himg, measure_iUnion hdisjimg hmeasimg]
    _ = ∑' i, volume (S ∩ U i) :=
        tsum_congr fun i => volume_image_fibreAffine hν (hg i) (S ∩ U i)
    _ = volume S := by rw [← measure_iUnion hdisjS (fun i => hS.inter (hU i)), ← hSdecomp]

/-! ## The Hensel square root -/

/-- The `PadicInt.toZMod`-preimage of an arbitrary set of residues is open. -/
theorem isOpen_preimage_toZMod (S : Set (ZMod p)) : IsOpen (toZMod ⁻¹' S : Set ℤ_[p]) := by
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨1, one_pos, fun y hy => ?_⟩
  have hdvd : (p : ℤ_[p]) ∣ y - x :=
    (norm_lt_one_iff_dvd _).mp (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hy)
  have hyx : toZMod y = toZMod x := by
    have h0 := dvd_iff_toZMod_eq_zero.mp hdvd
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  simpa only [Set.mem_preimage, hyx] using hx

/-- A `p`-adic integer with nonzero residue is a unit. -/
theorem isUnit_of_toZMod_ne_zero {x : ℤ_[p]} (hx : toZMod x ≠ 0) : IsUnit x := by
  rw [isUnit_iff]
  rcases lt_or_eq_of_le (norm_le_one x) with h | h
  · exact absurd (dvd_iff_toZMod_eq_zero.mp ((norm_lt_one_iff_dvd x).mp h)) hx
  · exact h

/-- **The Hensel square root, with its branch.** For odd `p`, a nonzero residue `j : ZMod p` and
`c : ℤ_[p]` whose residue is `j²`, there is exactly one `h : ℤ_[p]` with `h² = c` and
`h ≡ j (mod p)`. -/
theorem existsUnique_sq_eq_of_toZMod_eq (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) {c : ℤ_[p]}
    (hc : toZMod c = j ^ 2) : ∃! h : ℤ_[p], h ^ 2 = c ∧ toZMod h = j := by
  obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective (toZMod : ℤ_[p] →+* ZMod p) j
  have ha₀unit : IsUnit a₀ := isUnit_of_toZMod_ne_zero (by rw [ha₀]; exact hj)
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C c with hF
  have hderiv : Polynomial.derivative F = 2 * Polynomial.X := by
    simp [hF]; ring
  have hDnorm : ‖(Polynomial.aeval a₀) (Polynomial.derivative F)‖ = 1 := by
    rw [hderiv]
    simp only [map_mul, map_ofNat, Polynomial.aeval_X]
    rw [← isUnit_iff]
    exact (isUnit_two hp).mul ha₀unit
  have hcond : ‖(Polynomial.aeval a₀) F‖
      < ‖(Polynomial.aeval a₀) (Polynomial.derivative F)‖ ^ 2 := by
    rw [hDnorm, one_pow, show (Polynomial.aeval a₀) F = a₀ ^ 2 - c from by simp [hF],
      norm_lt_one_iff_dvd, dvd_iff_toZMod_eq_zero, map_sub, map_pow, ha₀, hc, sub_self]
  obtain ⟨z, hz, hzdist, -, huniq⟩ := hensels_lemma hcond
  rw [show (Polynomial.aeval z) F = z ^ 2 - c from by simp [hF], sub_eq_zero] at hz
  have hztoZ : toZMod z = j := by
    rw [hDnorm] at hzdist
    have h0 := dvd_iff_toZMod_eq_zero.mp ((norm_lt_one_iff_dvd _).mp hzdist)
    rw [map_sub, sub_eq_zero, ha₀] at h0
    exact h0
  refine ⟨z, ⟨hz, hztoZ⟩, ?_⟩
  rintro y ⟨hysq, hyj⟩
  refine huniq y ?_ ?_
  · rw [show (Polynomial.aeval y) F = y ^ 2 - c from by simp [hF], hysq, sub_self]
  · rw [hDnorm, norm_lt_one_iff_dvd, dvd_iff_toZMod_eq_zero, map_sub, hyj, ha₀, sub_self]

open Classical in
/-- **The Hensel square-root branch**, as a total function. `sqrtBranch j c` is the unique
`h : ℤ_[p]` with `h² = c` and `h ≡ j (mod p)` when one exists, and `0` otherwise; by
`PadicInt.existsUnique_sq_eq_of_toZMod_eq` one exists exactly when `p` is odd, `j ≠ 0` and
`c ≡ j² (mod p)`. -/
noncomputable def sqrtBranch (j : ZMod p) (c : ℤ_[p]) : ℤ_[p] :=
  if h : ∃ x : ℤ_[p], x ^ 2 = c ∧ toZMod x = j then h.choose else 0

/-- Where a branch exists, `PadicInt.sqrtBranch` is one. -/
theorem sqrtBranch_spec {j : ZMod p} {c : ℤ_[p]} (h : ∃ x : ℤ_[p], x ^ 2 = c ∧ toZMod x = j) :
    sqrtBranch j c ^ 2 = c ∧ toZMod (sqrtBranch j c) = j := by
  classical
  rw [sqrtBranch, dite_eq_left h]
  exact h.choose_spec

/-- Where no branch exists, `PadicInt.sqrtBranch` is `0`. -/
theorem sqrtBranch_eq_zero {j : ZMod p} {c : ℤ_[p]}
    (h : ¬ ∃ x : ℤ_[p], x ^ 2 = c ∧ toZMod x = j) : sqrtBranch j c = 0 := by
  classical
  rw [sqrtBranch, dite_eq_right h]

/-- `PadicInt.sqrtBranch j` vanishes off the residue class `{c | c ≡ j² (mod p)}`: a square root
congruent to `j` forces the residue of `c` to be `j²`. -/
theorem sqrtBranch_eq_zero_of_toZMod_ne {j : ZMod p} {c : ℤ_[p]} (h : toZMod c ≠ j ^ 2) :
    sqrtBranch j c = 0 :=
  sqrtBranch_eq_zero fun ⟨x, hx, hxj⟩ => h (by rw [← hx, map_pow, hxj])

/-- `PadicInt.sqrtBranch j c` squares to `c` on the residue class `{c | c ≡ j² (mod p)}`. -/
theorem sq_sqrtBranch (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) {c : ℤ_[p]}
    (hc : toZMod c = j ^ 2) : sqrtBranch j c ^ 2 = c :=
  (sqrtBranch_spec (existsUnique_sq_eq_of_toZMod_eq hp hj hc).exists).1

/-- `PadicInt.sqrtBranch j c` is congruent to `j` on the residue class `{c | c ≡ j² (mod p)}`. -/
theorem toZMod_sqrtBranch (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) {c : ℤ_[p]}
    (hc : toZMod c = j ^ 2) : toZMod (sqrtBranch j c) = j :=
  (sqrtBranch_spec (existsUnique_sq_eq_of_toZMod_eq hp hj hc).exists).2

/-- **Uniqueness.** Any square root of `c` congruent to `j` is `PadicInt.sqrtBranch j c`. -/
theorem eq_sqrtBranch (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) {c x : ℤ_[p]} (hx : x ^ 2 = c)
    (hxj : toZMod x = j) : x = sqrtBranch j c := by
  have hc : toZMod c = j ^ 2 := by rw [← hx, map_pow, hxj]
  obtain ⟨_, _, huniq⟩ := existsUnique_sq_eq_of_toZMod_eq hp hj hc
  rw [huniq x ⟨hx, hxj⟩, huniq (sqrtBranch j c) (sqrtBranch_spec ⟨x, hx, hxj⟩)]

/-- **The branch is an isometry of its residue class.** For `c, d ≡ j² (mod p)`,
`‖√c - √d‖ = ‖c - d‖`. -/
theorem norm_sqrtBranch_sub (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) {c d : ℤ_[p]}
    (hc : toZMod c = j ^ 2) (hd : toZMod d = j ^ 2) :
    ‖sqrtBranch j c - sqrtBranch j d‖ = ‖c - d‖ := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h := (isUnit_two hp).map (toZMod : ℤ_[p] →+* ZMod p)
    rw [show ((toZMod : ℤ_[p] →+* ZMod p) 2) = (2 : ZMod p) from map_ofNat _ 2] at h
    exact h.ne_zero
  have hsum : IsUnit (sqrtBranch j c + sqrtBranch j d) := by
    refine isUnit_of_toZMod_ne_zero ?_
    rw [map_add, toZMod_sqrtBranch hp hj hc, toZMod_sqrtBranch hp hj hd, ← two_mul]
    exact mul_ne_zero h2 hj
  have hfac : (sqrtBranch j c - sqrtBranch j d) * (sqrtBranch j c + sqrtBranch j d) = c - d :=
    calc (sqrtBranch j c - sqrtBranch j d) * (sqrtBranch j c + sqrtBranch j d)
        = sqrtBranch j c ^ 2 - sqrtBranch j d ^ 2 := by ring
      _ = c - d := by rw [sq_sqrtBranch hp hj hc, sq_sqrtBranch hp hj hd]
  have hnorm := congrArg norm hfac
  rwa [norm_mul, isUnit_iff.mp hsum, mul_one] at hnorm

/-- The branch is `1`-Lipschitz on its residue class, by `PadicInt.norm_sqrtBranch_sub`. -/
theorem lipschitzOnWith_sqrtBranch (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) :
    LipschitzOnWith 1 (sqrtBranch j : ℤ_[p] → ℤ_[p]) (toZMod ⁻¹' {j ^ 2}) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm, norm_sqrtBranch_sub hp hj hx hy]
  simp

/-- **The branch is continuous.** -/
theorem continuous_sqrtBranch (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) :
    Continuous (sqrtBranch j : ℤ_[p] → ℤ_[p]) := by
  rw [continuous_iff_continuousAt]
  intro c
  by_cases hc : toZMod c = j ^ 2
  · exact ((lipschitzOnWith_sqrtBranch hp hj).continuousOn c hc).continuousAt
      ((isOpen_preimage_toZMod {j ^ 2}).mem_nhds hc)
  · have hev : (sqrtBranch j : ℤ_[p] → ℤ_[p]) =ᶠ[nhds c] fun _ => 0 := by
      filter_upwards [(isOpen_preimage_toZMod ({j ^ 2}ᶜ)).mem_nhds hc] with y hy
      exact sqrtBranch_eq_zero_of_toZMod_ne hy
    exact (continuousAt_const (y := (0 : ℤ_[p]))).congr hev.symm

/-- **The branch is measurable.** -/
theorem measurable_sqrtBranch (hp : Odd p) {j : ZMod p} (hj : j ≠ 0) :
    Measurable (sqrtBranch j : ℤ_[p] → ℤ_[p]) := (continuous_sqrtBranch hp hj).measurable

/-! ## The involution of the coefficient plane -/

/-- `Φ(a₄, a₆) = (a₄, ν a₆ + (1 - ν) p³ h(a₄))`: the fibrewise affine map of slope `ν` whose
additive constant is `(1 - ν) p³` times the value at `a₄` of a branch function `h`; it is an
involution when `ν² = 1`. -/
noncomputable def involutionPlane (ν : ℤ_[p]) (h : ℤ_[p] → ℤ_[p]) :
    ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p] :=
  fibreAffine ν fun a₄ => (1 - ν) * (p : ℤ_[p]) ^ 3 * h a₄

/-- `Φ(z) = (z₁, ν z₂ + (1 - ν) p³ h(z₁))`. -/
@[simp]
theorem involutionPlane_apply (ν : ℤ_[p]) (h : ℤ_[p] → ℤ_[p]) (z : ℤ_[p] × ℤ_[p]) :
    involutionPlane ν h z = (z.1, ν * z.2 + (1 - ν) * (p : ℤ_[p]) ^ 3 * h z.1) := rfl

end PadicInt
