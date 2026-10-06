/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateFibreVolumeAdditive

/-!
# A lower bound on `δ_p(3)` at `p ≥ 5`

For every prime `p ≥ 5`, the scalar local density at Tamagawa number `3` satisfies
`δ_p(3) ≥ 1/(3p³)`; consequently the head sum `A_{p,3} = ∑_{1 ≤ t ≤ 4} δ_p(t) v_3(t)` satisfies
`A_{p,3} ≥ 1/(3p³)`.

The Tamagawa number `3` occurs only on split branches of Tate's algorithm: `I₃` split (Step 2),
`IV` split (Step 5) and `IV*` split (Step 8). Two of these strata are used. With `N = (p - 1)/2`
the number of nonzero squares modulo `p`:

* The split-`I₃` locus `{p ∤ a₄, v_p(4a₄³ + 27a₆²) = 3, 864 a₆ a square mod p}`, where the split
  test is that `-c₆ = 864 a₆` is a square in the residue field. For a unit `ν` with non-square
  residue, the quadratic twist `(a₄, a₆) ↦ (ν²a₄, ν³a₆)` preserves Haar measure and exchanges the
  split and non-split parts of the `I₃` locus, so the split part has at least half its mass, which
  is at least `2N²p⁻⁵`.
* The split-`IV` locus `{p² ∣ a₄, v_p(a₆) = 2, a₆/p² a square mod p}`, of mass `Np⁻⁵`. Here Step
  5's quadratic has discriminant `b₆(V)/ϖ² ≡ 4a₆/ϖ² (mod ϖ)` on the Step-2 translate `V`, so it
  splits when `a₆/p²` is a square modulo `p`.

The split-`I₃` mass alone does not suffice at `p = 5` (`3(p-1)² ≥ 2p²` fails there), but the total
`2N²p⁻⁵ + Np⁻⁵ = (p-1)/(2p⁴)` is at least `1/(3p³)`, which amounts to `(2N+1)(N-1) ≥ 0`.

## Main definitions

* `WeierstrassCurve.i3Locus`, `WeierstrassCurve.i3SplitLocus`: the `I₃` locus and its split part.
* `WeierstrassCurve.ivSplitLocus`: the split-`IV` locus.

## Main results

* `PadicInt.measure_image_mul_of_isUnit`: multiplication by a unit of `ℤ_[p]` preserves Haar
  measure.
* `WeierstrassCurve.splits_step5_quadratic`: Step 5's quadratic splits when `a₆/p²` is a square
  modulo `p`.
* `WeierstrassCurve.inv_three_mul_cube_le_δ_three`: `1/(3p³) ≤ δ_p(3)` for `p ≥ 5`.
* `WeierstrassCurve.inv_three_mul_cube_le_headSum_three`: `1/(3p³) ≤ A_{p,3}` for `p ≥ 5`.

## Implementation notes

The only difference formed in `ℝ≥0∞` is `1 - p⁻¹`, rewritten once as the product `2N p⁻¹`, so no
truncated subtraction enters; the numerical comparisons are settled in `ℕ`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace BSDTamagawa.HeadSumThree

open BSDTamagawa.HeadDensityTwoBound

variable {p : ℕ} [Fact p.Prime]

/-! ### The residue field of `ℤ_[p]` is `ZMod p` -/

/-- The ideal `(p)` of `ℤ_[p]` is the kernel of `PadicInt.toZMod`. -/
theorem span_p_eq_ker_toZMod :
    (Ideal.span {(p : ℤ_[p])}) = RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) :=
  (PadicInt.ker_toZMod.trans PadicInt.maximalIdeal_eq_span_p).symm

/-- The residue field of `ℤ_[p]` at `(p)`, as `ZMod p`. -/
noncomputable def residueEquiv (p : ℕ) [Fact p.Prime] :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq span_p_eq_ker_toZMod).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective PadicInt.toZMod))

/-- `residueEquiv` turns `CommRing.mod (p : ℤ_[p])` into `PadicInt.toZMod`. -/
@[simp]
theorem residueEquiv_mod (x : ℤ_[p]) :
    residueEquiv p (CommRing.mod (p : ℤ_[p]) x) = PadicInt.toZMod x := by
  rw [residueEquiv, RingEquiv.trans_apply, CommRing.mod, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Being a square transfers along a multiplicative equivalence. -/
theorem isSquare_mulEquiv_iff {A B : Type*} [Monoid A] [Monoid B] (e : A ≃* B) (a : A) :
    IsSquare (e a) ↔ IsSquare a :=
  ⟨fun h => by simpa using h.map e.symm, fun h => h.map e⟩

/-- `x` has square residue in `ℤ_[p] ⧸ (p)` exactly when `PadicInt.toZMod x` is a square in
`ZMod p`. -/
theorem isSquare_mod_iff_isSquare_toZMod (x : ℤ_[p]) :
    IsSquare (CommRing.mod (p : ℤ_[p]) x) ↔ IsSquare (PadicInt.toZMod x) := by
  rw [← residueEquiv_mod x]
  exact (isSquare_mulEquiv_iff (residueEquiv p).toMulEquiv _).symm

/-! ### Multiplication by the cube of a non-residue -/

/-- For `ν` of quadratic character `-1` and `x ≠ 0` in `ZMod p`, `ν³x` is a square exactly when `x`
is not. -/
theorem isSquare_cube_mul_iff {ν : ZMod p} (hν : quadraticChar (ZMod p) ν = -1)
    {x : ZMod p} (hx : x ≠ 0) : IsSquare (ν ^ 3 * x) ↔ ¬ IsSquare x := by
  have hν0 : ν ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hν; norm_num at hν
  have hne : ν ^ 3 * x ≠ 0 := mul_ne_zero (pow_ne_zero 3 hν0) hx
  rw [← quadraticChar_one_iff_isSquare hne, ← quadraticChar_neg_one_iff_not_isSquare,
    map_mul, map_pow, hν]
  constructor
  · intro h; linear_combination -h
  · intro h; rw [h]; ring

/-- For `p ≥ 5` there is a unit of `ℤ_[p]` whose residue has quadratic character `-1`. -/
theorem exists_isUnit_quadraticChar_eq_neg_one (hp : 5 ≤ p) :
    ∃ ν : ℤ_[p], IsUnit ν ∧ quadraticChar (ZMod p) (PadicInt.toZMod ν) = -1 := by
  obtain ⟨n, hn⟩ := quadraticChar_exists_neg_one (F := ZMod p) (ringChar_ne_two hp)
  obtain ⟨ν, hν⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) n
  have hn0 : n ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hn; norm_num at hn
  refine ⟨ν, isUnit_of_not_dvd ?_, by rw [hν]; exact hn⟩
  rw [PadicInt.dvd_iff_toZMod_eq_zero, hν]
  exact hn0

end BSDTamagawa.HeadSumThree

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ### Multiplication by a unit preserves Haar measure -/

/-- For an arbitrary set `S ⊆ ℤ_[p]` and a unit `ν`, `volume (ν · S) = volume S`. -/
theorem measure_image_mul_of_isUnit {ν : ℤ_[p]} (hν : IsUnit ν) (S : Set ℤ_[p]) :
    (volume : Measure ℤ_[p]) ((fun x => ν * x) '' S) = volume S := by
  set g := (fun x : ℤ_[p] => ν * x) with hg
  have hemb : MeasurableEmbedding g := measurableEmbedding_mul_left_of_ne_zero hν.ne_zero
  have hadd : ∀ x y : ℤ_[p], g (x + y) = g x + g y := by intro x y; simp only [hg]; ring
  have hsub : ∀ x y : ℤ_[p], g (x - y) = g x - g y := by intro x y; simp only [hg]; ring
  set μ' := Measure.comap g (volume : Measure ℤ_[p]) with hμ'
  have hμapp : ∀ s : Set ℤ_[p], μ' s = (volume : Measure ℤ_[p]) (g '' s) := fun s =>
    hemb.comap_apply _ _
  have _ : μ'.IsAddLeftInvariant := by
    rw [← MeasureTheory.forall_measure_preimage_add_iff]
    intro a A _
    rw [hμapp, hμapp]
    have hsetimg : g '' ((fun h => a + h) ⁻¹' A) = (fun h => g a + h) ⁻¹' (g '' A) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      refine ⟨fun ⟨x, hx, hxy⟩ => ⟨a + x, hx, by rw [← hxy, hadd]⟩, fun ⟨z, hz, hzeq⟩ => ?_⟩
      exact ⟨z - a, by simpa using hz, by rw [hsub, hzeq]; abel⟩
    rw [hsetimg]
    exact measure_preimage_add (volume : Measure ℤ_[p]) (g a) (g '' A)
  have _ : IsFiniteMeasure μ' :=
    ⟨by rw [hμapp]; exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _)⟩
  have heq := MeasureTheory.Measure.isAddInvariant_eq_smul_of_compactSpace μ'
    (volume : Measure ℤ_[p])
  set c := μ'.addHaarScalarFactor (volume : Measure ℤ_[p]) with hc
  obtain ⟨w, hw⟩ := hν.exists_right_inv
  have hrange : Set.range g = (Set.univ : Set ℤ_[p]) := by
    refine Set.eq_univ_of_forall fun y => ⟨w * y, ?_⟩
    rw [hg]
    calc ν * (w * y) = (ν * w) * y := by ring
      _ = y := by rw [hw, one_mul]
  have hcval : (c : ℝ≥0∞) = 1 := by
    have huniv : μ' Set.univ = 1 := by rw [hμapp, Set.image_univ, hrange, measure_univ]
    have huniv2 : μ' Set.univ = (c : ℝ≥0∞) := by rw [heq]; simp
    rw [← huniv2, huniv]
  rw [← hμapp, heq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hcval, one_mul]

/-- Multiplication by a unit of `ℤ_[p]` is measure preserving. -/
theorem measurePreserving_mul_of_isUnit {ν : ℤ_[p]} (hν : IsUnit ν) :
    MeasurePreserving (fun x : ℤ_[p] => ν * x) volume volume := by
  obtain ⟨w, hw⟩ := hν.exists_right_inv
  have hwu : IsUnit w := ⟨⟨w, ν, by rw [mul_comm]; exact hw, hw⟩, rfl⟩
  refine ⟨by fun_prop, ?_⟩
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA]
  have hpre : (fun x : ℤ_[p] => ν * x) ⁻¹' A = (fun x : ℤ_[p] => w * x) '' A := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun hx => ⟨ν * x, hx, ?_⟩, fun ⟨a, ha, hax⟩ => ?_⟩
    · calc w * (ν * x) = (ν * w) * x := by ring
        _ = x := by rw [hw, one_mul]
    · have hax' : ν * x = a := by
        rw [← hax]
        calc ν * (w * a) = (ν * w) * a := by ring
          _ = a := by rw [hw, one_mul]
      rwa [hax']
  rw [hpre, measure_image_mul_of_isUnit hwu A]

/-! ### Preimages of residue sets -/

/-- The `PadicInt.toZMod`-preimage of an arbitrary set of residues is measurable. -/
theorem measurableSet_preimage_toZMod_set (S : Set (ZMod p)) :
    MeasurableSet (toZMod ⁻¹' S : Set ℤ_[p]) := by
  simpa [Set.biUnion_preimage_singleton] using
    (Set.toFinite S).measurableSet_biUnion fun A _ => measurableSet_preimage_toZMod A

/-- For a finite set `S` of residues, the `PadicInt.toZMod`-preimage of `S` has Haar mass
`|S| p⁻¹`. -/
theorem volume_preimage_toZMod_coe (S : Finset (ZMod p)) :
    (volume : Measure ℤ_[p]) (toZMod ⁻¹' (S : Set (ZMod p))) = S.card * (p : ℝ≥0∞)⁻¹ := by
  classical
  have h : (toZMod ⁻¹' (S : Set (ZMod p)) : Set ℤ_[p]) = ⋃ A ∈ S, (toZMod ⁻¹' {A} : Set ℤ_[p]) := by
    ext a; simp
  rw [h, measure_biUnion_finset
    (fun A _ A' _ hAA' => Set.disjoint_left.2 fun _ h h' => hAA' (h.symm.trans h'))
    fun A _ => measurableSet_preimage_toZMod A]
  simp [volume_preimage_toZMod, Finset.sum_const, nsmul_eq_mul]

end PadicInt

namespace BSDTamagawa.HeadSumThree

open BSDTamagawa.HeadDensityTwoBound

variable {p : ℕ} [Fact p.Prime]

/-! ### The nonzero squares of `ZMod p` -/

open scoped Classical in
/-- The nonzero squares of `ZMod p`. -/
noncomputable def sqUnits (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter fun A => A ≠ 0 ∧ IsSquare A

open scoped Classical in
/-- The nonzero non-squares of `ZMod p`. -/
noncomputable def nonSqUnits (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter fun A => A ≠ 0 ∧ ¬ IsSquare A

/-- A residue lies in `sqUnits p` iff it is a nonzero square. -/
theorem mem_sqUnits_iff {A : ZMod p} : A ∈ sqUnits p ↔ A ≠ 0 ∧ IsSquare A := by
  classical simp [sqUnits]

/-- A residue lies in `nonSqUnits p` iff it is a nonzero non-square. -/
theorem mem_nonSqUnits_iff {A : ZMod p} : A ∈ nonSqUnits p ↔ A ≠ 0 ∧ ¬ IsSquare A := by
  classical simp [nonSqUnits]

/-- The squares and the non-squares partition the `p - 1` nonzero residues. -/
theorem card_sqUnits_add_card_nonSqUnits : (sqUnits p).card + (nonSqUnits p).card = p - 1 := by
  classical
  have h1 : sqUnits p = (Finset.univ.filter fun A : ZMod p => A ≠ 0).filter
      fun A => IsSquare A := by rw [sqUnits, Finset.filter_filter]
  have h2 : nonSqUnits p = (Finset.univ.filter fun A : ZMod p => A ≠ 0).filter
      fun A => ¬ IsSquare A := by rw [nonSqUnits, Finset.filter_filter]
  have h3 : (Finset.univ.filter fun A : ZMod p => A ≠ 0).card = p - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
  rw [h1, h2, Finset.card_filter_add_card_filter_not, h3]

/-- For `p ≥ 5`, there are as many nonzero squares as nonzero non-squares in `ZMod p`. -/
theorem card_sqUnits_eq_card_nonSqUnits (hp : 5 ≤ p) :
    (sqUnits p).card = (nonSqUnits p).card := by
  classical
  obtain ⟨ν, hν⟩ := quadraticChar_exists_neg_one (F := ZMod p) (ringChar_ne_two hp)
  have hν0 : ν ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hν; norm_num at hν
  refine Finset.card_bij' (fun A _ => ν * A) (fun A _ => ν⁻¹ * A) ?_ ?_ ?_ ?_
  · intro A hA
    rw [mem_sqUnits_iff] at hA
    rw [mem_nonSqUnits_iff]
    refine ⟨mul_ne_zero hν0 hA.1, ?_⟩
    rw [← quadraticChar_neg_one_iff_not_isSquare, map_mul, hν,
      (quadraticChar_one_iff_isSquare hA.1).2 hA.2]
    ring
  · intro A hA
    rw [mem_nonSqUnits_iff] at hA
    rw [mem_sqUnits_iff]
    have hν' : ν⁻¹ * A ≠ 0 := mul_ne_zero (inv_ne_zero hν0) hA.1
    refine ⟨hν', ?_⟩
    rw [← quadraticChar_one_iff_isSquare hν']
    have hAeq : A = ν * (ν⁻¹ * A) := by field_simp
    have hflip : quadraticChar (ZMod p) (ν * (ν⁻¹ * A))
        = - quadraticChar (ZMod p) (ν⁻¹ * A) := by rw [map_mul, hν]; ring
    rw [← hAeq, quadraticChar_neg_one_iff_not_isSquare.2 hA.2] at hflip
    exact (neg_inj.mp hflip).symm
  · intro A _; field_simp
  · intro A _; field_simp

/-- For `p ≥ 5`, `|sqUnits p| = |goodRes p|`; both equal `(p - 1)/2`. -/
theorem card_sqUnits_eq_card_goodRes (hp : 5 ≤ p) : (sqUnits p).card = (goodRes p).card := by
  have h1 := card_sqUnits_add_card_nonSqUnits (p := p)
  have h2 := card_sqUnits_eq_card_nonSqUnits hp
  have h3 := two_mul_card_goodRes hp
  omega

/-! ### A monic quadratic with square discriminant splits -/

/-- Over a field with `2 ≠ 0`, the quadratic `X² + aX - b` splits if its discriminant `a² + 4b` is
a square. -/
theorem splits_quadratic_of_isSquare {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b : K}
    (h : IsSquare (a ^ 2 + 4 * b)) :
    (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X
      + Polynomial.C (-b)).Splits := by
  obtain ⟨y, hy⟩ :=
    (WeierstrassCurve.TateAlgorithm.Step2.exists_sq_add_mul_sub_eq_zero_iff h2 a b).2 h
  refine Polynomial.Splits.of_natDegree_eq_two (x := y)
    (Polynomial.natDegree_quadratic one_ne_zero) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination hy

end BSDTamagawa.HeadSumThree

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The `I₃` locus of the coefficient plane, and its split part -/

variable (p) in
/-- The `I₃` locus: the pairs `(a₄, a₆)` with `p ∤ a₄` and `v_p(4a₄³ + 27a₆²) = 3`. -/
def i3Locus : Set (ℤ_[p] × ℤ_[p]) :=
  {x | ¬ (p : ℤ_[p]) ∣ x.1 ∧ emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) = 3}

variable (p) in
/-- The split part of the `I₃` locus: the points where `-c₆ = 864 a₆` is a square modulo `p`. -/
def i3SplitLocus : Set (ℤ_[p] × ℤ_[p]) :=
  i3Locus p ∩ {x | IsSquare (PadicInt.toZMod (864 * x.2))}

variable (p) in
/-- The non-split part of the `I₃` locus: the points where `864 a₆` is not a square modulo `p`. -/
def i3NonSplitLocus : Set (ℤ_[p] × ℤ_[p]) :=
  i3Locus p ∩ {x | ¬ IsSquare (PadicInt.toZMod (864 * x.2))}

/-- On the `I₃` locus, `p ∣ 4a₄³ + 27a₆²`. -/
theorem dvd_form_of_mem_i3Locus {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ i3Locus p) :
    (p : ℤ_[p]) ∣ 4 * x.1 ^ 3 + 27 * x.2 ^ 2 := by
  have h := pow_dvd_of_le_emultiplicity (a := (p : ℤ_[p])) (b := 4 * x.1 ^ 3 + 27 * x.2 ^ 2)
    (k := 1) (by rw [hx.2]; norm_num)
  rwa [pow_one] at h

/-- For `p ≥ 5`, on the `I₃` locus `p ∤ a₆`. -/
theorem not_dvd_snd_of_mem_i3Locus (hp : 5 ≤ p) {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ i3Locus p) :
    ¬ (p : ℤ_[p]) ∣ x.2 := by
  intro h6
  have h1 : (p : ℤ_[p]) ∣ 27 * x.2 ^ 2 := (h6.pow two_ne_zero).mul_left 27
  have h2 : (p : ℤ_[p]) ∣ 4 * x.1 ^ 3 := by
    have hs := dvd_sub (dvd_form_of_mem_i3Locus hx) h1
    rwa [show 4 * x.1 ^ 3 + 27 * x.2 ^ 2 - 27 * x.2 ^ 2 = 4 * x.1 ^ 3 from by ring] at hs
  rw [(isUnit_four hp).dvd_mul_left] at h2
  exact hx.1 (PadicInt.prime_p.dvd_of_dvd_pow h2)

/-- For `p ≥ 5`, on the `I₃` locus the residue of `864 a₆` is nonzero. -/
theorem toZMod_mul_snd_ne_zero (hp : 5 ≤ p) {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ i3Locus p) :
    PadicInt.toZMod (864 * x.2) ≠ 0 := by
  rw [Ne, ← PadicInt.dvd_iff_toZMod_eq_zero, (isUnit_eightSixFour hp).dvd_mul_left]
  exact not_dvd_snd_of_mem_i3Locus hp hx

/-- For `p ≥ 5`, on the `I₃` locus the discriminant has valuation `3`. -/
theorem emultiplicity_Δ_of_mem_i3Locus (hp : 5 ≤ p) {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ i3Locus p) :
    emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = 3 := by
  rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
    PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add]
  exact hx.2

/-- For `p ≥ 5`, the split `I₃` locus lies in the union of the strata over `t = 3`. -/
theorem i3SplitLocus_subset_iUnion_stratFibre (hp : 5 ≤ p) :
    i3SplitLocus p ⊆ ⋃ κ : KodairaSymbol, stratFibre p (κ, 3) := by
  intro x hx
  obtain ⟨hxL, hsq⟩ := hx
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((3 : ℕ) : ℕ∞) := by
    simpa using emultiplicity_Δ_of_mem_i3Locus hp hxL
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero_right] at hΔv
    exact absurd hΔv (by simp)
  have hUp : x ∈ nonsingularLocus p := hΔ
  have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
    rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
    exact hxL.1
  have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ :=
    dvd_Δ_of_emultiplicity_eq (by omega) hΔv
  have hsplit : Step2.TangentSplits (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    rw [Step2.tangentSplits_iff_isSquare_neg_c₆ hpΔ hc₄ (not_dvd_two_of_odd hodd),
      isSquare_mod_iff_isSquare_toZMod, ofShortNF_c₆,
      show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 from by ring]
    exact hsq
  obtain ⟨hk, ht⟩ := run_kodaira_tamagawa_of_tangentSplits hΔ hc₄ (t := 3) (by omega) hΔv hsplit
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.I 3, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-! ### Measurability -/

/-- The `I₃` locus is measurable. -/
theorem measurableSet_i3Locus : MeasurableSet (i3Locus p) := by
  have h1 : MeasurableSet {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1} := by
    have he : {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1}
        = (Prod.fst ⁻¹' ((Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) : Set ℤ_[p]))ᶜ := by
      ext x; simp [Ideal.mem_span_singleton]
    rw [he]
    exact (measurable_fst (PadicInt.measurableSet_span_pPow 1)).compl
  have hmeas : Measurable fun x : ℤ_[p] × ℤ_[p] => 4 * x.1 ^ 3 + 27 * x.2 ^ 2 := by fun_prop
  have h2 : MeasurableSet
      {x : ℤ_[p] × ℤ_[p] | emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) = 3} := by
    have := hmeas (PadicInt.measurableSet_setOf_emultiplicity_eq (p := p) 3)
    simpa using this
  exact h1.inter h2

/-- The set of `(a₄, a₆)` for which the residue of `864 a₆` is a square is measurable. -/
theorem measurableSet_setOf_isSquare_toZMod_snd :
    MeasurableSet {x : ℤ_[p] × ℤ_[p] | IsSquare (PadicInt.toZMod (864 * x.2))} := by
  have hm : Measurable fun x : ℤ_[p] × ℤ_[p] => (864 : ℤ_[p]) * x.2 := by fun_prop
  exact hm (PadicInt.measurableSet_preimage_toZMod_set {A : ZMod p | IsSquare A})

/-- The split `I₃` locus is measurable. -/
theorem measurableSet_i3SplitLocus : MeasurableSet (i3SplitLocus p) :=
  measurableSet_i3Locus.inter measurableSet_setOf_isSquare_toZMod_snd

/-! ### The mass of the `I₃` locus -/

/-- For `p ≥ 5` and `p ∤ a₄`, the `a₆`-slice of the `I₃` locus over `a₄` is the square level set
`PadicInt.sqLevelSet (sqTarget a₄) 3`. -/
theorem slice_i3Locus_eq (hp : 5 ≤ p) {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) :
    Prod.mk a ⁻¹' i3Locus p = PadicInt.sqLevelSet (sqTarget a) 3 := by
  ext b
  simp only [mem_preimage, i3Locus, mem_ofPred_eq, PadicInt.mem_sqLevelSet,
    emultiplicity_add_eq hp a b]
  exact ⟨fun h => by simpa using h.2, fun h => ⟨ha, by simpa using h⟩⟩

/-- For `p ≥ 5` and `a₄ ∈ goodFst p`, the `a₆`-slice of the `I₃` locus has mass `2(1 - p⁻¹)p⁻³`. -/
theorem volume_slice_i3Locus (hp : 5 ≤ p) {a : ℤ_[p]} (ha : a ∈ goodFst p) :
    (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' i3Locus p)
      = 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [slice_i3Locus_eq hp ha.1]
  exact PadicInt.measure_sqLevelSet_of_isSquare hodd (isUnit_sqTarget hp ha.1) ha.2 (by norm_num)

/-- For `p ≥ 5`, the `I₃` locus has Haar mass at least `|goodRes p| · p⁻¹ · 2(1 - p⁻¹)p⁻³`. -/
theorem volume_i3Locus_ge (hp : 5 ≤ p) :
    (goodRes p).card * (p : ℝ≥0∞)⁻¹ * (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3)
      ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i3Locus p) := by
  have hbound : ∀ a : ℤ_[p], (goodFst p).indicator
      (fun _ => 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3) a
        ≤ (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' i3Locus p) := by
    intro a
    by_cases ha : a ∈ goodFst p
    · rw [Set.indicator_of_mem ha, volume_slice_i3Locus hp ha]
    · rw [Set.indicator_of_notMem ha]; exact zero_le
  calc (goodRes p).card * (p : ℝ≥0∞)⁻¹ * (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3)
      = (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3) * volume (goodFst p) := by
        rw [volume_goodFst hp]; ring
    _ = ∫⁻ a, (goodFst p).indicator
          (fun _ => 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3) a ∂(volume : Measure ℤ_[p]) := by
        rw [lintegral_indicator (measurableSet_goodFst hp), setLIntegral_const]
    _ ≤ ∫⁻ a, (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' i3Locus p) ∂(volume : Measure ℤ_[p]) :=
        lintegral_mono hbound
    _ = (volume : Measure (ℤ_[p] × ℤ_[p])) (i3Locus p) := by
        rw [Measure.volume_eq_prod, Measure.prod_apply measurableSet_i3Locus]

/-- For `p ≥ 5`, the `I₃` locus has Haar mass at least `4N²p⁻⁵`, where `N = |goodRes p|`. -/
theorem four_mul_sq_card_le_volume_i3Locus (hp : 5 ≤ p) :
    4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5
      ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i3Locus p) := by
  refine le_trans (le_of_eq ?_) (volume_i3Locus_ge hp)
  rw [one_sub_inv_eq hp]
  ring

/-! ### The quadratic twist halves the `I₃` locus -/

/-- The quadratic twist of the coefficient plane by `ν`: `(a₄, a₆) ↦ (ν²a₄, ν³a₆)`. -/
noncomputable def twistPlane (ν : ℤ_[p]) : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p] :=
  Prod.map (fun x => ν ^ 2 * x) (fun y => ν ^ 3 * y)

/-- The first coordinate of `twistPlane ν x` is `ν² x₁`. -/
theorem twistPlane_fst (ν : ℤ_[p]) (x : ℤ_[p] × ℤ_[p]) : (twistPlane ν x).1 = ν ^ 2 * x.1 := rfl

/-- The second coordinate of `twistPlane ν x` is `ν³ x₂`. -/
theorem twistPlane_snd (ν : ℤ_[p]) (x : ℤ_[p] × ℤ_[p]) : (twistPlane ν x).2 = ν ^ 3 * x.2 := rfl

/-- The twist by a unit preserves Haar measure on the plane. -/
theorem measurePreserving_twistPlane {ν : ℤ_[p]} (hν : IsUnit ν) :
    MeasurePreserving (twistPlane ν) (volume : Measure (ℤ_[p] × ℤ_[p])) volume := by
  rw [Measure.volume_eq_prod]
  exact (PadicInt.measurePreserving_mul_of_isUnit (hν.pow 2)).prod
    (PadicInt.measurePreserving_mul_of_isUnit (hν.pow 3))

/-- The twist by a unit fixes the `I₃` locus. -/
theorem mem_i3Locus_twistPlane_iff {ν : ℤ_[p]} (hν : IsUnit ν) (x : ℤ_[p] × ℤ_[p]) :
    twistPlane ν x ∈ i3Locus p ↔ x ∈ i3Locus p := by
  have hform : 4 * (ν ^ 2 * x.1) ^ 3 + 27 * (ν ^ 3 * x.2) ^ 2
      = ν ^ 6 * (4 * x.1 ^ 3 + 27 * x.2 ^ 2) := by ring
  have hval : emultiplicity (p : ℤ_[p]) (4 * (ν ^ 2 * x.1) ^ 3 + 27 * (ν ^ 3 * x.2) ^ 2)
      = emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) := by
    rw [hform, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit (hν.pow 6), zero_add]
  simp only [i3Locus, mem_ofPred_eq, twistPlane_fst, twistPlane_snd]
  rw [hval, (hν.pow 2).dvd_mul_left]

/-- For `p ≥ 5`, on the `I₃` locus, twisting by `ν` with non-square residue flips whether the
residue of `864 a₆` is a square. -/
theorem isSquare_toZMod_twistPlane_iff (hp : 5 ≤ p) {ν : ℤ_[p]}
    (hχ : quadraticChar (ZMod p) (PadicInt.toZMod ν) = -1) {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ i3Locus p) :
    IsSquare (PadicInt.toZMod (864 * (twistPlane ν x).2))
      ↔ ¬ IsSquare (PadicInt.toZMod (864 * x.2)) := by
  have hcast : PadicInt.toZMod (864 * (twistPlane ν x).2)
      = PadicInt.toZMod ν ^ 3 * PadicInt.toZMod (864 * x.2) := by
    rw [twistPlane_snd,
      show (864 : ℤ_[p]) * (ν ^ 3 * x.2) = ν ^ 3 * (864 * x.2) from by ring, map_mul, map_pow]
  rw [hcast]
  exact isSquare_cube_mul_iff hχ (toZMod_mul_snd_ne_zero hp hx)

/-- For `p ≥ 5` and `ν` a unit with non-square residue, the non-split `I₃` locus is the preimage of
the split `I₃` locus under the twist by `ν`. -/
theorem i3NonSplitLocus_eq_preimage (hp : 5 ≤ p) {ν : ℤ_[p]} (hν : IsUnit ν)
    (hχ : quadraticChar (ZMod p) (PadicInt.toZMod ν) = -1) :
    i3NonSplitLocus p = twistPlane ν ⁻¹' i3SplitLocus p := by
  ext x
  simp only [i3NonSplitLocus, i3SplitLocus, Set.mem_inter_iff, Set.mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨hxL, hns⟩
    exact ⟨(mem_i3Locus_twistPlane_iff hν x).2 hxL,
      (isSquare_toZMod_twistPlane_iff hp hχ hxL).2 hns⟩
  · rintro ⟨hxL, hs⟩
    have hxL' : x ∈ i3Locus p := (mem_i3Locus_twistPlane_iff hν x).1 hxL
    exact ⟨hxL', (isSquare_toZMod_twistPlane_iff hp hχ hxL').1 hs⟩

/-- The split and non-split parts cover the `I₃` locus. -/
theorem i3Locus_eq_union :
    i3Locus p = i3SplitLocus p ∪ i3NonSplitLocus p := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · by_cases h : IsSquare (PadicInt.toZMod (864 * x.2))
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rcases hx with h | h <;> exact h.1

/-- For `p ≥ 5`, the mass of the `I₃` locus is at most twice the mass of its split part. -/
theorem volume_i3Locus_le_two_mul (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (i3Locus p) ≤ 2 * volume (i3SplitLocus p) := by
  obtain ⟨ν, hν, hχ⟩ := exists_isUnit_quadraticChar_eq_neg_one hp
  have hns : (volume : Measure (ℤ_[p] × ℤ_[p])) (i3NonSplitLocus p) = volume (i3SplitLocus p) := by
    rw [i3NonSplitLocus_eq_preimage hp hν hχ]
    exact (measurePreserving_twistPlane hν).measure_preimage
      measurableSet_i3SplitLocus.nullMeasurableSet
  calc (volume : Measure (ℤ_[p] × ℤ_[p])) (i3Locus p)
      ≤ volume (i3SplitLocus p) + volume (i3NonSplitLocus p) := by
        rw [i3Locus_eq_union]
        exact measure_union_le _ _
    _ = 2 * volume (i3SplitLocus p) := by rw [hns, two_mul]

/-- For `p ≥ 5`, the split `I₃` locus has Haar mass at least `2N²p⁻⁵`, where `N = |goodRes p|`. -/
theorem two_mul_sq_card_le_volume_i3SplitLocus (hp : 5 ≤ p) :
    2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5
      ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i3SplitLocus p) := by
  have h := (four_mul_sq_card_le_volume_i3Locus hp).trans (volume_i3Locus_le_two_mul hp)
  rw [← ENNReal.mul_le_mul_iff_left (c := (2 : ℝ≥0∞)) two_ne_zero (by norm_num)]
  calc 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5 * 2
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5 := by ring
    _ ≤ 2 * volume (i3SplitLocus p) := h
    _ = volume (i3SplitLocus p) * 2 := by ring

/-! ### Step 5's split test -/

/-- For a short model with `p² ∣ a₄` and `a₆ = p²u`, if the residue of `u` is a square then the
quadratic of Step 5 of Tate's algorithm, on the Step-2 translate, splits. -/
theorem splits_step5_quadratic (hp : 5 ≤ p) {a₄ a₆ u : ℤ_[p]} (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄)
    (ha₆ : a₆ = (p : ℤ_[p]) ^ 2 * u) (hsq : IsSquare (PadicInt.toZMod u)) :
    (quadratic (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) 1).toPoly.Splits := by
  have hϖ0 : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h6 : (p : ℤ_[p]) ^ 2 ∣ a₆ := ⟨u, ha₆⟩
  set V : WeierstrassCurve ℤ_[p] := Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆) with hV
  have hs3 := step3_run_eq_ok_of_dvd hp (dvd_trans (dvd_pow_self _ two_ne_zero) h4) h6
  have hv3 := Step3.run_hasValuation hs3
  have hc₄ : (p : ℤ_[p]) ^ 2 ∣ V.c₄ := by
    rw [hV, Step2.translate_c₄, ofShortNF_c₄]
    exact h4.mul_left _
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok V := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv3.b₂) hv3.b₆).2 hc₄)
  have hv4 := Step4.run_hasValuation hϖ0 hs4
  have ha₃ : (p : ℤ_[p]) ∣ V.a₃ := by simpa using hv4.a₃
  have e1 : (p : ℤ_[p]) * CommRing.div V.a₃ (p : ℤ_[p]) = V.a₃ := CommRing.mul_div hϖ0 ha₃
  have e2 : (p : ℤ_[p]) ^ 2 * CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2) = V.a₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ0) hv4.a₆
  have e3 : (p : ℤ_[p]) ^ 2 * CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) = V.b₆ :=
    CommRing.mul_div (pow_ne_zero 2 hϖ0) hv4.b₆
  have hdisc : CommRing.div V.a₃ (p : ℤ_[p]) ^ 2 + 4 * CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2)
      = CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hϖ0) ?_
    rw [e3, WeierstrassCurve.b₆]
    linear_combination ((p : ℤ_[p]) * CommRing.div V.a₃ (p : ℤ_[p]) + V.a₃) * e1 + 4 * e2
  have hmodw : CommRing.mod (p : ℤ_[p]) (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2))
      = 4 * CommRing.mod (p : ℤ_[p]) u := by
    have hcb := cb_dvd_c₆_add_mul_b₆_of_dvd (by simpa using hv4.b₂) hv4.b₄
    have hc₆ : V.c₆ = -864 * a₆ := by rw [hV, Step2.translate_c₆, ofShortNF_c₆]
    have hfac : V.c₆ + 216 * V.b₆
        = (p : ℤ_[p]) ^ 2 * (216 * (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) - 4 * u)) := by
      linear_combination hc₆ - 864 * ha₆ - 216 * e3
    rw [hfac] at hcb
    obtain ⟨z, hz⟩ := hcb
    have hdvd : (p : ℤ_[p]) ∣ 216 * (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) - 4 * u) :=
      ⟨z, mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by rw [hz]; ring)⟩
    rw [(isUnit_twoHundredSixteen hp).dvd_mul_left] at hdvd
    have h0 := (CommRing.mod_eq_zero (p : ℤ_[p])
      (CommRing.div V.b₆ ((p : ℤ_[p]) ^ 2) - 4 * u)).2 hdvd
    rw [map_sub, map_mul, map_ofNat, sub_eq_zero] at h0
    exact h0
  have h2' : (2 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≠ 0 := by
    rw [show (2 : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = CommRing.mod (p : ℤ_[p]) 2 from by
      simp only [map_ofNat], Ne, CommRing.mod_eq_zero]
    exact not_dvd_two_of_odd hodd
  have hquad : quadratic (p : ℤ_[p]) V 1
      = ⟨0, 1, CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₃ (p : ℤ_[p])),
        -CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2))⟩ := by
    simp [quadratic]
  have hsqd : IsSquare (CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₃ (p : ℤ_[p])) ^ 2
      + 4 * CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2))) := by
    obtain ⟨s, hs⟩ := (isSquare_mod_iff_isSquare_toZMod u).2 hsq
    refine ⟨2 * s, ?_⟩
    rw [show CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₃ (p : ℤ_[p])) ^ 2
          + 4 * CommRing.mod (p : ℤ_[p]) (CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2))
        = CommRing.mod (p : ℤ_[p])
            (CommRing.div V.a₃ (p : ℤ_[p]) ^ 2 + 4 * CommRing.div V.a₆ ((p : ℤ_[p]) ^ 2)) from by
      simp only [map_add, map_mul, map_pow, map_ofNat], hdisc, hmodw, hs]
    ring
  rw [hquad, Cubic.of_a_eq_zero rfl]
  exact splits_quadratic_of_isSquare h2' hsqd

/-! ### The split `IV` locus and its mass -/

variable (p) in
/-- The set of `a₆ = p²u` with `u` a unit whose residue is a square. -/
noncomputable def ivGoodSnd : Set ℤ_[p] :=
  PadicInt.scaleByPPow 2 '' (PadicInt.toZMod ⁻¹' (sqUnits p : Set (ZMod p)))

variable (p) in
/-- The split `IV` locus: `p² ∣ a₄` and `a₆ = p²u` with `u` a unit whose residue is a square. -/
noncomputable def ivSplitLocus : Set (ℤ_[p] × ℤ_[p]) :=
  ((Ideal.span {(p : ℤ_[p]) ^ 2} : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ ivGoodSnd p

/-- A point `(a₄, a₆)` lies in the split `IV` locus iff `p² ∣ a₄` and `a₆ = p²u` for some unit `u`
whose residue is a square. -/
theorem mem_ivSplitLocus_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ ivSplitLocus p ↔ (p : ℤ_[p]) ^ 2 ∣ x.1 ∧ ∃ u : ℤ_[p], ¬ (p : ℤ_[p]) ∣ u ∧
      IsSquare (PadicInt.toZMod u) ∧ x.2 = (p : ℤ_[p]) ^ 2 * u := by
  rw [ivSplitLocus, Set.mem_prod]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton, ivGoodSnd, Set.mem_image,
    Set.mem_preimage, mem_sqUnits_iff, PadicInt.scaleByPPow,
    ← PadicInt.dvd_iff_toZMod_eq_zero, ne_eq]
  constructor
  · rintro ⟨h1, u, ⟨hu0, husq⟩, hu2⟩
    exact ⟨h1, u, hu0, husq, hu2.symm⟩
  · rintro ⟨h1, u, hu, husq, hu2⟩
    exact ⟨h1, u, ⟨hu, husq⟩, hu2.symm⟩

/-- The split `IV` locus is measurable. -/
theorem measurableSet_ivSplitLocus : MeasurableSet (ivSplitLocus p) :=
  (PadicInt.measurableSet_span_pPow 2).prod
    (PadicInt.measurableSet_image_scaleByPPow
      (PadicInt.measurableSet_preimage_toZMod_set (sqUnits p : Set (ZMod p))))

/-- For `p ≥ 5`, the split `IV` locus has Haar mass `N p⁻⁵`, where `N = |goodRes p|`. -/
theorem volume_ivSplitLocus (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (ivSplitLocus p)
      = ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 := by
  have hz : (p : ℝ≥0∞) ^ (-((2 : ℕ) : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 2 :=
    (PadicInt.measure_span_pPow (p := p) 2).symm.trans (PadicInt.measure_span_pPow' 2)
  rw [ivSplitLocus, ivGoodSnd, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.measure_span_pPow' 2, PadicInt.measure_image_scaleByPPow,
    PadicInt.volume_preimage_toZMod_coe, card_sqUnits_eq_card_goodRes hp, hz]
  ring

/-- For `p ≥ 5`, the split `IV` locus lies in the union of the strata over `t = 3`. -/
theorem ivSplitLocus_subset_iUnion_stratFibre (hp : 5 ≤ p) :
    ivSplitLocus p ⊆ ⋃ κ : KodairaSymbol, stratFibre p (κ, 3) := by
  intro x hx
  obtain ⟨h4, u, hu, husq, h2eq⟩ := mem_ivSplitLocus_iff.1 hx
  have h6 : (p : ℤ_[p]) ^ 2 ∣ x.2 := ⟨u, h2eq⟩
  have h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ x.2 := by
    rintro ⟨z, hz⟩
    exact hu ⟨z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero)
      (by rw [← h2eq, hz]; ring)⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_five_dvd_ofShortNF_Δ_of_IV hp h4 h6 h6' (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  have hκ := run_kodairaSymbol_eq_IV_of_emultiplicity_eq_two hp hΔ h4 h6 h6'
  have hs3 := step3_run_eq_ok_of_dvd hp (dvd_trans (dvd_pow_self _ two_ne_zero) h4) h6
  have hv3 := Step3.run_hasValuation hs3
  have hc₄ : (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2)).c₄ := by
    rw [Step2.translate_c₄, ofShortNF_c₄]
    exact h4.mul_left _
  have hc₆ : ¬ (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2)).c₆ := by
    rw [Step2.translate_c₆, ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left]
    exact h6'
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF x.1 x.2)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv3.b₂) hv3.b₆).2 hc₄)
  have hv4 := Step4.run_hasValuation PadicInt.uniformizer_ne_zero hs4
  have hsp : (quadratic (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2))
      1).toPoly.Splits := splits_step5_quadratic hp h4 h2eq husq
  have hs5 : Step5.run (p : ℤ_[p]) (ofShortNF x.1 x.2) = Except.error
      ⟨Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2), KodairaSymbol.IV, 3⟩ := by
    rw [Step5.run.eq_def, hs4]
    simp only [except_ok_bind]
    rw [ite_eq_right fun hcon =>
      hc₆ ((cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv4.b₂) hv4.b₄).1 hcon)]
    simp [hsp]
  have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 3 := by
    rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hUp (step11_error_of_step5 hUp hs5)]
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.IV, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)⟩

/-! ### The bound on `δ_p(3)` and on `A_{p,3}` -/

/-- The split `I₃` locus and the split `IV` locus are disjoint. -/
theorem disjoint_i3SplitLocus_ivSplitLocus : Disjoint (i3SplitLocus p) (ivSplitLocus p) :=
  Set.disjoint_left.2 fun _ hx hx' =>
    hx.1.1 (dvd_trans (dvd_pow_self _ two_ne_zero) (mem_ivSplitLocus_iff.1 hx').1)

/-- For `p ≥ 5`, `p² ≤ 6N² + 3N`, where `N = |goodRes p|`. -/
theorem sq_le_six_mul_sq_add_three_mul (hp : 5 ≤ p) :
    p ^ 2 ≤ 6 * (goodRes p).card ^ 2 + 3 * (goodRes p).card := by
  have h1 := eq_two_mul_card_goodRes_add_one hp
  have h2 := two_le_card_goodRes hp
  nlinarith [h1, h2]

/-- For every prime `p ≥ 5`, `1/(3p³) ≤ δ_p(3)`. -/
theorem inv_three_mul_cube_le_δ_three (hp : 5 ≤ p) : 1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ δ p 3 := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  set N : ℝ≥0∞ := ((goodRes p).card : ℝ≥0∞) with hN
  have hmass : 2 * N ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5 + N * ((p : ℝ≥0∞)⁻¹) ^ 5 ≤ δ p 3 := by
    calc 2 * N ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5 + N * ((p : ℝ≥0∞)⁻¹) ^ 5
        ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i3SplitLocus p) + volume (ivSplitLocus p) :=
          add_le_add (two_mul_sq_card_le_volume_i3SplitLocus hp)
            (le_of_eq (volume_ivSplitLocus hp).symm)
      _ = volume (i3SplitLocus p ∪ ivSplitLocus p) :=
          (measure_union disjoint_i3SplitLocus_ivSplitLocus measurableSet_ivSplitLocus).symm
      _ ≤ volume (⋃ κ : KodairaSymbol, stratFibre p (κ, 3)) :=
          measure_mono (Set.union_subset (i3SplitLocus_subset_iUnion_stratFibre hp)
            (ivSplitLocus_subset_iUnion_stratFibre hp))
      _ = δ p 3 := volume_iUnion_stratFibre_kodaira 3
  have harith : 1 / (3 * (p : ℝ≥0∞) ^ 3)
      ≤ 2 * N ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5 + N * ((p : ℝ≥0∞)⁻¹) ^ 5 := by
    have h3 : ((3 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 3) ≠ 0 := mul_ne_zero three_ne_zero (pow_ne_zero 3 hp0)
    have h3t : ((3 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 3) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hpt)
    have h5 : ((p : ℝ≥0∞) ^ 5) ≠ 0 := pow_ne_zero 5 hp0
    have h5t : ((p : ℝ≥0∞) ^ 5) ≠ ⊤ := ENNReal.pow_ne_top hpt
    have hc : ((3 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 5) ≠ 0 := mul_ne_zero three_ne_zero h5
    have hct : ((3 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 5) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) h5t
    have hL : (3 * (p : ℝ≥0∞) ^ 3)⁻¹ * (3 * (p : ℝ≥0∞) ^ 5) = (p : ℝ≥0∞) ^ 2 := by
      rw [show (3 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 5 = (3 * (p : ℝ≥0∞) ^ 3) * (p : ℝ≥0∞) ^ 2 from by ring,
        ← mul_assoc, ENNReal.inv_mul_cancel h3 h3t, one_mul]
    have hR : (2 * N ^ 2 * ((p : ℝ≥0∞) ^ 5)⁻¹ + N * ((p : ℝ≥0∞) ^ 5)⁻¹) * (3 * (p : ℝ≥0∞) ^ 5)
        = 6 * N ^ 2 + 3 * N := by
      rw [show (2 * N ^ 2 * ((p : ℝ≥0∞) ^ 5)⁻¹ + N * ((p : ℝ≥0∞) ^ 5)⁻¹) * (3 * (p : ℝ≥0∞) ^ 5)
            = (6 * N ^ 2 + 3 * N) * (((p : ℝ≥0∞) ^ 5)⁻¹ * (p : ℝ≥0∞) ^ 5) from by ring,
        ENNReal.inv_mul_cancel h5 h5t, mul_one]
    rw [one_div, ← ENNReal.inv_pow,
      ← ENNReal.mul_le_mul_iff_left (c := 3 * (p : ℝ≥0∞) ^ 5) hc hct, hL, hR]
    calc (p : ℝ≥0∞) ^ 2 = ((p ^ 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((6 * (goodRes p).card ^ 2 + 3 * (goodRes p).card : ℕ) : ℝ≥0∞) :=
          Nat.cast_le.mpr (sq_le_six_mul_sq_add_three_mul hp)
      _ = 6 * N ^ 2 + 3 * N := by rw [hN]; push_cast; ring
  exact harith.trans hmass

/-- For every prime `p ≥ 5`, `1/(3p³) ≤ A_{p,3}`. -/
theorem inv_three_mul_cube_le_headSum_three (hp : 5 ≤ p) :
    1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ headSum p 3 := by
  calc 1 / (3 * (p : ℝ≥0∞) ^ 3) ≤ δ p 3 := inv_three_mul_cube_le_δ_three hp
    _ = δ p 3 * (padicValNat 3 3 : ℝ≥0∞) := by simp
    _ ≤ headSum p 3 := by
        rw [headSum]
        exact Finset.single_le_sum (f := fun t => δ p t * (padicValNat 3 t : ℝ≥0∞))
          (fun _ _ => zero_le) (by decide)

end WeierstrassCurve

