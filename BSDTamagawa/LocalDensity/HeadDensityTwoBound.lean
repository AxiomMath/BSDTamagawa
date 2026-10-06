/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.DegreeBound

/-!
# A lower bound on `δ_p(2)` at `p ≥ 5`

For every prime `p ≥ 5`, the scalar local density at Tamagawa number `2` satisfies
`δ_p(2) ≥ 1/(2p²)`; consequently the head sum `A_{p,2} = ∑_{1 ≤ t ≤ 4} δ_p(t) v_2(t)` satisfies
`A_{p,2} ≥ 1/(2p²)`.

If `v_p(Δ) = 2` and `p ∤ c₄`, Tate's algorithm terminates at Step 2 with output `(I₂, 2)`: the
Tamagawa number on the multiplicative branch is `n` in the split case and `2` in the non-split case
with `n = v_p(Δ)` even, so at `n = 2` the split test is irrelevant. For the short model,
`c₄ = -48a₄` and `Δ = -16(4a₄³ + 27a₆²)`, so at `p ≥ 5` the locus `{p ∤ a₄, v_p(4a₄³ + 27a₆²) = 2}`
lies in the strata over `t = 2`. Writing `4a₄³ + 27a₆² = 27(a₆² - c(a₄))` with `c(a₄) = -4a₄³/27`,
each `a₆`-slice is a square level set, of mass `2(1 - p⁻¹)p⁻²` when `c(a₄)` is a square and `0`
otherwise. Multiplication by a quadratic non-residue exchanges the residues `A` for which `-4A³/27`
is a square with those for which it is not, so exactly half of the nonzero residues qualify. The
locus therefore has mass `(p-1)²/p⁴`, and `2(p-1)² ≥ p²` for `p ≥ 5`.

## Main definitions

* `BSDTamagawa.HeadDensityTwoBound.goodRes`: the nonzero residues `A` for which `-4A³/27` is a
  square.
* `WeierstrassCurve.i2Locus`: the locus `{p ∤ a₄, v_p(4a₄³ + 27a₆²) = 2}`.
* `WeierstrassCurve.headSum`: the head sum `A_{p,r} = ∑_{1 ≤ t ≤ 4} δ_p(t) v_r(t)`.

## Main results

* `BSDTamagawa.HeadDensityTwoBound.two_mul_card_goodRes`: `2 |goodRes p| = p - 1` for `p ≥ 5`.
* `WeierstrassCurve.run_kodaira_tamagawa_of_emultiplicity_eq_two`: if `v_p(Δ) = 2` and `p ∤ c₄`,
  then Tate's algorithm returns `(I₂, 2)`.
* `WeierstrassCurve.i2Locus_subset_iUnion_stratFibre`: the `I₂` locus lies in the strata over
  `t = 2`.
* `WeierstrassCurve.volume_i2Locus_ge`: the `I₂` locus has Haar mass at least `(p-1)²/p⁴`.
* `WeierstrassCurve.inv_two_mul_sq_le_δ_two`: `1/(2p²) ≤ δ_p(2)` for `p ≥ 5`.
* `WeierstrassCurve.inv_two_mul_sq_le_headSum_two`: `1/(2p²) ≤ A_{p,2}` for `p ≥ 5`.

## Implementation notes

The mass `(p-1)²/p⁴` is the exact mass of the `I₂` locus, and `(p-1)²/p⁴ ≥ 1/(2p²)` fails at
`p = 3`. The difference `1 - p⁻¹` in `ℝ≥0∞` is rewritten once as the product `2N p⁻¹`, where
`p = 2N + 1`, so no truncated subtraction enters the estimate.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace BSDTamagawa.HeadDensityTwoBound

variable {p : ℕ} [Fact p.Prime]

/-! ### Small units of `ZMod p` -/

/-- `4 ≠ 0` in `ZMod p` for `p ≥ 5`. -/
theorem four_ne_zero (hp : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have h : ((4 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  simpa using h

/-- `27 ≠ 0` in `ZMod p` for `p ≥ 5`. -/
theorem twentySeven_ne_zero (hp : 5 ≤ p) : (27 : ZMod p) ≠ 0 := by
  have h : ((27 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have h3 : p ∣ 3 :=
      (Fact.out : p.Prime).dvd_of_dvd_pow (n := 3) (by norm_num at h ⊢; exact h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  simpa using h

/-- `ZMod p` does not have characteristic `2` for `p ≥ 5`. -/
theorem ringChar_ne_two (hp : 5 ≤ p) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

/-! ### The good residues: `A` for which `-4A³/27` is a square -/

/-- `sqRes A = -4A³/27` in `ZMod p`. -/
def sqRes (A : ZMod p) : ZMod p := -(4 * A ^ 3) * (27 : ZMod p)⁻¹

/-- `sqRes A ≠ 0` for `A ≠ 0` and `p ≥ 5`. -/
theorem sqRes_ne_zero (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) : sqRes A ≠ 0 :=
  mul_ne_zero (neg_ne_zero.2 (mul_ne_zero (four_ne_zero hp) (pow_ne_zero 3 hA)))
    (inv_ne_zero (twentySeven_ne_zero hp))

open scoped Classical in
/-- The good residues: the nonzero `A ∈ ZMod p` for which `sqRes A = -4A³/27` is a square. -/
noncomputable def goodRes (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter fun A => A ≠ 0 ∧ IsSquare (sqRes A)

open scoped Classical in
/-- The bad residues: the nonzero `A ∈ ZMod p` for which `sqRes A` is not a square. -/
noncomputable def badRes (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter fun A => A ≠ 0 ∧ ¬ IsSquare (sqRes A)

/-- `A` is a good residue iff `A ≠ 0` and `sqRes A` is a square. -/
theorem mem_goodRes_iff {A : ZMod p} : A ∈ goodRes p ↔ A ≠ 0 ∧ IsSquare (sqRes A) := by
  classical simp [goodRes]

/-- `A` is a bad residue iff `A ≠ 0` and `sqRes A` is not a square. -/
theorem mem_badRes_iff {A : ZMod p} : A ∈ badRes p ↔ A ≠ 0 ∧ ¬ IsSquare (sqRes A) := by
  classical simp [badRes]

/-- The good and bad residues partition the `p - 1` nonzero residues. -/
theorem card_goodRes_add_card_badRes : (goodRes p).card + (badRes p).card = p - 1 := by
  classical
  have h1 : goodRes p = (Finset.univ.filter fun A : ZMod p => A ≠ 0).filter
      fun A => IsSquare (sqRes A) := by rw [goodRes, Finset.filter_filter]
  have h2 : badRes p = (Finset.univ.filter fun A : ZMod p => A ≠ 0).filter
      fun A => ¬ IsSquare (sqRes A) := by rw [badRes, Finset.filter_filter]
  have h3 : (Finset.univ.filter fun A : ZMod p => A ≠ 0).card = p - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
  rw [h1, h2, Finset.card_filter_add_card_filter_not, h3]

/-- If `ν` has quadratic character `-1`, then `χ(sqRes (νA)) = -χ(sqRes A)`. -/
theorem quadraticChar_sqRes_mul {ν : ZMod p} (hν : quadraticChar (ZMod p) ν = -1) (A : ZMod p) :
    quadraticChar (ZMod p) (sqRes (ν * A)) = - quadraticChar (ZMod p) (sqRes A) := by
  have hcube : sqRes (ν * A) = ν ^ 3 * sqRes A := by simp only [sqRes]; ring
  rw [hcube, map_mul, map_pow, hν]; ring

/-- For `p ≥ 5`, there are as many good residues as bad residues. -/
theorem card_goodRes_eq_card_badRes (hp : 5 ≤ p) : (goodRes p).card = (badRes p).card := by
  classical
  obtain ⟨ν, hν⟩ := quadraticChar_exists_neg_one (F := ZMod p) (ringChar_ne_two hp)
  have hν0 : ν ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hν; norm_num at hν
  refine Finset.card_bij' (fun A _ => ν * A) (fun A _ => ν⁻¹ * A) ?_ ?_ ?_ ?_
  · intro A hA
    rw [mem_goodRes_iff] at hA
    rw [mem_badRes_iff]
    refine ⟨mul_ne_zero hν0 hA.1, ?_⟩
    rw [← quadraticChar_neg_one_iff_not_isSquare, quadraticChar_sqRes_mul hν,
      (quadraticChar_one_iff_isSquare (sqRes_ne_zero hp hA.1)).2 hA.2]
  · intro A hA
    rw [mem_badRes_iff] at hA
    rw [mem_goodRes_iff]
    have hν' : ν⁻¹ * A ≠ 0 := mul_ne_zero (inv_ne_zero hν0) hA.1
    refine ⟨hν', ?_⟩
    rw [← quadraticChar_one_iff_isSquare (sqRes_ne_zero hp hν')]
    have hAeq : A = ν * (ν⁻¹ * A) := by field_simp
    have hflip := quadraticChar_sqRes_mul (p := p) hν (ν⁻¹ * A)
    rw [← hAeq, quadraticChar_neg_one_iff_not_isSquare.2 hA.2] at hflip
    exact (neg_inj.mp hflip).symm
  · intro A _; field_simp
  · intro A _; field_simp

/-- For `p ≥ 5`, `2 |goodRes p| = p - 1`. -/
theorem two_mul_card_goodRes (hp : 5 ≤ p) : 2 * (goodRes p).card = p - 1 := by
  have h := card_goodRes_add_card_badRes (p := p)
  rw [← card_goodRes_eq_card_badRes hp] at h
  omega

/-- For `p ≥ 5`, `p = 2 |goodRes p| + 1`. -/
theorem eq_two_mul_card_goodRes_add_one (hp : 5 ≤ p) : p = 2 * (goodRes p).card + 1 := by
  have h := two_mul_card_goodRes hp
  omega

/-- `2 ≤ |goodRes p|` for `p ≥ 5`. -/
theorem two_le_card_goodRes (hp : 5 ≤ p) : 2 ≤ (goodRes p).card := by
  have h := two_mul_card_goodRes hp
  omega

/-! ### The `p`-adic square target -/

/-- `sqTarget a = -4a³/27` in `ℤ_[p]`, with the inverse of `27` taken as `Ring.inverse`. -/
noncomputable def sqTarget (a : ℤ_[p]) : ℤ_[p] := -(4 * a ^ 3) * Ring.inverse (27 : ℤ_[p])

/-- For `p ≥ 5`, `27 · Ring.inverse 27 = 1` in `ℤ_[p]`. -/
theorem twentySeven_mul_inverse (hp : 5 ≤ p) : (27 : ℤ_[p]) * Ring.inverse (27 : ℤ_[p]) = 1 :=
  Ring.mul_inverse_cancel _ (WeierstrassCurve.isUnit_twentySeven hp)

/-- `27 · sqTarget a = -4a³` for `p ≥ 5`. -/
theorem twentySeven_mul_sqTarget (hp : 5 ≤ p) (a : ℤ_[p]) :
    (27 : ℤ_[p]) * sqTarget a = -(4 * a ^ 3) := by
  rw [sqTarget]
  calc (27 : ℤ_[p]) * (-(4 * a ^ 3) * Ring.inverse (27 : ℤ_[p]))
      = -(4 * a ^ 3) * ((27 : ℤ_[p]) * Ring.inverse (27 : ℤ_[p])) := by ring
    _ = -(4 * a ^ 3) := by rw [twentySeven_mul_inverse hp, mul_one]

/-- A coefficient not divisible by `p` is a unit of `ℤ_[p]`. -/
theorem isUnit_of_not_dvd {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) : IsUnit a := by
  by_contra h
  exact ha (PadicInt.dvd_iff_not_isUnit.mpr h)

/-- `sqTarget a` is a unit whenever `p ∤ a` and `p ≥ 5`. -/
theorem isUnit_sqTarget (hp : 5 ≤ p) {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) :
    IsUnit (sqTarget a) := by
  have h : IsUnit ((27 : ℤ_[p]) * sqTarget a) := by
    rw [twentySeven_mul_sqTarget hp]
    exact (((WeierstrassCurve.isUnit_four hp).mul ((isUnit_of_not_dvd ha).pow 3))).neg
  exact (IsUnit.mul_iff.mp h).2

/-- The residue of `sqTarget a` is `sqRes` of the residue of `a`. -/
theorem toZMod_sqTarget (hp : 5 ≤ p) (a : ℤ_[p]) :
    PadicInt.toZMod (sqTarget a) = sqRes (PadicInt.toZMod a) := by
  have h4 : PadicInt.toZMod (4 : ℤ_[p]) = (4 : ZMod p) := map_ofNat _ 4
  have h27 : PadicInt.toZMod (27 : ℤ_[p]) = (27 : ZMod p) := map_ofNat _ 27
  have h : (27 : ZMod p) * PadicInt.toZMod (Ring.inverse (27 : ℤ_[p])) = 1 := by
    rw [← h27, ← map_mul, twentySeven_mul_inverse hp, map_one]
  have hinv : PadicInt.toZMod (Ring.inverse (27 : ℤ_[p])) = (27 : ZMod p)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)
  rw [sqTarget, sqRes, map_mul, map_neg, map_mul, map_pow, hinv, h4]

/-- For `p ≥ 5`, `v_p(4a³ + 27b²) = v_p(b² - sqTarget a)`. -/
theorem emultiplicity_add_eq (hp : 5 ≤ p) (a b : ℤ_[p]) :
    emultiplicity (p : ℤ_[p]) (4 * a ^ 3 + 27 * b ^ 2)
      = emultiplicity (p : ℤ_[p]) (b ^ 2 - sqTarget a) := by
  have hfac : 4 * a ^ 3 + 27 * b ^ 2 = 27 * (b ^ 2 - sqTarget a) := by
    linear_combination twentySeven_mul_sqTarget (p := p) hp a
  rw [hfac, emultiplicity_mul PadicInt.prime_p,
    PadicInt.emultiplicity_eq_zero_of_isUnit (WeierstrassCurve.isUnit_twentySeven hp), zero_add]

/-! ### The good first coordinates and their mass -/

variable (p) in
/-- The good first coordinates: the `a₄ ∈ ℤ_[p]` with `p ∤ a₄` for which `sqTarget a₄` is a
square. -/
def goodFst : Set ℤ_[p] := {a | ¬ (p : ℤ_[p]) ∣ a ∧ IsSquare (sqTarget a)}

/-- For `p ≥ 5`, `goodFst p` is the preimage of `goodRes p` under reduction modulo `p`. -/
theorem goodFst_eq_preimage (hp : 5 ≤ p) :
    goodFst p = PadicInt.toZMod ⁻¹' (goodRes p : Set (ZMod p)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  ext a
  simp only [goodFst, mem_ofPred_eq, mem_preimage, Finset.mem_coe, mem_goodRes_iff,
    ← PadicInt.dvd_iff_toZMod_eq_zero, ne_eq]
  exact and_congr_right fun ha => by
    rw [PadicInt.isSquare_iff_isSquare_toZMod hodd (isUnit_sqTarget hp ha), toZMod_sqTarget hp]

/-- `goodFst p` is measurable for `p ≥ 5`. -/
theorem measurableSet_goodFst (hp : 5 ≤ p) : MeasurableSet (goodFst p) := by
  have h : PadicInt.toZMod ⁻¹' (goodRes p : Set (ZMod p))
      = ⋃ A ∈ goodRes p, (PadicInt.toZMod ⁻¹' {A} : Set ℤ_[p]) := by
    ext a; simp
  rw [goodFst_eq_preimage hp, h]
  exact (goodRes p).measurableSet_biUnion fun A _ => PadicInt.measurableSet_preimage_toZMod A

/-- For `p ≥ 5`, the Haar mass of `goodFst p` is `|goodRes p| · p⁻¹`. -/
theorem volume_goodFst (hp : 5 ≤ p) :
    (volume : Measure ℤ_[p]) (goodFst p) = (goodRes p).card * (p : ℝ≥0∞)⁻¹ := by
  have h : PadicInt.toZMod ⁻¹' (goodRes p : Set (ZMod p))
      = ⋃ A ∈ goodRes p, (PadicInt.toZMod ⁻¹' {A} : Set ℤ_[p]) := by
    ext a; simp
  rw [goodFst_eq_preimage hp, h, measure_biUnion_finset
    (fun A _ A' _ hAA' => Set.disjoint_left.2 fun _ h h' => hAA' (h.symm.trans h'))
    fun A _ => PadicInt.measurableSet_preimage_toZMod A]
  simp [PadicInt.volume_preimage_toZMod, Finset.sum_const, nsmul_eq_mul]

end BSDTamagawa.HeadDensityTwoBound

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction
  TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The `v_p(Δ) = 2` dictionary -/

/-- If `v_p(Δ) = 2` and `p ∤ c₄`, then Tate's algorithm terminates with Kodaira symbol `I₂` and
Tamagawa number `2`. -/
theorem run_kodaira_tamagawa_of_emultiplicity_eq_two {W : WeierstrassCurve ℤ_[p]}
    (hΔ : W.Δ ≠ 0) (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄)
    (hn : emultiplicity (p : ℤ_[p]) W.Δ = 2) :
    (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 2 ∧
      (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hpΔ : (p : ℤ_[p]) ∣ W.Δ := by
    have h := pow_dvd_of_le_emultiplicity (a := (p : ℤ_[p])) (b := W.Δ) (k := 1)
      (by rw [hn]; norm_num)
    rwa [pow_one] at h
  have hs1 : Step1.run (p : ℤ_[p]) W = Except.ok W := by
    rw [Step1.run.eq_def]; exact ite_eq_left hpΔ
  obtain ⟨out, hs2⟩ : ∃ out, Step2.run (p : ℤ_[p]) W = Except.error out := by
    rcases he : Step2.run (p : ℤ_[p]) W with out | W'
    · exact ⟨out, rfl⟩
    · exact absurd (Step2.run_c₄ he ▸ (pow_one (p : ℤ_[p]) ▸ (Step2.run_hasValuation he).c₄)) hc₄
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step2 hΔ hs2)]
  rw [Step2.run.eq_def, hs1] at hs2
  simp only [except_ok_bind] at hs2
  by_cases hb : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂
  · rw [ite_eq_left hb] at hs2; exact absurd hs2 (by simp)
  · rw [ite_eq_right hb] at hs2
    obtain rfl := Except.error.inj hs2
    exact ⟨by simp [hn], by simp [hn]⟩

/-! ### The `I₂` locus of the coefficient plane -/

/-- `c₄ = -48a₄` for the short model `y² = x³ + a₄x + a₆`, since `b₂ = 0` and `b₄ = 2a₄`. -/
theorem ofShortNF_c₄ {R : Type*} [CommRing R] (a₄ a₆ : R) :
    (ofShortNF a₄ a₆).c₄ = -48 * a₄ := by
  simp only [c₄, b₂, b₄]; ring

/-- `-48` is a unit of `ℤ_[p]` for `p ≥ 5`. -/
theorem isUnit_neg_fortyEight (hp : 5 ≤ p) : IsUnit (-48 : ℤ_[p]) := by
  have h : IsUnit ((16 : ℤ_[p]) * 3) := (isUnit_sixteen hp).mul (PadicInt.isUnit_three hp)
  simpa [show (16 : ℤ_[p]) * 3 = 48 by norm_num] using h.neg

variable (p) in
/-- The `I₂` locus of the coefficient plane: the pairs `(a₄, a₆) ∈ ℤ_p × ℤ_p` with `p ∤ a₄` and
`v_p(4a₄³ + 27a₆²) = 2`. -/
def i2Locus : Set (ℤ_[p] × ℤ_[p]) :=
  {x | ¬ (p : ℤ_[p]) ∣ x.1 ∧ emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) = 2}

/-- For `p ≥ 5`, on the `I₂` locus the discriminant has valuation `2`. -/
theorem emultiplicity_Δ_of_mem_i2Locus (hp : 5 ≤ p) {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ i2Locus p) :
    emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = 2 := by
  rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
    PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add]
  exact hx.2

/-- For `p ≥ 5`, the `I₂` locus lies in the union of the strata over `t = 2`. -/
theorem i2Locus_subset_iUnion_stratFibre (hp : 5 ≤ p) :
    i2Locus p ⊆ ⋃ κ : KodairaSymbol, stratFibre p (κ, 2) := by
  intro x hx
  have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = 2 :=
    emultiplicity_Δ_of_mem_i2Locus hp hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero_right] at hΔv
    exact absurd hΔv (by simp)
  have hUp : x ∈ nonsingularLocus p := hΔ
  have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
    rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
    exact hx.1
  obtain ⟨hk, ht⟩ := run_kodaira_tamagawa_of_emultiplicity_eq_two hΔ hc₄ hΔv
  exact Set.mem_iUnion.2
    ⟨KodairaSymbol.I 2, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- The `I₂` locus is measurable. -/
theorem measurableSet_i2Locus : MeasurableSet (i2Locus p) := by
  have h1 : MeasurableSet {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1} := by
    have he : {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1}
        = (Prod.fst ⁻¹' ((Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) : Set ℤ_[p]))ᶜ := by
      ext x; simp [Ideal.mem_span_singleton]
    rw [he]
    exact (measurable_fst (PadicInt.measurableSet_span_pPow 1)).compl
  have hmeas : Measurable fun x : ℤ_[p] × ℤ_[p] => 4 * x.1 ^ 3 + 27 * x.2 ^ 2 := by fun_prop
  have h2 : MeasurableSet
      {x : ℤ_[p] × ℤ_[p] | emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) = 2} := by
    have := hmeas (PadicInt.measurableSet_setOf_emultiplicity_eq (p := p) 2)
    simpa using this
  exact h1.inter h2

/-! ### The mass of the `I₂` locus -/

/-- For `p ≥ 5` and `p ∤ a₄`, the `a₆`-slice of the `I₂` locus over `a₄` is the square level set
`PadicInt.sqLevelSet (sqTarget a₄) 2`. -/
theorem slice_i2Locus_eq (hp : 5 ≤ p) {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) :
    Prod.mk a ⁻¹' i2Locus p = PadicInt.sqLevelSet (sqTarget a) 2 := by
  ext b
  simp only [mem_preimage, i2Locus, mem_ofPred_eq, PadicInt.mem_sqLevelSet,
    emultiplicity_add_eq hp a b]
  exact ⟨fun h => by simpa using h.2, fun h => ⟨ha, by simpa using h⟩⟩

/-- For `p ≥ 5` and `a₄ ∈ goodFst p`, the `a₆`-slice of the `I₂` locus has mass `2(1 - p⁻¹)p⁻²`. -/
theorem volume_slice_i2Locus (hp : 5 ≤ p) {a : ℤ_[p]} (ha : a ∈ goodFst p) :
    (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' i2Locus p)
      = 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [slice_i2Locus_eq hp ha.1]
  exact PadicInt.measure_sqLevelSet_of_isSquare hodd (isUnit_sqTarget hp ha.1) ha.2 (by norm_num)

/-- For `p ≥ 5`, the `I₂` locus has Haar mass at least `|goodRes p| · p⁻¹ · 2(1 - p⁻¹)p⁻²`. -/
theorem volume_i2Locus_ge (hp : 5 ≤ p) :
    (goodRes p).card * (p : ℝ≥0∞)⁻¹ * (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2)
      ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i2Locus p) := by
  have hbound : ∀ a : ℤ_[p], (goodFst p).indicator
      (fun _ => 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2) a
        ≤ (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' i2Locus p) := by
    intro a
    by_cases ha : a ∈ goodFst p
    · rw [Set.indicator_of_mem ha, volume_slice_i2Locus hp ha]
    · rw [Set.indicator_of_notMem ha]; exact zero_le
  calc (goodRes p).card * (p : ℝ≥0∞)⁻¹ * (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2)
      = (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2) * volume (goodFst p) := by
        rw [volume_goodFst hp]; ring
    _ = ∫⁻ a, (goodFst p).indicator
          (fun _ => 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2) a ∂(volume : Measure ℤ_[p]) := by
        rw [lintegral_indicator (measurableSet_goodFst hp), setLIntegral_const]
    _ ≤ ∫⁻ a, (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' i2Locus p) ∂(volume : Measure ℤ_[p]) :=
        lintegral_mono hbound
    _ = (volume : Measure (ℤ_[p] × ℤ_[p])) (i2Locus p) := by
        rw [Measure.volume_eq_prod, Measure.prod_apply measurableSet_i2Locus]

/-! ### The bound on `δ_p(2)` -/

/-- For `p ≥ 5`, `1 - p⁻¹ = 2N p⁻¹` in `ℝ≥0∞`, where `N = |goodRes p|`. -/
theorem one_sub_inv_eq (hp : 5 ≤ p) :
    1 - (p : ℝ≥0∞)⁻¹ = 2 * ((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  refine ENNReal.sub_eq_of_eq_add (by simp [hp0]) ?_
  have hcast : (p : ℝ≥0∞) = 2 * ((goodRes p).card : ℝ≥0∞) + 1 := by
    exact_mod_cast eq_two_mul_card_goodRes_add_one hp
  calc (1 : ℝ≥0∞) = (p : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ := (ENNReal.mul_inv_cancel hp0 hpt).symm
    _ = 2 * ((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ := by rw [hcast]; ring

/-- For `p ≥ 5`, `p² ≤ 8 N²`, where `N = |goodRes p|`. -/
theorem sq_le_eight_mul_sq_card (hp : 5 ≤ p) :
    (p : ℝ≥0∞) ^ 2 ≤ 8 * ((goodRes p).card : ℝ≥0∞) ^ 2 := by
  have hnat : p ^ 2 ≤ 8 * (goodRes p).card ^ 2 := by
    nlinarith [eq_two_mul_card_goodRes_add_one hp, two_le_card_goodRes hp]
  exact_mod_cast hnat

/-- For every prime `p ≥ 5`, `1/(2p²) ≤ δ_p(2)`. -/
theorem inv_two_mul_sq_le_δ_two (hp : 5 ≤ p) : 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ δ p 2 := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  set N : ℝ≥0∞ := ((goodRes p).card : ℝ≥0∞) with hN
  have hmass : 4 * N ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 4
      ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i2Locus p) := by
    refine le_trans (le_of_eq ?_) (volume_i2Locus_ge hp)
    rw [one_sub_inv_eq hp, ← hN]
    ring
  have harith : 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ 4 * N ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 4 := by
    have h2 : ((2 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hp0)
    have h2t : ((2 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 2) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hpt)
    have h4 : ((p : ℝ≥0∞) ^ 4) ≠ 0 := pow_ne_zero 4 hp0
    have h4t : ((p : ℝ≥0∞) ^ 4) ≠ ⊤ := ENNReal.pow_ne_top hpt
    have hc : ((2 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 4) ≠ 0 := mul_ne_zero two_ne_zero h4
    have hct : ((2 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 4) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) h4t
    have hL : (2 * (p : ℝ≥0∞) ^ 2)⁻¹ * (2 * (p : ℝ≥0∞) ^ 4) = (p : ℝ≥0∞) ^ 2 := by
      rw [show (2 : ℝ≥0∞) * (p : ℝ≥0∞) ^ 4 = (2 * (p : ℝ≥0∞) ^ 2) * (p : ℝ≥0∞) ^ 2 by ring,
        ← mul_assoc, ENNReal.inv_mul_cancel h2 h2t, one_mul]
    have hR : 4 * N ^ 2 * ((p : ℝ≥0∞) ^ 4)⁻¹ * (2 * (p : ℝ≥0∞) ^ 4) = 8 * N ^ 2 := by
      rw [show 4 * N ^ 2 * ((p : ℝ≥0∞) ^ 4)⁻¹ * (2 * (p : ℝ≥0∞) ^ 4)
            = 8 * N ^ 2 * (((p : ℝ≥0∞) ^ 4)⁻¹ * (p : ℝ≥0∞) ^ 4) by ring,
        ENNReal.inv_mul_cancel h4 h4t, mul_one]
    rw [one_div, ← ENNReal.inv_pow,
      ← ENNReal.mul_le_mul_iff_left (c := 2 * (p : ℝ≥0∞) ^ 4) hc hct, hL, hR]
    exact sq_le_eight_mul_sq_card hp
  calc 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ 4 * N ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 4 := harith
    _ ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (i2Locus p) := hmass
    _ ≤ volume (⋃ κ : KodairaSymbol, stratFibre p (κ, 2)) :=
        measure_mono (i2Locus_subset_iUnion_stratFibre hp)
    _ = δ p 2 := volume_iUnion_stratFibre_kodaira 2

/-- The head sum `A_{p,r} = ∑_{1 ≤ t ≤ 4} δ_p(t) v_r(t)`, with `v_r = padicValNat r`. -/
noncomputable def headSum (p : ℕ) [Fact p.Prime] (r : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.Icc 1 4, δ p t * (padicValNat r t : ℝ≥0∞)

/-- For every prime `p ≥ 5`, `1/(2p²) ≤ A_{p,2}`. -/
theorem inv_two_mul_sq_le_headSum_two (hp : 5 ≤ p) : 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ headSum p 2 := by
  have hterm : δ p 2 * (padicValNat 2 2 : ℝ≥0∞) ≤ headSum p 2 := by
    rw [headSum]
    exact Finset.single_le_sum (f := fun t => δ p t * (padicValNat 2 t : ℝ≥0∞))
      (fun _ _ => zero_le) (by decide)
  calc 1 / (2 * (p : ℝ≥0∞) ^ 2) ≤ δ p 2 := inv_two_mul_sq_le_δ_two hp
    _ = δ p 2 * (padicValNat 2 2 : ℝ≥0∞) := by simp
    _ ≤ headSum p 2 := hterm

end WeierstrassCurve
