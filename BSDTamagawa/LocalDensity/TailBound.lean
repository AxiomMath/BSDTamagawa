/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Equidistribution.CylinderMeasure
public import BSDTamagawa.NumberTheory.ReductionValuation

/-!
# The tail bound `1 - δ_p(1) ≤ 3/p²`

The local Tamagawa number is `1` for all but `O(p^{-2})` of the coefficient plane:

  `1 - δ_p(1) ≤ 3/p²` for every prime `p ≥ 5`.

If `p² ∤ Δ` the reduction datum is `(I₀, 1)` or `(I₁, 1)`, so the Tamagawa number is `1`; this
holds at every prime. It remains to bound the mass of `{p² ∣ Δ}`. For `p ≥ 5` this locus is
`{p² ∣ 4a₄³ + 27a₆²}`. On `p ∣ a₄` it is the level-one cylinder `{p ∣ a₄, p ∣ a₆}`, of mass
`p^{-2}`. On `p ∤ a₄` each `a₄`-slice lies in two residue classes of `a₆` modulo `p²`, of total
mass at most `2p^{-2}`. The constant `3` is not sharp: the true mass is `p^{-2} + (p-1)p^{-3}`.

## Main definitions

* `PadicInt.redPairPow`: the reduction `ℤ_p × ℤ_p → (ℤ/p^kℤ)²`.
* `WeierstrassCurve.sqDvdΔLocus`: the locus of `(a₄, a₆) ∈ ℤ_p × ℤ_p` with `p² ∣ Δ`.

## Main results

* `PadicInt.volume_preimage_redPairPow`: for a finite set `S ⊆ (ℤ/p^kℤ)²` the cylinder
  `red_{p^k}⁻¹(S)` has Haar mass `|S| · p^{-2k}`.
* `WeierstrassCurve.volume_sqDvdΔLocus_le`: for `p ≥ 5` the locus `{p² ∣ Δ}` has Haar mass at most
  `3 p^{-2}`.
* `WeierstrassCurve.one_le_δ_one_add`: `1 ≤ δ_p(1) + 3/p²` for every prime `p ≥ 5`.
* `WeierstrassCurve.one_sub_δ_one_le`: `1 - δ_p(1) ≤ 3/p²` for every prime `p ≥ 5`.
* `WeierstrassCurve.exists_tail_bound_δ_one`: there are `C > 0` and `p₀` with `1 - δ_p(1) ≤ C/p²`
  for every prime `p ≥ p₀`.

## Implementation notes

Subtraction in `ℝ≥0∞` is truncated, so the additive form `1 ≤ δ_p(1) + 3/p²` is strictly stronger
than `1 - δ_p(1) ≤ 3/p²`, which holds vacuously when `δ_p(1) = 1`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ### Units and deep divisibility in `ℤ_[p]` -/

/-- A positive natural number smaller than `p` is a unit of `ℤ_[p]`. -/
theorem isUnit_natCast_of_lt {n : ℕ} (hn : 0 < n) (hnp : n < p) : IsUnit (n : ℤ_[p]) := by
  rw [isUnit_iff]
  rcases lt_or_eq_of_le (norm_le_one (n : ℤ_[p])) with hlt | heq
  · exact absurd (Nat.le_of_dvd hn (norm_natCast_lt_one_iff.mp hlt)) (by omega)
  · exact heq

/-- `3` is a unit of `ℤ_[p]` for `p ≥ 5`. -/
theorem isUnit_three (hp : 5 ≤ p) : IsUnit (3 : ℤ_[p]) := by
  simpa using isUnit_natCast_of_lt (p := p) (n := 3) (by norm_num) (by omega)

/-- An element of `ℤ_[p]` is divisible by `p` if and only if it is not a unit. -/
theorem dvd_iff_not_isUnit {y : ℤ_[p]} : (p : ℤ_[p]) ∣ y ↔ ¬ IsUnit y := by
  rw [dvd_iff_toZMod_eq_zero, ← RingHom.mem_ker, ker_toZMod, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]

/-- `p ^ n ∣ y` in `ℤ_[p]` exactly when the residue `PadicInt.toZModPow n y` vanishes. -/
theorem pow_dvd_iff_toZModPow_eq_zero {n : ℕ} {y : ℤ_[p]} :
    (p : ℤ_[p]) ^ n ∣ y ↔ toZModPow n y = 0 := by
  rw [← Ideal.mem_span_singleton, ← ker_toZModPow, RingHom.mem_ker]

/-- Two `p`-adic integers have the same residue modulo `p ^ n` exactly when `p ^ n` divides their
difference. -/
theorem toZModPow_eq_iff_pow_dvd_sub {n : ℕ} {x y : ℤ_[p]} :
    toZModPow n x = toZModPow n y ↔ (p : ℤ_[p]) ^ n ∣ x - y := by
  rw [pow_dvd_iff_toZModPow_eq_zero, map_sub, sub_eq_zero]

/-! ### The level-`k` residue-class cylinders of the coefficient plane -/

variable (p) in
/-- The reduction of a coefficient pair `(a₄, a₆) ∈ ℤ_p × ℤ_p` modulo `p ^ k`. Its fibres are the
level-`k` cylinders of the coefficient plane. -/
noncomputable def redPairPow (k : ℕ) (x : ℤ_[p] × ℤ_[p]) : ZMod (p ^ k) × ZMod (p ^ k) :=
  (toZModPow k x.1, toZModPow k x.2)

/-- A level-`k` cylinder is a product of two residue classes modulo `p ^ k`. -/
theorem preimage_redPairPow_singleton (k : ℕ) (c : ZMod (p ^ k) × ZMod (p ^ k)) :
    redPairPow p k ⁻¹' {c} = (toZModPow k ⁻¹' {c.1}) ×ˢ (toZModPow k ⁻¹' {c.2}) := by
  ext x
  simp [redPairPow, Prod.ext_iff, mem_prod]

/-- A level-`k` cylinder is measurable. -/
theorem measurableSet_preimage_redPairPow_singleton (k : ℕ) (c : ZMod (p ^ k) × ZMod (p ^ k)) :
    MeasurableSet (redPairPow p k ⁻¹' {c}) := by
  rw [preimage_redPairPow_singleton]
  exact (measurableSet_preimage_toZModPow k _).prod (measurableSet_preimage_toZModPow k _)

/-- A residue class of `ℤ_p × ℤ_p` modulo `p ^ k` has Haar mass `p^{-2k}`. -/
theorem volume_preimage_redPairPow_singleton (k : ℕ) (c : ZMod (p ^ k) × ZMod (p ^ k)) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (redPairPow p k ⁻¹' {c})
      = ((p : ℝ≥0∞)⁻¹) ^ (2 * k) := by
  rw [preimage_redPairPow_singleton, Measure.volume_eq_prod, Measure.prod_prod,
    volume_preimage_toZModPow, volume_preimage_toZModPow, ENNReal.inv_pow, ← pow_add, two_mul]

/-- A finite union of level-`k` cylinders is measurable. -/
theorem measurableSet_preimage_redPairPow (k : ℕ) (S : Finset (ZMod (p ^ k) × ZMod (p ^ k))) :
    MeasurableSet (redPairPow p k ⁻¹' (S : Set (ZMod (p ^ k) × ZMod (p ^ k)))) := by
  have hU : redPairPow p k ⁻¹' (S : Set (ZMod (p ^ k) × ZMod (p ^ k)))
      = ⋃ c ∈ S, redPairPow p k ⁻¹' {c} := by
    ext x; simp
  rw [hU]
  exact S.measurableSet_biUnion fun c _ => measurableSet_preimage_redPairPow_singleton k c

/-- For a finite set `S` of residue pairs modulo `p ^ k`, the cylinder `red_{p^k}⁻¹(S) ⊆ ℤ_p × ℤ_p`
has Haar mass `|S| · p^{-2k}`. -/
theorem volume_preimage_redPairPow (k : ℕ) (S : Finset (ZMod (p ^ k) × ZMod (p ^ k))) :
    (volume : Measure (ℤ_[p] × ℤ_[p]))
        (redPairPow p k ⁻¹' (S : Set (ZMod (p ^ k) × ZMod (p ^ k))))
      = S.card * ((p : ℝ≥0∞)⁻¹) ^ (2 * k) := by
  have hU : redPairPow p k ⁻¹' (S : Set (ZMod (p ^ k) × ZMod (p ^ k)))
      = ⋃ c ∈ S, redPairPow p k ⁻¹' {c} := by
    ext x; simp
  rw [hU, measure_biUnion_finset
    (fun c _ c' _ hcc' => Set.disjoint_left.2 fun _ h h' => hcc' (h.symm.trans h'))
    (fun c _ => measurableSet_preimage_redPairPow_singleton k c)]
  simp [volume_preimage_redPairPow_singleton, Finset.sum_const, nsmul_eq_mul]

end PadicInt

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The deep-discriminant locus and its residues modulo `p²` -/

variable (p) in
/-- The deep-discriminant locus of the coefficient plane: the pairs `(a₄, a₆) ∈ ℤ_p × ℤ_p` whose
short Weierstrass model has `p² ∣ Δ`, equivalently `v_p(Δ) ≥ 2`. -/
def sqDvdΔLocus : Set (ℤ_[p] × ℤ_[p]) := {x | (p : ℤ_[p]) ^ 2 ∣ (ofShortNF x.1 x.2).Δ}

variable (p) in
/-- The residue pairs `(A, B) ∈ (ℤ/p²ℤ)²` with `4A³ + 27B² = 0`: the reduction modulo `p²` of the
deep-discriminant locus, for `p ≥ 5`. -/
def deepResidues : Finset (ZMod (p ^ 2) × ZMod (p ^ 2)) :=
  Finset.univ.filter fun c => 4 * c.1 ^ 3 + 27 * c.2 ^ 2 = 0

/-- `16` is a unit of `ℤ_[p]` for `p ≥ 5`, being `2⁴`. -/
theorem isUnit_sixteen (hp : 5 ≤ p) : IsUnit (16 : ℤ_[p]) := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  simpa [show (2 : ℤ_[p]) ^ 4 = 16 by norm_num] using h2.pow 4

/-- `4` is a unit of `ℤ_[p]` for `p ≥ 5`, being `2²`. -/
theorem isUnit_four (hp : 5 ≤ p) : IsUnit (4 : ℤ_[p]) := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  simpa [show (2 : ℤ_[p]) ^ 2 = 4 by norm_num] using h2.pow 2

/-- `27` is a unit of `ℤ_[p]` for `p ≥ 5`, being `3³`. -/
theorem isUnit_twentySeven (hp : 5 ≤ p) : IsUnit (27 : ℤ_[p]) := by
  simpa [show (3 : ℤ_[p]) ^ 3 = 27 by norm_num] using (PadicInt.isUnit_three hp).pow 3

/-- For `p ≥ 5`, `p² ∣ Δ` is equivalent to `p² ∣ 4a₄³ + 27a₆²`. -/
theorem mem_sqDvdΔLocus_iff (hp : 5 ≤ p) {x : ℤ_[p] × ℤ_[p]} :
    x ∈ sqDvdΔLocus p ↔ (p : ℤ_[p]) ^ 2 ∣ 4 * x.1 ^ 3 + 27 * x.2 ^ 2 := by
  change (p : ℤ_[p]) ^ 2 ∣ (ofShortNF x.1 x.2).Δ ↔ _
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left]

/-- For `p ≥ 5` the deep-discriminant locus is the preimage under reduction modulo `p²` of the
residue pairs with `4A³ + 27B² = 0`. -/
theorem sqDvdΔLocus_eq_preimage (hp : 5 ≤ p) :
    sqDvdΔLocus p
      = PadicInt.redPairPow p 2 ⁻¹' (deepResidues p : Set (ZMod (p ^ 2) × ZMod (p ^ 2))) := by
  ext x
  rw [mem_sqDvdΔLocus_iff hp, PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  simp only [deepResidues, PadicInt.redPairPow, Finset.coe_filter, Finset.mem_univ, true_and,
    mem_preimage, Set.mem_ofPred_eq, map_add, map_mul, map_pow, map_ofNat]

/-- The deep-discriminant locus is measurable, being a finite union of level-two cylinders. -/
theorem measurableSet_sqDvdΔLocus (hp : 5 ≤ p) : MeasurableSet (sqDvdΔLocus p) := by
  rw [sqDvdΔLocus_eq_preimage hp]
  exact PadicInt.measurableSet_preimage_redPairPow 2 (deepResidues p)

/-! ### The mass of the deep-discriminant locus -/

/-- For `p ≥ 5` the deep-discriminant locus meets `{p ∣ a₄}` in the level-one cylinder
`{p ∣ a₄, p ∣ a₆}`. -/
theorem sqDvdΔLocus_inter_dvd_fst (hp : 5 ≤ p) :
    sqDvdΔLocus p ∩ {x : ℤ_[p] × ℤ_[p] | (p : ℤ_[p]) ∣ x.1}
      = PadicInt.redPair p ⁻¹' {(0, 0)} := by
  have h27 : IsUnit (27 : ℤ_[p]) := isUnit_twentySeven hp
  have h4a {a : ℤ_[p]} (ha : (p : ℤ_[p]) ∣ a) : (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 :=
    Dvd.dvd.mul_left ((pow_dvd_pow _ (by norm_num)).trans (pow_dvd_pow_of_dvd ha 3)) 4
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, PadicInt.redPair, Prod.mk.injEq,
    Set.mem_ofPred_eq, ← PadicInt.dvd_iff_toZMod_eq_zero, mem_sqDvdΔLocus_iff hp]
  constructor
  · rintro ⟨hd, ha⟩
    have h2 : (p : ℤ_[p]) ^ 2 ∣ 27 * x.2 ^ 2 := by simpa using dvd_sub hd (h4a ha)
    exact ⟨ha, PadicInt.prime_p.dvd_of_dvd_pow
      ((dvd_pow_self ((p : ℤ_[p])) two_ne_zero).trans (h27.dvd_mul_left.mp h2))⟩
  · rintro ⟨ha, hb⟩
    exact ⟨dvd_add (h4a ha) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hb 2) 27), ha⟩

/-- Fix `a₄ ∈ ℤ_[p]` with `p ∤ a₄` and `p ≥ 5`. Then the set of `a₆` with `p² ∣ 4a₄³ + 27a₆²` has
Haar mass at most `2 p^{-2}`: every solution is congruent modulo `p²` to `b₀` or `-b₀` for any one
solution `b₀`. -/
theorem volume_setOf_sq_dvd_le (hp : 5 ≤ p) {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) :
    (volume : Measure ℤ_[p]) {b : ℤ_[p] | (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 + 27 * b ^ 2}
      ≤ 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h4 : IsUnit (4 : ℤ_[p]) := isUnit_four hp
  have h27 : IsUnit (27 : ℤ_[p]) := isUnit_twentySeven hp
  rcases eq_empty_or_nonempty {b : ℤ_[p] | (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 + 27 * b ^ 2} with
    hE | ⟨b₀, hb₀⟩
  · rw [hE]; simp
  have hb₀' : (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 + 27 * b₀ ^ 2 := hb₀
  have hb₀unit : IsUnit b₀ := by
    by_contra hnu
    have hpb : (p : ℤ_[p]) ∣ b₀ := PadicInt.dvd_iff_not_isUnit.mpr hnu
    have h1 : (p : ℤ_[p]) ^ 2 ∣ 27 * b₀ ^ 2 := Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpb 2) 27
    have h2 : (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 := by
      have h := dvd_sub hb₀' h1
      rwa [show 4 * a ^ 3 + 27 * b₀ ^ 2 - 27 * b₀ ^ 2 = 4 * a ^ 3 from by ring] at h
    exact ha (PadicInt.prime_p.dvd_of_dvd_pow
      (h4.dvd_mul_left.mp ((dvd_pow_self ((p : ℤ_[p])) two_ne_zero).trans h2)))
  have hsub : {b : ℤ_[p] | (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 + 27 * b ^ 2}
      ⊆ (PadicInt.toZModPow 2 ⁻¹' {PadicInt.toZModPow 2 b₀})
        ∪ (PadicInt.toZModPow 2 ⁻¹' {PadicInt.toZModPow 2 (-b₀)}) := by
    intro b hb
    have hb' : (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 + 27 * b ^ 2 := hb
    have hd : (p : ℤ_[p]) ^ 2 ∣ 27 * ((b - b₀) * (b + b₀)) := by
      have h := dvd_sub hb' hb₀'
      rwa [show 4 * a ^ 3 + 27 * b ^ 2 - (4 * a ^ 3 + 27 * b₀ ^ 2)
        = 27 * ((b - b₀) * (b + b₀)) from by ring] at h
    have hd' : (p : ℤ_[p]) ^ 2 ∣ (b - b₀) * (b + b₀) := h27.dvd_mul_left.mp hd
    rcases PadicInt.isUnit_sub_or_isUnit_add hodd hb₀unit b with hu | hu
    · refine Or.inr ?_
      have hdvd : (p : ℤ_[p]) ^ 2 ∣ b + b₀ := hu.dvd_mul_left.mp hd'
      exact PadicInt.toZModPow_eq_iff_pow_dvd_sub.mpr (by rwa [sub_neg_eq_add])
    · refine Or.inl ?_
      rw [mul_comm] at hd'
      exact PadicInt.toZModPow_eq_iff_pow_dvd_sub.mpr (hu.dvd_mul_left.mp hd')
  calc (volume : Measure ℤ_[p]) {b : ℤ_[p] | (p : ℤ_[p]) ^ 2 ∣ 4 * a ^ 3 + 27 * b ^ 2}
      ≤ volume ((PadicInt.toZModPow 2 ⁻¹' {PadicInt.toZModPow 2 b₀})
          ∪ (PadicInt.toZModPow 2 ⁻¹' {PadicInt.toZModPow 2 (-b₀)})) := measure_mono hsub
    _ ≤ volume (PadicInt.toZModPow 2 ⁻¹' {PadicInt.toZModPow 2 b₀})
          + volume (PadicInt.toZModPow 2 ⁻¹' {PadicInt.toZModPow 2 (-b₀)}) :=
        measure_union_le _ _
    _ = 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
        rw [PadicInt.volume_preimage_toZModPow, PadicInt.volume_preimage_toZModPow]; ring

/-- The half of the deep-discriminant locus over `{p ∤ a₄}` is measurable. -/
theorem measurableSet_sqDvdΔLocus_inter_not_dvd_fst (hp : 5 ≤ p) :
    MeasurableSet (sqDvdΔLocus p ∩ {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1}) := by
  have h : {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1}
      = (Prod.fst ⁻¹' ((Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) : Set ℤ_[p]))ᶜ := by
    ext x
    simp [Ideal.mem_span_singleton]
  rw [h]
  exact (measurableSet_sqDvdΔLocus hp).inter
    (measurable_fst (PadicInt.measurableSet_span_pPow 1)).compl

/-- For every prime `p ≥ 5` the deep-discriminant locus `{p² ∣ Δ} ⊆ ℤ_p × ℤ_p` has Haar mass at
most `3 p^{-2}`. -/
@[bsd_tamagawa "T018j"]
theorem volume_sqDvdΔLocus_le (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (sqDvdΔLocus p) ≤ 3 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
  set A := sqDvdΔLocus p ∩ {x : ℤ_[p] × ℤ_[p] | (p : ℤ_[p]) ∣ x.1} with hA
  set B := sqDvdΔLocus p ∩ {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1} with hB
  have hcover : sqDvdΔLocus p ⊆ A ∪ B := fun x hx => by
    by_cases h : (p : ℤ_[p]) ∣ x.1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hAval : (volume : Measure (ℤ_[p] × ℤ_[p])) A = ((p : ℝ≥0∞) ^ 2)⁻¹ := by
    rw [hA, sqDvdΔLocus_inter_dvd_fst hp, PadicInt.volume_preimage_redPair_singleton]
  have hslice : ∀ a : ℤ_[p],
      (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' B) ≤ 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
    intro a
    by_cases ha : (p : ℤ_[p]) ∣ a
    · rw [show Prod.mk a ⁻¹' B = (∅ : Set ℤ_[p]) from
        eq_empty_iff_forall_notMem.2 fun b hb => hb.2 ha]
      simp
    · refine le_trans (measure_mono ?_) (volume_setOf_sq_dvd_le hp ha)
      exact fun b hb => (mem_sqDvdΔLocus_iff hp).mp hb.1
  have hBle : (volume : Measure (ℤ_[p] × ℤ_[p])) B ≤ 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
    calc (volume : Measure (ℤ_[p] × ℤ_[p])) B
        = ((volume : Measure ℤ_[p]).prod (volume : Measure ℤ_[p])) B := by
          rw [← Measure.volume_eq_prod]
      _ ≤ ∫⁻ a, (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' B) ∂(volume : Measure ℤ_[p]) :=
          Measure.prod_apply_le (measurableSet_sqDvdΔLocus_inter_not_dvd_fst hp)
      _ ≤ ∫⁻ _ : ℤ_[p], 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ ∂(volume : Measure ℤ_[p]) :=
          lintegral_mono hslice
      _ = 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by rw [lintegral_const, measure_univ, mul_one]
  calc (volume : Measure (ℤ_[p] × ℤ_[p])) (sqDvdΔLocus p)
      ≤ volume (A ∪ B) := measure_mono hcover
    _ ≤ volume A + volume B := measure_union_le _ _
    _ ≤ ((p : ℝ≥0∞) ^ 2)⁻¹ + 2 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
        rw [hAval]; exact add_le_add le_rfl hBle
    _ = 3 * ((p : ℝ≥0∞) ^ 2)⁻¹ := by ring

/-! ### From the coefficient plane to `δ_p(1)` -/

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-- Off the deep-discriminant locus the model is nonsingular: `Δ = 0` is divisible by `p²`. -/
theorem compl_sqDvdΔLocus_subset_nonsingularLocus : (sqDvdΔLocus p)ᶜ ⊆ nonsingularLocus p := by
  intro x hx
  have h : ¬ (p : ℤ_[p]) ^ 2 ∣ (ofShortNF x.1 x.2).Δ := hx
  change (ofShortNF x.1 x.2).Δ ≠ 0
  exact fun hΔ => h (hΔ ▸ dvd_zero _)

/-- Off the deep-discriminant locus the reduction datum is `(I₀, 1)` or `(I₁, 1)`. -/
theorem compl_sqDvdΔLocus_subset_stratFibre_union :
    (sqDvdΔLocus p)ᶜ
      ⊆ stratFibre p (KodairaSymbol.I 0, 1) ∪ stratFibre p (KodairaSymbol.I 1, 1) := by
  intro x hx
  have hU : x ∈ nonsingularLocus p := compl_sqDvdΔLocus_subset_nonsingularLocus hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := hU
  have hnd : ¬ (p : ℤ_[p]) ^ 2 ∣ (ofShortNF x.1 x.2).Δ := hx
  rcases run_kodairaSymbol_tamagawaNumber_of_not_sq_dvd hΔ hnd with h | h
  · exact Or.inl ((mem_stratFibre_iff hU).2 (by rw [strat]; exact Prod.ext h.1 h.2))
  · exact Or.inr ((mem_stratFibre_iff hU).2 (by rw [strat]; exact Prod.ext h.1 h.2))

/-- `δ_p((I₀, 1)) + δ_p((I₁, 1)) ≤ δ_p(1)`. -/
theorem deltaP_I0_add_deltaP_I1_le_δ_one :
    deltaP p (KodairaSymbol.I 0, 1) + deltaP p (KodairaSymbol.I 1, 1) ≤ δ p 1 := by
  have hdisj : Disjoint
      {W : ShortNF.Elliptic ℤ_[p] |
        ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = (KodairaSymbol.I 0, 1)}
      {W : ShortNF.Elliptic ℤ_[p] |
        ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = (KodairaSymbol.I 1, 1)} :=
    Set.disjoint_left.2 fun W hW hW' => by
      have hcon := hW.symm.trans hW'
      simp at hcon
  rw [deltaP, deltaP, ← measure_union hdisj
    (measurableSet_reductionDatum_fiber p (KodairaSymbol.I 1, 1)), δ]
  refine measure_mono fun W hW => ?_
  rcases hW with hW | hW <;> simpa using (Prod.ext_iff.1 hW).2

/-- The union of the two `𝒦₀` strata of the coefficient plane has mass at most `δ_p(1)`. -/
theorem volume_stratFibre_union_le_δ_one :
    (volume : Measure (ℤ_[p] × ℤ_[p]))
        (stratFibre p (KodairaSymbol.I 0, 1) ∪ stratFibre p (KodairaSymbol.I 1, 1))
      ≤ δ p 1 :=
  le_trans (measure_union_le _ _) (by
    rw [volume_stratFibre, volume_stratFibre]; exact deltaP_I0_add_deltaP_I1_le_δ_one)

/-! ### The tail bound -/

/-- For every prime `p ≥ 5`, `1 ≤ δ_p(1) + 3/p²`. -/
theorem one_le_δ_one_add (hp : 5 ≤ p) : 1 ≤ δ p 1 + 3 / (p : ℝ≥0∞) ^ 2 := by
  have hprob : IsProbabilityMeasure (volume : Measure (ℤ_[p] × ℤ_[p])) := by
    rw [Measure.volume_eq_prod]; infer_instance
  calc (1 : ℝ≥0∞) = volume (univ : Set (ℤ_[p] × ℤ_[p])) := measure_univ.symm
    _ = volume (sqDvdΔLocus p ∪ (sqDvdΔLocus p)ᶜ) := by rw [union_compl_self]
    _ ≤ volume (sqDvdΔLocus p) + volume ((sqDvdΔLocus p)ᶜ) := measure_union_le _ _
    _ ≤ 3 * ((p : ℝ≥0∞) ^ 2)⁻¹ + δ p 1 :=
        add_le_add (volume_sqDvdΔLocus_le hp)
          ((measure_mono compl_sqDvdΔLocus_subset_stratFibre_union).trans
            volume_stratFibre_union_le_δ_one)
    _ = δ p 1 + 3 / (p : ℝ≥0∞) ^ 2 := by rw [div_eq_mul_inv]; ring

/-- For every prime `p ≥ 5`, `1 - δ_p(1) ≤ 3/p²`. -/
@[bsd_tamagawa "T023a"]
theorem one_sub_δ_one_le (hp : 5 ≤ p) : 1 - δ p 1 ≤ 3 / (p : ℝ≥0∞) ^ 2 :=
  tsub_le_iff_right.2 (by rw [add_comm]; exact one_le_δ_one_add hp)

/-- There are `C > 0` and `p₀` such that `1 - δ_p(1) ≤ C/p²` for every prime `p ≥ p₀`. -/
@[bsd_tamagawa "T023a"]
theorem exists_tail_bound_δ_one :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧
      ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q → 1 - δ q 1 ≤ C / (q : ℝ≥0∞) ^ 2 :=
  ⟨3, 5, by norm_num, fun _ _ hq => one_sub_δ_one_le hq⟩

end WeierstrassCurve
