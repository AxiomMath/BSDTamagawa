/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Equidistribution.Fubini

/-!
# Residue-class cylinder measures and the good-reduction density

For a finite set `S ⊆ (ℤ/pℤ)²` of residue pairs, the cylinder `red_p⁻¹(S) ⊆ ℤ_p × ℤ_p` has Haar
mass `|S| / p²`. For `p ≥ 5` the cuspidal cubic `4a³ + 27b² = 0` has exactly `p` points over `𝔽_p`,
so the good-reduction locus `{(a₄, a₆) | p ∤ Δ}` has mass `1 - 1/p`. On it Tate's algorithm
terminates at Step 1 with answer `(I₀, 1)`, whence `δ_p(I₀, 1) ≥ 1 - 1/p` and `δ_p(1) ≥ 1 - 1/p`.

## Main definitions

* `PadicInt.redPair`: reduction of a coefficient pair modulo `p`.
* `WeierstrassCurve.cuspidalResidues`, `WeierstrassCurve.ellipticResidues`: the residue pairs on
  and off the cuspidal cubic.
* `WeierstrassCurve.goodLocus`: the good-reduction locus `{p ∤ Δ}` of the coefficient plane.

## Main results

* `PadicInt.volume_preimage_redPair`: the cylinder over `S` has mass `|S| / p²`.
* `WeierstrassCurve.card_cuspidalResidues`: the cuspidal cubic has `p` points over `𝔽_p`, `p ≥ 5`.
* `WeierstrassCurve.volume_goodLocus`: the good-reduction locus has mass `1 - 1/p`, `p ≥ 5`.
* `WeierstrassCurve.TateAlgorithm.run_eq_good_of_not_dvd_Δ`: if `ϖ ∤ Δ`, Tate's algorithm returns
  `(I₀, 1)`.
* `WeierstrassCurve.le_deltaP_I0`, `WeierstrassCurve.le_δ_one`: `δ_p(I₀, 1) ≥ 1 - 1/p` and
  `δ_p(1) ≥ 1 - 1/p` for `p ≥ 5`.

## Implementation notes

The good-reduction locus is strictly contained in the fibre `τ_p⁻¹(I₀, 1)`: a non-minimal model
such as `(p⁴a₄, p⁶a₆)` has `p ∣ Δ`, yet Tate's algorithm rescales it and returns the answer of
`(a₄, a₆)`. Hence the lower bounds are inequalities.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*, Quart. J. Math.
  72 (2021), Table 5.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-! ### Divisibility by `p` is vanishing of the residue -/

/-- `p ∣ y` in `ℤ_[p]` exactly when the residue `PadicInt.toZMod y` vanishes: the kernel of
`toZMod` is the maximal ideal, which is `span {p}`. -/
theorem dvd_iff_toZMod_eq_zero {y : ℤ_[p]} : (p : ℤ_[p]) ∣ y ↔ toZMod y = 0 := by
  rw [← Ideal.mem_span_singleton, ← maximalIdeal_eq_span_p, ← ker_toZMod, RingHom.mem_ker]

/-! ### The residue classes of `ℤ_[p]` modulo `p` -/

/-- A residue class of `ℤ_[p]` modulo `p` is a translate of the ideal `p ℤ_[p]`. -/
theorem preimage_toZMod_singleton (a : ZMod p) {x : ℤ_[p]} (hx : toZMod x = a) :
    (toZMod ⁻¹' {a} : Set ℤ_[p])
      = (fun h : ℤ_[p] => (-x) + h) ⁻¹'
          ((Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  ext y
  simp only [mem_preimage, mem_singleton_iff, SetLike.mem_coe, pow_one]
  rw [← maximalIdeal_eq_span_p, ← ker_toZMod, RingHom.mem_ker, map_add, map_neg, hx]
  exact ⟨fun hy => by rw [hy]; ring, fun hy => (neg_add_eq_zero.mp hy).symm⟩

/-- A residue class of `ℤ_[p]` modulo `p` is measurable. -/
theorem measurableSet_preimage_toZMod (a : ZMod p) :
    MeasurableSet (toZMod ⁻¹' {a} : Set ℤ_[p]) := by
  obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (toZMod : ℤ_[p] →+* ZMod p) a
  rw [preimage_toZMod_singleton a hx]
  exact (measurableSet_span_pPow 1).preimage (measurable_const_add _)

/-- Each residue class of `ℤ_[p]` modulo `p` has Haar probability mass `p⁻¹`. -/
theorem volume_preimage_toZMod (a : ZMod p) :
    (volume : Measure ℤ_[p]) (toZMod ⁻¹' {a} : Set ℤ_[p]) = (p : ℝ≥0∞)⁻¹ := by
  obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (toZMod : ℤ_[p] →+* ZMod p) a
  rw [preimage_toZMod_singleton a hx, measure_preimage_add, measure_span_pPow', pow_one]

/-! ### The residue-class cylinders of the coefficient plane -/

variable (p) in
/-- The reduction of a coefficient pair `(a₄, a₆) ∈ ℤ_p × ℤ_p` modulo `p`. Its fibres are the
level-one *cylinders* of the coefficient plane. -/
noncomputable def redPair (x : ℤ_[p] × ℤ_[p]) : ZMod p × ZMod p := (toZMod x.1, toZMod x.2)

/-- A cylinder is a product of two residue classes. -/
theorem preimage_redPair_singleton (c : ZMod p × ZMod p) :
    redPair p ⁻¹' {c} = (toZMod ⁻¹' {c.1}) ×ˢ (toZMod ⁻¹' {c.2}) := by
  ext x
  simp [redPair, Prod.ext_iff, mem_prod]

/-- A cylinder is measurable. -/
theorem measurableSet_preimage_redPair_singleton (c : ZMod p × ZMod p) :
    MeasurableSet (redPair p ⁻¹' {c}) := by
  rw [preimage_redPair_singleton]
  exact (measurableSet_preimage_toZMod _).prod (measurableSet_preimage_toZMod _)

/-- A residue class of `ℤ_p × ℤ_p` modulo `p` has mass `p⁻²`. -/
theorem volume_preimage_redPair_singleton (c : ZMod p × ZMod p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (redPair p ⁻¹' {c}) = ((p : ℝ≥0∞) ^ 2)⁻¹ := by
  rw [preimage_redPair_singleton, Measure.volume_eq_prod, Measure.prod_prod,
    volume_preimage_toZMod, volume_preimage_toZMod, ENNReal.inv_pow, sq]

/-- For a finite set `S` of residue pairs modulo `p`, the cylinder `red_p⁻¹(S) ⊆ ℤ_p × ℤ_p` has
Haar mass `|S| / p²`. -/
@[bsd_tamagawa "T018d"]
theorem volume_preimage_redPair (S : Finset (ZMod p × ZMod p)) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (redPair p ⁻¹' (S : Set (ZMod p × ZMod p)))
      = S.card * ((p : ℝ≥0∞) ^ 2)⁻¹ := by
  have hU : redPair p ⁻¹' (S : Set (ZMod p × ZMod p)) = ⋃ c ∈ S, redPair p ⁻¹' {c} := by
    ext x; simp
  rw [hU, measure_biUnion_finset
    (fun c _ c' _ hcc' => Set.disjoint_left.2 fun _ h h' => hcc' (h.symm.trans h'))
    (fun c _ => measurableSet_preimage_redPair_singleton c)]
  simp [volume_preimage_redPair_singleton, Finset.sum_const, nsmul_eq_mul]

end PadicInt

namespace WeierstrassCurve

/-! ### Small residues are units at `p ≥ 5` -/

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p` and a natural number `0 < n < p`, the residue `n` is nonzero in `ZMod p`. -/
theorem natCast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 :=
  fun h => absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff (ZMod p) p n).mp h)) (by omega)

/-! ### The cuspidal cubic over `𝔽_p` -/

variable (p) in
/-- The residue pairs `(a, b) ∈ 𝔽_p²` on the cuspidal cubic `4a³ + 27b² = 0`; equivalently, for
`p ≥ 5`, the pairs whose short Weierstrass model `y² = x³ + ax + b` is singular mod `p`. -/
def cuspidalResidues : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun c => 4 * c.1 ^ 3 + 27 * c.2 ^ 2 = 0

variable (p) in
/-- The residue pairs `(a, b) ∈ 𝔽_p²` off the cuspidal cubic: `4a³ + 27b² ≠ 0`. For `p ≥ 5` these
are exactly the residues of the coefficient pairs with good reduction. -/
def ellipticResidues : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun c => 4 * c.1 ^ 3 + 27 * c.2 ^ 2 ≠ 0

/-- The rational parametrization `t ↦ (-3t², 2t³)` of the cuspidal cubic. -/
def cuspParam (t : ZMod p) : ZMod p × ZMod p := (-3 * t ^ 2, 2 * t ^ 3)

/-- The parametrization `t ↦ (-3t², 2t³)` is injective for `p ≥ 5`. -/
theorem cuspParam_injective (hp : 5 ≤ p) : Function.Injective (cuspParam (p := p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
  intro t s hts
  simp only [cuspParam, Prod.mk.injEq] at hts
  obtain ⟨h1, h2'⟩ := hts
  have hsq : t ^ 2 = s ^ 2 := mul_left_cancel₀ (neg_ne_zero.mpr h3) h1
  have hcb : t ^ 3 = s ^ 3 := mul_left_cancel₀ h2 h2'
  by_cases hs : s = 0
  · subst hs; simpa using hsq
  · have key : (t - s) * s ^ 2 = 0 := by linear_combination (-t) * hsq + hcb
    rcases mul_eq_zero.mp key with h | h
    · exact sub_eq_zero.mp h
    · exact absurd ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h) hs

/-- For `p ≥ 5` the pairs with `4a³ + 27b² = 0` are exactly the `(-3t², 2t³)`. -/
theorem cuspidalResidues_eq_image (hp : 5 ≤ p) :
    cuspidalResidues p = Finset.image (cuspParam (p := p)) Finset.univ := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
  have h27 : (27 : ZMod p) ≠ 0 := fun h =>
    h3 ((pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp
      (show (3 : ZMod p) ^ 3 = 0 by rw [show ((3 : ZMod p)) ^ 3 = 27 by ring]; exact h))
  refine Finset.Subset.antisymm ?_ ?_
  · rintro ⟨a, b⟩ hc
    simp only [cuspidalResidues, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine Finset.mem_image.2 ⟨-3 * b / (2 * a), Finset.mem_univ _, ?_⟩
    by_cases ha : a = 0
    · have hb : b = 0 := by
        subst ha
        have h0 : (27 : ZMod p) * b ^ 2 = 0 := by linear_combination hc
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h h27
        · exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h
      subst ha; subst hb; simp [cuspParam]
    · have h2a : (2 : ZMod p) * a ≠ 0 := mul_ne_zero h2 ha
      refine Prod.ext ?_ ?_
      · change -3 * (-3 * b / (2 * a)) ^ 2 = a
        field_simp
        linear_combination -hc
      · change 2 * (-3 * b / (2 * a)) ^ 3 = b
        field_simp
        linear_combination (-b) * hc
  · intro c hc
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hc
    simp only [cuspidalResidues, Finset.mem_filter, Finset.mem_univ, true_and, cuspParam]
    ring

/-- For every prime `p ≥ 5`, `#{(a, b) ∈ 𝔽_p² : 4a³ + 27b² = 0} = p`. -/
@[bsd_tamagawa "T018e"]
theorem card_cuspidalResidues (hp : 5 ≤ p) : (cuspidalResidues p).card = p := by
  rw [cuspidalResidues_eq_image hp,
    Finset.card_image_of_injective _ (cuspParam_injective hp), Finset.card_univ, ZMod.card]

/-- The complement count: `#{(a, b) ∈ 𝔽_p² : 4a³ + 27b² ≠ 0} = p² - p`. -/
theorem card_ellipticResidues (hp : 5 ≤ p) : (ellipticResidues p).card = p ^ 2 - p := by
  classical
  have hdiff : ellipticResidues p = Finset.univ \ cuspidalResidues p := by
    ext c
    simp [ellipticResidues, cuspidalResidues]
  rw [hdiff, Finset.card_sdiff, Finset.inter_univ, card_cuspidalResidues hp, Finset.card_univ,
    Fintype.card_prod, ZMod.card, ← sq]

/-! ### The good-reduction locus and its mass -/

variable (p) in
/-- The good-reduction locus of the coefficient plane: the pairs `(a₄, a₆) ∈ ℤ_p × ℤ_p` whose short
Weierstrass model has `p ∤ Δ`. -/
def goodLocus : Set (ℤ_[p] × ℤ_[p]) := {x | ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ}

/-- For `p ≥ 5` the good-reduction locus is the cylinder over the residue pairs off the cuspidal
cubic. -/
theorem goodLocus_eq_preimage (hp : 5 ≤ p) :
    goodLocus p = PadicInt.redPair p ⁻¹' (ellipticResidues p : Set (ZMod p × ZMod p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
  have h16 : (16 : ZMod p) ≠ 0 := by
    rw [show (16 : ZMod p) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  ext x
  simp only [goodLocus, PadicInt.redPair, ellipticResidues, Finset.coe_filter,
    Finset.mem_univ, true_and, mem_preimage, Set.mem_ofPred_eq]
  rw [PadicInt.dvd_iff_toZMod_eq_zero, ofShortNF_Δ]
  simp only [map_mul, map_add, map_neg, map_pow, map_ofNat]
  rw [mul_eq_zero]
  constructor
  · exact fun h hz => h (Or.inr hz)
  · exact fun h hz => h (hz.resolve_left (by simpa using h16))

/-- For a prime `p ≥ 5`, the set of coefficient pairs `(a₄, a₆) ∈ ℤ_p × ℤ_p` with `p ∤ Δ` has
normalized Haar mass `1 - 1/p`. -/
@[bsd_tamagawa "T018f"]
theorem volume_goodLocus (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (goodLocus p) = 1 - (p : ℝ≥0∞)⁻¹ := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hple : p ≤ p ^ 2 := by nlinarith
  rw [goodLocus_eq_preimage hp, PadicInt.volume_preimage_redPair,
    card_ellipticResidues hp, ENNReal.natCast_sub]
  push_cast
  rw [ENNReal.sub_mul fun _ _ => ENNReal.inv_ne_top.mpr (pow_ne_zero 2 hp0),
    ENNReal.mul_inv_cancel (pow_ne_zero 2 hp0) (ENNReal.pow_ne_top hpt), sq, ENNReal.mul_inv
      (Or.inl hp0) (Or.inl hpt), ← mul_assoc, ENNReal.mul_inv_cancel hp0 hpt, one_mul]

end WeierstrassCurve

/-! ### Tate's algorithm at good reduction -/

namespace WeierstrassCurve.TateAlgorithm

open Except Ideal

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {ϖ : R}
  [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] {W : WeierstrassCurve R}

omit [IsDomain R] [IsNoetherianRing R] in
/-- If `ϖ ∤ Δ`, Step 6 of Tate's algorithm returns the good-reduction answer `(I₀, 1)`. -/
theorem step6_run_eq_good_of_not_dvd_Δ (h : ¬ ϖ ∣ W.Δ) :
    Step6.run ϖ W = error ⟨W, .I 0, 1⟩ := by
  rw [Step6.run, Step5.run, Step4.run, Step3.run, Step2.run, Step1.run, ite_eq_right h]; rfl

/-- If `ϖ ∤ Δ`, Step 7 of Tate's algorithm returns the good-reduction answer `(I₀, 1)`. -/
theorem step7_run_eq_good_of_not_dvd_Δ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (h : ¬ ϖ ∣ W.Δ) :
    Step7.run hϖ hΔ = error ⟨W, .I 0, 1⟩ := by
  rw [Step7.run]
  split
  next heq => rw [step6_run_eq_good_of_not_dvd_Δ h] at heq; exact heq ▸ rfl
  next W' heq =>
    rw [step6_run_eq_good_of_not_dvd_Δ h] at heq; exact absurd heq (by simp)

/-- If `ϖ ∤ Δ` then Tate's algorithm returns the curve itself, Kodaira symbol `I₀` and local
Tamagawa number `1`. -/
@[bsd_tamagawa "T018g"]
theorem run_eq_good_of_not_dvd_Δ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (h : ¬ ϖ ∣ W.Δ) :
    run hϖ hΔ = ⟨W, .I 0, 1⟩ := by
  refine run_eq_of_step11_error hϖ hΔ ?_
  rw [Step11.run, Step10.run, Step9.run, Step8.run, step7_run_eq_good_of_not_dvd_Δ hϖ hΔ h]
  rfl

end WeierstrassCurve.TateAlgorithm

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-- A pair with `p ∤ Δ` is nonsingular: `p ∣ 0`. -/
theorem goodLocus_subset_nonsingularLocus : goodLocus p ⊆ nonsingularLocus p :=
  fun _ hx hΔ => hx (hΔ ▸ dvd_zero _)

/-- The good-reduction locus is contained in the fibre `τ_p⁻¹(I₀, 1)`. -/
@[bsd_tamagawa "T018g"]
theorem goodLocus_subset_stratFibre :
    goodLocus p ⊆ stratFibre p (KodairaSymbol.I 0, 1) := by
  intro x hx
  refine (mem_stratFibre_iff (goodLocus_subset_nonsingularLocus hx)).2 ?_
  rw [strat, TateAlgorithm.run_eq_good_of_not_dvd_Δ PadicInt.uniformizer_ne_zero
    (goodLocus_subset_nonsingularLocus hx) hx]

/-- For every prime `p ≥ 5`, `δ_p(I₀, 1) ≥ 1 - 1/p`. -/
@[bsd_tamagawa "T018h"]
theorem le_deltaP_I0 (hp : 5 ≤ p) :
    1 - (p : ℝ≥0∞)⁻¹ ≤ deltaP p (KodairaSymbol.I 0, 1) := by
  rw [← volume_goodLocus hp, ← volume_stratFibre (p := p) (KodairaSymbol.I 0, 1)]
  exact measure_mono goodLocus_subset_stratFibre

/-- `δ_p(I₀, 1) ≤ δ_p(1)`. -/
theorem deltaP_I0_le_δ_one : deltaP p (KodairaSymbol.I 0, 1) ≤ δ p 1 :=
  measure_mono fun _ hW => by simpa using (Prod.ext_iff.1 hW).2

/-- For every prime `p ≥ 5`, `δ_p(1) ≥ 1 - 1/p`. -/
@[bsd_tamagawa "T018h"]
theorem le_δ_one (hp : 5 ≤ p) : 1 - (p : ℝ≥0∞)⁻¹ ≤ δ p 1 :=
  (le_deltaP_I0 hp).trans deltaP_I0_le_δ_one

end WeierstrassCurve
