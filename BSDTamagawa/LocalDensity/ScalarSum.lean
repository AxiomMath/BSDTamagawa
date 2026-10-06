/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.LocalConstancy
public import BSDTamagawa.NumberTheory.Measure

/-!
# The scalar local densities sum to one

For every prime `p`, `∑_{t ∈ ℕ} δ_p(t) = 1`, where `δ_p(t)` is the `μ_p`-measure of the fibre
`{W : c(τ_p(W)) = t}` of the local Tamagawa number on the elliptic locus. The fibres of a map into
`ℕ` are pairwise disjoint and cover the domain, `μ_p` is a probability measure, and the fibres are
measurable because the reduction datum is a locally constant function of the coefficients; so the
identity is countable additivity of `μ_p`, and no value of `δ_p(t)` is needed.

## Main definitions

* `WeierstrassCurve.ShortNF.Elliptic.coeffs`: the coefficient pair `(a₄, a₆)` of a nonsingular
  short model, as a point of the nonsingular locus `U_p ⊆ ℤ_[p] × ℤ_[p]`.

## Main results

* `WeierstrassCurve.measurableSet_tamagawaNumber_fiber`: the fibres of the local Tamagawa number
  are measurable.
* `WeierstrassCurve.tsum_δ`: `∑_{t ∈ ℕ} δ_p(t) = 1`.
-/

@[expose] public section

open Function MeasureTheory BSDTamagawa.LocalReduction BSDTamagawa.LocalConstancy

namespace WeierstrassCurve

/-! ### Coefficients of a point of the elliptic locus -/

/-- A short Weierstrass model is recovered from its two coefficients: if `W.IsShortNF` then
`W = E(a₄, a₆)`. -/
lemma ofShortNF_eq_self {R : Type*} [CommRing R] {W : WeierstrassCurve R} (h : W.IsShortNF) :
    ofShortNF W.a₄ W.a₆ = W := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  cases W
  simp_all [ofShortNF]

variable (p : ℕ) [Fact p.Prime]

/-- The coefficient pair `(a₄, a₆)` of a point of the elliptic locus, as a point of the nonsingular
locus `U_p ⊆ ℤ_[p] × ℤ_[p]`. -/
noncomputable def ShortNF.Elliptic.coeffs (W : ShortNF.Elliptic ℤ_[p]) : ↥(nonsingularLocus p) :=
  ⟨(W.val.val.a₄, W.val.val.a₆), by
    change (ofShortNF W.val.val.a₄ W.val.val.a₆).Δ ≠ 0
    rw [ofShortNF_eq_self W.val.property]; exact W.property⟩

/-- `coeffs` is measurable. -/
lemma ShortNF.Elliptic.measurable_coeffs : Measurable (ShortNF.Elliptic.coeffs p) :=
  Measurable.subtype_mk
    ((ShortNF.measurable_a₄.comp measurable_subtype_coe).prodMk
      (ShortNF.measurable_a₆.comp measurable_subtype_coe))

/-- Tate's algorithm at equal curves returns equal output, whatever the proofs of `Δ ≠ 0`. -/
private lemma run_eq_of_curve_eq {W W' : WeierstrassCurve ℤ_[p]} (h : W = W')
    (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) :
    TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ =
      TateAlgorithm.run (W := W') PadicInt.uniformizer_ne_zero hΔ' := by
  subst h; rfl

/-- The reduction datum `strat` at the coefficient pair of `W` has the same Tamagawa number as
`τ_p(W)`. -/
lemma tamagawaNumber_strat_coeffs (W : ShortNF.Elliptic ℤ_[p]) :
    (strat p (ShortNF.Elliptic.coeffs p W)).2 = (tauP p W).tamagawaNumber := by
  simp only [strat, tauP, ShortNF.Elliptic.coeffs]
  rw [run_eq_of_curve_eq p (ofShortNF_eq_self W.val.property) _ W.property]

/-- The fibres `{W | c(τ_p(W)) = n}` of the local Tamagawa number are measurable. -/
lemma measurableSet_tamagawaNumber_fiber (n : ℕ) :
    MeasurableSet {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = n} := by
  have h : {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = n} =
      ShortNF.Elliptic.coeffs p ⁻¹' (strat p ⁻¹' {K : ReductionData | K.2 = n}) := by
    ext W; simp only [Set.mem_ofPred_eq, Set.mem_preimage, tamagawaNumber_strat_coeffs]
  rw [h]
  exact ShortNF.Elliptic.measurable_coeffs p (isLocallyConstant_strat p _).measurableSet

/-! ### The identity -/

/-- The fibres of the local Tamagawa number are pairwise disjoint. -/
lemma pairwise_disjoint_tamagawaNumber_fiber :
    Pairwise (Disjoint on
      fun n : ℕ ↦ {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = n}) := by
  intro m n hmn
  simp only [Function.onFun, Set.disjoint_left, Set.mem_ofPred_eq]
  exact fun _ hm hn ↦ hmn (hm.symm.trans hn)

/-- The fibres of the local Tamagawa number cover the elliptic locus. -/
lemma iUnion_tamagawaNumber_fiber :
    (⋃ n : ℕ, {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = n}) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ Set.mem_iUnion.2 ⟨_, rfl⟩

/-- The scalar local densities sum to one: `∑_{t ∈ ℕ} δ_p(t) = 1`. Since `δ_p(0) = 0`, this is
`∑_{t ≥ 1} δ_p(t) = 1`. -/
@[bsd_tamagawa "T019"]
theorem tsum_δ : ∑' t : ℕ, δ p t = 1 := by
  simp only [δ]
  rw [← measure_iUnion (pairwise_disjoint_tamagawaNumber_fiber p)
      (measurableSet_tamagawaNumber_fiber p),
    iUnion_tamagawaNumber_fiber, measure_univ]

end WeierstrassCurve
