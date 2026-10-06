/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateRunInvariance

/-!
# Integral translates in Step 7's subprocedure, and the good model `V(t, C)`

The curve on which Tate's algorithm enters Step 7's `Iₙ*` subprocedure is obtained through chosen
lifts of residues, so it is not available in closed form. For a prime `p ≥ 5`, this file collects
ingredients for evaluating the subprocedure instead on the model

  `V(t, C) := ⟨0, 3pt, 0, 0, p³C⟩`,

on which `a₁ = a₃ = a₄ = 0`. Two curves in the subprocedure's entry state at level `2` that are
integral translates of each other receive the same Kodaira symbol and Tamagawa number, and
`V(t, C)` is the image of the short model `(-3p²t², p³(2t³ + C))` under `x ↦ x + pt`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_intTranslate_entry`: two integral translates
  in the entry state at level `2` give the subprocedure the same Kodaira symbol and Tamagawa
  number.
* `WeierstrassCurve.isIntTranslate_ofShortNF_goodModel`: `V(t, C)` is an integral translate of the
  short model with `a₄ = -3p²t²`, `a₆ = p³(2t³ + C)`.
* `WeierstrassCurve.TateAlgorithm.Step7.isIntTranslate_translate_of_step6_ok`: the model handed to
  the subprocedure is an integral translate of the input of `Step7.run`.
* `WeierstrassCurve.TateAlgorithm.Step7.run_error_eq_subprocedure_of_isIntTranslate`: whenever
  `Step7.run` answers through its subprocedure, its answer is the subprocedure's on any integral
  translate of its input that is in the entry state at level `2`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open TateAlgorithm

/-! ### The transfer lemma -/

/-- **Step 7's subprocedure, entered at level `2`, returns the same answer on two integral
translates in its entry state.**

`V` and `V'` are any two curves over `ℤ_[p]`, `5 ≤ p`, with nonvanishing discriminant, each
satisfying the subprocedure's entry hypotheses at `n = 2` (the valuation bundle
`⟨1, 1, 2, 3, 4, …⟩` and `¬ p² ∣ a₂`), and related by `IsIntTranslate`. Neither curve needs to be
the output of a step of the algorithm. -/
theorem TateAlgorithm.Step7.subprocedure_intTranslate_entry (hp : 5 ≤ p)
    {V V' : WeierstrassCurve ℤ_[p]} (hΔ : V.Δ ≠ 0) (hΔ' : V'.Δ ≠ 0)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv b₂' b₄' b₆' b₈' c₄' c₆' Δv' : ℕ}
    (hV : HasValuation (p : ℤ_[p]) V ⟨1, 1, 2, 3, 4, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (hV' : HasValuation (p : ℤ_[p]) V' ⟨1, 1, 2, 3, 4, b₂', b₄', b₆', b₈', c₄', c₆', Δv'⟩)
    (ha₂ : ¬(p : ℤ_[p]) ^ 2 ∣ V.a₂) (ha₂' : ¬(p : ℤ_[p]) ^ 2 ∣ V'.a₂)
    (h : IsIntTranslate V V') :
    (subprocedure PadicInt.uniformizer_ne_zero hΔ le_rfl hV ha₂).kodairaSymbol
        = (subprocedure PadicInt.uniformizer_ne_zero hΔ' le_rfl hV' ha₂').kodairaSymbol ∧
      (subprocedure PadicInt.uniformizer_ne_zero hΔ le_rfl hV ha₂).tamagawaNumber
        = (subprocedure PadicInt.uniformizer_ne_zero hΔ' le_rfl hV' ha₂').tamagawaNumber := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_two ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have h3 : IsUnit (3 : ℤ_[p]) := PadicInt.isUnit_three hp
  obtain ⟨r, s, t, hrel⟩ := h
  obtain ⟨hs, hr⟩ := Step7.dvd_sq_r_of_state PadicInt.prime_p h2 h3
    (by simpa using hV.a₁) (by simpa using hV.a₂) hV.a₃ hV.a₄ hV.a₆ ha₂
    (by rw [← hrel]; simpa using hV'.a₁) (by rw [← hrel]; simpa using hV'.a₂)
    (by rw [← hrel]; exact hV'.a₃) (by rw [← hrel]; exact hV'.a₄)
    (by rw [← hrel]; exact hV'.a₆)
  exact Step7.subprocedure_smul (d := max 6 (multiplicity (p : ℤ_[p]) V.Δ)) h2
    PadicInt.uniformizer_ne_zero hΔ hΔ' le_rfl hV hV' ha₂ ha₂' hrel hs hr
    (le_max_left _ _) (le_max_right _ _)

/-! ### The good model is an integral translate of a short model -/

/-- **`x ↦ x + pt` carries the short model `y² = x³ - 3p²t²x + p³(2t³ + C)` to `V(t, C)`.**

The change of variables is `VariableChange.mk 1 (pt) 0 0`. On a curve with `a₁ = a₂ = a₃ = 0` it
acts by `a₂ ↦ 3r`, `a₄ ↦ a₄ + 3r²` and `a₆ ↦ a₆ + ra₄ + r³`, so at `r = pt` the `a₄` coefficient
becomes `-3p²t² + 3p²t² = 0` and the `a₆` coefficient becomes
`p³(2t³ + C) - 3p³t³ + p³t³ = p³C`. -/
theorem isIntTranslate_ofShortNF_goodModel (t C : ℤ_[p]) :
    IsIntTranslate (ofShortNF (-3 * (p : ℤ_[p]) ^ 2 * t ^ 2) ((p : ℤ_[p]) ^ 3 * (2 * t ^ 3 + C)))
      (⟨0, 3 * (p : ℤ_[p]) * t, 0, 0, (p : ℤ_[p]) ^ 3 * C⟩ : WeierstrassCurve ℤ_[p]) := by
  refine ⟨(p : ℤ_[p]) * t, 0, 0, WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_⟩ <;>
    simp only [smulOne_a₁, smulOne_a₂, smulOne_a₃, smulOne_a₄, smulOne_a₆, ofShortNF] <;> ring

/-! ### The model the algorithm hands to the subprocedure -/

/-- **The curve `Step7.run` passes to its subprocedure is an integral translate of `Step7.run`'s
input.** The subprocedure is entered on `Step7.translate ϖ W'` where `Step6.run ϖ W = .ok W'`;
`W'` is an integral translate of `W`, and `Step7.translate` is a change of variables
`VariableChange.mk 1 _ 0 0`. -/
theorem TateAlgorithm.Step7.isIntTranslate_translate_of_step6_ok
    {W W' : WeierstrassCurve ℤ_[p]} (h : Step6.run (p : ℤ_[p]) W = Except.ok W') :
    IsIntTranslate W (Step7.translate (p : ℤ_[p]) W') :=
  (Step6.isIntTranslate_of_run_ok h).trans ⟨_, 0, 0, rfl⟩

/-- **Step 7's answer, read off any integral translate in the entry state.** Whenever `Step7.run`
answers through its subprocedure, that is, when `Step6.run` continues with `c` and the Step-6 cubic
has no triple root, its Kodaira symbol and Tamagawa number are those the subprocedure returns on
any curve `V` that is an integral translate of `Step7.run`'s input and satisfies the entry
hypotheses at level `2`. -/
theorem TateAlgorithm.Step7.run_error_eq_subprocedure_of_isIntTranslate (hp : 5 ≤ p)
    {W V c : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔV : V.Δ ≠ 0)
    (h6 : Step6.run (p : ℤ_[p]) W = Except.ok c)
    (htr : ¬(cubic (p : ℤ_[p]) c 1 1).HasTripleRoot) {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hV : HasValuation (p : ℤ_[p]) V ⟨1, 1, 2, 3, 4, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬(p : ℤ_[p]) ^ 2 ∣ V.a₂) (hIT : IsIntTranslate W V) {out : Output ℤ_[p]}
    (hrun : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol
        = (subprocedure PadicInt.uniformizer_ne_zero hΔV le_rfl hV ha₂).kodairaSymbol ∧
      out.tamagawaNumber
        = (subprocedure PadicInt.uniformizer_ne_zero hΔV le_rfl hV ha₂).tamagawaNumber := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hΔc : (Step7.translate (p : ℤ_[p]) c).Δ ≠ 0 := by
    rw [Step7.translate_Δ, Step6.run_Δ h6]; exact hΔ
  have hvT := Step7.hasValuation_translate hϖ (Step6.run_hasValuation hϖ h6)
    (Step6.run_hasDoubleRoot h6) htr
  have ha₂T := Step7.not_dvd_translate_a₂ hϖ (Step6.run_hasValuation hϖ h6).a₂
    (Step6.run_hasDoubleRoot h6) htr
  rw [Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h6 htr hΔc hvT ha₂T,
    Except.error.injEq] at hrun
  subst hrun
  exact Step7.subprocedure_intTranslate_entry hp hΔc hΔV hvT hV ha₂T ha₂
    ((IsIntTranslate.symm' (Step7.isIntTranslate_translate_of_step6_ok h6)).trans hIT)

end WeierstrassCurve
