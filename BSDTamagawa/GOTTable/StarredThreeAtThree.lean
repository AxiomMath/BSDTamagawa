/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.TwistThreeAtThree
public import BSDTamagawa.NumberTheory.Step11AtThree

/-!
# The deep branch at `p = 3`: Steps 1–7 traverse, and Step 8 is the first exit

Over `𝔽₃` the reduction of `y² = x³ + a₄x + a₆` has derivative `3x² + a₄ = a₄`, a constant. So
when `3 ∣ a₄` the reduction is `x³ + a₆ = (x + a₆)³`, a cusp with a triple root, and when
`3 ∣ a₄` and `3 ∣ a₆` the singular point is the origin. On a short model over `ℤ_3` with
`3³ ∣ a₄`, `3³ ∣ a₆` and `Δ ≠ 0`, Steps 1 through 7 of Tate's algorithm all traverse, and the curve
handed to Step 8 is `Step6.translate 3 (Step2.translate 3 (ofShortNF a₄ a₆))`. In characteristic
`3` the discriminant of the Step-6 cubic `X³ + bX² + cX + d` is `b²c² − 4c³ − 4b³d`, which
vanishes when `b = c = 0`, and the triple-root condition `b² = 3c` holds since both sides vanish.
The types `IV*`, `III*` and `II*` all lie on this branch, separated by Steps 8, 9 and 10.

## Main results

* `WeierstrassCurve.StarredThree.dvd_Δ_of_cb_dvd`: `3 ∣ Δ` on the deep branch.
* `WeierstrassCurve.StarredThree.step6_run_eq_ok`, `…step7_run_eq_ok`: Steps 1–6 and 1–7 traverse.
* `WeierstrassCurve.StarredThree.step8_run_eq_error_of_not_hasDoubleRoot`: Step 8's exit, reporting
  `IV*` with Tamagawa number `3` or `1` according as its quadratic splits.
* `WeierstrassCurve.StarredThree.mod_r_three`: `Step8.r` pinned modulo `3`.
-/

open CommRing Ideal CharP MeasureTheory

@[expose] public section

namespace WeierstrassCurve

namespace StarredThree

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The deep branch, and that Steps 1–7 traverse on it -/

/-- `3 ∣ Δ` on a short model with `3³ ∣ a₄` and `3³ ∣ a₆` — in fact `3⁹ ∣ Δ`, since
`Δ = −16(4a₄³ + 27a₆²)` and both terms are divisible by `3⁹`. -/
theorem dvd_Δ_of_cb_dvd (hp3 : p = 3) {a₄ a₆ : ℤ_[p]} (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄)
    (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆) : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨α, hα⟩ := h₄
  obtain ⟨β, hβ⟩ := h₆
  exact ⟨(p : ℤ_[p]) ^ 8 * (-16) * (4 * α ^ 3 + β ^ 2), by
    rw [ofShortNF_Δ, hα, hβ]; subst hp3; push_cast; ring⟩

/-- **Steps 1–6 traverse on the deep branch at `p = 3`.** The curve handed on is the Step-6
translate of the Step-2 translate; Step 6's cubic double-root test holds because in characteristic
`3` the discriminant of `X³ + bX² + cX + d` is `b²c² − 4c³ − 4b³d`, and `3² ∣ a₂`, `3³ ∣ a₄` make
`b` and `c` vanish. -/
theorem step6_run_eq_ok (hp3 : p = 3) {a₄ a₆ : ℤ_[p]} (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄)
    (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆) :
    Step6.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨ha₁0, ⟨A₂, hA₂⟩, ⟨A₄, hA₄⟩, -, -, -⟩ :=
    step2_translate_data_three hp3 h₄ h₆ (dvd_Δ_of_cb_dvd hp3 h₄ h₆)
  have h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) :=
    Step5.run_eq_ok_of_cb_dvd_three hp3 h₄ h₆
  obtain ⟨σ, hσ⟩ := dvd_step6_s hp3 ha₁0
  obtain ⟨A₃', hA₃'⟩ := (Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ h5)).a₃
  have hW2a₂ : (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))).a₂ = (p : ℤ_[p]) ^ 2 * (A₂ - σ ^ 2) := by
    rw [step6_translate_a₂ _ ha₁0, hA₂, hσ]; ring
  have hW2a₄ : (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))).a₄
        = (p : ℤ_[p]) ^ 3 * (A₄ - σ * A₃') := by
    rw [step6_translate_a₄ _ ha₁0, hA₄, hσ, hA₃']; ring
  rw [Step6.run.eq_def, h5]
  simp only [except_ok_bind]
  exact ite_eq_left (hasDoubleRoot_of_three hp3 hW2a₂ hW2a₄)

/-- **Steps 1–7 traverse on the deep branch at `p = 3`.** Step 7's test is the triple-root
condition `b² = 3c` on the same cubic, and at `p = 3` both sides vanish, so the `Iₘ*` subprocedure
is not reached from `3³ ∣ a₄ ∧ 3³ ∣ a₆`. -/
theorem step7_run_eq_ok (hp3 : p = 3) {a₄ a₆ : ℤ_[p]} (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0)
    (h₄ : (p : ℤ_[p]) ^ 3 ∣ a₄) (h₆ : (p : ℤ_[p]) ^ 3 ∣ a₆) :
    Step7.run (PadicInt.uniformizer_ne_zero (p := p)) hΔ0
      = Except.ok (Step6.translate (p : ℤ_[p])
        (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨ha₁0, ⟨A₂, hA₂⟩, -, -, -, -⟩ :=
    step2_translate_data_three hp3 h₄ h₆ (dvd_Δ_of_cb_dvd hp3 h₄ h₆)
  obtain ⟨σ, hσ⟩ := dvd_step6_s hp3 ha₁0
  have hW2a₂ : (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))).a₂ = (p : ℤ_[p]) ^ 2 * (A₂ - σ ^ 2) := by
    rw [step6_translate_a₂ _ ha₁0, hA₂, hσ]; ring
  have h6 := step6_run_eq_ok (a₆ := a₆) hp3 h₄ h₆
  rw [Step7.run]
  split
  · next out heq => rw [h6] at heq; exact absurd heq (by simp)
  · next W' heq =>
      obtain rfl : W' = Step6.translate (p : ℤ_[p])
          (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := Except.ok.inj (heq.symm.trans h6)
      exact dite_eq_left (hasTripleRoot_of_three hp3 hW2a₂)

/-! ### Step 8's exit: the `IV*` stratum -/

open scoped Classical in
/-- **Step 8 answers `IV*` when its quadratic has no double root.** The Tamagawa number is `3` or
`1` according as `Y² + (a₃/3²)Y − a₆/3⁴` splits over `𝔽₃` or not. -/
theorem step8_run_eq_error_of_not_hasDoubleRoot {W : WeierstrassCurve ℤ_[p]} (hΔ0 : W.Δ ≠ 0)
    {W' : WeierstrassCurve ℤ_[p]}
    (h7 : Step7.run (PadicInt.uniformizer_ne_zero (p := p)) hΔ0 = Except.ok W')
    (hnd : ¬ (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot) :
    Step8.run (PadicInt.uniformizer_ne_zero (p := p)) hΔ0
      = Except.error ⟨Step8.translate (p : ℤ_[p]) W', KodairaSymbol.IV!,
        if (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).toPoly.Splits
          then 3 else 1⟩ := by
  rw [Step8.run.eq_def, h7]
  simp only [except_ok_bind]
  exact ite_eq_right hnd

/-! ### `Step8.r` at `p = 3`

At `p = 3`, `Step8.r` is a lift of a cube root `root 3 (cubic ϖ W 1 1).d` in the residue field
`𝔽₃`, on which `x ↦ x³` is the identity, so `Step8.r` reduces to its own argument. -/

set_option maxHeartbeats 1000000 in
-- The `ExpChar` and `CharP` instances have to be supplied by hand, exactly as `Step8.r` itself
-- constructs them inside its `dif_pos` branch; instance search does not find them from `p = 3`.
/-- **`Step8.r` is pinned modulo `3`: it is the constant term of Step 6's cubic.** It is defined
as a cube root in the residue field `𝔽₃`, where cubing is the identity. -/
theorem mod_r_three (hp3 : p = 3) (V : WeierstrassCurve ℤ_[p]) :
    mod (p : ℤ_[p]) (Step8.r (p : ℤ_[p]) V) = (cubic (p : ℤ_[p]) V 1 1).d := by
  have h3 : (3 : ℤ_[p] ⧸ span {(p : ℤ_[p])}) = 0 := by
    rw [← map_ofNat (mod (p : ℤ_[p])) 3, mod_eq_zero]
    exact ⟨1, by subst hp3; push_cast; ring⟩
  have : CharP (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 3 := (charP_iff_prime_eq_zero (by decide)).mpr h3
  have : ExpChar (ℤ_[p] ⧸ span {(p : ℤ_[p])}) 3 := .prime (by decide)
  simp only [Step8.r, mod_out, dite_eq_left h3]
  subst hp3
  exact residue_root_self _

end StarredThree

end WeierstrassCurve

end
