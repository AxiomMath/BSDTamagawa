/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityFourExact

/-!
# Step 6's `I₀*` answer at every prime

Let `W` be a Weierstrass curve over `ℤ_[p]` with `W.Δ ≠ 0` on which Step 5 of Tate's algorithm
succeeds with output `W'`. If the Step-6 cubic of `Step6.translate p W'` has no double root, then
Tate's algorithm returns Kodaira symbol `I₀*` and Tamagawa number `1 + #roots`, where `#roots` is
the number of distinct roots of that cubic. This holds for every prime `p`, including `p = 2` and
`p = 3`.

## Main results

* `WeierstrassCurve.run_eq_I0star_of_not_hasDoubleRoot_of_step5`: if Step 5 succeeds with output
  `W'` and the Step-6 cubic of `Step6.translate p W'` has no double root, then Tate's algorithm
  returns `(I₀*, 1 + #roots)`.
* `WeierstrassCurve.run_eq_I0star_of_not_hasDoubleRoot_of_dvd`: the same conclusion for a short
  model `ofShortNF a₄ a₆` on which Step 5 returns `Step2.translate p (ofShortNF a₄ a₆)`.
* `WeierstrassCurve.run_eq_I0star_of_not_hasDoubleRoot_of_five_le`: for `5 ≤ p`, `p² ∣ a₄` and
  `p³ ∣ a₆`, the same conclusion for the short model `ofShortNF a₄ a₆`.
-/

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### General models -/

open scoped Classical in
/-- Let `W` be a curve over `ℤ_[p]` with `W.Δ ≠ 0` on which Step 5 of Tate's algorithm succeeds
with output `W'`, and suppose the Step-6 cubic of `Step6.translate p W'` has no double root. Then
Tate's algorithm returns Kodaira symbol `I₀*` and Tamagawa number `1 + #roots`, where `#roots` is
the number of distinct roots of that cubic. -/
theorem run_eq_I0star_of_not_hasDoubleRoot_of_step5 {W W' : WeierstrassCurve ℤ_[p]}
    (hΔ : W.Δ ≠ 0) (h5 : Step5.run (p : ℤ_[p]) W = Except.ok W')
    (hnd : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot) :
    (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
        = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = 1 + (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')
            1 1).toPoly.roots.toFinset.card := by
  classical
  set out : Output ℤ_[p] :=
    ⟨Step6.translate (p : ℤ_[p]) W', KodairaSymbol.I! 0,
      1 + (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).toPoly.roots.toFinset.card⟩
  have h6run : Step6.run (p : ℤ_[p]) W = Except.error out := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_right hnd
  have h7run : Step7.run (W := W) PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step7.run.eq_def]
    split
    next out' heq => rw [← Except.error.inj (h6run.symm.trans heq)]
    next W'' heq => exact absurd (heq.symm.trans h6run) (by simp)
  have h8run : Step8.run (W := W) PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step8.run.eq_def, h7run]; rfl
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step8 hΔ h8run)]
  exact ⟨rfl, rfl⟩

/-! ### Short models -/

open scoped Classical in
/-- Let `ofShortNF a₄ a₆` be a short model over `ℤ_[p]` with nonzero discriminant on which Step 5
of Tate's algorithm returns `Step2.translate p (ofShortNF a₄ a₆)`, and suppose the Step-6 cubic of
its Step-6 translate has no double root. Then Tate's algorithm returns Kodaira symbol `I₀*` and
Tamagawa number one more than the number of distinct roots of that cubic. -/
theorem run_eq_I0star_of_not_hasDoubleRoot_of_dvd {a₄ a₆ : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)))
    (hnd : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).HasDoubleRoot) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = 1 + (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
            (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).toPoly.roots.toFinset.card :=
  run_eq_I0star_of_not_hasDoubleRoot_of_step5 hΔ h5 hnd

open scoped Classical in
/-- For `5 ≤ p`, let `ofShortNF a₄ a₆` be a short model over `ℤ_[p]` with nonzero discriminant,
`p² ∣ a₄` and `p³ ∣ a₆`, and suppose the Step-6 cubic of the Step-6 translate of
`Step2.translate p (ofShortNF a₄ a₆)` has no double root. Then Tate's algorithm returns Kodaira
symbol `I₀*` and Tamagawa number one more than the number of distinct roots of that cubic. -/
theorem run_eq_I0star_of_not_hasDoubleRoot_of_five_le (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 3 ∣ a₆)
    (hnd : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).HasDoubleRoot) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber
        = 1 + (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
            (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))) 1 1).toPoly.roots.toFinset.card :=
  run_eq_I0star_of_not_hasDoubleRoot_of_dvd hΔ (step5_run_eq_ok_of_dvd hp h4 h6) hnd

example : @run_eq_I0star_of_not_hasDoubleRoot_of_five_le
    = @run_eq_I0star_of_not_hasDoubleRoot := rfl

end WeierstrassCurve

end
