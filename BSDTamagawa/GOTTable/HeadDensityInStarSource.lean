/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityIZeroStarOne

/-!
# An answer of `Iₘ*` with `m ≥ 1` is the answer of Step 7's subprocedure

Tate's algorithm emits a starred Kodaira symbol `Iₙ*` only at Step 6's error branch, which reports
`I₀*`, and at the two exits of Step 7's subprocedure, which report `I! (2n - 2)` and `I! (2n - 3)`
at stage `n ≥ 2`. Hence an answer `Iₘ*` with `m ≥ 1` of Steps 1–11 is an answer of Step 7's
subprocedure.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step6.kodairaSymbol_ne_Istar`: an answer of Steps 1–6 is never
  `I! m` with `m ≠ 0`.
* `WeierstrassCurve.TateAlgorithm.Step11.stepSeven_error_of_kodairaSymbol_eq_Istar`: an `I! m`
  answer of Steps 1–11 is already Step 7's answer.
* `WeierstrassCurve.TateAlgorithm.Step11.stepSeven_subprocedure_of_kodairaSymbol_eq_Istar`: an
  `I! m` answer with `m ≠ 0` of Steps 1–11 is the answer of Step 7's subprocedure.
* `WeierstrassCurve.step11_error_of_step7`: an answer of Step 7 is also the answer of Step 11.
-/

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]} {m : ℕ}

/-! ### A positively-indexed `Iₘ*` is emitted by neither Step 1–5 nor Step 6 -/

/-- Step 1 reports `I₀`, not a starred symbol. -/
theorem Step1.kodairaSymbol_ne_Istar (h : Step1.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I! m := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  simp

/-- Step 2 reports a multiplicative `Iₙ`, not a starred symbol. -/
theorem Step2.kodairaSymbol_ne_Istar (h : Step2.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I! m := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step1.kodairaSymbol_ne_Istar h
  · have hb : ¬ (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W').b₂ := by
      intro hb'
      rw [ite_eq_left hb'] at h
      simp at h
    rw [ite_eq_right hb] at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 3 reports `II`, not a starred symbol. -/
theorem Step3.kodairaSymbol_ne_Istar (h : Step3.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I! m := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_ne_Istar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 4 reports `III`, not a starred symbol. -/
theorem Step4.kodairaSymbol_ne_Istar (h : Step4.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I! m := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_ne_Istar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 5 reports `IV`, not a starred symbol. -/
theorem Step5.kodairaSymbol_ne_Istar (h : Step5.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I! m := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_ne_Istar h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- **No answer of Steps 1–6 is `Iₘ*` with `m ≥ 1`.** Step 6's own exit reports `I₀*`, of index
`0`, and Steps 1–5 report no starred symbol at all. -/
theorem Step6.kodairaSymbol_ne_Istar (hm : m ≠ 0)
    (h : Step6.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I! m := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_ne_Istar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Ne.symm (KodairaSymbol.Istar_ne_Istar_zero hm)

/-! ### An `Iₘ*` answer of Steps 1–11 is already Step 7's -/

/-- Step 8 reports `IV*`, so an `Iₘ*` answer at Step 8 came from Step 7. -/
theorem Step8.stepSeven_error_of_kodairaSymbol_eq_Istar (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! m) :
    Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- Step 9 reports `III*`, so an `Iₘ*` answer at Step 9 came from Step 7. -/
theorem Step9.stepSeven_error_of_kodairaSymbol_eq_Istar (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! m) :
    Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.stepSeven_error_of_kodairaSymbol_eq_Istar hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 10 reports `II*`, so an `Iₘ*` answer at Step 10 came from Step 7. -/
theorem Step10.stepSeven_error_of_kodairaSymbol_eq_Istar (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! m) :
    Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.stepSeven_error_of_kodairaSymbol_eq_Istar hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `Iₘ*` at Steps 1–11 is Step 7's answer**, at every index `m`. Step 11 answers
nothing on its own, and none of Steps 8, 9, 10 reports a starred symbol of the `Iₙ*` family. -/
theorem Step11.stepSeven_error_of_kodairaSymbol_eq_Istar (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! m) :
    Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.stepSeven_error_of_kodairaSymbol_eq_Istar hΔ h hκ
  · simp at h

/-- **An answer of `Iₘ*` with `m ≥ 1` at Steps 1–11 is the answer of Step 7's subprocedure**: it is
Step 7's answer, and it is not Step 6's. -/
theorem Step11.stepSeven_subprocedure_of_kodairaSymbol_eq_Istar (hΔ : W.Δ ≠ 0) (hm : m ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.I! m) :
    Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out ∧
      Step6.run (p : ℤ_[p]) W ≠ Except.error out :=
  ⟨Step11.stepSeven_error_of_kodairaSymbol_eq_Istar hΔ h hκ,
    fun h6 ↦ Step6.kodairaSymbol_ne_Istar hm h6 hκ⟩

end TateAlgorithm

/-! ### A Step-7 answer reaches Step 11 -/

/-- An error answer of Step 7 of Tate's algorithm is also the error answer of Step 11. -/
theorem step11_error_of_step7 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) {out : Output ℤ_[p]}
    (h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out :=
  step11_error_of_step8 hΔ (by rw [Step8.run.eq_def, h7]; rfl)

end WeierstrassCurve
