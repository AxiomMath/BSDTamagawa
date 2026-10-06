/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityInStarForward
public import BSDTamagawa.GOTTable.InStarEquality

/-!
# A positively-indexed `Iₘ*` carries Tamagawa number `2` or `4`

On the branch of Tate's algorithm where Step 6 returns `ok` and the triple-root test fails, the
answer reported by Step 7 has Tamagawa number `c ∈ {2, 4}`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.run_error_tamagawaNumber_eq_two_or_four`: if Step 6
  returns `ok` with a model whose cubic has no triple root, then the output of Step 7 has
  Tamagawa number `2` or `4`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy TateAlgorithm

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]} {m : ℕ}

/-- If Step 6 returns `ok` with a model `W''` whose cubic has no triple root, then the output of
Step 7 has Tamagawa number `2` or `4`. -/
theorem Step7.run_error_tamagawaNumber_eq_two_or_four (hΔ : W.Δ ≠ 0)
    {W'' : WeierstrassCurve ℤ_[p]} (h6 : Step6.run (p : ℤ_[p]) W = Except.ok W'')
    (hnt : ¬ (cubic (p : ℤ_[p]) W'' 1 1).HasTripleRoot)
    (h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.tamagawaNumber = 2 ∨ out.tamagawaNumber = 4 := by
  rw [Step7.run.eq_def] at h7
  split at h7
  · rename_i out'' heq
    rw [h6] at heq
    exact absurd heq (by simp)
  · rename_i W₀ heq
    rw [h6] at heq
    obtain rfl : W'' = W₀ := Except.ok.inj heq
    rw [dite_eq_right hnt] at h7
    obtain rfl := Except.error.inj h7
    exact Step7.subprocedure_tamagawaNumber_eq_two_or_four _ _ _ _ _

end TateAlgorithm

end WeierstrassCurve
