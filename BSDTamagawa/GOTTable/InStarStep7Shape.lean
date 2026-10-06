/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarEntryBridge

/-!
# What a Step-7 answer says about Step 6's output and the triple-root test

By definition,

  `Step7.run = match h : Step6.run ϖ W with
     | error out => error out
     | ok W'     => if (cubic ϖ W' 1 1).HasTripleRoot then ok W' else error <| subprocedure …`

so Step 7 answers in exactly two circumstances: it passes on an answer Step 6 already gave, or it
runs its `Iₙ*` subprocedure. Hence a Step-7 answer that is not Step 6's comes with `Step6.run`
returning `ok` and the triple-root test failing.

## Main results

* `step6_ok_and_not_hasTripleRoot_of_step7_error`: a Step-7 answer that is not Step 6's forces
  Step 6 to return `ok` and the cubic to have no triple root.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- **A Step-7 answer that is not Step 6's pins both branch conditions**: Step 6 returned `ok`, and
the triple-root test failed. -/
theorem step6_ok_and_not_hasTripleRoot_of_step7_error (hΔ : W.Δ ≠ 0)
    (h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hne : Step6.run (p : ℤ_[p]) W ≠ Except.error out) :
    ∃ W'', Step6.run (p : ℤ_[p]) W = Except.ok W'' ∧
      ¬ (cubic (p : ℤ_[p]) W'' 1 1).HasTripleRoot := by
  rw [Step7.run.eq_def] at h7
  split at h7
  · rename_i out'' heq
    obtain rfl := Except.error.inj h7
    exact absurd heq hne
  · rename_i W₀ heq
    refine ⟨W₀, heq, fun ht => ?_⟩
    rw [dite_eq_left ht] at h7
    simp at h7

end WeierstrassCurve
