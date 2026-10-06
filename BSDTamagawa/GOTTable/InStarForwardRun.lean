/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarSubset

/-!
# Step 7 of Tate's algorithm answers `Iₘ*` with `m ≥ 1`

On a nonsingular Weierstrass curve over `ℤ_[p]` for which Step 6 of Tate's algorithm returns `ok`
and the auxiliary cubic has no triple root, Step 7 terminates with Kodaira symbol `Iₘ*` for some
`m ≥ 1`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_exists_kodairaSymbol_eq_Istar_pos`: every
  answer of the `Iₙ*` subprocedure of Step 7 has Kodaira symbol `Iₘ*` with `m ≥ 1`.
* `WeierstrassCurve.TateAlgorithm.Step7.run_eq_error_of_not_hasTripleRoot`: if Step 6 returns `ok`
  and the auxiliary cubic has no triple root, then Step 7 answers, with Kodaira symbol `Iₘ*` for
  some `m ≥ 1`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]}

/-- Every answer of the `Iₙ*` subprocedure of Step 7 of Tate's algorithm has Kodaira symbol
`Iₘ*` for some `m ≥ 1`. -/
theorem Step7.subprocedure_exists_kodairaSymbol_eq_Istar_pos (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    ∃ m, m ≠ 0 ∧ (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = KodairaSymbol.I! m := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => refine ⟨_, ?_, rfl⟩; omega
  | case3 => refine ⟨_, ?_, rfl⟩; omega

/-- If Step 6 of Tate's algorithm returns `ok` with a curve `W''` whose auxiliary cubic has no
triple root, then Step 7 answers with Kodaira symbol `Iₘ*` for some `m ≥ 1`. -/
theorem Step7.run_eq_error_of_not_hasTripleRoot (hΔ : W.Δ ≠ 0) {W'' : WeierstrassCurve ℤ_[p]}
    (h6 : Step6.run (p : ℤ_[p]) W = Except.ok W'')
    (hnt : ¬ (cubic (p : ℤ_[p]) W'' 1 1).HasTripleRoot) :
    ∃ out, Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out ∧
      ∃ m, m ≠ 0 ∧ out.kodairaSymbol = KodairaSymbol.I! m := by
  rw [Step7.run.eq_def]
  split
  · rename_i out'' heq
    rw [h6] at heq
    exact absurd heq (by simp)
  · rename_i W₀ heq
    rw [h6] at heq
    obtain rfl : W'' = W₀ := Except.ok.inj heq
    rw [dite_eq_right hnt]
    refine ⟨_, rfl, ?_⟩
    apply Step7.subprocedure_exists_kodairaSymbol_eq_Istar_pos

end TateAlgorithm

end WeierstrassCurve
