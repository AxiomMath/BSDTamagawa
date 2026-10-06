/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityFourExact

/-!
# Entering Step 7's subprocedure is a residue condition on `(a₄/p², a₆/p³)`

In Tate's algorithm, Step 6 continues exactly when the Step-6 cubic has a double root, and Step 7
then answers through its `Iₙ*` subprocedure exactly when that cubic does not have a triple root:

  `Step6.run … = if (cubic ϖ W 1 1).HasDoubleRoot then ok W else error ⟨W, .I! 0, …⟩`
  `Step7.run … = match Step6.run ϖ W with
     | error out => error out
     | ok W'     => if (cubic ϖ W' 1 1).HasTripleRoot then ok W' else error <| subprocedure …`

So the entry condition of the subprocedure is `HasDoubleRoot ∧ ¬HasTripleRoot`. For a short model
`(p²A, p³B)` at a prime `p ≥ 5` this holds exactly when `(Ā, B̄)` lies on the cuspidal cubic
`4Ā³ + 27B̄² = 0` with `Ā ≠ 0`, i.e. in `doubleRootResidues p`. The triple-root half follows from
`c₄ = -48 p²A` after the Step-6 translation, with `-48` a unit at `p ≥ 5`, so that
`p³ ∣ c₄ ↔ p ∣ A`.

## Main results

* `hasTripleRoot_step6_cubic_iff_toZMod_eq_zero`: the Step-6 cubic has a triple root exactly when
  `toZMod A = 0`.
* `hasDoubleRoot_and_not_hasTripleRoot_iff_mem_doubleRootResidues`: the entry condition of Step 7's
  subprocedure is `(Ā, B̄) ∈ doubleRootResidues p`.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open TateAlgorithm

/-! ### `¬HasTripleRoot` is `Ā ≠ 0` -/

/-- **Step 7's triple-root test, read on the residue pair: `HasTripleRoot ↔ toZMod A = 0`.**

The triple-root test is `p³ ∣ c₄`. On `Step6.translate` of Step 5's output, `c₄ = -48 (p² A)`, and
`-48` is a unit at `p ≥ 5`, so the test is `p³ ∣ p²A`, that is, `p ∣ A`. No condition on `a₆`
beyond `h5` is needed, since the test reads `c₄` alone. -/
theorem hasTripleRoot_step6_cubic_iff_toZMod_eq_zero (hp : 5 ≤ p) {a₄ a₆ A : ℤ_[p]}
    (h4 : a₄ = (p : ℤ_[p]) ^ 2 * A)
    {W' : WeierstrassCurve ℤ_[p]}
    (h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok W') :
    (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasTripleRoot
      ↔ PadicInt.toZMod A = 0 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hv6 := Step6.hasValuation_translate hϖ (Step5.run_hasValuation hϖ h5)
  obtain ⟨A₁, hA₁⟩ := hv6.a₁
  obtain ⟨A₂, hA₂⟩ := hv6.a₂
  obtain ⟨A₃, hA₃⟩ := hv6.a₃
  obtain ⟨A₄, hA₄⟩ := hv6.a₄
  obtain ⟨A₆, hA₆⟩ := hv6.a₆
  rw [pow_one] at hA₁ hA₂
  have f₄ : (Step6.translate (p : ℤ_[p]) W').c₄ = -48 * ((p : ℤ_[p]) ^ 2 * A) := by
    rw [Step6.translate_c₄, Step5.run_c₄ h5, ofShortNF_c₄, h4]
  rw [hasTripleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆, f₄,
    (isUnit_neg_fortyEight hp).dvd_mul_left,
    show ((p : ℤ_[p]) ^ 3) = (p : ℤ_[p]) ^ 2 * (p : ℤ_[p]) from by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ), PadicInt.dvd_iff_toZMod_eq_zero]

/-! ### The entry condition is membership in `doubleRootResidues` -/

/-- **Entering Step 7's `Iₙ*` subprocedure is exactly `(Ā, B̄) ∈ doubleRootResidues p`.**

The conjunction `HasDoubleRoot ∧ ¬HasTripleRoot` is the branch condition of `Step6.run` and
`Step7.run` for answering through the subprocedure. Its first conjunct is equivalent to
`(Ā, B̄) ∈ cuspidalResidues p` and its second to `Ā ≠ 0`, and
`doubleRootResidues p = (cuspidalResidues p).filter (·.1 ≠ 0)`. -/
theorem hasDoubleRoot_and_not_hasTripleRoot_iff_mem_doubleRootResidues (hp : 5 ≤ p)
    {a₄ a₆ A B : ℤ_[p]} (h4 : a₄ = (p : ℤ_[p]) ^ 2 * A) (h6 : a₆ = (p : ℤ_[p]) ^ 3 * B)
    {W' : WeierstrassCurve ℤ_[p]}
    (h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok W') :
    ((cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot ∧
        ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasTripleRoot)
      ↔ (PadicInt.toZMod A, PadicInt.toZMod B) ∈ doubleRootResidues p := by
  rw [doubleRootResidues, Finset.mem_filter, (step6_cubic_bridge hp h4 h6 h5).1,
    hasTripleRoot_step6_cubic_iff_toZMod_eq_zero hp h4 h5]

end WeierstrassCurve
