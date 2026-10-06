/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.MultipliableConditional
public import BSDTamagawa.NumberTheory.TateRunInvariance

/-!
# Multipliability of the moment Euler product

For every real `x`, `∑_{p ∈ 𝒫} ‖G_p(x) - 1‖ < ∞`, so the Euler product `∏_p G_p(x)` of the moment
local factors converges absolutely and is multipliable. At every prime `p ≥ 5` the geometric tail
law holds, giving `‖G_p(x) - 1‖ ≤ C/p²` with `C` depending only on `⌈x⌉₊`; the finitely many primes
below `5` do not affect summability.

## Main results

* `WeierstrassCurve.summable_const_div_sq`: `∑_{n : ℕ} C/n² < ∞`.
* `WeierstrassCurve.summable_norm_momentLocalFactor_sub_one`: `∑_{p ∈ 𝒫} ‖G_p(x) - 1‖ < ∞`.
* `WeierstrassCurve.multipliable_momentLocalFactor`: `(G_p(x))_{p ∈ 𝒫}` is multipliable.
-/

@[expose] public section

namespace WeierstrassCurve

/-! ### The majorant `∑_n C/n² < ∞` over all of `ℕ` -/

/-- For every real `C`, `∑_{n : ℕ} C/n² < ∞`. -/
theorem summable_const_div_sq (C : ℝ) : Summable fun n : ℕ => C / (n : ℝ) ^ 2 :=
  ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left C).congr fun _ => mul_one_div _ _

/-! ### Absolute convergence and multipliability -/

/-- For every real `x`,

`∑_{p ∈ 𝒫} ‖G_p(x) - 1‖ < ∞`,

that is, the Euler product `∏_p G_p(x)` converges absolutely. -/
@[bsd_tamagawa "T059g"]
theorem summable_norm_momentLocalFactor_sub_one (x : ℝ) :
    Summable fun p : {q : ℕ // q.Prime} => ‖momentLocalFactor (p : ℕ) x - 1‖ := by
  have hpos : (0 : ℝ) ≤ momentBoundConst ⌈x⌉₊ := (momentBoundConst_pos ⌈x⌉₊).le
  have key : Summable fun n : ℕ => ‖momentLocalFactor n x - 1‖ := by
    refine (summable_nat_add_iff 5).mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_nat_add_iff 5).mpr (summable_const_div_sq (momentBoundConst ⌈x⌉₊))))
    by_cases hq : (n + 5).Prime
    · have : Fact (n + 5).Prime := ⟨hq⟩
      exact norm_momentLocalFactor_sub_one_le_of_tailLaw (p := n + 5)
        (hasTailGeometricLaw_of_stratScaleInvariant (by omega)
          (stratScaleInvariant_of_five_le (by omega))) ⌈x⌉₊ (Nat.le_ceil x)
    · rw [momentLocalFactor_of_not_prime hq, sub_self, norm_zero]
      positivity
  exact key.subtype Nat.Prime

/-- For every real `x`, the family `(G_p(x))_{p ∈ 𝒫}` is multipliable. -/
@[bsd_tamagawa "T059g"]
theorem multipliable_momentLocalFactor (x : ℝ) :
    Multipliable fun p : {q : ℕ // q.Prime} => momentLocalFactor (p : ℕ) x :=
  (multipliable_one_add_of_summable
    (f := fun p : {q : ℕ // q.Prime} => momentLocalFactor (p : ℕ) x - 1)
    (summable_norm_momentLocalFactor_sub_one x)).congr fun _ => by ring

end WeierstrassCurve
