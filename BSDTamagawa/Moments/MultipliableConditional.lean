/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.UniformLocalEstimate

/-!
# The majorant `∑_p C/p²` over the primes

For every real constant `C`, the series `∑_{p ∈ 𝒫} C/p²` over the primes converges. This is the
majorant for series over the primes whose terms are bounded by `C/p²`.

## Main results

* `WeierstrassCurve.summable_const_div_sq_prime`: `∑_{p ∈ 𝒫} C/p² < ∞`.
-/

@[expose] public section

namespace WeierstrassCurve

/-! ### The majorant `∑_p C/p²` -/

/-- For every real `C`, `∑_{p ∈ 𝒫} C/p² < ∞`. -/
theorem summable_const_div_sq_prime (C : ℝ) :
    Summable fun p : {q : ℕ // q.Prime} => C / ((p : ℕ) : ℝ) ^ 2 :=
  ((BSDTamagawa.PrimeSqTail.summable_primeSq.mul_left C).subtype Nat.Prime).congr fun p => by
    simp only [Function.comp_apply]
    rw [show BSDTamagawa.PrimeSqTail.primeSq (p : ℕ) = 1 / ((p : ℕ) : ℝ) ^ 2 from ite_eq_left p.2,
      mul_one_div]

end WeierstrassCurve
