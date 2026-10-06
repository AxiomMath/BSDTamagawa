/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.LocalDensity.Scalar

/-!
# The scalar local factor `h_p(s, w, 𝐳)`

For a prime `p` and parameters `(s, w, 𝐳)`, the scalar local factor is
`h_p(s, w, 𝐳) := ∑_{t ≥ 1} δ_p(t) ψ_{s, w, 𝐳}(t)`, where `δ_p(t)` is the scalar local density
(`WeierstrassCurve.δ`) and `ψ_{s, w, 𝐳}` the scalar weight (`WeierstrassCurve.scalarWeight`). The
definition, `WeierstrassCurve.scalarLocalFactor`, lives in `BSDTamagawa.Defs`; it takes the value
`1` at a non-prime index, and the sum is a `tsum` with the `t = 0` term removed.

## Main results

* `WeierstrassCurve.scalarLocalFactor_of_prime`: the value at a prime index.
* `WeierstrassCurve.scalarLocalFactor_eq_tsum_of_prime`: since `δ_p(0) = 0`, the sum over `t ≥ 1`
  equals the sum over all `t : ℕ`.
* `WeierstrassCurve.scalarLocalFactor_of_not_prime`: the value `1` at a non-prime index.

## Implementation notes

The `t = 0` term is excluded explicitly because the weight does not vanish there:
`ψ_{0, w, 𝐳}(0) = w^{Ω(0)} · 1 · 0^0 = 1` in Mathlib's `Complex.cpow` convention. It is the density
`δ_p(0) = 0` that makes the exclusion harmless.
-/

@[expose] public section

namespace WeierstrassCurve

/-- At a prime index the scalar local factor is `∑_{t ≥ 1} δ_p(t) ψ_{s, w, 𝐳}(t)`. -/
lemma scalarLocalFactor_of_prime (P : Finset ℕ) (p : ℕ) [Fact p.Prime] (s w : ℂ)
    (z : P → ℂ) :
    scalarLocalFactor P p s w z =
      ∑' t : ℕ, if t = 0 then 0 else ((δ p t).toReal : ℂ) * scalarWeight P s w z t :=
  dite_eq_left Fact.out

/-- Since `δ_p(0) = 0`, at a prime index the scalar local factor equals the sum over all of `ℕ`,
`h_p(s, w, 𝐳) = ∑_{t ≥ 0} δ_p(t) ψ_{s, w, 𝐳}(t)`. -/
lemma scalarLocalFactor_eq_tsum_of_prime (P : Finset ℕ) (p : ℕ) [Fact p.Prime] (s w : ℂ)
    (z : P → ℂ) :
    scalarLocalFactor P p s w z =
      ∑' t : ℕ, ((δ p t).toReal : ℂ) * scalarWeight P s w z t := by
  rw [scalarLocalFactor_of_prime]
  refine tsum_congr fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · rw [ite_eq_left rfl, δ_zero]
    simp
  · rw [ite_eq_right ht]

/-- At a non-prime index the scalar local factor is the neutral value `1`. -/
lemma scalarLocalFactor_of_not_prime {P : Finset ℕ} {p : ℕ} (hp : ¬ p.Prime) (s w : ℂ)
    (z : P → ℂ) :
    scalarLocalFactor P p s w z = 1 :=
  dite_eq_right hp

end WeierstrassCurve
