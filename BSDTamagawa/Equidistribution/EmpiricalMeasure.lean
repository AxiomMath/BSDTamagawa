/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Equidistribution.ConfigurationSpace

/-!
# The empirical measure `μ_{S,X}`

For a finite set of primes `S` and a real `X`, the empirical measure on the configuration space
`K_S` is

  `μ_{S,X} = (1 / N(X)) ∑_{Ht(a₄, a₆) ≤ X, Δ ≠ 0} δ_{((a₄, a₆))_{p ∈ S}}`,

where `δ_y` is the unit point mass at `y`, the sum ranges over the integer pairs counted by `N(X)`,
and `(a₄, a₆) ↦ ((a₄, a₆))_{p ∈ S}` is the diagonal embedding `ℤ² → ∏_{p ∈ S} ℤ_p²`.

## Main definitions

* `WeierstrassCurve.configEmbed`: the diagonal embedding `ℤ² → K_S`.
* `WeierstrassCurve.configEmpiricalMeasure`: the empirical measure `μ_{S,X}`.

## Implementation notes

When `N(X) = 0` the sum is the zero measure, and `(0 : ℝ≥0∞)⁻¹ = ∞` multiplies it to `0`, so
`μ_{S,X} = 0`.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

open scoped ENNReal

/-- The diagonal embedding `ℤ² → K_S`, sending an integer pair `(a₄, a₆)` to the family
`((a₄, a₆))_{p ∈ S}` of its images in `ℤ_p²`. -/
noncomputable def configEmbed (S : Finset ℕ) (a₄ a₆ : ℤ) : configSpace S :=
  fun p => ((a₄ : ℤ_[(p : ℕ)]), (a₆ : ℤ_[(p : ℕ)]))

/-- For a finite set of primes `S` and a real `X`, the empirical measure
`μ_{S,X} = (1 / N(X)) ∑ δ_{((a₄, a₆))_{p ∈ S}}` on `K_S`, with a unit point mass at the image of
each integer pair `(a₄, a₆)` of naive height at most `X` with `Δ ≠ 0`. -/
@[bsd_tamagawa "T033f"]
noncomputable def configEmpiricalMeasure (S : Finset ℕ) (X : ℝ) : Measure (configSpace S) :=
  (integralShortNFCount X : ℝ≥0∞)⁻¹ •
    Measure.sum fun q : { q : ℤ × ℤ // (integralShortNFHeight q.1 q.2 : ℝ) ≤ X
        ∧ q ∈ integralShortNFFamily } => Measure.dirac (configEmbed S q.1.1 q.1.2)

end WeierstrassCurve
