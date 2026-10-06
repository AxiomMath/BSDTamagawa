/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Equidistribution.ConfigurationSpace

/-!
# The limit measure `μ_S`

For a finite set of primes `S`, the limit measure `μ_S = ⊗_{p ∈ S} μ_p` on the configuration space
`K_S` is the product of the normalized Haar probability measures `μ_p` on `ℤ_p²`. It is a Borel
probability measure.

## Main definitions

* `WeierstrassCurve.configMeasure`: the limit measure `μ_S`.

## Main results

* `WeierstrassCurve.configMeasure_eq_volume`: `μ_S` is the `volume` of `K_S`.
* `WeierstrassCurve.borelSpace_configSpace`: the measurable structure on `K_S` is the Borel
  σ-algebra.
* `WeierstrassCurve.isProbabilityMeasure_configMeasure`: `μ_S` is a probability measure.
-/

@[expose] public section

-- Unfolding the large body of `addHaarMeasure` inside `Measure.pi` and `Measure.prod` makes
-- elaboration expensive, so it is kept irreducible here.
attribute [local irreducible] MeasureTheory.Measure.addHaarMeasure

namespace WeierstrassCurve

open MeasureTheory

/-- For a finite set of primes `S`, the limit measure `μ_S = ⊗_{p ∈ S} μ_p` on `K_S`, the product
over the primes of `S` of the normalized Haar probability measures on `ℤ_[p] × ℤ_[p]`.
-/
@[bsd_tamagawa "T033e"]
noncomputable def configMeasure (S : Finset ℕ) : Measure (configSpace S) :=
  Measure.pi fun _ => volume

/-- `μ_S` is the `volume` of `K_S`. -/
lemma configMeasure_eq_volume (S : Finset ℕ) : configMeasure S = volume := rfl

/-- The measurable structure on `K_S` is the Borel σ-algebra of its product topology. -/
@[bsd_tamagawa "T033e"]
lemma borelSpace_configSpace (S : Finset ℕ) : BorelSpace (configSpace S) :=
  inferInstance

/-- `μ_S` is a probability measure. -/
@[bsd_tamagawa "T033e"]
instance isProbabilityMeasure_configMeasure (S : Finset ℕ) :
    IsProbabilityMeasure (configMeasure S) := by
  rw [configMeasure_eq_volume]; infer_instance

end WeierstrassCurve
