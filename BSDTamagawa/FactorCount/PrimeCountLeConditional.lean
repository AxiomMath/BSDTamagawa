/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.FactorCount.MeanConditional

/-!
# `Ω(t) ≥ 1` for `t ≥ 2`

This file records the elementary fact `Ω(t) ≥ 1` for `t ≥ 2`, where `Ω` counts prime factors with
multiplicity.

It is the termwise ingredient for comparing the mean of the Tamagawa prime count `ω_Tam` with the
mean of `Ω(Tam(E))`. The pointwise inequality `ω(n) ≤ Ω(n)` does not transfer directly, since the
two limiting laws are different measures on `ℤ_{≥0}`; instead one compares the closed forms
`∑_{p ∈ 𝒫} (1 - δ_p(1))` and `∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) Ω(t)` termwise at each prime, using
`1 - δ_p(1) = ∑_{t ≥ 2} δ_p(t)` and `Ω(t) ≥ 1` for `t ≥ 2`.
-/

@[expose] public section

namespace BSDTamagawa.PrimeCountLeFactorCount

open MeasureTheory WeierstrassCurve BSDTamagawa.ValuationMean BSDTamagawa.FactorCountMean

/-- `Ω(t) ≥ 1` for `t ≥ 2`. -/
theorem one_le_cardFactors {t : ℕ} (ht : 2 ≤ t) : 1 ≤ ArithmeticFunction.cardFactors t :=
  ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr ht

end BSDTamagawa.PrimeCountLeFactorCount

namespace WeierstrassCurve

open BSDTamagawa.ValuationMean BSDTamagawa.FactorCountMean BSDTamagawa.PrimeCountLeFactorCount
  MeasureTheory

end WeierstrassCurve
