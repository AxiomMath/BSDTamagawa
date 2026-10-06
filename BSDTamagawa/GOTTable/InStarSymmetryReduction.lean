/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarTotalMass

/-!
# The `Iₙ*` symmetry, reduced to the strata's minimal parts

At a prime `p ≥ 5`, write `S_c = ∑_{n ≥ 1} δ_p((Iₙ*, c))`. If, stratum by stratum, the minimal
part of `(Iₘ*, 2)` and the minimal part of `(Iₘ*, 4)` have the same mass,

  `μ_p(τ_p⁻¹(Iₘ*, 2) ∖ σ_p(ℤ_p²)) = μ_p(τ_p⁻¹(Iₘ*, 4) ∖ σ_p(ℤ_p²))` for every `m ≥ 1`,

then `S₂ = S₄`, and hence `HasGOTDensities p`. Each stratum is `σ_p`-stable, so its density is the
mass of its minimal part times `(1 - p⁻¹⁰)⁻¹`, and this common factor cancels.

## Main results

* `deltaP_eq_volume_diff_mul_inv_one_sub`: `δ_p(K)` is the mass of the minimal part of the stratum
  of `K`, times `(1 - p⁻¹⁰)⁻¹`.
* `deltaP_eq_deltaP_of_volume_diff_eq`: equal minimal parts give equal densities.
* `tsum_deltaP_InStar_two_eq_four_of_volume_diff_eq`: equal minimal parts for every `m ≥ 1` give
  `S₂ = S₄`.
* `hasGOTDensities_of_volume_diff_eq`: equal minimal parts for every `m ≥ 1` give
  `HasGOTDensities p`.
-/

open MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-- **A reduction datum's density is the mass of its minimal part, folded**: at every prime
`p ≥ 5`, `δ_p(K) = μ_p(τ_p⁻¹(K) ∖ σ_p(ℤ_p²)) · (1 - p⁻¹⁰)⁻¹`. -/
theorem deltaP_eq_volume_diff_mul_inv_one_sub (hp : 5 ≤ p) (K : ReductionData) :
    deltaP p K
      = (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p K \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  have h := volume_eq_volume_diff_mul_inv_one_sub (p := p) (by omega)
    (mem_stratFibre_scaleProdByPPow_iff (stratScaleInvariant_of_five_le hp) K)
  rwa [volume_stratFibre] at h

/-- **Equal minimal parts give equal densities**, at every prime `p ≥ 5` and for any two reduction
data. Both sides fold through the same storey factor, so it cancels without being evaluated. -/
theorem deltaP_eq_deltaP_of_volume_diff_eq (hp : 5 ≤ p) {K K' : ReductionData}
    (h : (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p K \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
        = volume (stratFibre p K' \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))) :
    deltaP p K = deltaP p K' := by
  rw [deltaP_eq_volume_diff_mul_inv_one_sub hp, deltaP_eq_volume_diff_mul_inv_one_sub hp, h]

/-- **The symmetry `S₂ = S₄`, from the strata's minimal parts.** If for every `m ≥ 1` the minimal
parts of `(Iₘ*, 2)` and `(Iₘ*, 4)` have equal mass, then the two sums agree. -/
theorem tsum_deltaP_InStar_two_eq_four_of_volume_diff_eq (hp : 5 ≤ p)
    (hvol : ∀ m : ℕ, (volume : Measure (ℤ_[p] × ℤ_[p]))
        (stratFibre p (KodairaSymbol.I! (m + 1), 2) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = volume (stratFibre p (KodairaSymbol.I! (m + 1), 4) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))) :
    (∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 2))
      = ∑' n : ℕ, deltaP p (KodairaSymbol.I! (n + 1), 4) :=
  tsum_congr fun m => deltaP_eq_deltaP_of_volume_diff_eq hp (hvol m)

/-- **`HasGOTDensities p` from the strata's minimal parts.** At every prime `p ≥ 5`, if for every
`m ≥ 1` the minimal parts of `(Iₘ*, 2)` and `(Iₘ*, 4)` have equal mass, then
`HasGOTDensities p`. -/
theorem hasGOTDensities_of_volume_diff_eq (hp : 5 ≤ p)
    (hvol : ∀ m : ℕ, (volume : Measure (ℤ_[p] × ℤ_[p]))
        (stratFibre p (KodairaSymbol.I! (m + 1), 2) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = volume (stratFibre p (KodairaSymbol.I! (m + 1), 4) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))) :
    HasGOTDensities p :=
  hasGOTDensities_of_tsum_deltaP_InStar_eq hp
    (tsum_deltaP_InStar_two_eq_four_of_volume_diff_eq hp hvol)

end WeierstrassCurve
