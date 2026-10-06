/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarRegionSymmetry
public import BSDTamagawa.GOTTable.InStarStratumRegion

/-!
# The Griffin–Ono–Tsai densities at primes `p ≥ 5`

Let `p ≥ 5` be prime and `m ≥ 1`. The minimal part of the stratum `(Iₘ*, c)` of the `(A, B)`
plane is the image `deepScale p '' goodRegion p m c`, and the dilation `deepScale` multiplies Haar
measure by `p⁻⁵`. Hence equal masses of `goodRegion p m 2` and `goodRegion p m 4` for every
`m ≥ 1` give equal masses of the corresponding minimal parts, and therefore `HasGOTDensities p`.
Since these two regions do have equal mass, the Griffin–Ono–Tsai densities hold at every prime
`p ≥ 5`.

## Main results

* `volume_stratFibre_diff_eq_of_volume_goodRegion_eq`: equal masses of `goodRegion p m 2` and
  `goodRegion p m 4` give equal masses of the minimal parts of the strata `(Iₘ*, 2)` and
  `(Iₘ*, 4)`.
* `hasGOTDensities_of_volume_goodRegion_eq`: equal masses of these regions for every `m ≥ 1` give
  `HasGOTDensities p`.
* `hasGOTDensities_of_five_le`: `HasGOTDensities p` holds for every prime `p ≥ 5`.
-/

open MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-- For a prime `p ≥ 5` and `m ≥ 1`, if `goodRegion p m 2` and `goodRegion p m 4` have the same
mass, then so do the minimal parts of the strata `(Iₘ*, 2)` and `(Iₘ*, 4)`, that is, these strata
with the image of `scaleProdByPPow 4 6` removed. -/
theorem volume_stratFibre_diff_eq_of_volume_goodRegion_eq (hp : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m)
    (h : (volume : Measure (ℤ_[p] × ℤ_[p])) (goodRegion p m 2) = volume (goodRegion p m 4)) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratFibre p (KodairaSymbol.I! m, 2) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
      = volume (stratFibre p (KodairaSymbol.I! m, 4) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])) := by
  rw [stratFibre_Istar_diff_range_eq_deepScale_image hp hm 2,
    stratFibre_Istar_diff_range_eq_deepScale_image hp hm 4, deepScale,
    PadicInt.measure_image_scaleProdByPPow, PadicInt.measure_image_scaleProdByPPow, h]

/-- For a prime `p ≥ 5`, if for every `m ≥ 1` the regions `goodRegion p m 2` and
`goodRegion p m 4` have the same mass, then `HasGOTDensities p`. -/
theorem hasGOTDensities_of_volume_goodRegion_eq (hp : 5 ≤ p)
    (h : ∀ m : ℕ, 1 ≤ m →
      (volume : Measure (ℤ_[p] × ℤ_[p])) (goodRegion p m 2) = volume (goodRegion p m 4)) :
    HasGOTDensities p :=
  hasGOTDensities_of_volume_diff_eq hp fun m =>
    volume_stratFibre_diff_eq_of_volume_goodRegion_eq hp (Nat.succ_le_succ (Nat.zero_le m))
      (h (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))

/-- The Griffin–Ono–Tsai closed forms for the Tamagawa densities `δ_p(t)` hold at every prime
`p ≥ 5` and every Tamagawa value, with the numerator `3p² − 2p + 1` of `gotHeadLarge`. -/
theorem hasGOTDensities_of_five_le (hp : 5 ≤ p) : HasGOTDensities p :=
  hasGOTDensities_of_volume_goodRegion_eq hp fun _m hm =>
    volume_goodRegion_two_eq_four hp hm (measurableSet_goodRegion hp hm 2)

end WeierstrassCurve
