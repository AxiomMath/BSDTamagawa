/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarRunTwoFour

/-!
# `S₂ + S₄` as the mass of one set

The measure of the union of the strata of type `(Iₘ*, c)` with `m ≥ 1` and `c ∈ {2, 4}` is the
sum of the two series of their densities:

  `μ_p(⋃_{m ≥ 1} ⋃_{c ∈ {2,4}} τ_p⁻¹((Iₘ*, c))) = S₂ + S₄`,
  `S_c := ∑_{m ≥ 1} δ_p((Iₘ*, c))`.

## Main results

* `disjoint_stratFibre_of_ne_snd`: strata with different Tamagawa numbers are disjoint.
* `volume_iUnion_stratFibre_Istar_pos_two_four`: the measure of the union of the strata
  `(Iₘ*, c)`, `m ≥ 1`, `c ∈ {2, 4}`, is `S₂ + S₄`.

## Implementation notes

Both sums are `tsum`s in `ℝ≥0∞`, where every family is summable.
-/

open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy

/-- Strata with different Tamagawa numbers are disjoint, whatever their Kodaira symbols. -/
theorem disjoint_stratFibre_of_ne_snd {κ κ' : KodairaSymbol} {c c' : ℕ} (h : c ≠ c') :
    Disjoint (stratFibre p (κ, c)) (stratFibre p (κ', c')) :=
  Set.disjoint_left.2 fun x hx hx' => by
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
    exact h ((Prod.ext_iff.1 (((mem_stratFibre_iff hUp).1 hx).symm.trans
      ((mem_stratFibre_iff hUp).1 hx'))).2)

/-- The measure of the union of the strata `(Iₘ*, c)` over `m ≥ 1` and `c ∈ {2, 4}` is the sum
of the two series `∑_{m ≥ 1} δ_p((Iₘ*, 2))` and `∑_{m ≥ 1} δ_p((Iₘ*, 4))`. -/
theorem volume_iUnion_stratFibre_Istar_pos_two_four :
    (volume : Measure (ℤ_[p] × ℤ_[p]))
        (⋃ m : ℕ, ⋃ c ∈ ({2, 4} : Set ℕ), stratFibre p (KodairaSymbol.I! (m + 1), c))
      = (∑' m : ℕ, deltaP p (KodairaSymbol.I! (m + 1), 2))
        + ∑' m : ℕ, deltaP p (KodairaSymbol.I! (m + 1), 4) := by
  have hdisj : ∀ c : ℕ, Pairwise (Function.onFun Disjoint
      (fun m : ℕ => stratFibre p (KodairaSymbol.I! (m + 1), c))) := fun c i j hij =>
    disjoint_stratFibre_of_ne (fun h => hij (Nat.succ_injective (KodairaSymbol.I!.inj h))) c c
  have hmeas : ∀ m c : ℕ, MeasurableSet (stratFibre p (KodairaSymbol.I! (m + 1), c)) :=
    fun m c => (isOpen_stratFibre (p := p) (KodairaSymbol.I! (m + 1), c)).measurableSet
  have hdisj24 : Disjoint (⋃ m : ℕ, stratFibre p (KodairaSymbol.I! (m + 1), 2))
      (⋃ m : ℕ, stratFibre p (KodairaSymbol.I! (m + 1), 4)) := by
    rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    exact disjoint_stratFibre_of_ne_snd (by norm_num)
  have hsplit : (⋃ m : ℕ, ⋃ c ∈ ({2, 4} : Set ℕ), stratFibre p (KodairaSymbol.I! (m + 1), c))
      = (⋃ m : ℕ, stratFibre p (KodairaSymbol.I! (m + 1), 2))
        ∪ ⋃ m : ℕ, stratFibre p (KodairaSymbol.I! (m + 1), 4) := by
    simp only [Set.biUnion_pair]
    exact Set.iUnion_union_distrib _ _
  rw [hsplit, measure_union hdisj24 (MeasurableSet.iUnion fun m => hmeas m 4),
    measure_iUnion (hdisj 2) (fun m => hmeas m 2),
    measure_iUnion (hdisj 4) (fun m => hmeas m 4)]
  exact congrArg₂ (· + ·) (tsum_congr fun m => volume_stratFibre _)
    (tsum_congr fun m => volume_stratFibre _)

end WeierstrassCurve
