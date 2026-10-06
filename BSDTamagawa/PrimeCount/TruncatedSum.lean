/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Equidistribution.ResidueClass

/-!
# The truncated proportions `π_r(X)` sum to `1`

`∑_{r ≥ 0} π_r(X) = 1`, with `π_r(X)` the height-truncated proportion of curves whose Tamagawa
product has exactly `r` distinct prime factors. The fibres of `E ↦ ω_Tam(E)` partition the finite
height-truncated family `𝓔(X) = {(a₄, a₆) : Ht ≤ X, Δ ≠ 0}`, whose cardinality is `N(X)`.

## Main results

* `BSDTamagawa.FiberCount.tsum_ncard_fiber`: for a finite `S` and any `f`,
  `∑' b, #{a ∈ S : f a = b} = #S`.
* `WeierstrassCurve.integralShortNFCount_ne_zero_of_four_le`: `N(X) ≠ 0` for `X ≥ 4`.
* `WeierstrassCurve.tsum_tamagawaOmegaProportion_eq_one_of_count_ne_zero`: the identity whenever
  `N(X) ≠ 0`.
* `WeierstrassCurve.tsum_tamagawaOmegaProportion_eq_one`: the identity for every `X ≥ 4`.

## Implementation notes

The identity is often stated for `X ≥ 1`, but a nonsingular `(a₄, a₆)` of height
`max(4|a₄|³, 27a₆²) < 4` would have `a₄ = a₆ = 0`, whence `Δ = 0`. So `N(X) = 0` for `X < 4`, every
`π_r(X)` is then the junk value `0`, and the correct threshold is `X ≥ 4`. The sum over `r` is an
unconditional `tsum` with finite support.
-/

@[expose] public section

namespace BSDTamagawa.FiberCount

variable {α β : Type*} {S : Set α}

/-- **The fibering identity.** For a finite set `S` and an arbitrary map `f : α → β`, the
cardinalities of the fibres `{a ∈ S : f a = b}` sum to `#S`: `∑' b, #{a ∈ S : f a = b} = #S` in
`ℝ`. -/
theorem tsum_ncard_fiber (hS : S.Finite) (f : α → β) :
    ∑' b : β, ({a | a ∈ S ∧ f a = b}.ncard : ℝ) = S.ncard := by
  classical
  have hfib : ∀ b : β,
      ↑(hS.toFinset.filter fun a => f a = b) = {a | a ∈ S ∧ f a = b} := by
    intro b
    rw [Finset.coe_filter]
    exact Set.ext fun a => by rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hS.mem_toFinset]
  have hcard : ∀ b : β, ({a | a ∈ S ∧ f a = b}.ncard : ℝ) =
      ((hS.toFinset.filter fun a => f a = b).card : ℝ) := by
    intro b; rw [← hfib b, Set.ncard_coe_finset]
  have hzero : ∀ b ∉ hS.toFinset.image f, ({a | a ∈ S ∧ f a = b}.ncard : ℝ) = 0 := by
    intro b hb
    rw [hcard b, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun a ha hfa => hb (Finset.mem_image.2 ⟨a, ha, hfa⟩)
  rw [tsum_eq_sum hzero, Set.ncard_eq_toFinset_card S hS,
    Finset.card_eq_sum_card_image f hS.toFinset, Nat.cast_sum]
  exact Finset.sum_congr rfl fun b _ => hcard b

/-- **The fibre counts have finite support.** Only finitely many fibres of `f` over a finite set
`S` are nonempty: a nonempty fibre over `b` exhibits `b ∈ f '' S`. -/
theorem finite_setOf_ncard_fiber_ne_zero (hS : S.Finite) (f : α → β) :
    {b : β | {a | a ∈ S ∧ f a = b}.ncard ≠ 0}.Finite := by
  refine (hS.image f).subset fun b hb => ?_
  obtain ⟨a, ha, hfa⟩ := Set.nonempty_of_ncard_ne_zero hb
  exact ⟨a, ha, hfa⟩

/-- **The fibering identity, normalized.** If `#S ≠ 0`, then
`∑' b, #{a ∈ S : f a = b} / #S = 1`. -/
theorem tsum_ncard_fiber_div (hS : S.Finite) (hne : S.ncard ≠ 0) (f : α → β) :
    ∑' b : β, ({a | a ∈ S ∧ f a = b}.ncard : ℝ) / (S.ncard : ℝ) = 1 := by
  rw [tsum_div_const, tsum_ncard_fiber hS f, div_self (Nat.cast_ne_zero.mpr hne)]

end BSDTamagawa.FiberCount

namespace WeierstrassCurve

open BSDTamagawa.FiberCount

/-- The height-truncated family `𝓔(X) = {(a₄, a₆) : Ht ≤ X, Δ ≠ 0}` is finite for `0 ≤ X`. -/
theorem finite_setOf_height_le_and_mem_family {X : ℝ} (hX : 0 ≤ X) :
    {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite :=
  (heightBox X).finite_toSet.subset fun q hq =>
    Finset.mem_coe.2 ((mem_heightBox_iff hX q).2 hq.1)

/-- **`N(X) ≥ 1` for `X ≥ 4`**, as witnessed by `(a₄, a₆) = (-1, 0)`, of height `4` and
discriminant `64 ≠ 0`. -/
theorem integralShortNFCount_ne_zero_of_four_le {X : ℝ} (hX : 4 ≤ X) :
    integralShortNFCount X ≠ 0 := by
  have hmem : ((-1 : ℤ), (0 : ℤ)) ∈
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily} := by
    refine ⟨?_, (ofShortNF_Δ_ne_zero_iff _ _).2 (by norm_num)⟩
    have h : integralShortNFHeight (-1) 0 = 4 := by rw [integralShortNFHeight_eq]; norm_num
    rw [h]; exact_mod_cast hX
  exact Set.ncard_ne_zero_of_mem hmem (finite_setOf_height_le_and_mem_family (by linarith))

/-- The numerator of `π_r(X)` is the fibre of `ω_Tam` over `r` inside the height-truncated family:
`{E ∈ 𝓔(X) : ω_Tam(E) = r} = {E : Ht ≤ X, Δ ≠ 0, ω_Tam(E) = r}`. -/
theorem setOf_mem_and_tamagawaOmega_eq (r : ℕ) (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧ tamagawaOmega q.1 q.2 = r} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily ∧
        tamagawaOmega q.1 q.2 = r} :=
  Set.ext fun _ => by simp only [Set.mem_ofPred_eq, and_assoc]

/-- Whenever `N(X) ≠ 0`, the truncated proportions sum to `1`: `∑_{r ≥ 0} π_r(X) = 1`. -/
@[bsd_tamagawa "T041h"]
theorem tsum_tamagawaOmegaProportion_eq_one_of_count_ne_zero {X : ℝ}
    (hN : integralShortNFCount X ≠ 0) :
    ∑' r : ℕ, tamagawaOmegaProportion r X = 1 := by
  have hS : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite := Set.finite_of_ncard_ne_zero hN
  have := tsum_ncard_fiber_div hS hN fun q : ℤ × ℤ => tamagawaOmega q.1 q.2
  rw [← this]
  exact tsum_congr fun r => by
    rw [tamagawaOmegaProportion, ← setOf_mem_and_tamagawaOmega_eq r X]; rfl

/-- For every real `X ≥ 4`, `∑_{r ≥ 0} π_r(X) = 1`, with `π_r(X)` the height-truncated
proportion. -/
@[bsd_tamagawa "T041h"]
theorem tsum_tamagawaOmegaProportion_eq_one {X : ℝ} (hX : 4 ≤ X) :
    ∑' r : ℕ, tamagawaOmegaProportion r X = 1 :=
  tsum_tamagawaOmegaProportion_eq_one_of_count_ne_zero
    (integralShortNFCount_ne_zero_of_four_le hX)

end WeierstrassCurve
