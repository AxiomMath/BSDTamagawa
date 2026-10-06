/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.PrimeCount.TruncatedSum

/-!
# The truncated joint proportions `π_Λ(𝐫; X)` sum to `1`

For every finite set `Λ` of local reduction data, `∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫; X) = 1` whenever
`N(X) ≠ 0`, in particular for `X ≥ 4`. The fibres of `E ↦ 𝛚_Λ(E) := (ω_K(E))_{K ∈ Λ}` partition
the finite height-truncated family `𝓔(X) = {(a₄, a₆) : Ht ≤ X, Δ ≠ 0}`, so the numerators sum to
`N(X)`. The sum is an unconditional `tsum` over `↥Λ → ℕ` with finite support.

## Main results

* `WeierstrassCurve.tsum_jointReductionOmegaProportion_eq_one_of_count_ne_zero`: the sum is `1`
  when `N(X) ≠ 0`.
* `WeierstrassCurve.tsum_jointReductionOmegaProportion_eq_one`: the sum is `1` for `X ≥ 4`.
* `WeierstrassCurve.finite_setOf_jointReductionOmegaProportion_ne_zero`: only finitely many
  `π_Λ(𝐫; X)` are nonzero.

## Implementation notes

`N(X) = 0` for every `X < 4`, so on `1 ≤ X < 4` every `π_Λ(𝐫; X)` is `0 / 0 = 0` and the
identity fails; `X ≥ 4` is the sharp threshold. No hypothesis excluding good-reduction data from
`Λ` is needed: `ω_K` is a total `ℕ`-valued function.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.FiberCount

/-- The numerator set of `π_Λ(𝐫; X)` is the fibre of `𝛚_Λ = (ω_K)_{K ∈ Λ}` over `𝐫` inside the
height-truncated family. -/
theorem setOf_mem_and_jointReductionOmega_eq (Λ : Finset (KodairaSymbol × ℕ)) (r : Λ → ℕ)
    (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧
        (fun K : Λ => reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2) = r} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily ∧
        ∀ K : Λ, reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2 = r K} :=
  Set.ext fun _ => by simp only [Set.mem_ofPred_eq, and_assoc, funext_iff]

/-- Whenever the height-truncated family is nonempty, `N(X) ≠ 0`, the truncated joint proportions
sum to `1`: `∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫; X) = 1`, for every finite set `Λ` of local reduction data. -/
@[bsd_tamagawa "T040k"]
theorem tsum_jointReductionOmegaProportion_eq_one_of_count_ne_zero
    (Λ : Finset (KodairaSymbol × ℕ)) {X : ℝ} (hN : integralShortNFCount X ≠ 0) :
    ∑' r : Λ → ℕ, jointReductionOmegaProportion Λ r X = 1 := by
  have hS : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite := Set.finite_of_ncard_ne_zero hN
  have key := tsum_ncard_fiber_div hS hN
    fun (q : ℤ × ℤ) (K : Λ) => reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2
  rw [← key]
  exact tsum_congr fun r => by
    rw [jointReductionOmegaProportion, ← setOf_mem_and_jointReductionOmega_eq Λ r X]; rfl

/-- For every finite set `Λ` of local reduction data and every real `X ≥ 4`, the height-truncated
joint proportions sum to `1`: `∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫; X) = 1`. The bound `X ≥ 4` is sharp, since
`N(X) = 0` for every `X < 4`. -/
@[bsd_tamagawa "T040k"]
theorem tsum_jointReductionOmegaProportion_eq_one (Λ : Finset (KodairaSymbol × ℕ)) {X : ℝ}
    (hX : 4 ≤ X) :
    ∑' r : Λ → ℕ, jointReductionOmegaProportion Λ r X = 1 :=
  tsum_jointReductionOmegaProportion_eq_one_of_count_ne_zero Λ
    (integralShortNFCount_ne_zero_of_four_le hX)

/-- For every `X ≥ 0`, the set of multi-indices `𝐫` with `π_Λ(𝐫; X) ≠ 0` is finite. -/
theorem finite_setOf_jointReductionOmegaProportion_ne_zero (Λ : Finset (KodairaSymbol × ℕ))
    {X : ℝ} (hX : 0 ≤ X) :
    {r : Λ → ℕ | jointReductionOmegaProportion Λ r X ≠ 0}.Finite := by
  refine (finite_setOf_ncard_fiber_ne_zero (finite_setOf_height_le_and_mem_family hX)
    fun (q : ℤ × ℤ) (K : Λ) => reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2).subset
    fun r hr => ?_
  rw [Set.mem_ofPred_eq, setOf_mem_and_jointReductionOmega_eq Λ r X]
  exact fun h => hr (by rw [jointReductionOmegaProportion, h, Nat.cast_zero, zero_div])

end WeierstrassCurve
