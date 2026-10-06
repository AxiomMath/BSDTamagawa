/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.ReductionCount.TruncatedSum
public import BSDTamagawa.PrimeCount.DegeneratePoint

/-!
# The Tamagawa generating function at the degenerate point

At `Π = ∅`, `s = 0`, `u = w = 1`, the generating function `tamagawaGeneratingFunction` is the
polynomial whose coefficients are the height-truncated joint proportions of the counts of local
reduction data: `𝒵_{Λ, ∅, X}(0; 1, 1, ∅, 𝐮) = ∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫; X) 𝐮^𝐫`, where
`𝐮^𝐫 = ∏_{K ∈ Λ} u_K^{r_K}`. The sum is an unconditional `tsum` with finite support.

## Main results

* `tamagawaGeneratingFunction_eq_tsum_jointReductionOmegaProportion_of_count_ne_zero`: the
  identity whenever `N(X) ≠ 0`.
* `tamagawaGeneratingFunction_eq_tsum_jointReductionOmegaProportion`: the identity for `X ≥ 4`.

## Implementation notes

The identity needs `N(X) ≠ 0`, and `N(X) = 0` for every `X < 4`, since
`max(4|a₄|³, 27a₆²) < 4` forces `a₄ = a₆ = 0` and hence `Δ = 0`; so `X ≥ 4` is the exact
threshold. The factor `Tam(E)^{-0}` equals `1` for every base, `0` included
(`Complex.cpow_zero`), so no positivity of the Tamagawa product is used.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex BSDTamagawa.DegeneratePoint

/-- If `N(X) ≠ 0`, then for every finite set `Λ` of local reduction data and every `𝐮 ∈ ℂ^Λ`,
`𝒵_{Λ, ∅, X}(0; 1, 1, ∅, 𝐮) = ∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫; X) 𝐮^𝐫`, where `𝒵` is
`tamagawaGeneratingFunction`, `π_Λ(𝐫; X)` is `jointReductionOmegaProportion` and `𝐮^𝐫` is
`multiMonomial`. -/
@[bsd_tamagawa "T040l"]
theorem tamagawaGeneratingFunction_eq_tsum_jointReductionOmegaProportion_of_count_ne_zero
    (Λ : Finset (KodairaSymbol × ℕ)) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : Λ → ℂ) {X : ℝ} (hN : integralShortNFCount X ≠ 0) :
    tamagawaGeneratingFunction Λ ∅ 0 1 1 z uΛ X =
      ∑' r : Λ → ℕ, (jointReductionOmegaProportion Λ r X : ℂ) * multiMonomial r uΛ := by
  have hS : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite := Set.finite_of_ncard_ne_zero hN
  have key := tsum_ncard_fiber_div_mul hS
    (fun q : ℤ × ℤ => fun K : Λ => reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2)
    (fun r : Λ → ℕ => multiMonomial r uΛ) (integralShortNFCount X : ℂ)
  have hcoeff : ∀ r : Λ → ℕ, ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ |
      (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily} ∧
      (fun K : Λ => reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2) = r}.ncard : ℂ) /
      (integralShortNFCount X : ℂ) = (jointReductionOmegaProportion Λ r X : ℂ) := by
    intro r
    rw [jointReductionOmegaProportion, ← setOf_mem_and_jointReductionOmega_eq Λ r X]
    push_cast
    rfl
  have hR : ∑' r : Λ → ℕ,
      (jointReductionOmegaProportion Λ r X : ℂ) * multiMonomial r uΛ =
      (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.indicator
          (fun q => multiMonomial (fun K : Λ =>
            reductionOmega (K : KodairaSymbol × ℕ) q.1 q.2) uΛ) q) /
        (integralShortNFCount X : ℂ) :=
    Eq.trans (tsum_congr fun r => by rw [← hcoeff r]) key
  rw [tamagawaGeneratingFunction]
  refine Eq.trans ?_ hR.symm
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
  · rw [ite_eq_left (show _ ∧ _ from hq), Set.indicator_of_mem hq]
    simp only [one_pow, neg_zero, Complex.cpow_zero, multiMonomial_of_isEmpty, one_mul,
      mul_one, kodairaMonomial]
  · rw [ite_eq_right (show ¬(_ ∧ _) from hq), Set.indicator_of_notMem hq]

/-- Let `Λ` be a finite set of local reduction data. For every real `X ≥ 4` and every `𝐮 ∈ ℂ^Λ`,
`𝒵_{Λ, ∅, X}(0; 1, 1, ∅, 𝐮) = ∑_{𝐫 ∈ ℤ_{≥0}^Λ} π_Λ(𝐫; X) 𝐮^𝐫`, where `𝒵` is
`tamagawaGeneratingFunction`, `π_Λ(𝐫; X)` is `jointReductionOmegaProportion` and
`𝐮^𝐫 = ∏_{K ∈ Λ} u_K^{r_K}` is `multiMonomial`. -/
@[bsd_tamagawa "T040l"]
theorem tamagawaGeneratingFunction_eq_tsum_jointReductionOmegaProportion
    (Λ : Finset (KodairaSymbol × ℕ)) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : Λ → ℂ) {X : ℝ} (hX : 4 ≤ X) :
    tamagawaGeneratingFunction Λ ∅ 0 1 1 z uΛ X =
      ∑' r : Λ → ℕ, (jointReductionOmegaProportion Λ r X : ℂ) * multiMonomial r uΛ :=
  tamagawaGeneratingFunction_eq_tsum_jointReductionOmegaProportion_of_count_ne_zero Λ z uΛ
    (integralShortNFCount_ne_zero_of_four_le hX)

end WeierstrassCurve
