/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.GeneratingFunction.KodairaMonomial
public import BSDTamagawa.PrimeCount.TruncatedSum

/-!
# The Tamagawa generating function at the degenerate point

At `Λ = Π = ∅`, `s = 0`, `w = 1` the generating function `𝒵` is the polynomial of truncated
proportions: `𝒵_{∅, ∅, X}(0; u, 1, ∅, ∅) = ∑_{r ≥ 0} π_r(X) u^r`, where `π_r(X)` is the proportion
of curves of height at most `X` whose Tamagawa product has exactly `r` distinct prime factors. Four
of the five factors of the summand of `𝒵` are `1` at this point, and grouping the remaining sum by
the fibres of `ω_Tam` gives the coefficients.

## Main results

* `BSDTamagawa.DegeneratePoint.tsum_ncard_fiber_mul`: for a finite set `S`, a map `f` and a weight
  `g`, `∑' b, #{a ∈ S : f a = b} · g b = ∑' a, 1_S(a) · g (f a)`.
* `WeierstrassCurve.tamagawaGeneratingFunction_eq_tsum_tamagawaOmegaProportion_of_count_ne_zero`:
  the identity whenever `N(X) ≠ 0`.
* `WeierstrassCurve.tamagawaGeneratingFunction_eq_tsum_tamagawaOmegaProportion`: the identity for
  every `X ≥ 4`.

## Implementation notes

`𝒵` divides by `N(X)`, and `N(X) = 0` for every `X < 4`, since `max(4|a₄|³, 27a₆²) < 4` forces
`a₄ = a₆ = 0` and hence `Δ = 0`. So `X ≥ 4` is the exact threshold at which the standing assumption
`N(X) ≥ 1` holds. The sum over `r` is an unconditional `tsum` with finite support.
-/

@[expose] public section

namespace BSDTamagawa.DegeneratePoint

open BSDTamagawa.MultiIndex

variable {α β : Type*} {S : Set α}

/-- **A monomial in no variables is `1`.** `multiMonomial` over an empty index type is the empty
product. -/
theorem multiMonomial_of_isEmpty {P : Type*} [Fintype P] [IsEmpty P] (j : P → ℕ)
    (z : P → ℂ) : multiMonomial j z = 1 := by
  simp [multiMonomial]

/-- **The weighted fibering identity.** For a finite set `S`, an arbitrary map `f : α → β` and an
arbitrary weight `g : β → ℂ`, grouping the sum of `g ∘ f` over `S` by the fibres of `f` replaces
each fibre by its cardinality: `∑' b, #{a ∈ S : f a = b} · g b = ∑' a, 1_S(a) · g (f a)`. -/
theorem tsum_ncard_fiber_mul (hS : S.Finite) (f : α → β) (g : β → ℂ) :
    ∑' b : β, ({a | a ∈ S ∧ f a = b}.ncard : ℂ) * g b =
      ∑' a : α, S.indicator (fun a => g (f a)) a := by
  classical
  have hfib : ∀ b : β, ({a | a ∈ S ∧ f a = b}.ncard : ℂ) =
      ((hS.toFinset.filter fun a => f a = b).card : ℂ) := by
    intro b
    have hcoe : ↑(hS.toFinset.filter fun a => f a = b) = {a | a ∈ S ∧ f a = b} := by
      rw [Finset.coe_filter]
      exact Set.ext fun a => by rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hS.mem_toFinset]
    rw [← hcoe, Set.ncard_coe_finset]
  have hzeroR : ∀ b ∉ hS.toFinset.image f,
      ({a | a ∈ S ∧ f a = b}.ncard : ℂ) * g b = 0 := by
    intro b hb
    have h0 : (hS.toFinset.filter fun a => f a = b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun a ha hfa => hb (Finset.mem_image.2 ⟨a, ha, hfa⟩)
    rw [hfib b, h0, Nat.cast_zero, zero_mul]
  have hzeroL : ∀ a ∉ hS.toFinset, S.indicator (fun a => g (f a)) a = 0 :=
    fun a ha => Set.indicator_of_notMem (fun h => ha (hS.mem_toFinset.2 h)) _
  rw [tsum_eq_sum hzeroR, tsum_eq_sum hzeroL,
    Finset.sum_congr rfl fun a ha => Set.indicator_of_mem (hS.mem_toFinset.1 ha) _,
    Finset.sum_comp g f]
  exact Finset.sum_congr rfl fun b _ => by
    rw [hfib b, nsmul_eq_mul]

/-- **The weighted fibering identity, normalized.** For every `N : ℂ`,
`∑' b, (#{a ∈ S : f a = b} / N) · g b = (∑' a, 1_S(a) · g (f a)) / N`. -/
theorem tsum_ncard_fiber_div_mul (hS : S.Finite) (f : α → β) (g : β → ℂ) (N : ℂ) :
    ∑' b : β, ({a | a ∈ S ∧ f a = b}.ncard : ℂ) / N * g b =
      (∑' a : α, S.indicator (fun a => g (f a)) a) / N := by
  rw [← tsum_ncard_fiber_mul hS f g, ← tsum_div_const]
  exact tsum_congr fun b => div_mul_eq_mul_div _ _ _

end BSDTamagawa.DegeneratePoint

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex BSDTamagawa.DegeneratePoint

/-- Whenever `N(X) ≠ 0`, the generating function `𝒵` at the degenerate point `Λ = Π = ∅`, `s = 0`,
`w = 1` is the polynomial whose coefficients are the truncated proportions `π_r(X)`:
`𝒵_{∅, ∅, X}(0; u, 1, ∅, ∅) = ∑_{r ≥ 0} π_r(X) u^r`. -/
@[bsd_tamagawa "T041i"]
theorem tamagawaGeneratingFunction_eq_tsum_tamagawaOmegaProportion_of_count_ne_zero
    (u : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ) {X : ℝ}
    (hN : integralShortNFCount X ≠ 0) :
    tamagawaGeneratingFunction ∅ ∅ 0 u 1 z uΛ X =
      ∑' r : ℕ, (tamagawaOmegaProportion r X : ℂ) * u ^ r := by
  have hS : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite := Set.finite_of_ncard_ne_zero hN
  have key := tsum_ncard_fiber_div_mul hS (fun q : ℤ × ℤ => tamagawaOmega q.1 q.2)
    (fun r : ℕ => u ^ r) (integralShortNFCount X : ℂ)
  have hcoeff : ∀ r : ℕ, ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ |
      (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily} ∧
      tamagawaOmega q.1 q.2 = r}.ncard : ℂ) / (integralShortNFCount X : ℂ) =
      (tamagawaOmegaProportion r X : ℂ) := by
    intro r
    rw [tamagawaOmegaProportion, ← setOf_mem_and_tamagawaOmega_eq r X]
    push_cast
    rfl
  have hR : ∑' r : ℕ, (tamagawaOmegaProportion r X : ℂ) * u ^ r =
      (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.indicator
          (fun q => u ^ tamagawaOmega q.1 q.2) q) / (integralShortNFCount X : ℂ) :=
    Eq.trans (tsum_congr fun r => by rw [← hcoeff r]) key
  rw [tamagawaGeneratingFunction]
  refine Eq.trans ?_ hR.symm
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
  · rw [ite_eq_left (show _ ∧ _ from hq), Set.indicator_of_mem hq]
    simp only [one_pow, neg_zero, Complex.cpow_zero, mul_one, kodairaMonomial_empty,
      multiMonomial_of_isEmpty]
  · rw [ite_eq_right (show ¬(_ ∧ _) from hq), Set.indicator_of_notMem hq]

/-- For every real `X ≥ 4` and every `u : ℂ`, `𝒵_{∅, ∅, X}(0; u, 1, ∅, ∅) = ∑_{r ≥ 0} π_r(X) u^r`,
where `π_r(X)` is the truncated proportion of curves whose Tamagawa product has exactly `r`
distinct prime factors. -/
@[bsd_tamagawa "T041i"]
theorem tamagawaGeneratingFunction_eq_tsum_tamagawaOmegaProportion (u : ℂ)
    (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ) {X : ℝ} (hX : 4 ≤ X) :
    tamagawaGeneratingFunction ∅ ∅ 0 u 1 z uΛ X =
      ∑' r : ℕ, (tamagawaOmegaProportion r X : ℂ) * u ^ r :=
  tamagawaGeneratingFunction_eq_tsum_tamagawaOmegaProportion_of_count_ne_zero u z uΛ
    (integralShortNFCount_ne_zero_of_four_le hX)

end WeierstrassCurve
