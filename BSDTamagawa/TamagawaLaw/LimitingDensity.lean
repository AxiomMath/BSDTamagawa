/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The limiting Tamagawa density `P_Tam(m)`

For an integer `m ≥ 1`, the limiting Tamagawa density is
`P_Tam(m) := lim_{X → ∞} #{E : Ht(E) ≤ X, Tam(E) = m} / N(X)`, where `E` ranges over the short
Weierstrass models `E(a₄, a₆)` with `Δ ≠ 0`, `Ht` is the naive height, `N(X)` the number of such
models of height at most `X`, and `Tam` the Tamagawa product. The quotient at a finite height bound
is `tamagawaProportion m X`, and the density is `tamagawaDensity m`; both are defined in
`BSDTamagawa.Defs`. This file proves the bounds `0 ≤ P_Tam(m; X) ≤ 1`, the bound `0 ≤ P_Tam(m)`,
and that `P_Tam(m)` is the limit of `P_Tam(m; X)` whenever that limit exists.

## Main results

* `WeierstrassCurve.tamagawaProportion_nonneg`, `WeierstrassCurve.tamagawaProportion_le_one`:
  `0 ≤ P_Tam(m; X) ≤ 1` for every `m` and `X`.
* `WeierstrassCurve.tamagawaDensity_nonneg`: `0 ≤ P_Tam(m)`.
* `WeierstrassCurve.tendsto_tamagawaProportion`: if `P_Tam(m; X)` converges as `X → ∞`, its limit
  is `P_Tam(m)`.

## Implementation notes

`P_Tam(m)` is defined as `Filter.limsup` of `P_Tam(m; X)` along `X → ∞`. This agrees with the limit
whenever the limit exists, and, unlike `Filter.limUnder`, has a meaningful value (the upper
density) without any convergence hypothesis, so that `0 ≤ P_Tam(m)` holds unconditionally. For
`X < 4` one has `N(X) = 0` and the quotient is Lean's `0/0 = 0`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Theorem 1.1.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter Topology

/-- The truncated proportion `P_Tam(m; X)` is nonnegative, for every `m` and every `X`. -/
lemma tamagawaProportion_nonneg (m : ℕ) (X : ℝ) : 0 ≤ tamagawaProportion m X :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The truncated proportion `P_Tam(m; X)` is at most `1`, for every `m` and every `X`. -/
lemma tamagawaProportion_le_one (m : ℕ) (X : ℝ) : tamagawaProportion m X ≤ 1 := by
  have hsub : { p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X
        ∧ p ∈ integralShortNFFamily ∧ tamagawaProduct p.1 p.2 = m } ⊆
      { p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X
        ∧ p ∈ integralShortNFFamily } :=
    fun _ hp => ⟨hp.1, hp.2.1⟩
  by_cases hfin : { p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧
      p ∈ integralShortNFFamily }.Finite
  · rcases eq_or_ne (integralShortNFCount X) 0 with h0 | h0
    · rw [tamagawaProportion, h0]
      simp
    · rw [tamagawaProportion, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h0)]
      exact_mod_cast Set.ncard_le_ncard hsub hfin
  · rw [tamagawaProportion, show integralShortNFCount X = 0 from Set.Infinite.ncard hfin]
    simp

/-- The truncated proportion `X ↦ P_Tam(m; X)` is bounded above along `atTop`, by `1`. -/
lemma isBoundedUnder_le_tamagawaProportion (m : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (tamagawaProportion m) :=
  isBoundedUnder_of ⟨1, tamagawaProportion_le_one m⟩

/-- `P_Tam(m) ≥ 0` for every `m`. -/
lemma tamagawaDensity_nonneg (m : ℕ) : 0 ≤ tamagawaDensity m :=
  le_limsup_of_frequently_le (.of_forall (tamagawaProportion_nonneg m))
    (isBoundedUnder_le_tamagawaProportion m)

/-- If the truncated proportion `X ↦ P_Tam(m; X)` converges to `L`, then `P_Tam(m) = L`. -/
lemma tamagawaDensity_eq_of_tendsto {m : ℕ} {L : ℝ}
    (h : Tendsto (tamagawaProportion m) atTop (𝓝 L)) : tamagawaDensity m = L :=
  h.limsup_eq

/-- If the truncated proportion `X ↦ P_Tam(m; X)` converges, then it converges to `P_Tam(m)`. -/
lemma tendsto_tamagawaProportion {m : ℕ}
    (h : ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) :
    Tendsto (tamagawaProportion m) atTop (𝓝 (tamagawaDensity m)) := by
  obtain ⟨L, hL⟩ := h
  rwa [tamagawaDensity_eq_of_tendsto hL]

end WeierstrassCurve
