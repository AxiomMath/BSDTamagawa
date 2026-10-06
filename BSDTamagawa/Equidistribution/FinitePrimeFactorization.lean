/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Equidistribution.Fubini

/-!
# Finite-prime factorization of densities

Let `S` be a finite set of primes and let `f_p : 𝒦 → ℂ` be bounded for each `p ∈ S`. Then the
natural density

  `lim_{X → ∞} (1 / N(X)) ∑_{Ht(E) ≤ X} ∏_{p ∈ S} f_p(τ_p(E))`

exists and equals `∏_{p ∈ S} (∑_{K ∈ 𝒦} δ_p(K) f_p(K))`. The normalized sum is the integral of
`G = configProd S f` against the empirical measure `μ_{S,X}`, which converges to the integral
against the limit measure `μ_S`, and the latter factors over the primes of `S`.

## Main results

* `WeierstrassCurve.integral_configEmpiricalMeasure`: the integral against `μ_{S,X}` is the
  normalized sum over the curves of height at most `X`.
* `WeierstrassCurve.strat_configEmbed`: the reduction datum at the diagonal image of an integer
  pair is that of the pair.
* `WeierstrassCurve.tendsto_average_prod_tauZ`: the factorization of the density.

## Implementation notes

When `N(X) = 0` both sides of `integral_configEmpiricalMeasure` are `0`, so no hypothesis on `X` is
needed.
-/

@[expose] public section

open MeasureTheory Filter Topology

open scoped ENNReal

namespace BSDTamagawa.FinitePrimeFactorization

/-- The integral of `h` against a countable sum of unit point masses `∑_i δ_{g(i)}` is
`∑_i h(g(i))`. -/
theorem integral_measure_sum_dirac {ι : Type*} [Countable ι] {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (g : ι → α) (h : α → ℂ) :
    ∫ y, h y ∂Measure.sum (fun i => Measure.dirac (g i)) = ∑' i, h (g i) := by
  rw [show (Measure.sum fun i => Measure.dirac (g i))
      = Measure.sum fun i => (1 : ℝ≥0∞) • Measure.dirac (g i) by simp,
    integral_sum_dirac fun _ => ENNReal.one_ne_top]
  simp

end BSDTamagawa.FinitePrimeFactorization

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-! ### Integration against the empirical measure -/

/-- For every `h : K_S → ℂ`,
`∫ h dμ_{S,X} = (1 / N(X)) ∑_{Ht(a₄, a₆) ≤ X, Δ ≠ 0} h(((a₄, a₆))_{p ∈ S})`. -/
theorem integral_configEmpiricalMeasure (S : Finset ℕ) (X : ℝ) (h : configSpace S → ℂ) :
    ∫ y, h y ∂configEmpiricalMeasure S X
      = (integralShortNFCount X : ℂ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily}, h (configEmbed S E.1.1 E.1.2) := by
  have hsum : ∫ y, h y ∂(Measure.sum fun E : {E : ℤ × ℤ //
        (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧ E ∈ integralShortNFFamily} =>
        Measure.dirac (configEmbed S E.1.1 E.1.2))
      = ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
        E ∈ integralShortNFFamily}, h (configEmbed S E.1.1 E.1.2) :=
    BSDTamagawa.FinitePrimeFactorization.integral_measure_sum_dirac _ h
  rw [configEmpiricalMeasure, integral_smul_measure, hsum]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

/-! ### The integrand at a diagonal image -/

/-- For an integer pair `(a₄, a₆)` with `Δ ≠ 0`, the reduction datum `strat p` at the image of
`(a₄, a₆)` in `ℤ_p × ℤ_p` is the datum of the integral reduction map `τ_p = tauZ`. -/
theorem strat_configEmbed {S : Finset ℕ} {a₄ a₆ : ℤ} (hE : (a₄, a₆) ∈ integralShortNFFamily)
    (q : ↥(S.filter Nat.Prime)) (hq : configEmbed S a₄ a₆ q ∈ nonsingularLocus (q : ℕ)) :
    strat (q : ℕ) ⟨configEmbed S a₄ a₆ q, hq⟩
      = ((tauZ (q : ℕ) a₄ a₆).kodairaSymbol, (tauZ (q : ℕ) a₄ a₆).tamagawaNumber) := by
  have hΔ : (ofShortNF a₄ a₆).Δ ≠ 0 := hE
  rw [tauZ, dite_eq_left hΔ]
  rfl

/-- For an integer pair `(a₄, a₆)` with `Δ ≠ 0`,
`G(((a₄, a₆))_{p ∈ S}) = ∏_{p ∈ S} f_p(τ_p(a₄, a₆))`. -/
theorem configProd_configEmbed {S : Finset ℕ}
    (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ) {a₄ a₆ : ℤ}
    (hE : (a₄, a₆) ∈ integralShortNFFamily) :
    configProd S f (configEmbed S a₄ a₆)
      = ∏ q : ↥(S.filter Nat.Prime),
          f q ((tauZ (q : ℕ) a₄ a₆).kodairaSymbol, (tauZ (q : ℕ) a₄ a₆).tamagawaNumber) := by
  rw [configProd_apply_of_mem f (configEmbed_mem_configLocus hE)]
  exact Finset.prod_congr rfl fun q _ => by rw [strat_configEmbed hE q _]

/-! ### The factorization of densities -/

/-- Let `S` be a finite set of primes and let `f_p : 𝒦 → ℂ` be bounded for each `p ∈ S`. Then the
natural density `lim_{X → ∞} (1 / N(X)) ∑_{Ht(E) ≤ X} ∏_{p ∈ S} f_p(τ_p(E))` exists and equals
`∏_{p ∈ S} (∑_{K ∈ 𝒦} δ_p(K) f_p(K))`. -/
@[bsd_tamagawa "T033"]
theorem tendsto_average_prod_tauZ (S : Finset ℕ)
    (f : ↥(S.filter Nat.Prime) → ReductionData → ℂ) {B : ↥(S.filter Nat.Prime) → ℝ}
    (hf : ∀ q k, ‖f q k‖ ≤ B q) :
    Tendsto (fun X : ℝ => (integralShortNFCount X : ℂ)⁻¹ *
        ∑' E : {E : ℤ × ℤ // (integralShortNFHeight E.1 E.2 : ℝ) ≤ X ∧
            E ∈ integralShortNFFamily},
          ∏ q : ↥(S.filter Nat.Prime),
            f q ((tauZ (q : ℕ) E.1.1 E.1.2).kodairaSymbol,
              (tauZ (q : ℕ) E.1.1 E.1.2).tamagawaNumber))
      atTop
      (𝓝 (∏ q : ↥(S.filter Nat.Prime),
        ∑' K : ReductionData, ((deltaP (q : ℕ) K).toReal : ℂ) * f q K)) := by
  have hG : ∀ y ∈ configLocus S, configProd S f y = configProd S f y := fun _ _ => rfl
  have key := tendsto_integral_configProd S f hf hG
  rw [integral_configProd_eq_prod_tsum S f hf hG] at key
  refine key.congr fun X => ?_
  rw [integral_configEmpiricalMeasure S X (configProd S f)]
  exact congrArg _ (tsum_congr fun E => configProd_configEmbed f
    (show (E.1.1, E.1.2) ∈ integralShortNFFamily from E.2.2))

end WeierstrassCurve
