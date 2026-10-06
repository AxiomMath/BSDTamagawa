/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.FactorCount.GeneratingFunctionIdentity

/-!
# Existence and the generating function of `ρ_b`

For each `b ≥ 0` the density

`ρ_b := lim_{X → ∞} #{E : Ht(E) ≤ X, Ω(Tam(E)) = b} / N(X)`

exists, and

`∑_{b ≥ 0} ρ_b w^b = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) w^{Ω(t)})` for `‖w‖ ≤ 1`,

the Euler product converging absolutely on the closed unit disc. Here `E` ranges over the integral
short Weierstrass models with `Δ(E) ≠ 0`, `Ht` is the naive height, `N` the counting function,
`Tam` the Tamagawa product, `Ω = ArithmeticFunction.cardFactors` the number of prime factors *with*
multiplicity, and `δ_p(t)` the scalar local density.

## Main results

* `WeierstrassCurve.tendsto_cardFactorsTamagawaCount_div_integralShortNFCount`: the proportion of
  models with `Ht(E) ≤ X`, `Δ(E) ≠ 0` and `Ω(Tam(E)) = b` among all `N(X)` models of height at most
  `X` tends to `ρ_b`.
* `WeierstrassCurve.tsum_cardFactorsTamagawaDensity_mul_pow_eq_tprod_primes`: for `‖w‖ ≤ 1`,
  `∑_{b ≥ 0} ρ_b w^b = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) w^{Ω(t)})`.
* `WeierstrassCurve.multipliable_cardFactorsEulerFactor_primes`: for `‖w‖ ≤ 1` the family of local
  factors indexed by the primes is `Multipliable`.
* `WeierstrassCurve.summable_norm_cardFactorsEulerFactor_sub_one_primes`: for `‖w‖ ≤ 1`,
  `∑_{p ∈ 𝒫} ‖h_p - 1‖ < ∞`, where `h_p` is the local factor at `p`.
* `WeierstrassCurve.scalarLocalFactor_empty_zero_of_prime`: at a prime `p`,
  `h_p(0, w, ()) = ∑_{t ≥ 1} δ_p(t) w^{Ω(t)}`.
* `WeierstrassCurve.tprod_cardFactorsEulerFactor_primes`: the product over the primes of the local
  factors equals the `ℕ`-indexed product `∏'_p h_p(0, w, ())`.
* `WeierstrassCurve.hasSum_cardFactorsTamagawaDensity_mul_pow_tprod_primes`: for `‖w‖ ≤ 1` the
  family `(ρ_b w^b)_{b ≥ 0}` is summable with sum the Euler product.

## Implementation notes

The inner sum `∑_{t ≥ 1}` is written over all of `ℕ`; this is the same sum because `δ_p(0) = 0`.
The `ℝ≥0∞`-valued `δ_p(t)` enters `ℂ` as `((δ_p(t)).toReal : ℂ)`, so the subtractions `h_p - 1`
take place in `ℂ`. The Euler product is a `tprod` indexed by the subtype `{q : ℕ // q.Prime}`; the
`ℕ`-indexed product of the local factors agrees with it since `h_p = 1` at every non-prime `p`. The
local factor is taken at `Π = ∅` and `s = 0`, so the vector `𝐳` lives on an empty index type and
the constraint `∀ ℓ, ‖z ℓ‖ ≤ 1` is vacuous.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

/-! ### The local factor at `Π = ∅`, `s = 0` -/

/-- At a prime `p`, the scalar local factor at `Π = ∅` and `s = 0` is
`h_p(0, w, ()) = ∑_{t ≥ 1} δ_p(t) w^{Ω(t)}`, the sum being written over all of `ℕ`. -/
theorem scalarLocalFactor_empty_zero_of_prime (p : ℕ) [Fact p.Prime] (w : ℂ)
    (z : (∅ : Finset ℕ) → ℂ) :
    scalarLocalFactor ∅ p 0 w z
      = ∑' t : ℕ, ((δ p t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t := by
  rw [scalarLocalFactor_eq_tsum_of_prime]
  exact tsum_congr fun t => by rw [scalarWeight_empty_zero]

/-- For `‖w‖ ≤ 1`, `∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) w^{Ω(t)}) = ∏'_{p : ℕ} h_p(0, w, ())`. -/
theorem tprod_cardFactorsEulerFactor_primes {w : ℂ} (hw : ‖w‖ ≤ 1)
    (z : (∅ : Finset ℕ) → ℂ) :
    ∏' p : {q : ℕ // q.Prime},
        (∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t)
      = ∏' p : ℕ, scalarLocalFactor ∅ p 0 w z := by
  have hz1 : ∀ ℓ : (∅ : Finset ℕ), ‖z ℓ‖ ≤ 1 := fun ℓ => (Finset.notMem_empty _ ℓ.2).elim
  rw [← tprod_scalarLocalFactor_primes ∅ (by simp) hw hz1]
  refine tprod_congr fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact (scalarLocalFactor_empty_zero_of_prime (p : ℕ) w z).symm

/-! ### The density exists -/

/-- For every `b : ℕ`, `lim_{X → ∞} #{E : Ht(E) ≤ X, Δ(E) ≠ 0, Ω(Tam(E)) = b} / N(X) = ρ_b`, where
the numerator counts the pairs `(a₄, a₆) ∈ ℤ²` whose short Weierstrass model is nonsingular, of
naive height at most `X`, and whose Tamagawa product has exactly `b` prime factors counted with
multiplicity. -/
@[bsd_tamagawa "T046a"]
theorem tendsto_cardFactorsTamagawaCount_div_integralShortNFCount (b : ℕ) :
    Tendsto (fun X : ℝ =>
        ({p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
          ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b}.ncard : ℝ) /
          integralShortNFCount X)
      atTop (𝓝 (cardFactorsTamagawaDensity b)) :=
  tendsto_cardFactorsTamagawaProportion_cardFactorsTamagawaDensity b

/-! ### The generating function -/

/-- For `‖w‖ ≤ 1`, the family `(ρ_b w^b)_{b ≥ 0}` is summable with sum
`∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) w^{Ω(t)})`. -/
theorem hasSum_cardFactorsTamagawaDensity_mul_pow_tprod_primes {w : ℂ} (hw : ‖w‖ ≤ 1) :
    HasSum (fun b : ℕ => ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b)
      (∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t) := by
  rw [tprod_cardFactorsEulerFactor_primes hw (fun _ => 0),
    ← tsum_cardFactorsTamagawaDensity_mul_pow hw]
  exact (Summable.of_norm (summable_norm_cardFactorsTamagawaDensity_mul_pow hw)).hasSum

/-- For every `w : ℂ` with `‖w‖ ≤ 1`,
`∑_{b ≥ 0} ρ_b w^b = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) w^{Ω(t)})`. -/
@[bsd_tamagawa "T046a"]
theorem tsum_cardFactorsTamagawaDensity_mul_pow_eq_tprod_primes {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∑' b : ℕ, ((cardFactorsTamagawaDensity b : ℝ) : ℂ) * w ^ b
      = ∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t :=
  (hasSum_cardFactorsTamagawaDensity_mul_pow_tprod_primes hw).tsum_eq

/-! ### Absolute convergence of the Euler product on the closed disc -/

/-- For every `w` with `‖w‖ ≤ 1`, the family of local factors `(∑_{t ≥ 1} δ_p(t) w^{Ω(t)})_{p ∈ 𝒫}`
is `Multipliable`. -/
@[bsd_tamagawa "T046a"]
theorem multipliable_cardFactorsEulerFactor_primes {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t :=
  (multipliable_scalarLocalFactor_primes ∅ (s := 0) (z := fun _ => 0) (by simp) hw
    (fun ℓ => (Finset.notMem_empty _ ℓ.2).elim)).congr fun p => by
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact scalarLocalFactor_empty_zero_of_prime (p : ℕ) w _

/-- For every `w` with `‖w‖ ≤ 1`, `∑_{p ∈ 𝒫} ‖(∑_{t ≥ 1} δ_p(t) w^{Ω(t)}) - 1‖ < ∞`. -/
@[bsd_tamagawa "T046a"]
theorem summable_norm_cardFactorsEulerFactor_sub_one_primes {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable fun p : {q : ℕ // q.Prime} =>
      ‖(∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * w ^ ArithmeticFunction.cardFactors t)
        - 1‖ :=
  (((summable_scalarLocalFactor_sub_one ∅ (s := 0) (z := fun _ => 0) (by simp) hw
    (fun ℓ => (Finset.notMem_empty _ ℓ.2).elim)).subtype Nat.Prime).congr fun p => by
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact congrArg (· - 1) (scalarLocalFactor_empty_zero_of_prime (p : ℕ) w _)).norm

end WeierstrassCurve
