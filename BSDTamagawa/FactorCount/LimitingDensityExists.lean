/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarSpecialization
public import BSDTamagawa.PrimeCount.LimitingDensityExists

/-!
# Existence of the limiting density `ρ_b`

For every integer `b ≥ 0`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Ω(Tam(E)) = b} / N(X) = ρ_b`,

with `Ω` the number of prime factors counted with multiplicity and
`ρ_b = cardFactorsTamagawaDensity b`. Since `ρ_b` is a `Filter.limUnder`, the single statement
`Tendsto … atTop (𝓝 ρ_b)` asserts both that the limit exists and that it equals `ρ_b`.

## Main results

* `WeierstrassCurve.tendsto_cardFactorsTamagawaProportion_cardFactorsTamagawaDensity`: the
  proportion of models with `Ω(Tam(E)) = b` tends to `ρ_b`.
* `WeierstrassCurve.scalarWeight_empty_zero`: `ψ_{0, w, ()}(t) = w^{Ω(t)}`.
* `WeierstrassCurve.tendsto_tsum_indicator_cardFactorsMonomial_div`: for `‖w‖ < 1`, the empirical
  average of `w^{Ω(Tam(E))}` over models of height at most `X` tends to `∏'_p h_p(0, w, ())`.
* `WeierstrassCurve.setOf_mem_and_cardFactorsIndex_eq`: the fibre of `Ω(Tam(·))` over the
  `Unit`-multi-index attached to `b` is the set counted by the numerator of `ρ_b(X)`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex
open BSDTamagawa.FiberCount BSDTamagawa.DegeneratePoint BSDTamagawa.PrimeCountDensity

/-! ### The `w`-specialization -/

/-- At `Π = ∅` and `s = 0` the scalar weight is a power of `w`: for every `t : ℕ`,
`ψ_{0, w, ()}(t) = w^{Ω(t)}`. -/
theorem scalarWeight_empty_zero (w : ℂ) (z : (∅ : Finset ℕ) → ℂ) (t : ℕ) :
    scalarWeight ∅ 0 w z t = w ^ ArithmeticFunction.cardFactors t := by
  rw [scalarWeight, multiMonomial_of_isEmpty, mul_one, neg_zero, Complex.cpow_zero, mul_one]

/-- For `w = z ()` in the open unit disc,

`G_X(w) = (1/N(X)) ∑_{Ht(E) ≤ X} w^{Ω(Tam(E))} ⟶ ∏'_{p} h_p(0, w, ())` as `X → ∞`,

with `h_p` the scalar local factor taken at `Π = ∅`; the cut-off to height at most `X` is written
with `Set.indicator` and `w^{Ω(Tam(E))}` as a `Unit`-monomial. -/
theorem tendsto_tsum_indicator_cardFactorsMonomial_div (z : Unit → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.indicator
          (fun q => multiMonomial (⇑(Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
            ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)))) z) q) /
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.ncard : ℂ))
      atTop (𝓝 (∏' p : ℕ, scalarLocalFactor ∅ p 0 (z ()) (fun _ => 0))) := by
  refine (tendsto_scalarWeightSum_tprod_scalarLocalFactor ∅ (by simp)
    (mem_scalarParamRegion.2 ⟨by simp, (hz ()).le, fun _ => by simp⟩)
    (fun _ => 0)).congr fun X => ?_
  rw [ncard_setOf_height_le_and_mem_family]
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
  · rw [ite_eq_left (show _ ∧ _ from hq), Set.indicator_of_mem hq, scalarWeight_empty_zero]
    simp [multiMonomial]
  · rw [ite_eq_right (show ¬(_ ∧ _) from hq), Set.indicator_of_notMem hq]

/-! ### The fibre of `Ω(Tam(·))` -/

/-- Under `ℕ ≃ (Unit →₀ ℕ)`, the fibre of `q ↦ Ω(Tam(q))` over the multi-index attached to `b` is
the set counted by the numerator of `ρ_b(X)`. -/
theorem setOf_mem_and_cardFactorsIndex_eq (b : ℕ) (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧
        Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
            ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)) =
          Finsupp.equivFunOnFinite.symm (fun _ : Unit => b)} =
      {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
        ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b} :=
  Set.ext fun q => by simp only [Set.mem_ofPred_eq, and_assoc, EmbeddingLike.apply_eq_iff_eq,
    funext_iff, forall_const]

/-! ### Existence of the limiting density -/

/-- For every `b : ℕ`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Δ(E) ≠ 0, Ω(Tam(E)) = b} / N(X) = ρ_b`,

with `Ω = ArithmeticFunction.cardFactors` and `ρ_b = cardFactorsTamagawaDensity b`: the limit
exists and equals `ρ_b`. -/
@[bsd_tamagawa "T046e"]
theorem tendsto_cardFactorsTamagawaProportion_cardFactorsTamagawaDensity (b : ℕ) :
    Tendsto (fun X : ℝ =>
        ({p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
          ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b}.ncard : ℝ) /
          integralShortNFCount X)
      atTop (𝓝 (cardFactorsTamagawaDensity b)) := by
  have hEq : ∀ X : ℝ,
      ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily} ∧
            Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
                ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)) =
              Finsupp.equivFunOnFinite.symm (fun _ : Unit => b)}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ) =
      ({p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ p ∈ integralShortNFFamily ∧
        ArithmeticFunction.cardFactors (tamagawaProduct p.1 p.2) = b}.ncard : ℝ) /
        integralShortNFCount X := fun X => by
    rw [setOf_mem_and_cardFactorsIndex_eq b X, ncard_setOf_height_le_and_mem_family]
  have h := tendsto_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (fun q : ℤ × ℤ => Finsupp.equivFunOnFinite.symm (fun _ : Unit =>
      ArithmeticFunction.cardFactors (tamagawaProduct q.1 q.2)))
    (fun z : Unit → ℂ => ∏' p : ℕ, scalarLocalFactor ∅ p 0 (z ()) (fun _ => 0)) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_cardFactorsMonomial_div z hz)
    (Finsupp.equivFunOnFinite.symm (fun _ : Unit => b))
  rw [cardFactorsTamagawaDensity]
  simpa only [hEq] using h

end WeierstrassCurve
