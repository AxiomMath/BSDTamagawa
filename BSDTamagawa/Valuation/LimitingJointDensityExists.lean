/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarSpecialization
public import BSDTamagawa.PrimeCount.LimitingDensityExists

/-!
# Existence of the limiting joint valuation density `Q_Π(𝐣)`

Let `Π` be a finite set of primes. For every multi-index `𝐣 ∈ ℤ_{≥0}^Π`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, v_ℓ(Tam(E)) = j_ℓ ∀ ℓ ∈ Π} / N(X) = Q_Π(𝐣)`,

that is, the limit defining the joint valuation density `Q_Π(𝐣)` exists. It follows from the
convergence, for `𝐳` in the open unit polydisc, of the empirical averages

`H_X(𝐳) = (1/N(X)) ∑_{Ht(E) ≤ X} 𝐳^{𝐯_Π(Tam(E))} ⟶ ∏_p h_p(0, 1, 𝐳)`,

by coefficient extraction from generating functions of probability vectors.

## Main results

* `WeierstrassCurve.scalarWeight_zero_one`: the scalar weight at `(s, w) = (0, 1)` is
  `ψ_{0, 1, 𝐳}(t) = 𝐳^{𝐯(t)}`.
* `WeierstrassCurve.tendsto_tsum_indicator_tamagawaValuationMonomial_div`: `H_X(𝐳)` tends to
  `∏_p h_p(0, 1, 𝐳)` on the open unit polydisc.
* `WeierstrassCurve.setOf_mem_and_tamagawaValuationIndex_eq`: the fibre of the valuation vector
  over a multi-index is the set counted by the numerator of `Q_Π(𝐣; X)`.
* `WeierstrassCurve.tendsto_tamagawaValuationProportion_tamagawaValuationDensity`: the limit
  defining `Q_Π(𝐣)` exists.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex
open BSDTamagawa.FiberCount BSDTamagawa.PrimeCountDensity

/-! ### The `𝐳`-specialization of the scalar Euler product -/

/-- For every `t : ℕ`,

`ψ_{0, 1, 𝐳}(t) = 𝐳^{(v_ℓ(t))_{ℓ ∈ Π}}`,

with `ψ` the scalar weight. -/
theorem scalarWeight_zero_one (P : Finset ℕ) (z : P → ℂ) (t : ℕ) :
    scalarWeight P 0 1 z t = multiMonomial (fun ℓ : P => padicValNat ℓ t) z := by
  rw [scalarWeight, one_pow, one_mul, neg_zero, Complex.cpow_zero, mul_one]

/-- For a finite set of primes `Π` and `𝐳` in the *open* unit polydisc,

`H_X(𝐳) = (1/N(X)) ∑_{Ht(E) ≤ X} 𝐳^{𝐯_Π(Tam(E))} ⟶ ∏'_{p} h_p(0, 1, 𝐳)` as `X → ∞`,

with `h_p` the scalar local factor. -/
theorem tendsto_tsum_indicator_tamagawaValuationMonomial_div (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (z : P → ℂ) (hz : ∀ ℓ : P, ‖z ℓ‖ < 1) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ, {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.indicator
          (fun q => multiMonomial (⇑(Finsupp.equivFunOnFinite.symm
            (tamagawaValuationVector P q.1 q.2))) z) q) /
          ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily}.ncard : ℂ))
      atTop (𝓝 (∏' p : ℕ, scalarLocalFactor P p 0 1 z)) := by
  refine (tendsto_scalarWeightSum_tprod_scalarLocalFactor P hP
    (mem_scalarParamRegion.2 ⟨by simp, by simp, fun ℓ => (hz ℓ).le⟩)
    (fun _ => 0)).congr fun X => ?_
  rw [ncard_setOf_height_le_and_mem_family]
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}
  · rw [ite_eq_left (show _ ∧ _ from hq), Set.indicator_of_mem hq, scalarWeight_zero_one]
    rfl
  · rw [ite_eq_right (show ¬(_ ∧ _) from hq), Set.indicator_of_notMem hq]

/-! ### The fibre of the valuation vector -/

/-- The fibre of `q ↦ 𝐯_Π(Tam(q))`, read as a `↥Π →₀ ℕ`, over the multi-index attached to `𝐣` is
the set of `q` of height at most `X` with `Δ ≠ 0` and `v_ℓ(Tam(q)) = j_ℓ` for all `ℓ ∈ Π`. -/
theorem setOf_mem_and_tamagawaValuationIndex_eq (P : Finset ℕ) (j : P → ℕ) (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧
        Finsupp.equivFunOnFinite.symm (tamagawaValuationVector P q.1 q.2) =
          Finsupp.equivFunOnFinite.symm j} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
        ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ} :=
  Set.ext fun q => by simp only [Set.mem_ofPred_eq, and_assoc, EmbeddingLike.apply_eq_iff_eq,
    funext_iff]

/-! ### Existence of the limit -/

/-- Let `Π` be a finite set of primes. For every multi-index `𝐣 ∈ ℤ_{≥0}^Π`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Δ(E) ≠ 0, v_ℓ(Tam(E)) = j_ℓ ∀ ℓ ∈ Π} / N(X) = Q_Π(𝐣)`,

where `Q_Π(𝐣)` is the joint valuation density `tamagawaValuationDensity Π 𝐣`. -/
@[bsd_tamagawa "T044f"]
theorem tendsto_tamagawaValuationProportion_tamagawaValuationDensity (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (j : P → ℕ) :
    Tendsto (fun X : ℝ =>
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ}.ncard : ℝ) /
          integralShortNFCount X)
      atTop (𝓝 (tamagawaValuationDensity P j)) := by
  have hEq : ∀ X : ℝ,
      ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
            q ∈ integralShortNFFamily} ∧
            Finsupp.equivFunOnFinite.symm (tamagawaValuationVector P q.1 q.2) =
              Finsupp.equivFunOnFinite.symm j}.ncard : ℝ) /
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
          q ∈ integralShortNFFamily}.ncard : ℝ) =
      ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
        ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ}.ncard : ℝ) /
        integralShortNFCount X := fun X => by
    rw [setOf_mem_and_tamagawaValuationIndex_eq P j X, ncard_setOf_height_le_and_mem_family]
  have h := tendsto_ncard_fiber_div_limUnder
    (fun X : ℝ => {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily})
    (fun q : ℤ × ℤ => Finsupp.equivFunOnFinite.symm (tamagawaValuationVector P q.1 q.2))
    (fun z : P → ℂ => ∏' p : ℕ, scalarLocalFactor P p 0 1 z) 4
    (fun X hX => finite_setOf_height_le_and_mem_family (by linarith))
    (fun _ hX => integralShortNFCount_ne_zero_of_four_le hX)
    (fun z hz => tendsto_tsum_indicator_tamagawaValuationMonomial_div P hP z hz)
    (Finsupp.equivFunOnFinite.symm j)
  rw [tamagawaValuationDensity]
  simpa only [hEq] using h

end WeierstrassCurve
