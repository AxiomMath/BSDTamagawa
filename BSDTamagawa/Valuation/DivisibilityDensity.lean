/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.NoDivisorDensity

/-!
# The single-prime divisibility density of the Tamagawa product

For a fixed prime `ℓ`, let `P = P_{\{ℓ\}}` be the limiting law of the `ℓ`-adic valuation of the
Tamagawa product `Tam(E)` of short Weierstrass curves ordered by height, a probability measure on
`ℤ_{≥0}^{\{ℓ\}}`. Then

`P(ℓ ∣ Tam(E)) = 1 - ∏_{p ∈ 𝒫} (∑_{ℓ ∤ t} δ_p(t))`,
where `δ_p(t)` is the local density of Tamagawa number `t` at `p`, and the Euler product converges.
The event `ℓ ∣ Tam(E)` is the complement of the event `ℓ ∤ Tam(E)`, whose mass is the Euler
product. The identity is stated in `ℝ`, where the subtraction is not truncated at `0`.

## Main results

* `WeierstrassCurve.setOf_coprime_singleton_eq_notDvd`: for a prime `ℓ`,
  `(t, ∏_{m ∈ \{ℓ\}} m) = 1` iff `ℓ ∤ t`.
* `WeierstrassCurve.setOf_singleton_ne_zero_eq_compl`: the event `{𝐣 : j_ℓ ≠ 0}` is the complement
  of the singleton `{𝟎}` in `ℤ_{≥0}^{\{ℓ\}}`.
* `WeierstrassCurve.multipliable_notDvdDensity_primes`: the family `(∑_{ℓ ∤ t} δ_p(t))_{p ∈ 𝒫}` is
  multipliable.
* `WeierstrassCurve.tamagawaValuationMeasure_dvd_toReal`: the divisibility density formula.
-/

@[expose] public section

namespace WeierstrassCurve

open MeasureTheory

/-! ### The singleton `Π = {ℓ}` -/

/-- For a prime `ℓ`, `(t, ∏_{m ∈ \{ℓ\}} m) = 1` iff `ℓ ∤ t`. -/
theorem setOf_coprime_singleton_eq_notDvd {l : ℕ} (hl : l.Prime) :
    {t : ℕ | Nat.Coprime t (∏ x ∈ ({l} : Finset ℕ), x)} = {t : ℕ | ¬ l ∣ t} := by
  ext t
  simp only [Finset.prod_singleton, Set.mem_ofPred_eq]
  rw [Nat.coprime_comm]
  exact hl.coprime_iff_not_dvd

/-- The event `{𝐣 : j_ℓ ≠ 0}` is the complement of the singleton `{𝟎}` in `ℤ_{≥0}^{\{ℓ\}}`: the
index type `↥{ℓ}` has exactly one element, so a multi-index vanishes iff its coordinate at `ℓ`
does. -/
theorem setOf_singleton_ne_zero_eq_compl (l : ℕ) :
    {j : ↥({l} : Finset ℕ) → ℕ | j ⟨l, Finset.mem_singleton_self l⟩ ≠ 0}
      = ({0} : Set (↥({l} : Finset ℕ) → ℕ))ᶜ := by
  ext j
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq, not_iff_not, Set.mem_ofPred_eq]
  refine ⟨fun h => funext fun m => ?_, fun h => by rw [h]; rfl⟩
  have hm : m = ⟨l, Finset.mem_singleton_self l⟩ := Subtype.ext (Finset.mem_singleton.1 m.2)
  rw [hm]
  exact h

/-! ### The divisibility density -/

/-- For a prime `ℓ` the family `(∑_{ℓ ∤ t} δ_p(t))_{p ∈ 𝒫}` is `Multipliable`: the net of partial
products over the finite sets of primes converges. -/
@[bsd_tamagawa "T044c"]
theorem multipliable_notDvdDensity_primes {l : ℕ} (hl : l.Prime) :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal := by
  rw [← setOf_coprime_singleton_eq_notDvd hl]
  exact multipliable_coprimeDensity_primes {l} fun m hm => by
    rw [Finset.mem_singleton.1 hm]; exact hl

/-- For a fixed prime `ℓ`, with `P` the limiting joint valuation law on `ℤ_{≥0}^{\{ℓ\}}`,

`P(ℓ ∣ Tam(E)) = 1 - ∏_{p ∈ 𝒫} (∑_{ℓ ∤ t} δ_p(t))`,

with `δ_p(t)` the local Tamagawa density at `p`. The event on the left is the set of multi-indices
whose coordinate at `ℓ` is nonzero, which is the event `ℓ ∣ Tam(E)`. The identity is one of real
numbers. -/
@[bsd_tamagawa "T044c"]
theorem tamagawaValuationMeasure_dvd_toReal {l : ℕ} (hl : l.Prime) :
    (tamagawaValuationMeasure {l}
        {j : ↥({l} : Finset ℕ) → ℕ | j ⟨l, Finset.mem_singleton_self l⟩ ≠ 0}).toReal
      = 1 - ∏' p : {q : ℕ // q.Prime},
        ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal := by
  have hA : ∀ m ∈ ({l} : Finset ℕ), Nat.Prime m := fun m hm => by
    rw [Finset.mem_singleton.1 hm]; exact hl
  have hprob := isProbabilityMeasure_tamagawaValuationMeasure {l} hA
  have hmass : (tamagawaValuationMeasure {l} ({0} : Set (↥({l} : Finset ℕ) → ℕ))).toReal
      = ∏' p : {q : ℕ // q.Prime}, ∑' t : ↥{t : ℕ | ¬ l ∣ t}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal := by
    rw [← setOf_forall_eq_zero_eq_singleton, tamagawaValuationMeasure_notDvd_toReal _ hA,
      setOf_coprime_singleton_eq_notDvd hl]
  have hsum : (tamagawaValuationMeasure {l} ({0} : Set (↥({l} : Finset ℕ) → ℕ))).toReal
      + (tamagawaValuationMeasure {l} ({0} : Set (↥({l} : Finset ℕ) → ℕ))ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      prob_add_prob_compl (measurableSet_singleton _), ENNReal.toReal_one]
  rw [setOf_singleton_ne_zero_eq_compl, ← hmass]
  linarith

end WeierstrassCurve
