/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Family.TamagawaProduct

/-!
# The reduction-datum prime count `ω_K`

`ω_K(E) := #{p prime : τ_p(E) = K}` counts the primes at which the integral short Weierstrass model
`E = E(a₄, a₆)` has local reduction datum exactly `K`; it is the `K`-refined analogue of the
Tamagawa prime count `ω_Tam`. Here `K : KodairaSymbol × ℕ` is a pair (Kodaira symbol, local
Tamagawa number), the datum `WeierstrassCurve.localReductionDatum` at a non-prime index is
`(I₀, 1)`, and `ω_K` is `WeierstrassCurve.reductionOmega`, a `Set.ncard`; both are defined in
`BSDTamagawa.Defs`.

## Main results

* `WeierstrassCurve.localReductionDatum_mem_K0_of_not_sq_dvd`: if `p² ∤ Δ` the datum lies in `𝒦₀`.
* `WeierstrassCurve.finite_setOf_localReductionDatum_eq`: for `K ∉ 𝒦₀` only finitely many primes
  have datum `K`.

## Implementation notes

The hypothesis `K ∉ 𝒦₀` cannot be dropped: for `K = (I₀, 1)` the set of indices is co-finite, and
`ω_K(E) = 0` is the `Set.ncard` value on an infinite set.
-/

@[expose] public section

namespace WeierstrassCurve

/-- At a prime index, the reduction datum is the `(kodairaSymbol, tamagawaNumber)` pair of
`τ_p`. -/
lemma localReductionDatum_of_prime (p : ℕ) [Fact p.Prime] (a₄ a₆ : ℤ) :
    localReductionDatum p a₄ a₆ =
      ((tauZ p a₄ a₆).kodairaSymbol, (tauZ p a₄ a₆).tamagawaNumber) :=
  dite_eq_left Fact.out

/-- At a non-prime index, the reduction datum is the neutral value `(I₀, 1)`. -/
lemma localReductionDatum_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (a₄ a₆ : ℤ) :
    localReductionDatum p a₄ a₆ = (KodairaSymbol.I 0, 1) :=
  dite_eq_right hp

/-- The second component of the reduction datum is the local Tamagawa number `c_p(E)`. -/
lemma localReductionDatum_snd (p : ℕ) (a₄ a₆ : ℤ) :
    (localReductionDatum p a₄ a₆).2 = localTamagawaNumber p a₄ a₆ := by
  rw [localReductionDatum, localTamagawaNumber]
  split <;> rfl

/-- On the singular locus `Δ = 0` (where `τ_p` is set to good reduction) the reduction datum is
`(I₀, 1)` at every index. -/
lemma localReductionDatum_of_Δ_eq_zero (p : ℕ) {a₄ a₆ : ℤ}
    (h : (ofShortNF a₄ a₆).Δ = 0) :
    localReductionDatum p a₄ a₆ = (KodairaSymbol.I 0, 1) := by
  rw [localReductionDatum]
  split
  · rw [tauZ, dite_eq_right (not_not_intro h)]
  · rfl

/-- If `p² ∤ Δ(E(a₄, a₆))` then the reduction datum at `p` lies in `𝒦₀`. -/
lemma localReductionDatum_mem_K0_of_not_sq_dvd (p : ℕ) (a₄ a₆ : ℤ)
    (hnd : ¬ (p ^ 2 : ℤ) ∣ (ofShortNF a₄ a₆).Δ) :
    localReductionDatum p a₄ a₆ ∈ K0 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [localReductionDatum_of_prime]
    exact tauZ_mem_K0_of_not_sq_dvd p a₄ a₆ hnd
  · rw [localReductionDatum_of_not_prime hp]
    exact Set.mem_insert _ _

/-- For `K ∉ 𝒦₀` the set `{p : τ_p(E) = K}` is finite. -/
@[bsd_tamagawa "T012"]
lemma finite_setOf_localReductionDatum_eq {K : KodairaSymbol × ℕ} (hK : K ∉ K0)
    (a₄ a₆ : ℤ) :
    {p : ℕ | localReductionDatum p a₄ a₆ = K}.Finite := by
  by_cases hΔ : (ofShortNF a₄ a₆).Δ = 0
  · refine Set.Finite.subset Set.finite_empty fun p hp => ?_
    simp only [Set.mem_ofPred_eq] at hp
    refine absurd (hp ▸ ?_) hK
    rw [localReductionDatum_of_Δ_eq_zero p hΔ]
    exact Set.mem_insert _ _
  · refine Set.Finite.subset (Set.finite_Iic (ofShortNF a₄ a₆).Δ.natAbs) fun p hp => ?_
    have hdvd : (p : ℤ) ^ 2 ∣ (ofShortNF a₄ a₆).Δ := by
      by_contra hnd
      exact hK (hp ▸ localReductionDatum_mem_K0_of_not_sq_dvd p a₄ a₆ hnd)
    have hnat : p ^ 2 ∣ (ofShortNF a₄ a₆).Δ.natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    have hle : p ^ 2 ≤ (ofShortNF a₄ a₆).Δ.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hΔ) hnat
    exact Set.mem_Iic.mpr ((Nat.le_self_pow two_ne_zero p).trans hle)

end WeierstrassCurve
