/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.ReductionValuation
public import BSDTamagawa.NumberTheory.Reduction

/-!
# Local Tamagawa numbers `c_p` and the Tamagawa product `Tam`

For a prime `p`, the local Tamagawa number of `E` is the index `c_p(E) = [E(ℚ_p) : E_0(ℚ_p)]` of
the subgroup of points with nonsingular reduction. It is `WeierstrassCurve.localTamagawaNumber`,
the `tamagawaNumber` projection of the local reduction map `WeierstrassCurve.tauZ` (Tate's
algorithm), extended by `1` at non-prime indices. The Tamagawa product `Tam(E) = ∏_p c_p(E)` is
`WeierstrassCurve.tamagawaProduct`, a `finprod`. Both are defined in `BSDTamagawa.Defs`.

## Main results

* `WeierstrassCurve.localTamagawaNumber_pos`: `0 < c_p(E)` for every `p` and `(a₄, a₆)`.
* `WeierstrassCurve.localTamagawaNumber_eq_one_of_not_dvd`: `c_p(E) = 1` when `p² ∤ Δ`.
* `WeierstrassCurve.mulSupport_localTamagawaNumber_finite`: only finitely many `c_p(E)` differ from
  `1`.
* `WeierstrassCurve.tamagawaProduct_eq_prod_of_mulSupport_subset`: `Tam(E)` equals the finite
  product over any set containing every prime with `c_p(E) ≠ 1`.
* `WeierstrassCurve.tamagawaProduct_pos`: `Tam(E)` is a positive integer.
-/

@[expose] public section

namespace WeierstrassCurve

/-- At a prime index, `c_p` is the `tamagawaNumber` projection of the reduction datum `τ_p`. -/
lemma localTamagawaNumber_of_prime (p : ℕ) [Fact p.Prime] (a₄ a₆ : ℤ) :
    localTamagawaNumber p a₄ a₆ = (tauZ p a₄ a₆).tamagawaNumber :=
  dite_eq_left Fact.out

/-- At a non-prime index, `c_p` is the neutral value `1`. -/
lemma localTamagawaNumber_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (a₄ a₆ : ℤ) :
    localTamagawaNumber p a₄ a₆ = 1 :=
  dite_eq_right hp

/-- The local Tamagawa number `c_p(E)` is positive, for every index `p` and every pair
`(a₄, a₆)`. -/
@[bsd_tamagawa "T004"]
lemma localTamagawaNumber_pos (p : ℕ) (a₄ a₆ : ℤ) : 0 < localTamagawaNumber p a₄ a₆ := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [localTamagawaNumber_of_prime]
    exact tauZ_tamagawaNumber_pos p a₄ a₆
  · rw [localTamagawaNumber_of_not_prime hp]
    exact Nat.one_pos

/-- `c_p(E)` never vanishes. -/
lemma localTamagawaNumber_ne_zero (p : ℕ) (a₄ a₆ : ℤ) : localTamagawaNumber p a₄ a₆ ≠ 0 :=
  (localTamagawaNumber_pos p a₄ a₆).ne'

/-- `1 < c_p(E)` if and only if `c_p(E) ≠ 1`. -/
lemma one_lt_localTamagawaNumber_iff (p : ℕ) (a₄ a₆ : ℤ) :
    1 < localTamagawaNumber p a₄ a₆ ↔ localTamagawaNumber p a₄ a₆ ≠ 1 := by
  have := localTamagawaNumber_pos p a₄ a₆
  omega

/-- On the singular locus `Δ = 0` (where `τ_p` is set to good reduction) every local Tamagawa
number is `1`. -/
lemma localTamagawaNumber_of_Δ_eq_zero (p : ℕ) {a₄ a₆ : ℤ}
    (h : (ofShortNF a₄ a₆).Δ = 0) :
    localTamagawaNumber p a₄ a₆ = 1 := by
  rw [localTamagawaNumber]
  split
  · rw [tauZ, dite_eq_right (not_not_intro h)]
  · rfl

/-- If `p² ∤ Δ(E(a₄, a₆))` then `c_p(E) = 1`. -/
lemma localTamagawaNumber_eq_one_of_not_dvd (p : ℕ) (a₄ a₆ : ℤ)
    (hnd : ¬ (p ^ 2 : ℤ) ∣ (ofShortNF a₄ a₆).Δ) :
    localTamagawaNumber p a₄ a₆ = 1 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [localTamagawaNumber_of_prime]
    have hK0 := tauZ_mem_K0_of_not_sq_dvd p a₄ a₆ hnd
    simp only [K0, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hK0
    exact hK0.elim (fun h => h.2) (fun h => h.2)
  · exact localTamagawaNumber_of_not_prime hp a₄ a₆

/-- Only finitely many primes contribute a factor `≠ 1` to the Tamagawa product `∏_p c_p(E)`. -/
@[bsd_tamagawa "T004"]
lemma mulSupport_localTamagawaNumber_finite (a₄ a₆ : ℤ) :
    (Function.mulSupport fun p : ℕ => localTamagawaNumber p a₄ a₆).Finite := by
  by_cases hΔ : (ofShortNF a₄ a₆).Δ = 0
  · refine Set.Finite.subset Set.finite_empty fun p hp => ?_
    exact absurd (localTamagawaNumber_of_Δ_eq_zero p hΔ) hp
  · refine Set.Finite.subset (Set.finite_Iic (ofShortNF a₄ a₆).Δ.natAbs) fun p hp => ?_
    rw [Function.mem_mulSupport] at hp
    have hdvd : ((p : ℤ)) ^ 2 ∣ (ofShortNF a₄ a₆).Δ := by
      by_contra hnd
      exact hp (localTamagawaNumber_eq_one_of_not_dvd p a₄ a₆ hnd)
    have hnat : p ^ 2 ∣ (ofShortNF a₄ a₆).Δ.natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    have hle : p ^ 2 ≤ (ofShortNF a₄ a₆).Δ.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hΔ) hnat
    exact Set.mem_Iic.mpr ((Nat.le_self_pow two_ne_zero p).trans hle)

/-- If a finite set `S` of indices contains every prime with `c_p(E) ≠ 1`, then the truncated
product `∏_{p ∈ S} c_p(E)` equals `Tam(E)`. -/
lemma tamagawaProduct_eq_prod_of_mulSupport_subset {a₄ a₆ : ℤ} {S : Finset ℕ}
    (hS : ∀ p : ℕ, localTamagawaNumber p a₄ a₆ ≠ 1 → p ∈ S) :
    tamagawaProduct a₄ a₆ = ∏ p ∈ S, localTamagawaNumber p a₄ a₆ :=
  finprod_eq_prod_of_mulSupport_subset _ fun p hp => hS p hp

/-- There is a `Finset ℕ` containing every index with `c_p(E) ≠ 1`, over which the truncated
product equals `Tam(E)`. -/
lemma exists_finset_tamagawaProduct_eq_prod (a₄ a₆ : ℤ) :
    ∃ S : Finset ℕ, (∀ p : ℕ, localTamagawaNumber p a₄ a₆ ≠ 1 → p ∈ S) ∧
      tamagawaProduct a₄ a₆ = ∏ p ∈ S, localTamagawaNumber p a₄ a₆ := by
  refine ⟨(mulSupport_localTamagawaNumber_finite a₄ a₆).toFinset, fun p hp => ?_, ?_⟩
  · exact (Set.Finite.mem_toFinset _).mpr hp
  · exact tamagawaProduct_eq_prod_of_mulSupport_subset
      fun p hp => (Set.Finite.mem_toFinset _).mpr hp

/-- The Tamagawa product `Tam(E)` is a positive integer, for every `(a₄, a₆)`. -/
@[bsd_tamagawa "T004"]
lemma tamagawaProduct_pos (a₄ a₆ : ℤ) : 0 < tamagawaProduct a₄ a₆ := by
  obtain ⟨S, -, hS⟩ := exists_finset_tamagawaProduct_eq_prod a₄ a₆
  rw [hS]
  exact Finset.prod_pos fun p _ => localTamagawaNumber_pos p a₄ a₆

/-- `Tam(E)` never vanishes. -/
lemma tamagawaProduct_ne_zero (a₄ a₆ : ℤ) : tamagawaProduct a₄ a₆ ≠ 0 :=
  (tamagawaProduct_pos a₄ a₆).ne'

end WeierstrassCurve
