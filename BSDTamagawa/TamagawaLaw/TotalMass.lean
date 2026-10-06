/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.DirichletSeries

/-!
# Total mass of the limiting Tamagawa distribution

The family `(P_Tam(m))_{m ≥ 1}` of limiting densities of the global Tamagawa number is summable
with

`∑_{m ≥ 1} P_Tam(m) = 1`,

i.e. it is a probability distribution on the positive integers.

## Main results

* `WeierstrassCurve.tprod_primes_tsum_δ_zero_eq_one`: the Euler product
  `∏_p ∑_{t ≥ 1} δ_p(t) t^{-s}` equals `1` at `s = 0`.
* `WeierstrassCurve.summable_tamagawaDensity`: the family `P_Tam` is summable.
* `WeierstrassCurve.tsum_tamagawaDensity_eq_one`: its total mass is `1`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

/-- **The Euler product at `s = 0` is `1`.** The product over the primes of the local factors
`∑_{t ≥ 1} δ_p(t) t^{-s}` equals `1` at `s = 0`. -/
lemma tprod_primes_tsum_δ_zero_eq_one :
    ∏' p : {q : ℕ // q.Prime},
        (∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-(0 : ℂ))) = 1 := by
  rw [tprod_primes_tsum_δ_mul_cpow_eq (s := 0) (by simp) fun _ => (1 : ℂ)]
  exact tprod_scalarLocalFactor_empty_one_zero _

/-- If `X ↦ P_Tam(m; X)` converges for every `m`, then the limiting densities `P_Tam(m)` are
summable with

`∑_{m ≥ 1} P_Tam(m) = 1`. -/
theorem summable_and_tsum_tamagawaDensity_eq_one_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) :
    Summable tamagawaDensity ∧ ∑' m : ℕ, tamagawaDensity m = 1 := by
  refine ⟨summable_tamagawaDensity_of_tendsto hconv, ?_⟩
  have h := tsum_tamagawaDensity_mul_cpow_of_tendsto hconv (s := 0) (by simp)
  rw [tprod_primes_tsum_δ_zero_eq_one,
    tsum_congr fun m : ℕ => by rw [neg_zero, Complex.cpow_zero, mul_one],
    ← Complex.ofReal_tsum] at h
  exact_mod_cast h

/-- The family `(P_Tam(m))_{m ≥ 1}` of limiting Tamagawa densities is summable. -/
@[bsd_tamagawa "T018c"]
theorem summable_tamagawaDensity : Summable tamagawaDensity :=
  (summable_and_tsum_tamagawaDensity_eq_one_of_tendsto exists_tendsto_tamagawaProportion).1

/-- The total mass of the limiting Tamagawa distribution is `1`:

`∑_{m ≥ 1} P_Tam(m) = 1`,

so the limiting densities form a probability distribution on the positive integers. The sum is
written over all of `ℕ`, which is the same sum, since `P_Tam(0) = 0`. -/
@[bsd_tamagawa "T018c"]
theorem tsum_tamagawaDensity_eq_one : ∑' m : ℕ, tamagawaDensity m = 1 :=
  (summable_and_tsum_tamagawaDensity_eq_one_of_tendsto exists_tendsto_tamagawaProportion).2

end WeierstrassCurve
