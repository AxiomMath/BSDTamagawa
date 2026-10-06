/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarLocalFactorDeviation
public import BSDTamagawa.LocalDensity.SummableTailMass

/-!
# Multipliability of the scalar Euler product

For parameters `(s, w, 𝐳) ∈ 𝒟₀` (that is, `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for every
`ℓ ∈ Π`), the family of scalar local factors `h_p(s, w, 𝐳)` is multipliable. Writing
`a_p := h_p(s, w, 𝐳) - 1`, one has `‖a_p‖ ≤ 2(1 - δ_p(1)) ≤ 6/p²` for `p ≥ 5`, so `∑_p ‖a_p‖ < ∞`,
and a family `(1 + a_p)` with summable norms is multipliable in `ℂ` (Rudin, *Real and Complex
Analysis*, Theorem 15.6).

## Main results

* `WeierstrassCurve.summable_scalarLocalFactor_sub_one`: `∑_p |h_p(s, w, 𝐳) - 1| < ∞` on `𝒟₀`.
* `WeierstrassCurve.multipliable_scalarLocalFactor`: the family `p ↦ h_p(s, w, 𝐳)`, indexed by `ℕ`,
  is multipliable on `𝒟₀`.
* `WeierstrassCurve.multipliable_scalarLocalFactor_primes`: the same family indexed by the primes
  is multipliable.

## Implementation notes

The family is indexed by `ℕ`, with `h_p = 1` at every non-prime index, so its partial products
agree with those over the primes.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.PrimeSqTail

/-! ### The `O(p⁻²)` bound on the deviation -/

/-- For every index `p ≥ 5` and every `(s, w, 𝐳) ∈ 𝒟₀`, `‖h_p(s, w, 𝐳) - 1‖ ≤ 6 · primeSq p`, where
`primeSq p` is `p⁻²` at a prime and `0` otherwise. -/
lemma norm_scalarLocalFactor_sub_one_le_primeSq (P : Finset ℕ) (p : ℕ) (hp : 5 ≤ p)
    {s w : ℂ} {z : P → ℂ} (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    ‖scalarLocalFactor P p s w z - 1‖ ≤ 6 * primeSq p := by
  by_cases hpp : p.Prime
  · have : Fact p.Prime := ⟨hpp⟩
    have h₁ := norm_scalarLocalFactor_sub_one_le P p hs hw hz
    have h₂ := one_sub_δ_one_toReal_le (p := p) hp
    have hps : (6 : ℝ) * primeSq p = 2 * (3 / (p : ℝ) ^ 2) := by
      rw [primeSq, ite_eq_left hpp]; ring
    rw [hps]
    linarith
  · rw [scalarLocalFactor_of_not_prime hpp, sub_self, norm_zero, primeSq, ite_eq_right hpp]
    simp

/-! ### Summability of the deviations -/

/-- On `𝒟₀` the family `p ↦ h_p(s, w, 𝐳) - 1` is summable. -/
lemma summable_scalarLocalFactor_sub_one (P : Finset ℕ) {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Summable (fun p : ℕ => scalarLocalFactor P p s w z - 1) := by
  refine (summable_primeSq.mul_left 6).of_norm_bounded_eventually_nat ?_
  filter_upwards [Filter.eventually_ge_atTop 5] with p hp
  exact norm_scalarLocalFactor_sub_one_le_primeSq P p hp hs hw hz

/-! ### Multipliability -/

/-- For every `(s, w, 𝐳) ∈ 𝒟₀`, that is, `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`,
the family of scalar local factors `p ↦ h_p(s, w, 𝐳)` is multipliable. (The index type is `ℕ`, and
`h_p = 1` at every non-prime index.) -/
@[bsd_tamagawa "T036j"]
theorem multipliable_scalarLocalFactor (P : Finset ℕ) {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Multipliable (fun p : ℕ => scalarLocalFactor P p s w z) :=
  (multipliable_one_add_of_summable
    (summable_scalarLocalFactor_sub_one P hs hw hz).norm).congr fun p => by ring

/-- The family `(h_p(s, w, 𝐳))_{p ∈ 𝒫}`, indexed by the primes, is multipliable on `𝒟₀`. -/
theorem multipliable_scalarLocalFactor_primes (P : Finset ℕ) {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Multipliable fun p : {q : ℕ // q.Prime} => scalarLocalFactor P (p : ℕ) s w z := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      scalarLocalFactor P x s w z = 1 := fun x hx =>
    scalarLocalFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) s w z
  exact (Subtype.coe_injective.multipliable_iff hone).2
    (multipliable_scalarLocalFactor P hs hw hz)

end WeierstrassCurve
