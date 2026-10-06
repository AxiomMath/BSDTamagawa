/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateRunInvariance
public import BSDTamagawa.LocalDensity.MomentEstimate
public import BSDTamagawa.LocalDensity.SecondMoment

/-!
# The geometric tail law at primes `p ≥ 5`, and moment bounds for the local densities

Since `StratScaleInvariant p` holds for every prime `p ≥ 5`, the geometric tail law
`HasTailGeometricLaw p` holds there unconditionally. Consequently the moments of the local density
`δ_q` satisfy bounds of the shape `C / q²` (respectively `1 + C / q²`) for every prime `q` beyond a
threshold.

## Main results

* `WeierstrassCurve.hasTailGeometricLaw_of_five_le`: `HasTailGeometricLaw p` for every prime
  `p ≥ 5`.
* `WeierstrassCurve.exists_moment_bounds`: the `Ω`-moment and every `v_ℓ`-moment of `δ_q` are
  `O(q⁻²)`.
* `WeierstrassCurve.exists_second_moment_bounds`: the second `Ω`-moment and every mixed valuation
  moment of `δ_q` are `O(q⁻²)`.
* `WeierstrassCurve.exists_moment_estimate`: the `k`-th moment of `δ_q` is `1 + O_k(q⁻²)`.
* `WeierstrassCurve.exists_uniform_moment_bound`: `‖G_q(x) - 1‖ ≤ C_k / q²` uniformly for
  `-1 ≤ x ≤ k`.
-/

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.AdditiveMoment

variable {p : ℕ} [Fact p.Prime]

/-- **The geometric tail law at every prime `p ≥ 5`.** -/
theorem hasTailGeometricLaw_of_five_le (hp : 5 ≤ p) : HasTailGeometricLaw p :=
  hasTailGeometricLaw_of_stratScaleInvariant hp (stratScaleInvariant_of_five_le hp)

/-- There is a threshold `p₀` (namely `5`) such that `HasTailGeometricLaw q` holds for every prime
`q ≥ p₀`. -/
theorem exists_forall_hasTailGeometricLaw :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q → HasTailGeometricLaw q :=
  ⟨5, fun _ _ hq => hasTailGeometricLaw_of_five_le hq⟩

/-- There are a constant `C > 0` and a threshold `p₀` such that for every prime `q ≥ p₀`, both the
`Ω`-moment and every `v_ℓ`-moment of `δ_q` are at most `C / q²`. -/
@[bsd_tamagawa "T023d"]
theorem exists_moment_bounds :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      (∑' t : ℕ, δ q t * (ArithmeticFunction.cardFactors t : ℝ≥0∞)) ≤ C / (q : ℝ≥0∞) ^ 2 ∧
        ∀ ℓ : ℕ, (∑' t : ℕ, δ q t * ((t.factorization) ℓ : ℝ≥0∞)) ≤ C / (q : ℝ≥0∞) ^ 2 :=
  exists_moment_bounds_of_tailLaw exists_forall_hasTailGeometricLaw

/-- There are a constant `C > 0` and a threshold `p₀` such that for every prime `q ≥ p₀`, the
second `Ω`-moment and every mixed valuation moment of `δ_q` are at most `C / q²`. -/
@[bsd_tamagawa "T023e"]
theorem exists_second_moment_bounds :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      (∑' t : ℕ, δ q t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2) ≤ C / (q : ℝ≥0∞) ^ 2 ∧
        ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime →
          (∑' t : ℕ, δ q t * (padicValNat ℓ t : ℝ≥0∞) * (padicValNat ℓ' t : ℝ≥0∞))
            ≤ C / (q : ℝ≥0∞) ^ 2 :=
  exists_second_moment_bounds_of_tailLaw exists_forall_hasTailGeometricLaw

/-- For every `k`, the `k`-th moment of `δ_q` is `1 + O_k(q⁻²)` for every large prime. -/
@[bsd_tamagawa "T023b"]
theorem exists_moment_estimate (k : ℕ) :
    ∃ C : ℝ, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      (∑' t : ℕ, (δ q t).toReal * (t : ℝ) ^ k) ≤ 1 + C / (q : ℝ) ^ 2 :=
  ⟨momentBoundConst k, 5, momentBoundConst_pos k,
    fun q _ hq => tsum_δ_toReal_mul_pow_le_of_tailLaw q (hasTailGeometricLaw_of_five_le hq) k⟩

/-- For every `k`, the local moment factor satisfies `‖G_q(x) - 1‖ ≤ C_k / q²` uniformly for
`-1 ≤ x ≤ k` at every large prime. -/
@[bsd_tamagawa "T059f"]
theorem exists_uniform_moment_bound (k : ℕ) :
    ∃ C : ℝ, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      ∀ x : ℝ, -1 ≤ x → x ≤ (k : ℝ) → ‖momentLocalFactor q x - 1‖ ≤ C / (q : ℝ) ^ 2 :=
  ⟨momentBoundConst k, 5, momentBoundConst_pos k,
    fun q _ hq _ _ hxk =>
      norm_momentLocalFactor_sub_one_le_of_tailLaw q (hasTailGeometricLaw_of_five_le hq) k hxk⟩

end WeierstrassCurve
