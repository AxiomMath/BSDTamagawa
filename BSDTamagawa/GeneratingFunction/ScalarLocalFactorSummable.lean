/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.LocalDensity.ScalarSum
public import BSDTamagawa.GeneratingFunction.ScalarLocalFactor
public import BSDTamagawa.GeneratingFunction.ScalarWeightBound

/-!
# The scalar local factor is an absolutely convergent series on `𝒟₀`

For a prime `p` and parameters `(s, w, 𝐳) ∈ 𝒟₀` (that is, `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1`
for every `ℓ ∈ Π`), the family `(δ_p(t) ψ_{s, w, 𝐳}(t))_t` is absolutely summable, and the scalar
local factor `h_p(s, w, 𝐳)` is its sum. Each term is dominated in norm by `δ_p(t)`, since
`‖ψ_{s, w, 𝐳}(t)‖ ≤ 1` on `𝒟₀`, and the densities have total mass `1`. The family is indexed by all
of `ℕ`; the `t = 0` term vanishes because `δ_p(0) = 0`.

## Main results

* `WeierstrassCurve.summable_δ_toReal`: the real-valued scalar local densities are summable.
* `WeierstrassCurve.summable_norm_δ_toReal_mul_scalarWeight`: absolute summability of the family
  `(δ_p(t) ψ_{s, w, 𝐳}(t))_t` on `𝒟₀`.
* `WeierstrassCurve.hasSum_scalarLocalFactor`: on `𝒟₀`, `h_p(s, w, 𝐳)` is the sum of that family.
-/

@[expose] public section

namespace WeierstrassCurve

variable (P : Finset ℕ) (p : ℕ)

/-! ### The dominating family -/

/-- The total mass of the scalar local densities is finite: `∑_t δ_p(t) ≠ ⊤`. -/
lemma tsum_δ_ne_top [Fact p.Prime] : ∑' t : ℕ, δ p t ≠ ⊤ := by
  rw [tsum_δ]
  exact ENNReal.one_ne_top

/-- The real-valued scalar local densities `t ↦ δ_p(t)` are summable. -/
lemma summable_δ_toReal [Fact p.Prime] : Summable fun t : ℕ => (δ p t).toReal :=
  ENNReal.summable_toReal (tsum_δ_ne_top p)

/-! ### The termwise bound -/

/-- On `𝒟₀` the `t`-th term of the series for `h_p` has norm at most `δ_p(t)`, for every
`t : ℕ`. -/
lemma norm_δ_toReal_mul_scalarWeight_le [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (t : ℕ) :
    ‖((δ p t).toReal : ℂ) * scalarWeight P s w z t‖ ≤ (δ p t).toReal := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [δ_zero]
  · have hnorm : ‖((δ p t).toReal : ℂ)‖ = (δ p t).toReal := by
      rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [norm_mul, hnorm]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg
      (norm_scalarWeight_le_one P hs hw hz ht)

/-! ### Absolute summability, and `h_p` as the sum of the series -/

/-- If `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`, then the family
`(δ_p(t) ψ_{s, w, 𝐳}(t))_{t ∈ ℕ}` is absolutely summable. -/
@[bsd_tamagawa "T036g"]
theorem summable_norm_δ_toReal_mul_scalarWeight [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Summable fun t : ℕ => ‖((δ p t).toReal : ℂ) * scalarWeight P s w z t‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_δ_toReal_mul_scalarWeight_le P p hs hw hz) (summable_δ_toReal p)

/-- The family `(δ_p(t) ψ_{s, w, 𝐳}(t))_t` is summable on `𝒟₀`. -/
lemma summable_δ_toReal_mul_scalarWeight [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Summable fun t : ℕ => ((δ p t).toReal : ℂ) * scalarWeight P s w z t :=
  Summable.of_norm (summable_norm_δ_toReal_mul_scalarWeight P p hs hw hz)

/-- On `𝒟₀` the scalar local factor `h_p(s, w, 𝐳)` is the sum of the absolutely convergent series
`∑_t δ_p(t) ψ_{s, w, 𝐳}(t)`. -/
@[bsd_tamagawa "T036g"]
theorem hasSum_scalarLocalFactor [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    HasSum (fun t : ℕ => ((δ p t).toReal : ℂ) * scalarWeight P s w z t)
      (scalarLocalFactor P p s w z) := by
  rw [scalarLocalFactor_eq_tsum_of_prime]
  exact (summable_δ_toReal_mul_scalarWeight P p hs hw hz).hasSum

end WeierstrassCurve
