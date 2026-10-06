/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarLocalFactorSummable

/-!
# Deviation bound for the scalar local factor

For a prime `p` and parameters `(s, w, 𝐳) ∈ 𝒟₀` (that is, `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1`
for every `ℓ ∈ Π`), the scalar local factor satisfies `|h_p(s, w, 𝐳) - 1| ≤ 2 (1 - δ_p(1))`. Since
the densities `δ_p(t)` have total mass `1`, `h_p(s, w, 𝐳) - 1 = ∑_t δ_p(t) (ψ_{s, w, 𝐳}(t) - 1)`;
the `t = 1` term vanishes because `ψ_{s, w, 𝐳}(1) = 1`, and every other term has norm at most
`2 δ_p(t)`.

## Main results

* `WeierstrassCurve.scalarWeight_one`: `ψ_{s, w, 𝐳}(1) = 1`.
* `WeierstrassCurve.hasSum_δ_toReal`: the real-valued scalar local densities sum to `1`.
* `WeierstrassCurve.norm_scalarLocalFactor_sub_one_le`: `|h_p(s, w, 𝐳) - 1| ≤ 2 (1 - δ_p(1))`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

variable (P : Finset ℕ) (p : ℕ)

/-! ### The `t = 1` term of the series -/

/-- The scalar weight is `1` at `t = 1`: `ψ_{s, w, 𝐳}(1) = 1`. -/
lemma scalarWeight_one (s w : ℂ) (z : P → ℂ) : scalarWeight P s w z 1 = 1 := by
  rw [scalarWeight]
  simp [multiMonomial]

/-! ### The total mass in `ℝ` and in `ℂ` -/

/-- The real-valued scalar local densities sum to `1`: `∑_t δ_p(t) = 1` in `ℝ`. -/
lemma hasSum_δ_toReal [Fact p.Prime] : HasSum (fun t : ℕ => (δ p t).toReal) 1 := by
  have hne : ∀ t : ℕ, δ p t ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top (tsum_δ_ne_top p)
  have hval : ∑' t : ℕ, (δ p t).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hne, tsum_δ]
    simp
  simpa [hval] using (summable_δ_toReal p).hasSum

/-- The scalar local densities, coerced to `ℂ`, sum to `1`. -/
lemma hasSum_ofReal_δ_toReal [Fact p.Prime] :
    HasSum (fun t : ℕ => ((δ p t).toReal : ℂ)) 1 := by
  simpa [Function.comp_def] using
    (hasSum_δ_toReal p).map Complex.ofRealHom Complex.continuous_ofReal

/-- The family `t ↦ if t = 1 then 0 else 2 δ_p(t)` has sum `2 (1 - δ_p(1))`. -/
lemma hasSum_scalarDeviationBound [Fact p.Prime] :
    HasSum (fun t : ℕ => if t = 1 then 0 else 2 * (δ p t).toReal)
      (2 * (1 - (δ p 1).toReal)) := by
  have h₁ : HasSum (fun t : ℕ => 2 * (δ p t).toReal) 2 := by
    simpa using (hasSum_δ_toReal p).mul_left 2
  have h₂ : HasSum (fun t : ℕ => if t = 1 then 2 * (δ p 1).toReal else 0)
      (2 * (δ p 1).toReal) := hasSum_ite_eq 1 _
  have h := h₁.sub h₂
  have hfun : (fun t : ℕ => 2 * (δ p t).toReal - if t = 1 then 2 * (δ p 1).toReal else 0)
      = fun t : ℕ => if t = 1 then 0 else 2 * (δ p t).toReal := by
    funext t
    by_cases ht : t = 1 <;> simp [ht]
  have hval : (2 : ℝ) - 2 * (δ p 1).toReal = 2 * (1 - (δ p 1).toReal) := by ring
  rwa [hfun, hval] at h

/-! ### The termwise bound -/

/-- On `𝒟₀` the `t`-th term of `∑_t δ_p(t) (ψ_{s, w, 𝐳}(t) - 1)` has norm at most `2 δ_p(t)`, and
it vanishes at `t = 1`. -/
lemma norm_δ_toReal_mul_scalarWeight_sub_one_le [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (t : ℕ) :
    ‖((δ p t).toReal : ℂ) * (scalarWeight P s w z t - 1)‖
      ≤ if t = 1 then 0 else 2 * (δ p t).toReal := by
  by_cases ht1 : t = 1
  · subst ht1
    simp [scalarWeight_one]
  rw [ite_eq_right ht1]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [δ_zero]
  · have hψ : ‖scalarWeight P s w z t - 1‖ ≤ 2 :=
      calc ‖scalarWeight P s w z t - 1‖ ≤ ‖scalarWeight P s w z t‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ 2 := by
            rw [norm_one]
            linarith [norm_scalarWeight_le_one P hs hw hz ht]
    have hnorm : ‖((δ p t).toReal : ℂ)‖ = (δ p t).toReal := by
      rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [norm_mul, hnorm]
    have := mul_le_mul_of_nonneg_left hψ (ENNReal.toReal_nonneg (a := δ p t))
    linarith

/-! ### The deviation bound -/

/-- For a prime `p` and every `(s, w, 𝐳) ∈ 𝒟₀`, that is, `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for
every `ℓ ∈ Π`, the scalar local factor satisfies `|h_p(s, w, 𝐳) - 1| ≤ 2 (1 - δ_p(1))`. -/
@[bsd_tamagawa "T036i"]
theorem norm_scalarLocalFactor_sub_one_le [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    ‖scalarLocalFactor P p s w z - 1‖ ≤ 2 * (1 - (δ p 1).toReal) := by
  have hmain : HasSum (fun t : ℕ => ((δ p t).toReal : ℂ) * (scalarWeight P s w z t - 1))
      (scalarLocalFactor P p s w z - 1) := by
    simpa [mul_sub] using
      (hasSum_scalarLocalFactor P p hs hw hz).sub (hasSum_ofReal_δ_toReal p)
  exact hmain.norm_le_of_bounded (hasSum_scalarDeviationBound p)
    (norm_δ_toReal_mul_scalarWeight_sub_one_le P p hs hw hz)

end WeierstrassCurve
