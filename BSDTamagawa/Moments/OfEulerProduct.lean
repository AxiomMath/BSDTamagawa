/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.Continuity
public import BSDTamagawa.Moments.DirichletSpecialization
public import BSDTamagawa.Moments.MonotoneConvergence

/-!
# Moments of the Tamagawa distribution under the Euler-product hypothesis

Let `P_Tam(m) = tamagawaDensity m`, let `M_k = ∑_{m ≥ 1} P_Tam(m) m^{k}` be its `k`-th moment
`tamagawaMoment k`, and let `G_p(k) = momentLocalFactor p k` be the local factor at a prime `p`.
Assuming the Euler-product hypothesis `HasEulerProductOffHalfPlane`, the moment series converges
absolutely and `M_k = ∏_{p ∈ 𝒫} G_p(k)`.

## Main results

* `WeierstrassCurve.summable_tamagawaDensity_succ_mul_pow_of_euler`: the family
  `(P_Tam(m) m^{k})_{m ≥ 1}` is summable.
* `WeierstrassCurve.ofReal_tamagawaMoment_eq_tprod_momentLocalFactor_of_euler`: the identity
  `M_k = ∏_{p ∈ 𝒫} G_p(k)` in `ℂ`.

## Implementation notes

Every sum is a `tsum` and every product a `tprod`. The `ℝ≥0∞` arithmetic is `ENNReal.ofReal` moved
across a convergent nonnegative series (`ENNReal.ofReal_tsum_of_nonneg`), which is additive;
nothing is subtracted in `ℝ≥0∞`, where a difference truncates at `0`. Each `tsum` whose value is
used is preceded by its summability.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

variable (k : ℕ)

/-! ### The moment identity -/

/-- The truncated moment `∑_{m ≥ 1} P_Tam(m) m^{k-σ}`, coerced into `ℂ`, tends to
`∏_{p ∈ 𝒫} G_p(k)` as `σ ↓ 0`. -/
theorem tendsto_ofReal_tsum_tamagawaDensity_succ_mul_rpow_of_euler
    (heuler : HasEulerProductOffHalfPlane) :
    Tendsto (fun σ : ℝ =>
        ((∑' n : ℕ, tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ))) :=
  Tendsto.congr
    (fun σ => (tsum_tamagawaDensity_succ_mul_rpow_of_euler heuler ((k : ℝ) - σ)).symm)
    (tendsto_tprod_momentLocalFactor k)

/-- The Euler product `∏_{p ∈ 𝒫} G_p(k)` has zero imaginary part. -/
theorem im_tprod_momentLocalFactor_of_euler (heuler : HasEulerProductOffHalfPlane) :
    (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).im = 0 := by
  have h : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ))
      (𝓝 (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).im) :=
    (Tendsto.comp (Complex.continuous_im.tendsto _)
      (tendsto_ofReal_tsum_tamagawaDensity_succ_mul_rpow_of_euler k heuler)).congr
      fun _ => by simp
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The Euler product `∏_{p ∈ 𝒫} G_p(k)` is the coercion into `ℂ` of its own real part. -/
theorem ofReal_re_tprod_momentLocalFactor_of_euler (heuler : HasEulerProductOffHalfPlane) :
    (((∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ) :=
  Complex.ext (by simp) (by simp [im_tprod_momentLocalFactor_of_euler k heuler])

/-- The truncated moment `∑_{m ≥ 1} P_Tam(m) m^{k-σ}` tends in `ℝ` to the real part of
`∏_{p ∈ 𝒫} G_p(k)` as `σ ↓ 0`. -/
theorem tendsto_tsum_tamagawaDensity_succ_mul_rpow_of_euler
    (heuler : HasEulerProductOffHalfPlane) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ))
      (𝓝[>] 0)
      (𝓝 (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re) :=
  (Tendsto.comp (Complex.continuous_re.tendsto _)
    (tendsto_ofReal_tsum_tamagawaDensity_succ_mul_rpow_of_euler k heuler)).congr
    fun _ => by simp

/-- The real part of the Euler product `∏_{p ∈ 𝒫} G_p(k)` is nonnegative. -/
theorem re_tprod_momentLocalFactor_nonneg_of_euler (heuler : HasEulerProductOffHalfPlane) :
    0 ≤ (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re :=
  ge_of_tendsto (tendsto_tsum_tamagawaDensity_succ_mul_rpow_of_euler k heuler)
    (Eventually.of_forall fun _ => tsum_nonneg fun n =>
      mul_nonneg (tamagawaDensity_nonneg (n + 1)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The `ℝ≥0∞`-valued truncated moment `∑_{m ≥ 1} ENNReal.ofReal (P_Tam(m) m^{k-σ})` is
`ENNReal.ofReal` of the real truncated moment. -/
theorem tsum_ofReal_tamagawaDensity_succ_mul_rpow_of_euler
    (heuler : HasEulerProductOffHalfPlane) (σ : ℝ) :
    (∑' n : ℕ, ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ)))
      = ENNReal.ofReal
          (∑' n : ℕ, tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ)) :=
  (ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (tamagawaDensity_nonneg (n + 1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (summable_tamagawaDensity_succ_mul_rpow_of_euler heuler ((k : ℝ) - σ))).symm

/-- In `[0, ∞]`,

`∑_{m ≥ 1} P_Tam(m) m^{k} = ENNReal.ofReal (∏_{p ∈ 𝒫} G_p(k)).re`. -/
theorem tsum_ofReal_tamagawaDensity_succ_mul_pow_eq_of_euler
    (heuler : HasEulerProductOffHalfPlane) :
    (∑' n : ℕ, ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k))
      = ENNReal.ofReal
          (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re := by
  refine tendsto_nhds_unique (tendsto_tsum_ofReal_tamagawaDensity_mul_rpow k) ?_
  have hc : Tendsto (fun r : ℝ => ENNReal.ofReal r)
      (𝓝 (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re)
      (𝓝 (ENNReal.ofReal
        (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re)) :=
    ENNReal.continuous_ofReal.tendsto _
  exact (hc.comp (tendsto_tsum_tamagawaDensity_succ_mul_rpow_of_euler k heuler)).congr
    fun σ => (tsum_ofReal_tamagawaDensity_succ_mul_rpow_of_euler k heuler σ).symm

/-- The family `(P_Tam(m) m^{k})_{m ≥ 1}` is summable; its terms being nonnegative, the moment
series converges absolutely. -/
theorem summable_tamagawaDensity_succ_mul_pow_of_euler (heuler : HasEulerProductOffHalfPlane) :
    Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k :=
  summable_of_tsum_ofReal_ne_top
    (fun n => mul_nonneg (tamagawaDensity_nonneg (n + 1)) (pow_nonneg (Nat.cast_nonneg _) k))
    (by
      rw [tsum_ofReal_tamagawaDensity_succ_mul_pow_eq_of_euler k heuler]
      exact ENNReal.ofReal_ne_top)

/-- The moment `M_k` is the real part of the Euler product: `M_k = (∏_{p ∈ 𝒫} G_p(k)).re`. -/
theorem tamagawaMoment_eq_re_tprod_momentLocalFactor_of_euler
    (heuler : HasEulerProductOffHalfPlane) :
    tamagawaMoment k
      = (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ)).re := by
  have hEq := tsum_ofReal_tamagawaDensity_succ_mul_pow_eq_of_euler k heuler
  have hne : (∑' n : ℕ, ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k)) ≠ ⊤ := by
    rw [hEq]; exact ENNReal.ofReal_ne_top
  have h := toReal_tsum_ofReal_tamagawaDensity_mul_pow (k := k) hne
  rw [hEq, ENNReal.toReal_ofReal (re_tprod_momentLocalFactor_nonneg_of_euler k heuler)] at h
  exact h.symm

/-- For every integer `k ≥ 0`,

`M_k = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{k})`,

with `M_k = tamagawaMoment k` and the local factor `momentLocalFactor p k`. -/
theorem ofReal_tamagawaMoment_eq_tprod_momentLocalFactor_of_euler
    (heuler : HasEulerProductOffHalfPlane) :
    ((tamagawaMoment k : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ) := by
  rw [tamagawaMoment_eq_re_tprod_momentLocalFactor_of_euler k heuler]
  exact ofReal_re_tprod_momentLocalFactor_of_euler k heuler

end WeierstrassCurve
