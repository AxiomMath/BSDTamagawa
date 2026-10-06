/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.Multipliable
public import BSDTamagawa.Moments.DirichletSpecializationConditional

/-!
# Moments of the Tamagawa density as an Euler product, granted the Euler product identity

Granted the Euler product identity `HasEulerProductOffHalfPlane` for the Dirichlet series of the
limiting Tamagawa density, for every real `x` the family `(P_Tam(m) m^x)_m` is summable and

`∑_{m ≥ 1} P_Tam(m) m^x = ∏_{p ∈ 𝒫} G_p(x)`,

where `G_p` is the moment local factor. The absolute convergence of the Euler product at the
exponent `-x`, which the identity requires, holds unconditionally.

## Main results

* `WeierstrassCurve.summable_norm_tamagawaEulerFactor_neg_sub_one`: the Euler product at the
  exponent `-x` converges absolutely.
* `WeierstrassCurve.summable_tamagawaDensity_mul_rpow_of_euler` and
  `WeierstrassCurve.tsum_tamagawaDensity_mul_rpow_of_euler`: summability and the Euler product
  identity, indexed by `m : ℕ`.
* `WeierstrassCurve.summable_tamagawaDensity_succ_mul_rpow_of_euler` and
  `WeierstrassCurve.tsum_tamagawaDensity_succ_mul_rpow_of_euler`: the same in the reindexing
  `m = n + 1`.
-/

@[expose] public section

namespace WeierstrassCurve

/-- For every real `x`, the Euler product `∏_p (∑_{t ≥ 1} δ_p(t) t^{x})` converges absolutely: the
deviations `‖tamagawaEulerFactor p (-x) - 1‖` are summable over the primes. -/
theorem summable_norm_tamagawaEulerFactor_neg_sub_one (x : ℝ) :
    Summable fun p : {q : ℕ // q.Prime} => ‖tamagawaEulerFactor p (-((x : ℝ) : ℂ)) - 1‖ :=
  (summable_norm_momentLocalFactor_sub_one x).congr fun p => by rw [tamagawaEulerFactor_neg]

/-- Granted the Euler product identity, for every real `x` the family `(P_Tam(m) m^{x})_{m}` is
summable. -/
theorem summable_tamagawaDensity_mul_rpow_of_euler (heuler : HasEulerProductOffHalfPlane) (x : ℝ) :
    Summable fun m : ℕ => tamagawaDensity m * (m : ℝ) ^ x := by
  refine ((heuler (-((x : ℝ) : ℂ)))
    (summable_norm_tamagawaEulerFactor_neg_sub_one x)).1.congr fun m => ?_
  rw [neg_neg, ofReal_tamagawaDensity_mul_natCast_cpow, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (tamagawaDensity_nonneg m)
      (Real.rpow_nonneg (Nat.cast_nonneg m) x))]

/-- Granted the Euler product identity, for every real `x`,

`∑_{m ≥ 1} P_Tam(m) m^{x} = ∏_{p ∈ 𝒫} G_p(x)`,

the left-hand side being a real number coerced into `ℂ`. -/
theorem tsum_tamagawaDensity_mul_rpow_of_euler (heuler : HasEulerProductOffHalfPlane) (x : ℝ) :
    ((∑' m : ℕ, tamagawaDensity m * (m : ℝ) ^ x : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) x := by
  have hid := ((heuler (-((x : ℝ) : ℂ)))
    (summable_norm_tamagawaEulerFactor_neg_sub_one x)).2
  rw [neg_neg] at hid
  have hp : (∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p (-((x : ℝ) : ℂ)))
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) x :=
    tprod_congr fun p => tamagawaEulerFactor_neg p x
  rw [Complex.ofReal_tsum, ← hp, ← hid]
  exact tsum_congr fun m => (ofReal_tamagawaDensity_mul_natCast_cpow m x).symm

/-- Granted the Euler product identity, for every real `x` the family
`(P_Tam(n + 1) (n + 1)^{x})_{n}` is summable. -/
theorem summable_tamagawaDensity_succ_mul_rpow_of_euler (heuler : HasEulerProductOffHalfPlane)
    (x : ℝ) : Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ x :=
  (summable_nat_add_iff 1).mpr (summable_tamagawaDensity_mul_rpow_of_euler heuler x)

/-- Granted the Euler product identity, for every real `x`,

`∑_{n ≥ 0} P_Tam(n+1) (n+1)^{x} = ∏_{p ∈ 𝒫} G_p(x)`. -/
theorem tsum_tamagawaDensity_succ_mul_rpow_of_euler (heuler : HasEulerProductOffHalfPlane)
    (x : ℝ) :
    ((∑' n : ℕ, tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) x := by
  have h0 := (summable_tamagawaDensity_mul_rpow_of_euler heuler x).tsum_eq_zero_add
  rw [tamagawaDensity_zero, zero_mul, zero_add] at h0
  rw [← h0]
  exact tsum_tamagawaDensity_mul_rpow_of_euler heuler x

end WeierstrassCurve
