/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.LocalDensity.SummableTailMass

/-!
# Absolute and locally uniform convergence of the Euler product `F` on `ℂ`

Write `a_p := 1 - δ_p(1)` for the local tail mass (`WeierstrassCurve.tamagawaLocalTailMass`), so
that the local Euler factor is `F_p(u) = δ_p(1) + (1 - δ_p(1)) u = 1 + a_p (u - 1)`. Then for every
compact `E ⊆ ℂ`, `∑_p sup_{u ∈ E} |a_p (u - 1)| < ∞`, and the partial products `∏_{p ∈ S} F_p(u)`
over finite sets of primes converge, absolutely and uniformly on `E`, to the infinite product;
hence locally uniformly on all of `ℂ`.

## Main results

* `WeierstrassCurve.summable_iSup_norm_tamagawaLocalTailMass_mul`:
  `∑_p ⨆_{u ∈ E} ‖a_p (u - 1)‖ < ∞` on a compact `E`.
* `WeierstrassCurve.multipliable_tamagawaOmegaEulerFactor`: at each `u` the family `(F_p(u))_p` is
  `Multipliable`.
* `WeierstrassCurve.hasProdUniformlyOn_tamagawaOmegaEulerFactor`: uniform convergence on a compact
  `E`.
* `WeierstrassCurve.hasProdLocallyUniformly_tamagawaOmegaEulerFactor`: locally uniform convergence
  on all of `ℂ`.

## References

* W. Rudin, *Real and Complex Analysis*, Theorem 15.6.
-/

@[expose] public section

namespace WeierstrassCurve

/-! ### The local factor as `1 + a_p (u - 1)`, and the norm of its deviation from `1` -/

/-- **The local Euler factor in `1 + a_p(u - 1)` form:** `F_p(u) = 1 + (1 - δ_p(1))(u - 1)`. -/
theorem tamagawaOmegaEulerFactor_eq_one_add (p : ℕ) (u : ℂ) :
    tamagawaOmegaEulerFactor p u = 1 + (tamagawaLocalTailMass p : ℂ) * (u - 1) :=
  sub_eq_iff_eq_add'.mp (tamagawaOmegaEulerFactor_sub_one p u)

/-- `‖a_p (u - 1)‖ = a_p ‖u - 1‖`, the local tail mass `a_p` being nonnegative. -/
theorem norm_tamagawaLocalTailMass_mul (p : ℕ) (u : ℂ) :
    ‖(tamagawaLocalTailMass p : ℂ) * (u - 1)‖ = tamagawaLocalTailMass p * ‖u - 1‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (tamagawaLocalTailMass_nonneg p)]

/-- **The deviation of the local factor from `1`, in norm:** `‖F_p(u) - 1‖ = a_p ‖u - 1‖`. -/
theorem norm_tamagawaOmegaEulerFactor_sub_one (p : ℕ) (u : ℂ) :
    ‖tamagawaOmegaEulerFactor p u - 1‖ = tamagawaLocalTailMass p * ‖u - 1‖ := by
  rw [tamagawaOmegaEulerFactor_sub_one, norm_tamagawaLocalTailMass_mul]

/-- **The deviations are absolutely summable at every `u`:** `∑_p ‖F_p(u) - 1‖ < ∞`. -/
theorem summable_norm_tamagawaOmegaEulerFactor_sub_one (u : ℂ) :
    Summable fun p : ℕ => ‖tamagawaOmegaEulerFactor p u - 1‖ :=
  (summable_tamagawaLocalTailMass.mul_right ‖u - 1‖).congr fun p =>
    (norm_tamagawaOmegaEulerFactor_sub_one p u).symm

/-! ### Bounds on a compact set -/

/-- **A compact set is bounded:** on a compact `E ⊆ ℂ` there is `R > 0` with `‖u - 1‖ ≤ R` for
every `u ∈ E`. -/
theorem exists_pos_forall_norm_sub_one_le {E : Set ℂ} (hE : IsCompact E) :
    ∃ R : ℝ, 0 < R ∧ ∀ u ∈ E, ‖u - 1‖ ≤ R := by
  obtain ⟨R, hR0, hRsub⟩ := hE.isBounded.subset_closedBall_lt 0 1
  exact ⟨R, hR0, fun u hu => by simpa [Metric.mem_closedBall, dist_eq_norm] using hRsub hu⟩

/-- **The termwise bound on `E`:** `‖a_p (u - 1)‖ ≤ a_p R` for `u ∈ E`, where `R` bounds `‖u - 1‖`
on `E`. -/
theorem norm_tamagawaLocalTailMass_mul_le {E : Set ℂ} {R : ℝ} (hR : ∀ u ∈ E, ‖u - 1‖ ≤ R)
    (p : ℕ) {u : ℂ} (hu : u ∈ E) :
    ‖(tamagawaLocalTailMass p : ℂ) * (u - 1)‖ ≤ tamagawaLocalTailMass p * R := by
  rw [norm_tamagawaLocalTailMass_mul]
  exact mul_le_mul_of_nonneg_left (hR u hu) (tamagawaLocalTailMass_nonneg p)

/-! ### Summability of the suprema over a compact set -/

/-- For every compact `E ⊆ ℂ`, `∑_p sup_{u ∈ E} |a_p (u - 1)| < ∞`, with `a_p = 1 - δ_p(1)` the
local tail mass. The supremum is the `ℝ`-valued `⨆ u : E`, which is `0` when `E = ∅`. -/
@[bsd_tamagawa "T041g"]
theorem summable_iSup_norm_tamagawaLocalTailMass_mul {E : Set ℂ} (hE : IsCompact E) :
    Summable fun p : ℕ => ⨆ u : E, ‖(tamagawaLocalTailMass p : ℂ) * ((u : ℂ) - 1)‖ := by
  obtain ⟨R, hR0, hR⟩ := exists_pos_forall_norm_sub_one_le hE
  exact Summable.of_nonneg_of_le (fun p => Real.iSup_nonneg fun u => norm_nonneg _)
    (fun p => Real.iSup_le (fun u => norm_tamagawaLocalTailMass_mul_le hR p u.2)
      (mul_nonneg (tamagawaLocalTailMass_nonneg p) hR0.le))
    (summable_tamagawaLocalTailMass.mul_right R)

/-! ### Absolute and locally uniform convergence -/

/-- At every `u : ℂ` the family of local Euler factors `(F_p(u))_p` is multipliable: the net of
partial products `∏_{p ∈ S} F_p(u)` over finite `S`, directed by inclusion, converges, so its limit
`∏' p, F_p(u)` is independent of the order of the factors. -/
@[bsd_tamagawa "T041g"]
theorem multipliable_tamagawaOmegaEulerFactor (u : ℂ) :
    Multipliable fun p : ℕ => tamagawaOmegaEulerFactor p u :=
  (multipliable_one_add_of_summable (summable_norm_tamagawaOmegaEulerFactor_sub_one u)).congr
    fun _ => add_sub_cancel _ _

/-- For every compact `E ⊆ ℂ`, the partial products `∏_{p ∈ S} F_p(u)` converge to `∏' p, F_p(u)`
uniformly on `E` as `S` increases through the finite sets of indices. -/
@[bsd_tamagawa "T041g"]
theorem hasProdUniformlyOn_tamagawaOmegaEulerFactor {E : Set ℂ} (hE : IsCompact E) :
    HasProdUniformlyOn tamagawaOmegaEulerFactor
      (fun u => ∏' p : ℕ, tamagawaOmegaEulerFactor p u) E := by
  obtain ⟨R, hR0, hR⟩ := exists_pos_forall_norm_sub_one_le hE
  have key := Summable.hasProdUniformlyOn_one_add
    (f := fun (p : ℕ) (u : ℂ) => (tamagawaLocalTailMass p : ℂ) * (u - 1)) hE
    (summable_tamagawaLocalTailMass.mul_right R)
    (Filter.Eventually.of_forall fun p u hu => norm_tamagawaLocalTailMass_mul_le hR p hu)
    (fun p => (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn)
  simpa only [← tamagawaOmegaEulerFactor_eq_one_add] using key

/-- The partial products `∏_{p ∈ S} F_p(u)` converge to `∏' p, F_p(u)` locally uniformly on all of
`ℂ`. -/
@[bsd_tamagawa "T041g"]
theorem hasProdLocallyUniformly_tamagawaOmegaEulerFactor :
    HasProdLocallyUniformly tamagawaOmegaEulerFactor
      (fun u => ∏' p : ℕ, tamagawaOmegaEulerFactor p u) :=
  hasProdLocallyUniformly_of_forall_compact fun _ hK =>
    hasProdUniformlyOn_tamagawaOmegaEulerFactor hK

end WeierstrassCurve
