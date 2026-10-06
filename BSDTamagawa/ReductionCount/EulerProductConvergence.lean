/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.ReductionCount.JointEulerProduct
public import BSDTamagawa.LocalDensity.SummableReductionDensity

/-!
# Convergence of the joint Euler product `F_Λ` on `ℂ^Λ`

Let `Λ ⊆ 𝒦 ∖ 𝒦₀` be a finite set of local reduction data and let `𝐮 = (u_K)_{K ∈ Λ}` range over
`ℂ^Λ = ↥Λ → ℂ`. The local factor `F_{Λ,p}(𝐮) = 1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K` equals
`1 + ∑_{K ∈ Λ} δ_p(K)(u_K - 1)`; on every compact `E ⊆ ℂ^Λ` the series
`∑_p sup_{𝐮 ∈ E} |∑_{K ∈ Λ} δ_p(K)(u_K - 1)|` converges; and consequently the partial products
`∏_{p ∈ S} F_{Λ,p}(𝐮)` over finite sets `S` of primes converge to `F_Λ(𝐮)` absolutely, uniformly on
compact sets, and locally uniformly on all of `ℂ^Λ`.

## Main results

* `WeierstrassCurve.jointReductionOmegaEulerFactor_eq_one_add_of_prime`: the identity
  `F_{Λ,p}(𝐮) = 1 + ∑_{K ∈ Λ} δ_p(K)(u_K - 1)` at a prime `p`.
* `WeierstrassCurve.summable_iSup_norm_sum_stratumLocalMass_mul`: summability of
  `⨆_{𝐮 ∈ E} ‖∑_{K ∈ Λ} δ_p(K)(u_K - 1)‖` over `p`, for compact `E`.
* `WeierstrassCurve.multipliable_jointReductionOmegaEulerFactor`: the family `(F_{Λ,p}(𝐮))_p` is
  multipliable at each `𝐮`.
* `WeierstrassCurve.hasProdUniformlyOn_jointReductionOmegaEulerFactor`: uniform convergence to
  `jointReductionOmegaEulerProduct Λ` on a compact `E ⊆ ℂ^Λ`.
* `WeierstrassCurve.hasProdLocallyUniformly_jointReductionOmegaEulerFactor`: locally uniform
  convergence on all of `ℂ^Λ`.

## Implementation notes

The density enters through `stratumLocalMass K`, which is `(δ_p(K)).toReal` at a prime index and
`0` elsewhere, so the identities below hold at every index `p : ℕ`. No globally uniform statement
holds: the majorant `∑_{K ∈ Λ} δ_p(K) R` grows with the bound `R` on `‖u_K - 1‖`.

## References

* W. Rudin, *Real and Complex Analysis*, Theorem 15.6.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam

/-! ### The local factor as `1 + ∑_{K ∈ Λ} δ_p(K)(u_K - 1)` -/

/-- For every index `p : ℕ`, `F_{Λ,p}(𝐮) - 1 = ∑_{K ∈ Λ} δ_p(K)(u_K - 1)`, with `δ_p(K)` read as
`stratumLocalMass K p`; at a non-prime index both sides are `0`. -/
theorem jointReductionOmegaEulerFactor_sub_one (Λ : Finset ReductionData) (p : ℕ) (u : Λ → ℂ) :
    jointReductionOmegaEulerFactor Λ p u - 1
      = ∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * (u K - 1) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [jointReductionOmegaEulerFactor_of_prime]
    simp only [stratumLocalMass_of_prime, mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  · rw [jointReductionOmegaEulerFactor_of_not_prime hp]
    simp [stratumLocalMass_of_not_prime _ hp]

/-- For every index `p : ℕ`, `F_{Λ,p}(𝐮) = 1 + ∑_{K ∈ Λ} δ_p(K)(u_K - 1)`, with `δ_p(K)` read as
`stratumLocalMass K p`. -/
theorem jointReductionOmegaEulerFactor_eq_one_add (Λ : Finset ReductionData) (p : ℕ)
    (u : Λ → ℂ) :
    jointReductionOmegaEulerFactor Λ p u
      = 1 + ∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * (u K - 1) :=
  sub_eq_iff_eq_add'.mp (jointReductionOmegaEulerFactor_sub_one Λ p u)

/-- For a prime `p` and every `𝐮 ∈ ℂ^Λ`,
`1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K = 1 + ∑_{K ∈ Λ} δ_p(K)(u_K - 1)`, where the left-hand
side is the local factor `jointReductionOmegaEulerFactor Λ p 𝐮` and the densities are read in `ℂ`
through `ENNReal.toReal`. -/
@[bsd_tamagawa "T040j"]
theorem jointReductionOmegaEulerFactor_eq_one_add_of_prime {Λ : Finset ReductionData} (p : ℕ)
    [Fact p.Prime] (u : Λ → ℂ) :
    jointReductionOmegaEulerFactor Λ p u
      = 1 + ∑ K : ↥Λ, ((deltaP p (K : ReductionData)).toReal : ℂ) * (u K - 1) := by
  rw [jointReductionOmegaEulerFactor_eq_one_add]
  simp only [stratumLocalMass_of_prime]

/-! ### The compact set enters only through a bound on the coordinates `‖u_K - 1‖` -/

/-- For a compact `E ⊆ ℂ^Λ` there is `R > 0` with `‖u_K - 1‖ ≤ R` for every `𝐮 ∈ E` and every
`K ∈ Λ`. -/
theorem exists_pos_forall_norm_coord_sub_one_le {Λ : Finset ReductionData} {E : Set (Λ → ℂ)}
    (hE : IsCompact E) : ∃ R : ℝ, 0 < R ∧ ∀ u ∈ E, ∀ K : ↥Λ, ‖u K - 1‖ ≤ R := by
  obtain ⟨R, hR0, hRsub⟩ := hE.isBounded.subset_closedBall_lt 0 1
  refine ⟨R, hR0, fun u hu K => ?_⟩
  calc ‖u K - 1‖ = dist (u K) ((1 : Λ → ℂ) K) := by simp [dist_eq_norm]
    _ ≤ dist u (1 : Λ → ℂ) := dist_le_pi_dist u 1 K
    _ ≤ R := Metric.mem_closedBall.mp (hRsub hu)

/-- If `‖u_K - 1‖ ≤ R` for every `K ∈ Λ`, then `‖∑_{K ∈ Λ} δ_p(K)(u_K - 1)‖ ≤ ∑_{K ∈ Λ} δ_p(K) R`.
-/
theorem norm_sum_stratumLocalMass_mul_le {Λ : Finset ReductionData} {R : ℝ} (p : ℕ)
    {u : Λ → ℂ} (hu : ∀ K : ↥Λ, ‖u K - 1‖ ≤ R) :
    ‖∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * (u K - 1)‖
      ≤ ∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p * R := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun K _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (stratumLocalMass_nonneg _ p)]
  exact mul_le_mul_of_nonneg_left (hu K) (stratumLocalMass_nonneg _ p)

/-- If `Λ` avoids `𝒦₀`, then `∑_p ∑_{K ∈ Λ} δ_p(K) R < ∞` for every real `R`. -/
theorem summable_sum_stratumLocalMass {Λ : Finset ReductionData} (hΛ : Admissible Λ) (R : ℝ) :
    Summable fun p : ℕ => ∑ K : ↥Λ, stratumLocalMass (K : ReductionData) p * R :=
  summable_sum (s := Finset.univ) fun K _ =>
    (summable_stratumLocalMass (hΛ (K : ReductionData) K.2)).mul_right R

/-! ### Summability of the suprema over a compact set -/

/-- For every compact `E ⊆ ℂ^Λ`, `∑_{p ∈ 𝒫} sup_{𝐮 ∈ E} |∑_{K ∈ Λ} δ_p(K)(u_K - 1)| < ∞`, the
supremum being the real `⨆` over `E` (equal to `0` when `E` is empty). -/
@[bsd_tamagawa "T040j"]
theorem summable_iSup_norm_sum_stratumLocalMass_mul {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) {E : Set (Λ → ℂ)} (hE : IsCompact E) :
    Summable fun p : ℕ => ⨆ v : E,
      ‖∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ)
        * ((v : Λ → ℂ) K - 1)‖ := by
  obtain ⟨R, hR0, hR⟩ := exists_pos_forall_norm_coord_sub_one_le hE
  exact Summable.of_nonneg_of_le (fun p => Real.iSup_nonneg fun _ => norm_nonneg _)
    (fun p => Real.iSup_le (fun v => norm_sum_stratumLocalMass_mul_le p (hR _ v.2))
      (Finset.sum_nonneg fun K _ => mul_nonneg (stratumLocalMass_nonneg _ p) hR0.le))
    (summable_sum_stratumLocalMass hΛ R)

/-! ### Absolute and locally uniform convergence -/

/-- At every `𝐮 ∈ ℂ^Λ` the family of joint local Euler factors `(F_{Λ,p}(𝐮))_p` is multipliable:
the partial products `∏_{p ∈ S} F_{Λ,p}(𝐮)` over finite `S`, directed by inclusion, converge, so
the product is independent of the order of the factors. -/
@[bsd_tamagawa "T040j"]
theorem multipliable_jointReductionOmegaEulerFactor {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) (u : Λ → ℂ) :
    Multipliable fun p : ℕ => jointReductionOmegaEulerFactor Λ p u := by
  obtain ⟨R, hR0, hR⟩ :=
    exists_pos_forall_norm_coord_sub_one_le (E := ({u} : Set (Λ → ℂ))) isCompact_singleton
  refine (multipliable_one_add_of_summable (f := fun p : ℕ =>
      ∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * (u K - 1)) ?_).congr
    fun p => (jointReductionOmegaEulerFactor_eq_one_add Λ p u).symm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_sum_stratumLocalMass_mul_le p (hR u rfl))
    (summable_sum_stratumLocalMass hΛ R)

/-- For every compact `E ⊆ ℂ^Λ`, the partial products `∏_{p ∈ S} F_{Λ,p}(𝐮)` converge to `F_Λ(𝐮)`
uniformly on `E` as `S` increases through the finite subsets of the primes. -/
@[bsd_tamagawa "T040j"]
theorem hasProdUniformlyOn_jointReductionOmegaEulerFactor {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) {E : Set (Λ → ℂ)} (hE : IsCompact E) :
    HasProdUniformlyOn (jointReductionOmegaEulerFactor Λ)
      (jointReductionOmegaEulerProduct Λ) E := by
  obtain ⟨R, hR0, hR⟩ := exists_pos_forall_norm_coord_sub_one_le hE
  have key := Summable.hasProdUniformlyOn_one_add
    (f := fun (p : ℕ) (v : Λ → ℂ) =>
      ∑ K : ↥Λ, ((stratumLocalMass (K : ReductionData) p : ℝ) : ℂ) * (v K - 1)) hE
    (summable_sum_stratumLocalMass hΛ R)
    (Filter.Eventually.of_forall fun p _ hv => norm_sum_stratumLocalMass_mul_le p (hR _ hv))
    (fun _ => (continuous_finsetSum _ fun K _ =>
      continuous_const.mul ((continuous_apply K).sub continuous_const)).continuousOn)
  have h : HasProdUniformlyOn (jointReductionOmegaEulerFactor Λ)
      (fun v => ∏' p : ℕ, jointReductionOmegaEulerFactor Λ p v) E := by
    simpa only [← jointReductionOmegaEulerFactor_eq_one_add] using key
  exact h

/-- The partial products `∏_{p ∈ S} F_{Λ,p}(𝐮)` converge to `F_Λ(𝐮)` locally uniformly on all of
`ℂ^Λ`. -/
@[bsd_tamagawa "T040j"]
theorem hasProdLocallyUniformly_jointReductionOmegaEulerFactor {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) :
    HasProdLocallyUniformly (jointReductionOmegaEulerFactor Λ)
      (jointReductionOmegaEulerProduct Λ) :=
  hasProdLocallyUniformly_of_forall_compact fun _ hK =>
    hasProdUniformlyOn_jointReductionOmegaEulerFactor hΛ hK

/-! ### Restatements -/

/-- For every compact `E ⊆ ℂ^Λ`, the functions `S ↦ ∏_{p ∈ S} F_{Λ,p}(·)` tend to `F_Λ(·)`
uniformly on `E` along `atTop` on `Finset ℕ`. -/
theorem tendstoUniformlyOn_finsetProd_jointReductionOmegaEulerFactor
    {Λ : Finset ReductionData} (hΛ : Admissible Λ) {E : Set (Λ → ℂ)} (hE : IsCompact E) :
    TendstoUniformlyOn
      (fun S : Finset ℕ => fun v : Λ → ℂ => ∏ p ∈ S, jointReductionOmegaEulerFactor Λ p v)
      (jointReductionOmegaEulerProduct Λ) Filter.atTop E :=
  (hasProdUniformlyOn_jointReductionOmegaEulerFactor hΛ hE).tendstoUniformlyOn

/-- The family `(F_{Λ,p}(𝐮))_{p ∈ 𝒫}` indexed by the primes is multipliable. -/
theorem multipliable_jointReductionOmegaEulerFactor_primes {Λ : Finset ReductionData}
    (hΛ : Admissible Λ) (u : Λ → ℂ) :
    Multipliable fun p : {q : ℕ // q.Prime} => jointReductionOmegaEulerFactor Λ (p : ℕ) u := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      jointReductionOmegaEulerFactor Λ x u = 1 := fun x hx =>
    jointReductionOmegaEulerFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) u
  exact (Subtype.coe_injective.multipliable_iff hone).2
    (multipliable_jointReductionOmegaEulerFactor hΛ u)

end WeierstrassCurve
