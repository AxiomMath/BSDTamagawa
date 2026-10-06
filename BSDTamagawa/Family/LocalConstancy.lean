/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceRun

/-!
# Local constancy of the local reduction datum `τ_p`

Fix a prime `p` and let `U_p := {(a₄, a₆) ∈ ℤ_p × ℤ_p | Δ(a₄, a₆) ≠ 0}` be the nonsingular locus of
the coefficient plane of short Weierstrass models over `ℤ_p`. The reduction datum
`(a₄, a₆) ↦ (Kodaira symbol, local Tamagawa number)` of `E(a₄, a₆)`, computed by Tate's algorithm,
is locally constant on `U_p`; consequently `f ∘ τ_p` is continuous on `U_p` for every `f : 𝒦 → ℂ`.

## Main definitions

* `BSDTamagawa.LocalConstancy.nonsingularLocus`: the set of coefficient pairs
  `(a₄, a₆) ∈ ℤ_p × ℤ_p` whose short model has nonzero discriminant.
* `BSDTamagawa.LocalConstancy.strat`: the Kodaira symbol and local Tamagawa number of the short
  model at a point of `nonsingularLocus`.

## Main results

* `BSDTamagawa.LocalConstancy.isLocallyConstant_strat`: `strat` is locally constant on
  `nonsingularLocus`.
* `BSDTamagawa.LocalConstancy.continuous_comp_strat`: for every `f : 𝒦 → ℂ`, the map `f ∘ strat` is
  continuous on `nonsingularLocus`.

## Implementation notes

Only the reduction datum is locally constant, not the whole `TateAlgorithm.Output`: its minimal
model varies with `(a₄, a₆)`. The continuity statement is often made for bounded `f`; boundedness
plays no role, so `continuous_comp_strat` assumes nothing about `f`.
-/

@[expose] public section

open WeierstrassCurve BSDTamagawa.LocalReduction

namespace BSDTamagawa.LocalConstancy

/-! ### Congruence of short models is divisibility of the two coefficient differences -/

/-- Two short Weierstrass models are congruent to depth `n` as soon as their `a₄`'s and their
`a₆`'s differ by multiples of `ϖ ^ n`: the remaining three coefficients of a short model are `0`,
so those components of `WeierstrassCurve.congrDepth_iff_sub_mem` are trivial. -/
theorem congrDepth_ofShortNF_of_dvd {R : Type*} [CommRing R] (ϖ : R) (n : ℕ)
    {a₄ a₆ a₄' a₆' : R} (h₄ : ϖ ^ n ∣ a₄ - a₄') (h₆ : ϖ ^ n ∣ a₆ - a₆') :
    CongrDepth ϖ n (ofShortNF a₄ a₆) (ofShortNF a₄' a₆') := by
  rw [congrDepth_iff_sub_mem]
  exact ⟨by simp, by simp, by simp, Ideal.mem_span_singleton.mpr h₄,
    Ideal.mem_span_singleton.mpr h₆⟩

variable (p : ℕ) [Fact p.Prime]

/-- `U_p`: coefficient pairs over `ℤ_p` giving a nonsingular short model. -/
def nonsingularLocus : Set (ℤ_[p] × ℤ_[p]) := {x | (ofShortNF x.1 x.2).Δ ≠ 0}

/-- The local reduction datum of a point of `U_p`: the Kodaira symbol and the local Tamagawa number
returned by Tate's algorithm at the uniformizer `(p : ℤ_p)` on the short model
`y² = x³ + a₄ x + a₆`. -/
noncomputable def strat (x : ↥(nonsingularLocus p)) : ReductionData :=
  let o := TateAlgorithm.run (W := ofShortNF x.val.1 x.val.2)
             PadicInt.uniformizer_ne_zero x.property
  (o.kodairaSymbol, o.tamagawaNumber)

/-! ### `p`-adic balls and divisibility -/

private theorem pow_dvd_sub_of_dist_lt {n : ℕ} {a b : ℤ_[p]}
    (h : dist a b < (p : ℝ) ^ (-n : ℤ)) : (p : ℤ_[p]) ^ n ∣ a - b := by
  rw [dist_eq_norm] at h
  exact Ideal.mem_span_singleton.mp ((PadicInt.norm_le_pow_iff_mem_span_pow _ n).mp h.le)

private theorem strat_eq_of_dvd (x y : ↥(nonsingularLocus p))
    (h₄ : (p : ℤ_[p]) ^ (multiplicity (p : ℤ_[p]) (ofShortNF x.val.1 x.val.2).Δ + 1) ∣
      x.val.1 - y.val.1)
    (h₆ : (p : ℤ_[p]) ^ (multiplicity (p : ℤ_[p]) (ofShortNF x.val.1 x.val.2).Δ + 1) ∣
      x.val.2 - y.val.2) :
    strat p x = strat p y := by
  have h := TateAlgorithm.run_finite_determination (W := ofShortNF x.val.1 x.val.2)
    (W' := ofShortNF y.val.1 y.val.2) PadicInt.uniformizer_ne_zero x.property y.property
    (congrDepth_ofShortNF_of_dvd _ _ h₄ h₆)
  simp only [strat, Prod.mk.injEq]
  exact ⟨h.1, h.2⟩

/-! ### Local constancy -/

/-- On the nonsingular locus `U_p ⊆ ℤ_p × ℤ_p`, the map sending `(a₄, a₆)` to the Kodaira symbol
and local Tamagawa number of `E(a₄, a₆)` — Tate's algorithm at `p` — is locally constant for the
subspace topology inherited from the product of the `p`-adic topologies. -/
@[bsd_tamagawa "T031"]
theorem isLocallyConstant_strat : IsLocallyConstant (strat p) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  set n : ℕ := multiplicity (p : ℤ_[p]) (ofShortNF x.val.1 x.val.2).Δ + 1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hε : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos hp0 _
  refine ⟨Subtype.val ⁻¹' (Metric.ball x.val.1 ((p : ℝ) ^ (-n : ℤ)) ×ˢ
      Metric.ball x.val.2 ((p : ℝ) ^ (-n : ℤ))),
    (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage continuous_subtype_val,
    ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hε⟩, fun y hy => ?_⟩
  obtain ⟨hy₁, hy₂⟩ := hy
  exact (strat_eq_of_dvd p x y (pow_dvd_sub_of_dist_lt p (Metric.mem_ball'.mp hy₁))
    (pow_dvd_sub_of_dist_lt p (Metric.mem_ball'.mp hy₂))).symm

/-- For every `f : 𝒦 → ℂ`, the composition `f ∘ τ_p` is continuous on `U_p` (no boundedness of `f`
is needed). -/
@[bsd_tamagawa "T031"]
theorem continuous_comp_strat (f : ReductionData → ℂ) :
    Continuous (fun x : ↥(nonsingularLocus p) => f (strat p x)) :=
  ((isLocallyConstant_strat p).comp f).continuous

end BSDTamagawa.LocalConstancy
