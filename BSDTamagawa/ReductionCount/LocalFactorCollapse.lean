/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.LocalWeightTrivial
public import BSDTamagawa.PrimeCount.LocalFactorCollapse

/-!
# Collapse of the master local factor at `Π = ∅`, `u = w = 1`, `s = 0`

For a finite `Λ ⊆ 𝒦 ∖ 𝒦₀`, a prime `p` and a Kodaira-parameter vector `𝐮 = (u_K)_{K ∈ Λ} ∈ ℂ^Λ`,

  `β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, 1, 1, ∅, 𝐮)`
  `  = 1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K`,

where `β_p` is the trivial-stratum mass `WeierstrassCurve.β`, `δ_p(K)` the local reduction density
`WeierstrassCurve.deltaP` and `Φ_p` the local weight `WeierstrassCurve.localWeight`. On this face
`Φ_p(K)` is `u_K` for `K ∈ Λ` and `1` otherwise, so the summand is `δ_p(K)` plus a correction
supported on `Λ`; the densities sum to `1` over `𝒦`, and the `𝒦₀` block of the sum is `β_p`.

## Main definitions

* `WeierstrassCurve.kodairaCorrection`: the `Λ`-supported correction `[K ∈ Λ] · δ_p(K)(u_K - 1)`.

## Main results

* `WeierstrassCurve.localWeight_face_of_mem`, `WeierstrassCurve.localWeight_face_of_not_mem`: on
  this face `Φ_p` is `u_K` for `K ∈ Λ` and `1` otherwise.
* `WeierstrassCurve.localFactor_collapse_kodaira`: the identity above.

## Implementation notes

The sum over `𝒦 ∖ 𝒦₀ = 𝒦₀ᶜ` is a `tsum`, its `δ_p`-support being infinite; the sums over `Λ` are
`Finset` sums over `↥Λ`. The densities are coerced to `ℂ` by `ENNReal.toReal` followed by
`Complex.ofReal`, and `1 - ∑_{K ∈ Λ} δ_p(K)` is a subtraction in `ℂ` after that coercion; in
`ℝ≥0∞` it would truncate.
-/

@[expose] public section

open Function MeasureTheory BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam
  BSDTamagawa.MultiIndex

namespace WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

/-! ### The Kodaira indicator monomial -/

open scoped Classical in
/-- `∏_{K' ∈ Λ} u_{K'}^{𝟙[K = K']} = u_K` when `K ∈ Λ`. -/
lemma multiMonomial_indicator_of_mem {Λ : Finset (KodairaSymbol × ℕ)} {K : KodairaSymbol × ℕ}
    (h : K ∈ Λ) (uΛ : Λ → ℂ) :
    multiMonomial (fun K' : Λ => if K = (K' : KodairaSymbol × ℕ) then 1 else 0) uΛ
      = uΛ ⟨K, h⟩ := by
  have hone : ∀ b : ↥Λ, b ∈ (Finset.univ : Finset ↥Λ) → b ≠ ⟨K, h⟩ →
      uΛ b ^ (if K = (b : KodairaSymbol × ℕ) then 1 else 0) = 1 := by
    intro b _ hb
    have hne : K ≠ (b : KodairaSymbol × ℕ) := fun hKb => hb (Subtype.ext hKb.symm)
    rw [ite_eq_right hne, pow_zero]
  rw [multiMonomial, Finset.prod_eq_single_of_mem (⟨K, h⟩ : ↥Λ) (Finset.mem_univ _) hone]
  simp

open scoped Classical in
/-- `∏_{K' ∈ Λ} u_{K'}^{𝟙[K = K']} = 1` when `K ∉ Λ`. -/
lemma multiMonomial_indicator_of_not_mem {Λ : Finset (KodairaSymbol × ℕ)}
    {K : KodairaSymbol × ℕ} (h : K ∉ Λ) (uΛ : Λ → ℂ) :
    multiMonomial (fun K' : Λ => if K = (K' : KodairaSymbol × ℕ) then 1 else 0) uΛ = 1 := by
  rw [multiMonomial]
  refine Finset.prod_eq_one fun b _ => ?_
  have hne : K ≠ (b : KodairaSymbol × ℕ) := fun hKb => h (by rw [hKb]; exact b.2)
  rw [ite_eq_right hne, pow_zero]

/-! ### The local weight on the face `Π = ∅`, `u = w = 1`, `s = 0` -/

open scoped Classical in
/-- At `Π = ∅`, `u = w = 1`, `s = 0`, the local weight is the Kodaira indicator monomial:
`Φ_p(K; 0, 1, 1, ∅, 𝐮) = ∏_{K' ∈ Λ} u_{K'}^{𝟙[K = K']}`. -/
lemma localWeight_kodairaFace (Λ : Finset (KodairaSymbol × ℕ)) (K : KodairaSymbol × ℕ)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) :
    localWeight Λ ∅ K 0 1 1 z uΛ
      = multiMonomial (fun K' : Λ => if K = (K' : KodairaSymbol × ℕ) then 1 else 0) uΛ := by
  rw [localWeight]
  simp [multiMonomial]

/-- `Φ_p(K; 0, 1, 1, ∅, 𝐮) = u_K` for `K ∈ Λ`. -/
lemma localWeight_face_of_mem {Λ : Finset (KodairaSymbol × ℕ)} {K : KodairaSymbol × ℕ}
    (h : K ∈ Λ) (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) :
    localWeight Λ ∅ K 0 1 1 z uΛ = uΛ ⟨K, h⟩ := by
  rw [localWeight_kodairaFace, multiMonomial_indicator_of_mem h]

/-- `Φ_p(K; 0, 1, 1, ∅, 𝐮) = 1` for `K ∉ Λ`. -/
lemma localWeight_face_of_not_mem {Λ : Finset (KodairaSymbol × ℕ)} {K : KodairaSymbol × ℕ}
    (h : K ∉ Λ) (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) :
    localWeight Λ ∅ K 0 1 1 z uΛ = 1 := by
  rw [localWeight_kodairaFace, multiMonomial_indicator_of_not_mem h]

/-! ### The `Λ`-supported correction -/

open scoped Classical in
/-- The `Λ`-supported correction `[K ∈ Λ] · δ_p(K)(u_K - 1)`: the difference between the summand
`δ_p(K) Φ_p(K; 0, 1, 1, ∅, 𝐮)` and the density `δ_p(K)`. -/
noncomputable def kodairaCorrection (Λ : Finset (KodairaSymbol × ℕ)) (uΛ : Λ → ℂ)
    (K : KodairaSymbol × ℕ) : ℂ :=
  if h : K ∈ Λ then ((deltaP p K).toReal : ℂ) * (uΛ ⟨K, h⟩ - 1) else 0

/-- The correction `kodairaCorrection` sums to `∑_{K ∈ Λ} δ_p(K)(u_K - 1)`. -/
lemma hasSum_kodairaCorrection (Λ : Finset (KodairaSymbol × ℕ)) (uΛ : Λ → ℂ) :
    HasSum (kodairaCorrection p Λ uΛ)
      (∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * (uΛ K - 1)) := by
  have hzero : ∀ K ∉ Λ, kodairaCorrection p Λ uΛ K = 0 := by
    intro K hK
    rw [kodairaCorrection, dite_eq_right hK]
  have hval : ∑ K ∈ Λ, kodairaCorrection p Λ uΛ K
      = ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * (uΛ K - 1) := by
    rw [← Finset.sum_coe_sort Λ (kodairaCorrection p Λ uΛ)]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [kodairaCorrection, dite_eq_left K.2]
  rw [← hval]
  exact hasSum_sum_of_ne_finset_zero hzero

/-- On the face `Π = ∅`, `u = w = 1`, `s = 0`,
`δ_p(K) Φ_p(K; 0, 1, 1, ∅, 𝐮) = δ_p(K) + [K ∈ Λ] · δ_p(K)(u_K - 1)`. -/
lemma deltaP_mul_localWeight_face (Λ : Finset (KodairaSymbol × ℕ))
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) :
    (fun K : KodairaSymbol × ℕ => ((deltaP p K).toReal : ℂ) * localWeight Λ ∅ K 0 1 1 z uΛ)
      = fun K : KodairaSymbol × ℕ =>
          ((deltaP p K).toReal : ℂ) + kodairaCorrection p Λ uΛ K := by
  classical
  funext K
  by_cases hK : K ∈ Λ
  · rw [localWeight_face_of_mem hK, kodairaCorrection, dite_eq_left hK]; ring
  · rw [localWeight_face_of_not_mem hK, kodairaCorrection, dite_eq_right hK]; ring

/-! ### The collapse -/

/-- For a finite `Λ ⊆ 𝒦 ∖ 𝒦₀`, a prime `p` and every Kodaira-parameter vector `𝐮 = (u_K)_{K ∈ Λ}`
in `ℂ^Λ`,
`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, 1, 1, ∅, 𝐮) = 1 - ∑_{K ∈ Λ} δ_p(K) + ∑_{K ∈ Λ} δ_p(K) u_K`,
with `β_p` the trivial-stratum mass, `δ_p(K)` the local reduction density and `Φ_p` the local
weight. -/
@[bsd_tamagawa "T040i"]
theorem localFactor_collapse_kodaira {Λ : Finset (KodairaSymbol × ℕ)} (hΛ : Admissible Λ)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : Λ → ℂ) :
    ((β p).toReal : ℂ)
        + ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
            ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
              * localWeight Λ ∅ (K : KodairaSymbol × ℕ) 0 1 1 z uΛ
      = 1 - ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
          + ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * uΛ K := by
  have h1 : HasSum (fun K : KodairaSymbol × ℕ => ((deltaP p K).toReal : ℂ)) 1 := by
    simpa [Function.comp_def] using
      (hasSum_deltaP_toReal p).map Complex.ofRealHom Complex.continuous_ofReal
  have htot : HasSum (fun K : KodairaSymbol × ℕ =>
      ((deltaP p K).toReal : ℂ) * localWeight Λ ∅ K 0 1 1 z uΛ)
      (1 + ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * (uΛ K - 1)) := by
    rw [deltaP_mul_localWeight_face p Λ z uΛ]
    exact h1.add (hasSum_kodairaCorrection p Λ uΛ)
  have hK0 : ∑' K : ↥(K0 : Set (KodairaSymbol × ℕ)),
      (((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
        * localWeight Λ ∅ (K : KodairaSymbol × ℕ) 0 1 1 z uΛ) = ((β p).toReal : ℂ) := by
    rw [tsum_subtype_K0 (M := ℂ) fun K => ((deltaP p K).toReal : ℂ)
        * localWeight Λ ∅ K 0 1 1 z uΛ,
      localWeight_eq_one Λ ∅ (show (KodairaSymbol.I 0, 1) ∈ K0 by simp [K0]) hΛ 0 1 1 z uΛ,
      localWeight_eq_one Λ ∅ (show (KodairaSymbol.I 1, 1) ∈ K0 by simp [K0]) hΛ 0 1 1 z uΛ,
      β_add, ENNReal.toReal_add (deltaP_ne_top p _) (deltaP_ne_top p _)]
    push_cast
    ring
  rw [← hK0, htot.summable.tsum_subtype_add_tsum_subtype_compl K0, htot.tsum_eq]
  have hsplit : ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * (uΛ K - 1)
      = ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) * uΛ K
        - ∑ K : ↥Λ, ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun K _ => by ring
  rw [hsplit]
  ring

end WeierstrassCurve
