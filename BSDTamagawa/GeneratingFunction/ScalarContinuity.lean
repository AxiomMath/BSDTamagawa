/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarUniformConvergence

/-!
# Continuity of the scalar Euler product on `𝒟₀`

The map `(s, w, 𝐳) ↦ ∏_{p ∈ 𝒫} h_p(s, w, 𝐳)` is continuous on the polydisc
`𝒟₀ = {Re(s) ≥ 0, |w| ≤ 1, |z_ℓ| ≤ 1 ∀ ℓ ∈ Π}`, as a uniform limit of continuous functions: each
factor `h_p` is a uniformly convergent series of continuous functions, and the partial products
converge to the Euler product uniformly on `𝒟₀`.

## Main results

* `WeierstrassCurve.continuousOn_scalarLocalFactor`: each factor `h_p` is continuous on `𝒟₀`.
* `WeierstrassCurve.continuousOn_prod_scalarLocalFactor`: each partial product `∏_{p ∈ S} h_p` is
  continuous on `𝒟₀`.
* `WeierstrassCurve.continuousOn_tprod_scalarLocalFactor`: the Euler product `∏'_p h_p` is
  continuous on `𝒟₀`.

## Implementation notes

The map `s ↦ (0 : ℂ) ^ (-s)` is discontinuous at `s = 0` in Mathlib's convention, so the scalar
weight `ψ_{s, w, 𝐳}(t)` is continuous in the parameters only for `t ≠ 0`. The `t = 0` term of the
series for `h_p` is nevertheless continuous, being identically `0` because `δ_p(0) = 0`.
-/

@[expose] public section

open Filter

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-! ### Continuity of the summand of the series for `h_p` -/

/-- For `t ≠ 0` the map `(s, w, 𝐳) ↦ ψ_{s, w, 𝐳}(t) = w^{Ω(t)} (∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}) t^{-s}` is
continuous on `ℂ × ℂ × ℂ^Π`. -/
lemma continuous_scalarWeight_of_ne_zero (P : Finset ℕ) {t : ℕ} (ht : t ≠ 0) :
    Continuous fun x : ℂ × ℂ × (P → ℂ) => scalarWeight P x.1 x.2.1 x.2.2 t := by
  have hw : Continuous fun x : ℂ × ℂ × (P → ℂ) => x.2.1 ^ ArithmeticFunction.cardFactors t :=
    (continuous_fst.comp continuous_snd).pow _
  have hz : Continuous fun x : ℂ × ℂ × (P → ℂ) =>
      multiMonomial (fun ℓ : P => padicValNat ℓ t) x.2.2 := by
    simp only [multiMonomial]
    exact continuous_finsetProd _ fun ℓ _ =>
      ((continuous_apply ℓ).comp (continuous_snd.comp continuous_snd)).pow _
  have hs : Continuous fun x : ℂ × ℂ × (P → ℂ) => (t : ℂ) ^ (-x.1) :=
    Continuous.const_cpow continuous_fst.neg (Or.inl (Nat.cast_ne_zero.mpr ht))
  simpa only [scalarWeight] using (hw.fun_mul hz).fun_mul hs

/-- For every `t : ℕ` the map `(s, w, 𝐳) ↦ δ_p(t) ψ_{s, w, 𝐳}(t)` is continuous; for `t = 0` it is
identically `0` since `δ_p(0) = 0`. -/
lemma continuous_δ_toReal_mul_scalarWeight (P : Finset ℕ) (p : ℕ) [Fact p.Prime] (t : ℕ) :
    Continuous fun x : ℂ × ℂ × (P → ℂ) =>
      ((δ p t).toReal : ℂ) * scalarWeight P x.1 x.2.1 x.2.2 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [δ_zero, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul]
    exact continuous_const
  · exact (continuous_scalarWeight_of_ne_zero P ht).const_mul _

/-! ### Each factor `h_p` is continuous on `𝒟₀` -/

/-- Each scalar local factor `(s, w, 𝐳) ↦ h_p(s, w, 𝐳)` is continuous on `𝒟₀`. -/
lemma continuousOn_scalarLocalFactor (P : Finset ℕ) (p : ℕ) :
    ContinuousOn (fun x : ℂ × ℂ × (P → ℂ) => scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (scalarParamRegion P) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hrw : (fun x : ℂ × ℂ × (P → ℂ) => scalarLocalFactor P p x.1 x.2.1 x.2.2)
        = fun x : ℂ × ℂ × (P → ℂ) =>
          ∑' t : ℕ, ((δ p t).toReal : ℂ) * scalarWeight P x.1 x.2.1 x.2.2 t :=
      funext fun x => scalarLocalFactor_eq_tsum_of_prime P p x.1 x.2.1 x.2.2
    rw [hrw]
    exact continuousOn_tsum (u := fun t : ℕ => (δ p t).toReal)
      (fun t => (continuous_δ_toReal_mul_scalarWeight P p t).continuousOn)
      (summable_δ_toReal p)
      fun t x hx => norm_δ_toReal_mul_scalarWeight_le P p hx.1 hx.2.1 hx.2.2 t
  · simp only [scalarLocalFactor_of_not_prime hp]
    exact continuousOn_const

/-! ### The partial products are continuous on `𝒟₀` -/

/-- Each partial product `(s, w, 𝐳) ↦ ∏_{p ∈ S} h_p(s, w, 𝐳)` is continuous on `𝒟₀`. -/
lemma continuousOn_prod_scalarLocalFactor (P S : Finset ℕ) :
    ContinuousOn (fun x : ℂ × ℂ × (P → ℂ) => ∏ p ∈ S, scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (scalarParamRegion P) :=
  continuousOn_finsetProd S fun p _ => continuousOn_scalarLocalFactor P p

/-! ### The Euler product is continuous on `𝒟₀` -/

/-- The map `(s, w, 𝐳) ↦ ∏_{p ∈ 𝒫} h_p(s, w, 𝐳)` is continuous on `𝒟₀`. (The product is over all of
`ℕ`, with `h_p = 1` at every non-prime index.) -/
@[bsd_tamagawa "T036l"]
theorem continuousOn_tprod_scalarLocalFactor (P : Finset ℕ) :
    ContinuousOn (fun x : ℂ × ℂ × (P → ℂ) => ∏' p : ℕ, scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (scalarParamRegion P) :=
  (tendstoUniformlyOn_prod_scalarLocalFactor P).continuousOn
    (Frequently.of_forall fun S => continuousOn_prod_scalarLocalFactor P S)

end WeierstrassCurve
