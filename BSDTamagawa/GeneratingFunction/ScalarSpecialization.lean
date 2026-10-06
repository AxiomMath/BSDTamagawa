/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.MasterEulerProduct
public import BSDTamagawa.GeneratingFunction.ScalarUniformConvergence
public import BSDTamagawa.GeneratingFunction.LocalFactorCollapse
public import BSDTamagawa.GeneratingFunction.KodairaMonomial

/-!
# The scalar specialization of the master Euler product

For a finite set of primes `Π` and `(s, w, 𝐳) ∈ 𝒟₀`,

`lim_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} ψ_{s, w, 𝐳}(Tam(E)) = ∏_{p ∈ 𝒫} h_p(s, w, 𝐳)`,

the limit on the left existing. Here `ψ_{s, w, 𝐳}` is the scalar weight, `h_p` the scalar local
factor, `Ht` and `N(X)` the height and counting function, and `Tam(E)` the Tamagawa product. This
is the master Euler product at `Λ = ∅` and `u = 1`.

## Main results

* `WeierstrassCurve.tamagawaGeneratingFunction_eq_scalarWeightSum`: the generating function
  `𝒵_{∅, Π, X}(s; 1, w, 𝐳, ())` is the empirical average of `ψ_{s, w, 𝐳}(Tam(E))`.
* `WeierstrassCurve.tprod_scalarLocalFactor_primes`: `∏'_{p ∈ 𝒫} h_p = ∏'_{p : ℕ} h_p` on `𝒟₀`.
* `WeierstrassCurve.tendsto_scalarWeightSum_tprod_scalarLocalFactor`: the limit formula above.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex

/-! ### The left-hand side: `𝒵_{∅, Π, X}(s; 1, w, 𝐳, ())` is the empirical average of `ψ` -/

open scoped Classical in
/-- The generating function at `Λ = ∅`, `u = 1` is the empirical average of the scalar weight:

`𝒵_{∅, Π, X}(s; 1, w, 𝐳, ()) = (1/N(X)) ∑_{Ht(E) ≤ X} ψ_{s, w, 𝐳}(Tam(E))`. -/
theorem tamagawaGeneratingFunction_eq_scalarWeightSum (P : Finset ℕ) (s w : ℂ) (z : P → ℂ)
    (uΛ : (∅ : Finset ReductionData) → ℂ) (X : ℝ) :
    tamagawaGeneratingFunction ∅ P s 1 w z uΛ X =
      (∑' q : ℤ × ℤ, if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
          scalarWeight P s w z (tamagawaProduct q.1 q.2) else 0) /
        (integralShortNFCount X : ℂ) := by
  rw [tamagawaGeneratingFunction]
  congr 1
  refine tsum_congr fun q => ?_
  by_cases hq : (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily
  · rw [ite_eq_left hq, ite_eq_left hq, scalarWeight, kodairaMonomial_empty, one_pow, one_mul,
      mul_one]
    rfl
  · rw [ite_eq_right hq, ite_eq_right hq]

/-! ### The right-hand side: `∏' p : ℕ` is the product over the primes -/

/-- For `(s, w, 𝐳) ∈ 𝒟₀`, `∏'_{p ∈ 𝒫} h_p(s, w, 𝐳) = ∏'_{p : ℕ} h_p(s, w, 𝐳)`. -/
theorem tprod_scalarLocalFactor_primes (P : Finset ℕ) {s w : ℂ} {z : P → ℂ} (hs : 0 ≤ s.re)
    (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    ∏' p : {q : ℕ // q.Prime}, scalarLocalFactor P (p : ℕ) s w z
      = ∏' p : ℕ, scalarLocalFactor P p s w z := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      scalarLocalFactor P x s w z = 1 := fun x hx =>
    scalarLocalFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) s w z
  exact ((Subtype.coe_injective.hasProd_iff hone).2
    (multipliable_scalarLocalFactor P hs hw hz).hasProd).tprod_eq

/-! ### The limit formula -/

open scoped Classical in
/-- Let `Π` be a finite set of primes and `(s, w, 𝐳) ∈ 𝒟₀`, that is, `Re(s) ≥ 0`, `‖w‖ ≤ 1` and
`‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`. Then the limit on the left exists and

`lim_{X → ∞} (1/N(X)) ∑_{Ht(E) ≤ X} ψ_{s, w, 𝐳}(Tam(E)) = ∏_{p ∈ 𝒫} h_p(s, w, 𝐳)`. -/
@[bsd_tamagawa "T036m"]
theorem tendsto_scalarWeightSum_tprod_scalarLocalFactor (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {s w : ℂ} {z : P → ℂ}
    (hx : (s, w, z) ∈ scalarParamRegion P) (uΛ : (∅ : Finset ReductionData) → ℂ) :
    Tendsto (fun X : ℝ =>
        (∑' q : ℤ × ℤ,
            if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
              scalarWeight P s w z (tamagawaProduct q.1 q.2) else 0) /
          (integralShortNFCount X : ℂ))
      atTop (𝓝 (∏' p : ℕ, scalarLocalFactor P p s w z)) := by
  have huΛ : ∀ K : (∅ : Finset ReductionData), ‖uΛ K‖ ≤ 1 :=
    fun K => (Finset.notMem_empty _ K.2).elim
  have h := tendsto_tamagawaGeneratingFunction_tprod_localFactor ∅ P (by simp) hP hx.1
    (by simp : ‖(1 : ℂ)‖ ≤ 1) hx.2.1 hx.2.2 huΛ
  have hfac : ∀ p : {q : ℕ // q.Prime},
      ((@β (p : ℕ) ⟨p.2⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((@deltaP (p : ℕ) ⟨p.2⟩ (K : ReductionData)).toReal : ℂ)
            * localWeight ∅ P (K : ReductionData) s 1 w z uΛ
        = scalarLocalFactor P (p : ℕ) s w z := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact localFactor_eq_scalarLocalFactor P (p : ℕ) uΛ hx.1 hx.2.1 hx.2.2
  rw [tprod_congr hfac, tprod_scalarLocalFactor_primes P hx.1 hx.2.1 hx.2.2] at h
  exact h.congr fun X => tamagawaGeneratingFunction_eq_scalarWeightSum P s w z uΛ X

end WeierstrassCurve
