/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GeneratingFunction.ScalarMultipliable

/-!
# Uniform convergence of the scalar Euler product on `𝒟₀`

The partial products `(∏_{p ∈ S} h_p)_S`, indexed by the finite sets `S ⊆ ℕ` directed by inclusion,
converge to `∏_p h_p` uniformly on the region
`𝒟₀ = {(s, w, 𝐳) : Re(s) ≥ 0, |w| ≤ 1, |z_ℓ| ≤ 1 ∀ ℓ ∈ Π}`, and hence uniformly on every subset of
`𝒟₀`. The proof is the Weierstrass `M`-test with the parameter-free majorant `M_p = 2(1 - δ_p(1))`:
for finite `S ⊆ T`,
`‖∏_{p ∈ T} h_p - ∏_{p ∈ S} h_p‖ ≤ (exp ∑_p M_p) (exp (∑_{p ∈ T \ S} M_p) - 1)`.

## Main definitions

* `WeierstrassCurve.scalarParamRegion`: the region `𝒟₀ ⊆ ℂ × ℂ × ℂ^Π`.

## Main results

* `WeierstrassCurve.mem_scalarParamRegion`: membership in `𝒟₀` is the conjunction of the three
  inequalities `Re(s) ≥ 0`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1`.
* `WeierstrassCurve.tendstoUniformlyOn_prod_scalarLocalFactor`: the net of partial products tends
  to `∏'_p h_p` uniformly on `𝒟₀`.
* `WeierstrassCurve.hasProdUniformlyOn_scalarLocalFactor`: `HasProdUniformlyOn` for the family
  `p ↦ h_p` on `𝒟₀`.
* `WeierstrassCurve.hasProdUniformlyOn_scalarLocalFactor_of_subset`: the same on every subset of
  `𝒟₀`.

## Implementation notes

Mathlib's `Summable.hasProdUniformlyOn_one_add` does not apply, since `𝒟₀` is not compact, and
neither does `hasProdUniformlyOn_of_clog`, since `h_p` is not known to be nonzero on `𝒟₀` at small
primes; the `M`-test is therefore run directly.
-/

@[expose] public section

open Filter

open scoped Topology

namespace WeierstrassCurve

/-! ### The region `𝒟₀` -/

/-- The parameter region `𝒟₀`: for a finite set of primes `Π`,
`𝒟₀ = {(s, w, 𝐳) ∈ ℂ × ℂ × ℂ^Π : Re(s) ≥ 0, |w| ≤ 1, |z_ℓ| ≤ 1 for all ℓ ∈ Π}`, the face `Λ = ∅`,
`u = 1` of the polydisc `𝒟`. -/
def scalarParamRegion (P : Finset ℕ) : Set (ℂ × ℂ × (P → ℂ)) :=
  {x | 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ∀ ℓ : P, ‖x.2.2 ℓ‖ ≤ 1}

/-- A parameter tuple `(s, w, 𝐳)` lies in `𝒟₀` exactly when `0 ≤ s.re`, `‖w‖ ≤ 1` and `‖z ℓ‖ ≤ 1`
for all `ℓ`. -/
lemma mem_scalarParamRegion {P : Finset ℕ} {s w : ℂ} {z : P → ℂ} :
    (s, w, z) ∈ scalarParamRegion P ↔ 0 ≤ s.re ∧ ‖w‖ ≤ 1 ∧ ∀ ℓ : P, ‖z ℓ‖ ≤ 1 :=
  Iff.rfl

/-! ### The parameter-free majorant `M_p = 2(1 - δ_p(1))` -/

/-- The majorant `M_p = 2(1 - δ_p(1))` is nonnegative. -/
lemma two_mul_tamagawaLocalTailMass_nonneg (p : ℕ) : 0 ≤ 2 * tamagawaLocalTailMass p := by
  have := tamagawaLocalTailMass_nonneg p
  linarith

/-- The majorant is summable: `∑_p 2(1 - δ_p(1)) < ∞`. -/
lemma summable_two_mul_tamagawaLocalTailMass :
    Summable fun p : ℕ => 2 * tamagawaLocalTailMass p :=
  summable_tamagawaLocalTailMass.mul_left 2

/-- For every `p : ℕ` and every `x ∈ 𝒟₀`, `‖h_p(x) - 1‖ ≤ 2(1 - δ_p(1))`, the right-hand side being
free of the parameters (and both sides being `0` at a non-prime index). -/
lemma norm_scalarLocalFactor_sub_one_le_tailMass (P : Finset ℕ) (p : ℕ)
    {x : ℂ × ℂ × (P → ℂ)} (hx : x ∈ scalarParamRegion P) :
    ‖scalarLocalFactor P p x.1 x.2.1 x.2.2 - 1‖ ≤ 2 * tamagawaLocalTailMass p := by
  obtain ⟨hs, hw, hz⟩ := hx
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [tamagawaLocalTailMass_of_prime]
    exact norm_scalarLocalFactor_sub_one_le P p hs hw hz
  · simp [scalarLocalFactor_of_not_prime hp, tamagawaLocalTailMass_of_not_prime hp]

/-! ### The two uniform estimates -/

/-- For every finite set `S` and every point of `𝒟₀`, `‖∏_{p ∈ S} h_p‖ ≤ exp (∑_p M_p)`. -/
lemma norm_prod_scalarLocalFactor_le (P : Finset ℕ) {x : ℂ × ℂ × (P → ℂ)}
    (hx : x ∈ scalarParamRegion P) (S : Finset ℕ) :
    ‖∏ p ∈ S, scalarLocalFactor P p x.1 x.2.1 x.2.2‖
      ≤ Real.exp (∑' p : ℕ, 2 * tamagawaLocalTailMass p) := by
  obtain ⟨s, w, z⟩ := x
  calc ‖∏ p ∈ S, scalarLocalFactor P p s w z‖
      ≤ ∏ p ∈ S, ‖scalarLocalFactor P p s w z‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ S, (1 + 2 * tamagawaLocalTailMass p) := by
        refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
        have hdev : ‖scalarLocalFactor P p s w z - 1‖ ≤ 2 * tamagawaLocalTailMass p :=
          norm_scalarLocalFactor_sub_one_le_tailMass P p hx
        have hsplit : ‖scalarLocalFactor P p s w z‖
            ≤ ‖scalarLocalFactor P p s w z - 1‖ + 1 := by
          simpa using norm_le_norm_sub_add (scalarLocalFactor P p s w z) (1 : ℂ)
        linarith
    _ ≤ Real.exp (∑ p ∈ S, 2 * tamagawaLocalTailMass p) :=
        Real.prod_one_add_le_exp_sum S two_mul_tamagawaLocalTailMass_nonneg
    _ ≤ Real.exp (∑' p : ℕ, 2 * tamagawaLocalTailMass p) :=
        Real.exp_le_exp.mpr (summable_two_mul_tamagawaLocalTailMass.sum_le_tsum _
          fun p _ => two_mul_tamagawaLocalTailMass_nonneg p)

/-- For finite `S ⊆ T` and every `x ∈ 𝒟₀`,
`‖∏_{p ∈ T} h_p - ∏_{p ∈ S} h_p‖ ≤ (exp ∑_p M_p) (exp (∑_{p ∈ T \ S} M_p) - 1)`, with
`M_p = 2(1 - δ_p(1))`. -/
lemma norm_prod_scalarLocalFactor_sub_prod_le (P : Finset ℕ) {x : ℂ × ℂ × (P → ℂ)}
    (hx : x ∈ scalarParamRegion P) {S T : Finset ℕ} (hST : S ⊆ T) :
    ‖(∏ p ∈ T, scalarLocalFactor P p x.1 x.2.1 x.2.2)
        - ∏ p ∈ S, scalarLocalFactor P p x.1 x.2.1 x.2.2‖
      ≤ Real.exp (∑' p : ℕ, 2 * tamagawaLocalTailMass p)
        * (Real.exp (∑ p ∈ T \ S, 2 * tamagawaLocalTailMass p) - 1) := by
  classical
  obtain ⟨s, w, z⟩ := x
  have hsplit : ∏ p ∈ T, scalarLocalFactor P p s w z
      = (∏ p ∈ S, scalarLocalFactor P p s w z)
        * ∏ p ∈ T \ S, scalarLocalFactor P p s w z := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hST]
  have htail : ‖(∏ p ∈ T \ S, scalarLocalFactor P p s w z) - 1‖
      ≤ Real.exp (∑ p ∈ T \ S, 2 * tamagawaLocalTailMass p) - 1 := by
    have hMathlib := Finset.norm_prod_one_add_sub_one_le (T \ S)
      fun p => scalarLocalFactor P p s w z - 1
    simp only [add_sub_cancel] at hMathlib
    have hsum : ∑ p ∈ T \ S, ‖scalarLocalFactor P p s w z - 1‖
        ≤ ∑ p ∈ T \ S, 2 * tamagawaLocalTailMass p :=
      Finset.sum_le_sum fun p _ => norm_scalarLocalFactor_sub_one_le_tailMass P p hx
    linarith [Real.exp_le_exp.mpr hsum]
  rw [hsplit, ← mul_sub_one]
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_prod_scalarLocalFactor_le P hx S) htail
    (norm_nonneg _) (Real.exp_nonneg _))

/-! ### Uniform convergence -/

/-- The net `S ↦ ∏_{p ∈ S} h_p`, over the finite sets `S ⊆ ℕ` directed by inclusion, tends to
`∏'_p h_p` uniformly on `𝒟₀`. -/
theorem tendstoUniformlyOn_prod_scalarLocalFactor (P : Finset ℕ) :
    TendstoUniformlyOn
      (fun (S : Finset ℕ) (x : ℂ × ℂ × (P → ℂ)) =>
        ∏ p ∈ S, scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (fun x : ℂ × ℂ × (P → ℂ) => ∏' p : ℕ, scalarLocalFactor P p x.1 x.2.1 x.2.2)
      atTop (scalarParamRegion P) := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hnhds : {y : ℝ | Real.exp (∑' p : ℕ, 2 * tamagawaLocalTailMass p) * (Real.exp y - 1)
      < ε / 2} ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt
        (fun y : ℝ => Real.exp (∑' p : ℕ, 2 * tamagawaLocalTailMass p) * (Real.exp y - 1)) 0 := by
      fun_prop
    have hzero : (fun y : ℝ =>
        Real.exp (∑' p : ℕ, 2 * tamagawaLocalTailMass p) * (Real.exp y - 1)) 0 = 0 := by
      simp
    exact hcont.preimage_mem_nhds (hzero ▸ Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  obtain ⟨S₀, hS₀⟩ := summable_two_mul_tamagawaLocalTailMass.vanishing hnhds
  filter_upwards [eventually_ge_atTop S₀] with S hS x hx
  obtain ⟨s, w, z⟩ := x
  obtain ⟨hs, hw, hz⟩ := hx
  have hfinite : ∀ T : Finset ℕ, S ⊆ T →
      ‖(∏ p ∈ T, scalarLocalFactor P p s w z)
        - ∏ p ∈ S, scalarLocalFactor P p s w z‖ ≤ ε / 2 := fun T hT =>
    (norm_prod_scalarLocalFactor_sub_prod_le P ⟨hs, hw, hz⟩ hT).trans
      (le_of_lt (hS₀ (T \ S) (Finset.disjoint_left.mpr fun p hp hp₀ =>
        (Finset.mem_sdiff.mp hp).right (Finset.mem_of_subset hS hp₀))))
  have hlimit : ‖(∏' p : ℕ, scalarLocalFactor P p s w z)
      - ∏ p ∈ S, scalarLocalFactor P p s w z‖ ≤ ε / 2 := by
    have htendsto : Tendsto
        (fun T : Finset ℕ => ∏ p ∈ T, scalarLocalFactor P p s w z) atTop
        (𝓝 (∏' p : ℕ, scalarLocalFactor P p s w z)) :=
      (multipliable_scalarLocalFactor P hs hw hz).hasProd
    refine le_of_tendsto ((htendsto.sub_const _).norm) ?_
    filter_upwards [eventually_ge_atTop S] with T hT using hfinite T hT
  rw [dist_eq_norm]
  linarith

/-- The partial products `(∏_{p ∈ S} h_p)_S`, indexed by the finite sets `S ⊆ ℕ` directed by
inclusion, converge to `∏_p h_p` uniformly on `𝒟₀`. (The index type is `ℕ`, and `h_p = 1` at every
non-prime index.) -/
@[bsd_tamagawa "T036k"]
theorem hasProdUniformlyOn_scalarLocalFactor (P : Finset ℕ) :
    HasProdUniformlyOn
      (fun (p : ℕ) (x : ℂ × ℂ × (P → ℂ)) => scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (fun x : ℂ × ℂ × (P → ℂ) => ∏' p : ℕ, scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (scalarParamRegion P) :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (tendstoUniformlyOn_prod_scalarLocalFactor P)

/-- The partial products of the scalar Euler product converge uniformly on every subset of `𝒟₀`. -/
@[bsd_tamagawa "T036k"]
theorem hasProdUniformlyOn_scalarLocalFactor_of_subset (P : Finset ℕ)
    {s : Set (ℂ × ℂ × (P → ℂ))} (hs : s ⊆ scalarParamRegion P) :
    HasProdUniformlyOn
      (fun (p : ℕ) (x : ℂ × ℂ × (P → ℂ)) => scalarLocalFactor P p x.1 x.2.1 x.2.2)
      (fun x : ℂ × ℂ × (P → ℂ) => ∏' p : ℕ, scalarLocalFactor P p x.1 x.2.1 x.2.2) s :=
  (hasProdUniformlyOn_scalarLocalFactor P).mono hs

end WeierstrassCurve
