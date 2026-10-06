/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.PrimeSquareTail
public import BSDTamagawa.LocalDensity.BoundedLocalProduct
public import BSDTamagawa.GeneratingFunction.TruncatedIdentity

/-!
# Absolute convergence of the master Euler product

For the master local factor

  `L_p(s; u, w, 𝐳, 𝐮) = β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, u, w, 𝐳, 𝐮)`,

where `β_p` is the trivial-stratum mass (`WeierstrassCurve.β`), `δ_p(K)` the local reduction
density (`WeierstrassCurve.deltaP`), `Φ_p` the local weight (`WeierstrassCurve.localWeight`) and
`𝒦₀ = {(I₀, 1), (I₁, 1)}`, and the closed parameter polydisc
`𝒟 = {Re(s) ≥ 0, |u| ≤ 1, |w| ≤ 1, |z_ℓ| ≤ 1, |u_K| ≤ 1}`:

* `sup_𝒟 |L_p - 1| ≤ 18/p²` at every prime;
* `∑_p sup_𝒟 |L_p - 1| < ∞`;
* the Euler product `∏_p L_p` converges absolutely on `𝒟`;
* the convergence is uniform on `𝒟`, hence on every compact subset of it.

## Main definitions

* `WeierstrassCurve.masterLocalFactor`: the factor `L_p`, as an `ℕ`-indexed family equal to `1`
  off the primes.

## Main results

* `WeierstrassCurve.norm_masterLocalFactor_sub_one_le_of_bound`: if `‖Φ_p‖ ≤ M`, then
  `|L_p - 1| ≤ 9(M + 1)/p²`.
* `WeierstrassCurve.exists_sup_norm_masterLocalFactor_sub_one_le`:
  `∃ C > 0, ∃ p₀, sup_𝒟 |L_p - 1| ≤ C/p²` for `p ≥ p₀`, with `C = 18`, `p₀ = 2`.
* `WeierstrassCurve.summable_iSup_norm_masterLocalFactor_sub_one`:
  `∑_p sup_{x ∈ D} |L_p(x) - 1| < ∞` for every `D ⊆ 𝒟`.
* `WeierstrassCurve.multipliable_masterLocalFactor`: absolute convergence of `∏_p L_p` at every
  point of `𝒟`.
* `WeierstrassCurve.multipliable_masterLocalFactor_primes`: the same for the product indexed by
  the primes.
* `WeierstrassCurve.hasProdUniformlyOn_masterLocalFactor`: uniform convergence of the net of
  partial products on every `D ⊆ 𝒟`.

## Implementation notes

The polydisc `𝒟` is not given a Lean definition: pointwise statements carry the five inequalities
as hypotheses, and the statements about a supremum or about uniformity are made for an arbitrary
set `D` of tuples `(s, u, w, 𝐳, 𝐮) : ℂ × ℂ × ℂ × ℂ^Π × ℂ^Λ` satisfying them. Since the majorant
`18/p²` is independent of the parameters, uniformity holds on all of `𝒟`, without compactness.
-/

@[expose] public section

open Filter

open scoped Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam BSDTamagawa.PrimeSqTail

/-! ### The master local factor `L_p` -/

/-- The master local factor: for a finite set `Λ` of reduction data, a finite set of primes `Π`,
an index `p : ℕ` and parameters `s, u, w : ℂ`, `𝐳 = (z_ℓ)_{ℓ ∈ Π}`, `𝐮 = (u_K)_{K ∈ Λ}`,

  `L_p := β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, u, w, 𝐳, 𝐮)`

at a prime index, and `1` at every other index. The sum is a `tsum` over the subtype `𝒦₀ᶜ`, and the
densities are coerced to `ℂ` through `ENNReal.toReal`. -/
noncomputable def masterLocalFactor (Λ : Finset ReductionData) (P : Finset ℕ) (p : ℕ)
    (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) : ℂ :=
  if h : p.Prime then
    ((@β p ⟨h⟩).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
      ((@deltaP p ⟨h⟩ (K : ReductionData)).toReal : ℂ)
        * localWeight Λ P (K : ReductionData) s u w z uΛ
  else 1

/-- At a prime index the master local factor is `β_p + ∑_{K ∉ 𝒦₀} δ_p(K) Φ_p(K; s, u, w, 𝐳, 𝐮)`. -/
lemma masterLocalFactor_of_prime (Λ : Finset ReductionData) (P : Finset ℕ) (p : ℕ) [Fact p.Prime]
    (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) :
    masterLocalFactor Λ P p s u w z uΛ = ((β p).toReal : ℂ)
      + ∑' K : ↥(K0ᶜ : Set ReductionData), ((deltaP p (K : ReductionData)).toReal : ℂ)
        * localWeight Λ P (K : ReductionData) s u w z uΛ :=
  dite_eq_left Fact.out

/-- At a non-prime index the master local factor is `1`. -/
lemma masterLocalFactor_of_not_prime {Λ : Finset ReductionData} {P : Finset ℕ} {p : ℕ}
    (hp : ¬ p.Prime) (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) :
    masterLocalFactor Λ P p s u w z uΛ = 1 :=
  dite_eq_right hp

/-! ### The deviation `|L_p - 1|` at a prime -/

/-- If `b = 1 - T` with `0 ≤ T ≤ D`, `‖S‖ ≤ T · M` and `0 ≤ M`, then `‖b + S - 1‖ ≤ D(M + 1)`. -/
private lemma norm_ofReal_add_sub_one_le {b : ℝ} {S : ℂ} {T M D : ℝ} (hb : b = 1 - T)
    (hS : ‖S‖ ≤ T * M) (hT0 : 0 ≤ T) (hTD : T ≤ D) (hM : 0 ≤ M) :
    ‖(b : ℂ) + S - 1‖ ≤ D * (M + 1) := by
  rw [show ((b : ℂ) + S - 1) = S - (T : ℂ) by rw [hb]; push_cast; ring]
  calc ‖S - (T : ℂ)‖ ≤ ‖S‖ + ‖(T : ℂ)‖ := norm_sub_le _ _
    _ ≤ T * M + T := by rw [Complex.norm_of_nonneg hT0]; linarith
    _ = T * (M + 1) := by ring
    _ ≤ D * (M + 1) := mul_le_mul_of_nonneg_right hTD (by linarith)

/-- If `0 ≤ M` and `‖Φ_p(K; s, u, w, 𝐳, 𝐮)‖ ≤ M` for every `K ∈ 𝒦`, then at every prime `p`,
`‖L_p(s; u, w, 𝐳, 𝐮) - 1‖ ≤ 9(M + 1)/p²`. -/
theorem norm_masterLocalFactor_sub_one_le_of_bound (Λ : Finset ReductionData) (P : Finset ℕ)
    (p : ℕ) [Fact p.Prime] (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ K : ReductionData, ‖localWeight Λ P K s u w z uΛ‖ ≤ M) :
    ‖masterLocalFactor Λ P p s u w z uΛ - 1‖ ≤ 9 * (M + 1) / (p : ℝ) ^ 2 := by
  rw [masterLocalFactor_of_prime]
  refine (norm_ofReal_add_sub_one_le
    (T := ∑' K : ↥(K0ᶜ : Set ReductionData), (deltaP p (K : ReductionData)).toReal)
    (by linarith [β_toReal_add_tsum_compl_K0_toReal p])
    (norm_tsum_compl_K0_localWeight_le p s u w z uΛ hbdd)
    (tsum_nonneg fun _ => ENNReal.toReal_nonneg)
    (tsum_compl_K0_toReal_le_nine_div_sq p) hM).trans_eq (by ring)

/-- For parameters with `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` and `‖u_K‖ ≤ 1`, at every
prime `p`, `‖L_p(s; u, w, 𝐳, 𝐮) - 1‖ ≤ 18/p²`. -/
theorem norm_masterLocalFactor_sub_one_le_eighteen_div_sq (Λ : Finset ReductionData)
    (P : Finset ℕ) (p : ℕ) [Fact p.Prime] {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ}
    (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1)
    (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    ‖masterLocalFactor Λ P p s u w z uΛ - 1‖ ≤ 18 / (p : ℝ) ^ 2 :=
  (norm_masterLocalFactor_sub_one_le_of_bound Λ P p s u w z uΛ zero_le_one
    (norm_localWeight_le_one Λ P hs hu hw hz huΛ)).trans_eq (by norm_num)

/-! ### The parameter-free majorant `18 · primeSq p` -/

/-- `18 · primeSq p` is nonnegative. -/
lemma eighteen_mul_primeSq_nonneg (p : ℕ) : 0 ≤ 18 * primeSq p :=
  mul_nonneg (by norm_num) (primeSq_nonneg p)

/-- `∑_p 18 · primeSq p < ∞`. -/
lemma summable_eighteen_mul_primeSq : Summable fun p : ℕ => 18 * primeSq p :=
  summable_primeSq.mul_left 18

/-- For every `p : ℕ` and every parameter tuple in the polydisc, `‖L_p - 1‖ ≤ 18 · primeSq p`. -/
theorem norm_masterLocalFactor_sub_one_le_primeSq (Λ : Finset ReductionData) (P : Finset ℕ)
    (p : ℕ) {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    ‖masterLocalFactor Λ P p s u w z uΛ - 1‖ ≤ 18 * primeSq p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [show (18 : ℝ) * primeSq p = 18 / (p : ℝ) ^ 2 by rw [primeSq, ite_eq_left hp]; ring]
    exact norm_masterLocalFactor_sub_one_le_eighteen_div_sq Λ P p hs hu hw hz huΛ
  · rw [masterLocalFactor_of_not_prime hp, sub_self, norm_zero, primeSq, ite_eq_right hp]
    simp

/-! ### The per-prime sup bound -/

/-- There are constants `C > 0` and `p₀` such that, for every finite admissible `Λ`, every finite
set of primes `Π` and every parameter tuple `(s, u, w, 𝐳, 𝐮) ∈ 𝒟` — that is, `Re(s) ≥ 0`,
`‖u‖ ≤ 1`, `‖w‖ ≤ 1`, `‖z_ℓ‖ ≤ 1` and `‖u_K‖ ≤ 1` — `‖L_q(s; u, w, 𝐳, 𝐮) - 1‖ ≤ C/q²` for every
prime `q ≥ p₀`. The constants do not depend on `Λ`, `Π` or the parameters. -/
@[bsd_tamagawa "T036a"]
theorem exists_sup_norm_masterLocalFactor_sub_one_le :
    ∃ C : ℝ, ∃ p₀ : ℕ, 0 < C ∧
      ∀ (Λ : Finset ReductionData), Admissible Λ → ∀ (P : Finset ℕ) (s u w : ℂ) (z : P → ℂ)
        (uΛ : Λ → ℂ), 0 ≤ s.re → ‖u‖ ≤ 1 → ‖w‖ ≤ 1 → (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
        (∀ K : Λ, ‖uΛ K‖ ≤ 1) → ∀ q : ℕ, q.Prime → p₀ ≤ q →
          ‖masterLocalFactor Λ P q s u w z uΛ - 1‖ ≤ C / (q : ℝ) ^ 2 :=
  ⟨18, 2, by norm_num, fun Λ _ P s u w z uΛ hs hu hw hz huΛ q hq _ =>
    haveI : Fact q.Prime := ⟨hq⟩
    norm_masterLocalFactor_sub_one_le_eighteen_div_sq Λ P q hs hu hw hz huΛ⟩

/-! ### Summability of the suprema -/

/-- For every set `D` of parameter tuples contained in the polydisc `𝒟`, the family
`p ↦ sup_{x ∈ D} ‖L_p(x) - 1‖` is summable. -/
@[bsd_tamagawa "T036a"]
theorem summable_iSup_norm_masterLocalFactor_sub_one (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))}
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) :
    Summable fun p : ℕ => ⨆ x ∈ D,
      ‖masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 - 1‖ := by
  refine Summable.of_nonneg_of_le
    (fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _hx => norm_nonneg _)
    (fun p => Real.iSup_le (fun x => Real.iSup_le (fun hx => ?_) (eighteen_mul_primeSq_nonneg p))
      (eighteen_mul_primeSq_nonneg p))
    summable_eighteen_mul_primeSq
  obtain ⟨hs, hu, hw, hz, huΛ⟩ := hD x hx
  exact norm_masterLocalFactor_sub_one_le_primeSq Λ P p hs hu hw hz huΛ

/-! ### Absolute convergence of the Euler product -/

/-- At a point of `𝒟`, the family `p ↦ L_p(s; u, w, 𝐳, 𝐮) - 1` is summable. -/
theorem summable_masterLocalFactor_sub_one (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Summable fun p : ℕ => masterLocalFactor Λ P p s u w z uΛ - 1 :=
  summable_eighteen_mul_primeSq.of_norm_bounded fun p =>
    norm_masterLocalFactor_sub_one_le_primeSq Λ P p hs hu hw hz huΛ

/-- At every point of the polydisc `𝒟` the family `p ↦ L_p(s; u, w, 𝐳, 𝐮)` is multipliable. -/
@[bsd_tamagawa "T036a"]
theorem multipliable_masterLocalFactor (Λ : Finset ReductionData) (P : Finset ℕ) {s u w : ℂ}
    {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Multipliable fun p : ℕ => masterLocalFactor Λ P p s u w z uΛ :=
  (multipliable_one_add_of_summable
    (summable_masterLocalFactor_sub_one Λ P hs hu hw hz huΛ).norm).congr fun p => by ring

/-- At every point of the polydisc `𝒟`, the family `(L_p)_{p ∈ 𝒫}` indexed by the primes is
multipliable. -/
theorem multipliable_masterLocalFactor_primes (Λ : Finset ReductionData) (P : Finset ℕ)
    {s u w : ℂ} {z : P → ℂ} {uΛ : Λ → ℂ} (hs : 0 ≤ s.re) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (huΛ : ∀ K : Λ, ‖uΛ K‖ ≤ 1) :
    Multipliable fun p : {q : ℕ // q.Prime} => masterLocalFactor Λ P (p : ℕ) s u w z uΛ := by
  have hone : ∀ x ∉ Set.range (Subtype.val : {q : ℕ // q.Prime} → ℕ),
      masterLocalFactor Λ P x s u w z uΛ = 1 := fun x hx =>
    masterLocalFactor_of_not_prime (by simpa [Subtype.range_coe] using hx) s u w z uΛ
  exact (Subtype.coe_injective.multipliable_iff hone).mpr
    (multipliable_masterLocalFactor Λ P hs hu hw hz huΛ)

/-! ### Uniform convergence -/

/-- On `D ⊆ 𝒟`, every partial product `∏_{p ∈ S} L_p` has norm at most
`exp (∑_p 18 · primeSq p)`. -/
lemma norm_prod_masterLocalFactor_le (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))}
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1)
    {x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)} (hx : x ∈ D) (S : Finset ℕ) :
    ‖∏ p ∈ S, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2‖
      ≤ Real.exp (∑' p : ℕ, 18 * primeSq p) := by
  obtain ⟨s, u, w, z, uΛ⟩ := x
  obtain ⟨hs, hu, hw, hz, huΛ⟩ := hD _ hx
  calc ‖∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ‖
      ≤ ∏ p ∈ S, ‖masterLocalFactor Λ P p s u w z uΛ‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ S, (1 + 18 * primeSq p) := by
        refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
        have hdev := norm_masterLocalFactor_sub_one_le_primeSq Λ P p hs hu hw hz huΛ
        have hsplit : ‖masterLocalFactor Λ P p s u w z uΛ‖
            ≤ ‖masterLocalFactor Λ P p s u w z uΛ - 1‖ + 1 := by
          simpa using norm_le_norm_sub_add (masterLocalFactor Λ P p s u w z uΛ) (1 : ℂ)
        linarith
    _ ≤ Real.exp (∑ p ∈ S, 18 * primeSq p) :=
        Real.prod_one_add_le_exp_sum S eighteen_mul_primeSq_nonneg
    _ ≤ Real.exp (∑' p : ℕ, 18 * primeSq p) :=
        Real.exp_le_exp.mpr (summable_eighteen_mul_primeSq.sum_le_tsum _
          fun p _ => eighteen_mul_primeSq_nonneg p)

/-- For finite `S ⊆ T` and every `x ∈ D ⊆ 𝒟`,
`‖∏_{p ∈ T} L_p - ∏_{p ∈ S} L_p‖ ≤ (exp ∑_p M_p)(exp (∑_{p ∈ T ∖ S} M_p) - 1)`
with `M_p = 18 · primeSq p`. -/
lemma norm_prod_masterLocalFactor_sub_prod_le (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))}
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1)
    {x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)} (hx : x ∈ D) {S T : Finset ℕ} (hST : S ⊆ T) :
    ‖(∏ p ∈ T, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        - ∏ p ∈ S, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2‖
      ≤ Real.exp (∑' p : ℕ, 18 * primeSq p)
        * (Real.exp (∑ p ∈ T \ S, 18 * primeSq p) - 1) := by
  classical
  obtain ⟨s, u, w, z, uΛ⟩ := x
  obtain ⟨hs, hu, hw, hz, huΛ⟩ := hD _ hx
  have hsplit : ∏ p ∈ T, masterLocalFactor Λ P p s u w z uΛ
      = (∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ)
        * ∏ p ∈ T \ S, masterLocalFactor Λ P p s u w z uΛ := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hST]
  have htail : ‖(∏ p ∈ T \ S, masterLocalFactor Λ P p s u w z uΛ) - 1‖
      ≤ Real.exp (∑ p ∈ T \ S, 18 * primeSq p) - 1 := by
    have hM := Finset.norm_prod_one_add_sub_one_le (T \ S)
      fun p => masterLocalFactor Λ P p s u w z uΛ - 1
    simp only [add_sub_cancel] at hM
    have hsum : ∑ p ∈ T \ S, ‖masterLocalFactor Λ P p s u w z uΛ - 1‖
        ≤ ∑ p ∈ T \ S, 18 * primeSq p :=
      Finset.sum_le_sum fun p _ =>
        norm_masterLocalFactor_sub_one_le_primeSq Λ P p hs hu hw hz huΛ
    linarith [Real.exp_le_exp.mpr hsum]
  rw [hsplit, ← mul_sub_one]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_prod_masterLocalFactor_le Λ P hD hx S) htail (norm_nonneg _)
      (Real.exp_nonneg _))

/-- For every `D ⊆ 𝒟` the net `S ↦ ∏_{p ∈ S} L_p`, over the finite sets `S ⊆ ℕ` directed by
inclusion, tends to `∏'_p L_p` uniformly on `D`. -/
theorem tendstoUniformlyOn_prod_masterLocalFactor (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))}
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) :
    TendstoUniformlyOn
      (fun (S : Finset ℕ) (x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)) =>
        ∏ p ∈ S, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ) =>
        ∏' p : ℕ, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      atTop D := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hnhds : {y : ℝ | Real.exp (∑' p : ℕ, 18 * primeSq p) * (Real.exp y - 1) < ε / 2}
      ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt
        (fun y : ℝ => Real.exp (∑' p : ℕ, 18 * primeSq p) * (Real.exp y - 1)) 0 := by fun_prop
    have hzero : (fun y : ℝ =>
        Real.exp (∑' p : ℕ, 18 * primeSq p) * (Real.exp y - 1)) 0 = 0 := by simp
    exact hcont.preimage_mem_nhds (hzero ▸ Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  obtain ⟨S₀, hS₀⟩ := summable_eighteen_mul_primeSq.vanishing hnhds
  filter_upwards [eventually_ge_atTop S₀] with S hS x hx
  obtain ⟨s, u, w, z, uΛ⟩ := x
  have hfinite : ∀ T : Finset ℕ, S ⊆ T →
      ‖(∏ p ∈ T, masterLocalFactor Λ P p s u w z uΛ)
        - ∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ‖
      ≤ ε / 2 := fun T hT =>
    (norm_prod_masterLocalFactor_sub_prod_le Λ P hD hx hT).trans
      (hS₀ (T \ S) (Finset.disjoint_left.mpr fun p hp hp₀ =>
        (Finset.mem_sdiff.mp hp).right (hS hp₀))).le
  have hlimit : ‖(∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ)
      - ∏ p ∈ S, masterLocalFactor Λ P p s u w z uΛ‖ ≤ ε / 2 := by
    obtain ⟨hs, hu, hw, hz, huΛ⟩ := hD _ hx
    have htendsto : Tendsto
        (fun T : Finset ℕ => ∏ p ∈ T, masterLocalFactor Λ P p s u w z uΛ) atTop
        (𝓝 (∏' p : ℕ, masterLocalFactor Λ P p s u w z uΛ)) :=
      (multipliable_masterLocalFactor Λ P hs hu hw hz huΛ).hasProd
    refine le_of_tendsto ((htendsto.sub_const _).norm) ?_
    filter_upwards [eventually_ge_atTop S] with T hT using hfinite T hT
  rw [dist_eq_norm]
  linarith

/-- For every set `D` of parameter tuples contained in the polydisc `𝒟`, the partial products
`(∏_{p ∈ S} L_p)_S`, indexed by the finite sets `S` directed by inclusion, converge to `∏_p L_p`
uniformly on `D`; in particular on every compact subset of `𝒟`. -/
@[bsd_tamagawa "T036a"]
theorem hasProdUniformlyOn_masterLocalFactor (Λ : Finset ReductionData) (P : Finset ℕ)
    {D : Set (ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ))}
    (hD : ∀ x ∈ D, 0 ≤ x.1.re ∧ ‖x.2.1‖ ≤ 1 ∧ ‖x.2.2.1‖ ≤ 1 ∧
      (∀ ℓ : P, ‖x.2.2.2.1 ℓ‖ ≤ 1) ∧ ∀ K : Λ, ‖x.2.2.2.2 K‖ ≤ 1) :
    HasProdUniformlyOn
      (fun (p : ℕ) (x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ)) =>
        masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x : ℂ × ℂ × ℂ × (P → ℂ) × (Λ → ℂ) =>
        ∏' p : ℕ, masterLocalFactor Λ P p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      D :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr
    (tendstoUniformlyOn_prod_masterLocalFactor Λ P hD)

end WeierstrassCurve
