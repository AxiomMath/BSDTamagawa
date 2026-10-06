/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.GeneratingFunctionIdentity

/-!
# Existence and the joint generating function of `Q_Π`

Let `Π` be a finite set of primes. For each multi-index `𝐣 = (j_ℓ)_{ℓ ∈ Π} ∈ ℤ_{≥0}^Π` the density

`Q_Π(𝐣) := lim_{X → ∞} #{E : Ht(E) ≤ X, v_ℓ(Tam(E)) = j_ℓ for all ℓ ∈ Π} / N(X)`

exists, and for `|z_ℓ| ≤ 1`

`∑_{𝐣 ∈ ℤ_{≥0}^Π} Q_Π(𝐣) 𝐳^𝐣 = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)})`,

the Euler product converging absolutely and uniformly on the closed unit polydisc. Here `E` ranges
over the Weierstrass models `E(a₄, a₆)` with `Δ(E) ≠ 0`, `Ht` is the naive height, `N` the counting
function, `Tam` the Tamagawa product, `v_ℓ = padicValNat ℓ` the `ℓ`-adic valuation, and `δ_p(t)`
the scalar local density.

## Main results

* `WeierstrassCurve.tendsto_tamagawaValuationCount_div_integralShortNFCount`: the proportion of
  integral short Weierstrass models of height at most `X` with `v_ℓ(Tam(E)) = j_ℓ` for all `ℓ ∈ Π`
  tends to `Q_Π(𝐣)` as `X → ∞`.
* `WeierstrassCurve.tsum_tamagawaValuationDensity_mul_multiMonomial_eq_tprod_primes`: the joint
  generating function `∑_𝐣 Q_Π(𝐣) 𝐳^𝐣` equals the Euler product over the primes on the closed unit
  polydisc.
* `WeierstrassCurve.multipliable_tamagawaValuationEulerFactor_primes`: the family of local factors
  is multipliable at every point of the closed unit polydisc.
* `WeierstrassCurve.summable_norm_tamagawaValuationEulerFactor_sub_one_primes`: the deviations
  `‖h_p - 1‖` of the local factors are summable over the primes on the closed unit polydisc.
* `WeierstrassCurve.hasProdUniformlyOn_tamagawaValuationEulerFactor_primes`: the Euler product
  converges uniformly on the closed unit polydisc.
* `WeierstrassCurve.scalarLocalFactor_zero_one_of_prime`: the scalar local factor at `s = 0`,
  `w = 1` is `h_p(0, 1, 𝐳) = ∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}`.

## Implementation notes

The inner sum `∑_{t ≥ 1}` is written `∑' t : ℕ`, which is the same sum since `δ_p(0) = 0`. The
`ℝ≥0∞`-valued density `δ_p(t)` enters `ℂ` as `((δ_p(t)).toReal : ℂ)`, so the differences `h_p - 1`
are taken in `ℂ`. The Euler product is a `tprod` indexed by the subtype `{q : ℕ // q.Prime}`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-! ### Reindexing a uniformly convergent product to a subtype of its index set -/

/-- If every index outside `{n // p n}` contributes the factor `1` and the `ℕ`-indexed product
converges uniformly on `E` to `g`, then the product over `{n // p n}` converges uniformly on `E` to
`g`. -/
private lemma hasProdUniformlyOn_primes_of_eq_one {M β : Type*} [CommMonoid M] [UniformSpace M]
    {f : ℕ → β → M} {g : β → M} {E : Set β} {p : ℕ → Prop}
    (hone : ∀ n, ¬ p n → f n = 1) (h : HasProdUniformlyOn f g E) :
    HasProdUniformlyOn (fun q : {n : ℕ // p n} => f (q : ℕ)) g E := by
  classical
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at h ⊢
  intro v hv
  obtain ⟨S, hS⟩ := eventually_atTop.1 (h v hv)
  refine eventually_atTop.2 ⟨S.subtype p, fun T hT x hx => ?_⟩
  have hneutral : ∀ n ∈ T.image (Subtype.val : {n : ℕ // p n} → ℕ) ∪ S,
      n ∉ T.image (Subtype.val : {n : ℕ // p n} → ℕ) → f n x = 1 := fun n hn hn' =>
    congrFun (hone n fun hp => hn' (Finset.mem_image.2
      ⟨⟨n, hp⟩, hT (Finset.mem_subtype.2 ((Finset.mem_union.1 hn).resolve_left hn')), rfl⟩)) x
  have hprod : ∏ q ∈ T, f (q : ℕ) x
      = ∏ n ∈ T.image (Subtype.val : {n : ℕ // p n} → ℕ) ∪ S, f n x :=
    (Finset.prod_image fun a _ b _ hab => Subtype.coe_injective hab).symm.trans
      (Finset.prod_subset Finset.subset_union_left hneutral)
  change (g x, ∏ q ∈ T, f (q : ℕ) x) ∈ v
  rw [hprod]
  exact hS _ Finset.subset_union_right x hx

/-! ### The local factor at `s = 0`, `w = 1` -/

/-- At a prime `p`, the scalar local factor at `s = 0`, `w = 1` is

`h_p(0, 1, 𝐳) = ∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}`,

the sum being written over all of `ℕ`. -/
theorem scalarLocalFactor_zero_one_of_prime (P : Finset ℕ) (p : ℕ) [Fact p.Prime] (z : P → ℂ) :
    scalarLocalFactor P p 0 1 z
      = ∑' t : ℕ, ((δ p t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t := by
  rw [scalarLocalFactor_eq_tsum_of_prime]
  exact tsum_congr fun t => by rw [scalarWeight_zero_one, multiMonomial]

/-- For `‖z_ℓ‖ ≤ 1` at every `ℓ ∈ Π`,

`∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}) = ∏'_{p : ℕ} h_p(0, 1, 𝐳)`. -/
theorem tprod_tamagawaValuationEulerFactor_primes (P : Finset ℕ) {z : P → ℂ}
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    ∏' p : {q : ℕ // q.Prime},
        (∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
      = ∏' p : ℕ, scalarLocalFactor P p 0 1 z := by
  rw [← tprod_scalarLocalFactor_primes P (by simp) (by simp) hz]
  refine tprod_congr fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact (scalarLocalFactor_zero_one_of_prime P (p : ℕ) z).symm

/-! ### The density exists -/

/-- Let `Π` be a finite set of primes. For every multi-index `𝐣 ∈ ℤ_{≥0}^Π`,

`lim_{X → ∞} #{E : Ht(E) ≤ X, Δ(E) ≠ 0, v_ℓ(Tam(E)) = j_ℓ ∀ ℓ ∈ Π} / N(X) = Q_Π(𝐣)`.

The numerator counts the pairs `(a₄, a₆) ∈ ℤ²` whose short Weierstrass model is nonsingular, has
naive height at most `X`, and whose Tamagawa product has `ℓ`-adic valuation exactly `j_ℓ` at every
`ℓ ∈ Π`; the denominator is `N(X)`. -/
@[bsd_tamagawa "T044a"]
theorem tendsto_tamagawaValuationCount_div_integralShortNFCount (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (j : P → ℕ) :
    Tendsto (fun X : ℝ =>
        ({q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          ∀ ℓ : P, tamagawaValuationVector P q.1 q.2 ℓ = j ℓ}.ncard : ℝ) /
          integralShortNFCount X)
      atTop (𝓝 (tamagawaValuationDensity P j)) :=
  tendsto_tamagawaValuationProportion_tamagawaValuationDensity P hP j

/-! ### The joint generating function -/

/-- For every `𝐳` in the closed unit polydisc, the family `(Q_Π(𝐣) 𝐳^𝐣)_{𝐣 ∈ ℤ_{≥0}^Π}` is summable
with sum `∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)})`. -/
theorem hasSum_tamagawaValuationDensity_mul_multiMonomial_tprod_primes (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {z : P → ℂ} (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    HasSum (fun j : P → ℕ => ((tamagawaValuationDensity P j : ℝ) : ℂ) * multiMonomial j z)
      (∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) := by
  rw [tprod_tamagawaValuationEulerFactor_primes P hz,
    ← tsum_tamagawaValuationDensity_mul_multiMonomial P hP hz]
  exact (Summable.of_norm (summable_norm_tamagawaValuationDensity_mul_multiMonomial P hP hz)).hasSum

/-- Let `Π` be a finite set of primes and `𝐳 ∈ ℂ^Π` with `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`. Then

`∑_{𝐣 ∈ ℤ_{≥0}^Π} Q_Π(𝐣) 𝐳^𝐣 = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)})`,

with `Q_Π(𝐣)` the joint density, `𝐳^𝐣` the multi-monomial, `δ_p(t)` the scalar local density
entering `ℂ` as `((δ_p(t)).toReal : ℂ)`, and `v_ℓ = padicValNat ℓ`. -/
@[bsd_tamagawa "T044a"]
theorem tsum_tamagawaValuationDensity_mul_multiMonomial_eq_tprod_primes (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) {z : P → ℂ} (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    ∑' j : P → ℕ, ((tamagawaValuationDensity P j : ℝ) : ℂ) * multiMonomial j z
      = ∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t :=
  (hasSum_tamagawaValuationDensity_mul_multiMonomial_tprod_primes P hP hz).tsum_eq

/-! ### Absolute and uniform convergence on the closed unit polydisc -/

/-- At every `𝐳` with `‖z_ℓ‖ ≤ 1` for all `ℓ ∈ Π` the family of local factors
`(∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)})_{p ∈ 𝒫}` is `Multipliable`. -/
@[bsd_tamagawa "T044a"]
theorem multipliable_tamagawaValuationEulerFactor_primes (P : Finset ℕ) {z : P → ℂ}
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t :=
  (multipliable_scalarLocalFactor_primes P (s := 0) (w := 1) (by simp) (by simp) hz).congr
    fun p => by
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact scalarLocalFactor_zero_one_of_prime P (p : ℕ) z

/-- At every `𝐳` with `‖z_ℓ‖ ≤ 1` for all `ℓ ∈ Π`,

`∑_{p ∈ 𝒫} ‖(∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)}) - 1‖ < ∞`. -/
@[bsd_tamagawa "T044a"]
theorem summable_norm_tamagawaValuationEulerFactor_sub_one_primes (P : Finset ℕ) {z : P → ℂ}
    (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Summable fun p : {q : ℕ // q.Prime} =>
      ‖(∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t) - 1‖ :=
  (((summable_scalarLocalFactor_sub_one P (s := 0) (w := 1) (by simp) (by simp)
    hz).subtype Nat.Prime).congr fun p => by
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact congrArg (· - 1) (scalarLocalFactor_zero_one_of_prime P (p : ℕ) z)).norm

/-- The partial products `(∏_{p ∈ S} h_p(0, 1, 𝐳))_S` over the finite sets `S ⊆ ℕ`, directed by
inclusion, converge to `∏'_p h_p(0, 1, 𝐳)` uniformly on the closed unit polydisc
`{𝐳 : ‖z_ℓ‖ ≤ 1 ∀ ℓ ∈ Π}`. -/
theorem hasProdUniformlyOn_scalarLocalFactor_zero_one (P : Finset ℕ) :
    HasProdUniformlyOn (fun (p : ℕ) (z : P → ℂ) => scalarLocalFactor P p 0 1 z)
      (fun z : P → ℂ => ∏' p : ℕ, scalarLocalFactor P p 0 1 z)
      {z : P → ℂ | ∀ ℓ : P, ‖z ℓ‖ ≤ 1} := by
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  refine TendstoUniformlyOn.mono
    ((hasProdUniformlyOn_iff_tendstoUniformlyOn.1
      (hasProdUniformlyOn_scalarLocalFactor P)).comp
        (fun z : P → ℂ => ((0 : ℂ), (1 : ℂ), z))) fun z hz => ?_
  exact mem_scalarParamRegion.2 ⟨by simp, by simp, hz⟩

/-- The partial products

`∏_{p ∈ S} (∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ Π} z_ℓ^{v_ℓ(t)})`

over the finite sets `S` of primes, directed by inclusion, converge to the Euler product uniformly
on the closed unit polydisc `{𝐳 : ‖z_ℓ‖ ≤ 1 ∀ ℓ ∈ Π}`. -/
@[bsd_tamagawa "T044a"]
theorem hasProdUniformlyOn_tamagawaValuationEulerFactor_primes (P : Finset ℕ) :
    HasProdUniformlyOn
      (fun (p : {q : ℕ // q.Prime}) (z : P → ℂ) =>
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
      (fun z : P → ℂ => ∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : P, z ℓ ^ padicValNat ℓ t)
      {z : P → ℂ | ∀ ℓ : P, ‖z ℓ‖ ≤ 1} := by
  have h := hasProdUniformlyOn_primes_of_eq_one (p := Nat.Prime)
    (fun n hn => funext fun z => scalarLocalFactor_of_not_prime hn 0 1 z)
    (hasProdUniformlyOn_scalarLocalFactor_zero_one P)
  refine (h.congr (Eventually.of_forall fun T z _ =>
      Finset.prod_congr rfl fun q _ => ?_)).congr_right
    fun z hz => (tprod_tamagawaValuationEulerFactor_primes P hz).symm
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact scalarLocalFactor_zero_one_of_prime P (q : ℕ) z

end WeierstrassCurve
