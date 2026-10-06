/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Valuation.JointDensity
public import BSDTamagawa.Valuation.LawProbability

/-!
# The density of Tamagawa products prime to a finite set of primes

For a finite set `A` of primes, let `P = P_A = ∑_𝐣 Q_A(𝐣) δ_𝐣` be the limiting joint law of the
valuations `(v_ℓ(Tam(E)))_{ℓ ∈ A}` of the Tamagawa product of short Weierstrass curves ordered by
height, a probability measure on `ℤ_{≥0}^A`. Then

`P(ℓ ∤ Tam(E) for all ℓ ∈ A) = ∏_{p ∈ 𝒫} (∑_{t ≥ 1, (t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t))`,

where `δ_p(t)` is the local density of Tamagawa number `t` at `p`, and the Euler product converges.
The identity is the joint generating-function identity `∑_𝐣 Q_A(𝐣) 𝐳^𝐣 = ∏_p h_p(𝐳)` evaluated at
`𝐳 = 𝟎`, with the convention `0^0 = 1`.

## Main results

* `WeierstrassCurve.tsum_δ_mul_zero_pow_eq_ofReal_tsum_coprime`: at `𝐳 = 𝟎` the local factor is
  `∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ A} 0^{v_ℓ(t)} = ∑_{t ≥ 1, (t, ∏_ℓ ℓ) = 1} δ_p(t)`.
* `WeierstrassCurve.setOf_forall_eq_zero_eq_singleton`: the event `{𝐣 : j_ℓ = 0 ∀ ℓ ∈ A}` is the
  singleton `{𝟎}`.
* `WeierstrassCurve.hasProd_coprimeDensity_primes`: the restricted Euler product converges, with
  value `Q_A(𝟎)`.
* `WeierstrassCurve.multipliable_coprimeDensity_primes`: the restricted Euler product converges.
* `WeierstrassCurve.tamagawaValuationMeasure_notDvd_toReal`: the density formula.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-! ### Convergence of a real product read off its complex image -/

/-- If the family `(↑(f i))_{i}` of complex numbers has product `L`, then the real family `f` has
product `L.re`. -/
private lemma hasProd_real_of_hasProd_ofReal {ι : Type*} {f : ι → ℝ} {L : ℂ}
    (h : HasProd (fun i => (f i : ℂ)) L) : HasProd f L.re :=
  ((Complex.continuous_re.tendsto L).comp h).congr fun s => by
    rw [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]

/-! ### The local factor at `𝐳 = 𝟎` -/

/-- For a finite set `A` of primes, the family `t ↦ δ_p(t) ∏_{ℓ ∈ A} 0^{v_ℓ(t)}` is supported on
the `t` coprime to `∏_{ℓ ∈ A} ℓ`. -/
private lemma support_δ_mul_zero_pow_subset_coprime (A : Finset ℕ) (hA : ∀ ℓ ∈ A, Nat.Prime ℓ)
    (p : ℕ) [Fact p.Prime] :
    Function.support (fun t : ℕ => ((δ p t).toReal : ℂ) * ∏ ℓ : A, (0 : ℂ) ^ padicValNat ℓ t)
      ⊆ {t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)} := by
  intro t ht
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ht
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · exact absurd (by simp [δ_zero]) ht.1
  · refine Nat.coprime_prod_right_iff.2 fun ℓ hℓ => ?_
    rw [Nat.coprime_comm]
    refine ((hA ℓ hℓ).coprime_iff_not_dvd).2 fun hdvd => ht.2 ?_
    have hval : padicValNat ℓ t ≠ 0 := by
      have : Fact (Nat.Prime ℓ) := ⟨hA ℓ hℓ⟩
      exact (dvd_iff_padicValNat_ne_zero htpos.ne').1 hdvd
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨ℓ, hℓ⟩ : A)) (zero_pow hval)

/-- At a prime `p` and a finite set `A` of primes,

`∑_{t ≥ 1} δ_p(t) ∏_{ℓ ∈ A} 0^{v_ℓ(t)} = ∑_{t ≥ 1, (t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t)`,

the left-hand side in `ℂ` and the right-hand side in `ℝ`, coerced. -/
theorem tsum_δ_mul_zero_pow_eq_ofReal_tsum_coprime (A : Finset ℕ) (hA : ∀ ℓ ∈ A, Nat.Prime ℓ)
    (p : ℕ) [Fact p.Prime] :
    (∑' t : ℕ, ((δ p t).toReal : ℂ) * ∏ ℓ : A, (0 : ℂ) ^ padicValNat ℓ t)
      = ((∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (δ p t).toReal : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum,
    ← tsum_subtype_eq_of_support_subset (support_δ_mul_zero_pow_subset_coprime A hA p)]
  refine tsum_congr fun t => ?_
  have h1 : ∏ ℓ : A, (0 : ℂ) ^ padicValNat ℓ (t : ℕ) = 1 :=
    Finset.prod_eq_one fun ℓ _ => by
      rw [padicValNat.eq_zero_of_not_dvd (((hA ℓ ℓ.2).coprime_iff_not_dvd).1
        (Nat.coprime_comm.1 (Nat.coprime_prod_right_iff.1 t.2 ℓ ℓ.2))), pow_zero]
  rw [h1, mul_one]

/-! ### The event `{𝐣 : j_ℓ = 0 for all ℓ ∈ A}` -/

/-- The set of multi-indices all of whose coordinates vanish is the singleton `{𝟎}`. -/
theorem setOf_forall_eq_zero_eq_singleton (A : Finset ℕ) :
    {j : A → ℕ | ∀ ℓ : A, j ℓ = 0} = {0} := by
  ext j
  simp [funext_iff]

/-! ### The density formula -/

/-- For a finite set `A` of primes the Euler product of the restricted local densities converges,
with value the joint density at the zero multi-index:

`∏_{p ∈ 𝒫} (∑_{t ≥ 1, (t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t)) = Q_A(𝟎)`. -/
theorem hasProd_coprimeDensity_primes (A : Finset ℕ) (hA : ∀ ℓ ∈ A, Nat.Prime ℓ) :
    HasProd (fun p : {q : ℕ // q.Prime} =>
        ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal)
      (tamagawaValuationDensity A 0) := by
  have hfac : ∀ p : {q : ℕ // q.Prime},
      (∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : A, (0 : ℂ) ^ padicValNat ℓ t)
        = ((∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)},
            (@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℝ) : ℂ) := fun p => by
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact tsum_δ_mul_zero_pow_eq_ofReal_tsum_coprime A hA (p : ℕ)
  have hval : ((tamagawaValuationDensity A 0 : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * ∏ ℓ : A, (0 : ℂ) ^ padicValNat ℓ t := by
    rw [← tsum_tamagawaValuationDensity_mul_multiMonomial_eq_tprod_primes A hA
      (z := fun _ => 0) (by simp), tsum_eq_single 0 ?_]
    · simp [multiMonomial]
    · intro j hj
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : A, j ℓ ≠ 0 := not_forall.1 fun hc => hj (funext hc)
      rw [show multiMonomial j (fun _ : A => (0 : ℂ)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ ℓ) (zero_pow hℓ), mul_zero]
  have hC : HasProd (fun p : {q : ℕ // q.Prime} =>
      ((∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℝ) : ℂ))
      ((tamagawaValuationDensity A 0 : ℝ) : ℂ) := by
    rw [hval, tprod_congr hfac]
    exact ((multipliable_tamagawaValuationEulerFactor_primes A
      (z := fun _ => 0) (by simp)).congr hfac).hasProd
  simpa using hasProd_real_of_hasProd_ofReal hC

/-- For a finite set `A` of primes the family of restricted local sums
`(∑_{t ≥ 1, (t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t))_{p ∈ 𝒫}` is `Multipliable`: the net of partial products
over the finite sets of primes converges. -/
@[bsd_tamagawa "T044b"]
theorem multipliable_coprimeDensity_primes (A : Finset ℕ) (hA : ∀ ℓ ∈ A, Nat.Prime ℓ) :
    Multipliable fun p : {q : ℕ // q.Prime} =>
      ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal :=
  (hasProd_coprimeDensity_primes A hA).multipliable

/-- For a finite set `A` of primes, with `P = P_A` the limiting joint valuation law on `ℤ_{≥0}^A`,

`P(ℓ ∤ Tam(E) for all ℓ ∈ A) = ∏_{p ∈ 𝒫} (∑_{t ≥ 1, (t, ∏_{ℓ ∈ A} ℓ) = 1} δ_p(t))`,

with `δ_p(t)` the local Tamagawa density at `p`. The event on the left is the set of multi-indices
with all coordinates `0`, which is `ℓ ∤ Tam(E)` for every `ℓ ∈ A`. -/
@[bsd_tamagawa "T044b"]
theorem tamagawaValuationMeasure_notDvd_toReal (A : Finset ℕ) (hA : ∀ ℓ ∈ A, Nat.Prime ℓ) :
    (tamagawaValuationMeasure A {j : A → ℕ | ∀ ℓ : A, j ℓ = 0}).toReal
      = ∏' p : {q : ℕ // q.Prime},
        ∑' t : ↥{t : ℕ | Nat.Coprime t (∏ ℓ ∈ A, ℓ)}, (@δ (p : ℕ) ⟨p.2⟩ t).toReal := by
  rw [setOf_forall_eq_zero_eq_singleton A, tamagawaValuationMeasure_singleton_toReal A hA,
    (hasProd_coprimeDensity_primes A hA).tprod_eq]

end WeierstrassCurve
