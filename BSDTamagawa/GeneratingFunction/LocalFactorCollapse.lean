/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.GeneratingFunction.LocalWeightTrivial
public import BSDTamagawa.GeneratingFunction.ScalarLocalFactorSummable
public import BSDTamagawa.PrimeCount.LocalFactorCollapse

/-!
# Collapse of the local Euler factor to the scalar local factor

For a prime `p` and parameters `(s, w, 𝐳) ∈ 𝒟₀` — `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for
every `ℓ ∈ Π` — taking `Λ = ∅` and `u = 1` in the local weight,
`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, 1, w, 𝐳, ()) = h_p(s, w, 𝐳)`,
where `β_p` is the trivial-stratum mass (`WeierstrassCurve.β`), `δ_p(K)` the local reduction
density (`WeierstrassCurve.deltaP`), `Φ_p` the local weight (`WeierstrassCurve.localWeight`) and
`h_p` the scalar local factor (`WeierstrassCurve.scalarLocalFactor`). On this face the local
weight depends on `K` only through its Tamagawa value `c(K)`, so the `𝒦`-indexed sum is summed
fibrewise over `c`.

## Main results

* `WeierstrassCurve.localWeight_eq_scalarWeight`: on the face `Λ = ∅`, `u = 1`, the local weight
  is the scalar weight at `c(K)`.
* `WeierstrassCurve.deltaP_eq_zero_of_snd_zero`: a reduction datum with `c(K) = 0` has density
  `0`.
* `WeierstrassCurve.hasSum_deltaP_toReal_mul_scalarWeight`: the `𝒦`-indexed series sums to
  `h_p(s, w, 𝐳)`.
* `WeierstrassCurve.localFactor_eq_scalarLocalFactor`: the collapse identity above.

## Implementation notes

`𝒦 ∖ 𝒦₀` is `𝒦₀ᶜ`, `𝒦` being the whole type `KodairaSymbol × ℕ`, and its `δ_p`-support is
infinite, so the sum over it is a `tsum` rather than a `finsum`. The densities are coerced to `ℂ`
by `ENNReal.toReal` followed by `Complex.ofReal`; this is lossless since every density is finite.
-/

@[expose] public section

open MeasureTheory BSDTamagawa.MultiIndex

namespace WeierstrassCurve

variable (P : Finset ℕ) (p : ℕ)

/-! ### The summand on the face `Λ = ∅`, `u = 1` -/

/-- On the face `Λ = ∅`, `u = 1`, the local weight `Φ_p(K; s, 1, w, 𝐳, ())` equals the scalar
weight `ψ_{s, w, 𝐳}(c(K))`. -/
lemma localWeight_eq_scalarWeight (K : KodairaSymbol × ℕ) (s w : ℂ) (z : P → ℂ)
    (uΛ : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ) :
    localWeight ∅ P K s 1 w z uΛ = scalarWeight P s w z K.2 := by
  rw [localWeight, scalarWeight]
  simp [multiMonomial]

/-! ### The `c(K) = 0` data are null -/

/-- A reduction datum `K` with Tamagawa value `c(K) = 0` has local density `δ_p(K) = 0`. -/
lemma deltaP_eq_zero_of_snd_zero [Fact p.Prime] {K : KodairaSymbol × ℕ} (hK : K.2 = 0) :
    deltaP p K = 0 := by
  have hempty : {W : ShortNF.Elliptic ℤ_[p] |
      ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = K} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun W hW => ?_
    have h : ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = K := hW
    exact absurd ((congrArg Prod.snd h).trans hK) (tauP_tamagawaNumber_pos p W).ne'
  rw [deltaP, hempty, measure_empty]

/-! ### Absolute summability over `𝒦` -/

/-- On `𝒟₀`, the term `δ_p(K) ψ_{s, w, 𝐳}(c(K))` has norm at most `δ_p(K)`. -/
lemma norm_deltaP_toReal_mul_scalarWeight_le [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (K : KodairaSymbol × ℕ) :
    ‖((deltaP p K).toReal : ℂ) * scalarWeight P s w z K.2‖ ≤ (deltaP p K).toReal := by
  rcases Nat.eq_zero_or_pos K.2 with h | h
  · simp [deltaP_eq_zero_of_snd_zero p h]
  · have hnorm : ‖((deltaP p K).toReal : ℂ)‖ = (deltaP p K).toReal := by
      rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [norm_mul, hnorm]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg
      (norm_scalarWeight_le_one P hs hw hz h)

/-- On `𝒟₀`, the family `(δ_p(K) ψ_{s, w, 𝐳}(c(K)))_{K ∈ 𝒦}` is summable. -/
lemma summable_deltaP_toReal_mul_scalarWeight [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    Summable fun K : KodairaSymbol × ℕ =>
      ((deltaP p K).toReal : ℂ) * scalarWeight P s w z K.2 :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_deltaP_toReal_mul_scalarWeight_le P p hs hw hz) (hasSum_deltaP_toReal p).summable)

/-! ### Summing over the fibres of `c` -/

/-- At a fixed Tamagawa value `t`, the densities `δ_p((κ, t))` sum in `ℂ` to `δ_p(t)`. -/
lemma hasSum_deltaP_toReal_kodaira [Fact p.Prime] (t : ℕ) :
    HasSum (fun κ : KodairaSymbol => ((deltaP p (κ, t)).toReal : ℂ)) ((δ p t).toReal : ℂ) := by
  have hsummable : Summable fun κ : KodairaSymbol => (deltaP p (κ, t)).toReal :=
    ENNReal.summable_toReal (by rw [tsum_deltaP_kodaira]; exact δ_ne_top p t)
  have hval : ∑' κ : KodairaSymbol, (deltaP p (κ, t)).toReal = (δ p t).toReal := by
    rw [← ENNReal.tsum_toReal_eq fun κ => deltaP_ne_top p (κ, t), tsum_deltaP_kodaira]
  have h := hsummable.hasSum
  rw [hval] at h
  simpa [Function.comp_def] using h.map Complex.ofRealHom Complex.continuous_ofReal

/-- On `𝒟₀`, the family `(δ_p(K) ψ_{s, w, 𝐳}(c(K)))_{K ∈ 𝒦}` sums to `h_p(s, w, 𝐳)`. -/
lemma hasSum_deltaP_toReal_mul_scalarWeight [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    HasSum (fun K : KodairaSymbol × ℕ =>
        ((deltaP p K).toReal : ℂ) * scalarWeight P s w z K.2)
      (scalarLocalFactor P p s w z) := by
  have hsum := summable_deltaP_toReal_mul_scalarWeight P p hs hw hz
  have hfib := (((Equiv.prodComm ℕ KodairaSymbol).hasSum_iff).2 hsum.hasSum).prod_fiberwise
    fun t => (hasSum_deltaP_toReal_kodaira p t).mul_right (scalarWeight P s w z t)
  have heq : ∑' K : KodairaSymbol × ℕ, ((deltaP p K).toReal : ℂ) * scalarWeight P s w z K.2
      = scalarLocalFactor P p s w z :=
    hfib.unique (hasSum_scalarLocalFactor P p hs hw hz)
  rw [← heq]
  exact hsum.hasSum

/-! ### The collapse -/

/-- For a prime `p` and `(s, w, 𝐳) ∈ 𝒟₀` — `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`
— taking `Λ = ∅` and `u = 1` in the local weight,
`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; s, 1, w, 𝐳, ()) = h_p(s, w, 𝐳)`, with `β_p` the trivial-stratum
mass, `δ_p(K)` the local reduction density and `h_p` the scalar local factor. The densities are
coerced to `ℂ` through `ENNReal.toReal`. -/
@[bsd_tamagawa "T036h"]
theorem localFactor_eq_scalarLocalFactor [Fact p.Prime] {s w : ℂ} {z : P → ℂ}
    (uΛ : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ)
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) :
    ((β p).toReal : ℂ)
        + ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
            ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
              * localWeight ∅ P (K : KodairaSymbol × ℕ) s 1 w z uΛ
      = scalarLocalFactor P p s w z := by
  have hface : (fun K : KodairaSymbol × ℕ =>
        ((deltaP p K).toReal : ℂ) * localWeight ∅ P K s 1 w z uΛ)
      = fun K : KodairaSymbol × ℕ => ((deltaP p K).toReal : ℂ) * scalarWeight P s w z K.2 :=
    funext fun K => by rw [localWeight_eq_scalarWeight]
  have htot : HasSum (fun K : KodairaSymbol × ℕ =>
      ((deltaP p K).toReal : ℂ) * localWeight ∅ P K s 1 w z uΛ)
      (scalarLocalFactor P p s w z) := by
    rw [hface]; exact hasSum_deltaP_toReal_mul_scalarWeight P p hs hw hz
  have hone : ∀ K ∈ K0, localWeight ∅ P K s 1 w z uΛ = 1 :=
    fun K hK => localWeight_eq_one ∅ P hK (by simp) s 1 w z uΛ
  have hK0 : ∑' K : ↥K0, (((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
      * localWeight ∅ P (K : KodairaSymbol × ℕ) s 1 w z uΛ) = ((β p).toReal : ℂ) := by
    rw [tsum_subtype_K0 (M := ℂ) fun K => ((deltaP p K).toReal : ℂ)
      * localWeight ∅ P K s 1 w z uΛ,
      hone (KodairaSymbol.I 0, 1) (by simp [K0]), hone (KodairaSymbol.I 1, 1) (by simp [K0]),
      β_add, ENNReal.toReal_add (deltaP_ne_top p _) (deltaP_ne_top p _)]
    push_cast
    ring
  rw [← hK0, htot.summable.tsum_subtype_add_tsum_subtype_compl K0, htot.tsum_eq]

end WeierstrassCurve
