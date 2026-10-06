/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.LocalDensity.TrivialStratumMass
public import BSDTamagawa.LocalDensity.ScalarSum
public import BSDTamagawa.LocalDensity.Scalar

/-!
# Collapse of the master local factor at `Λ = Π = ∅`, `w = 1`, `s = 0`

For a prime `p` and `u ∈ ℂ`,
`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, u, 1, ∅, ∅) = δ_p(1) + (1 - δ_p(1)) u`, where `β_p` is the
trivial-datum mass (`WeierstrassCurve.β`), `δ_p(K)` the local reduction density
(`WeierstrassCurve.deltaP`), `δ_p(1)` the scalar local density (`WeierstrassCurve.δ`) and `Φ_p` the
local weight (`WeierstrassCurve.localWeight`). On this face `Φ_p(K) = u^{𝟙[c(K) > 1]}`, and the
identity follows from the aggregation `∑'_{κ} δ_p((κ, t)) = δ_p(t)` of the reduction densities over
the Kodaira symbol, which is countable additivity of `μ_p` over the fibres of the reduction datum.

## Main definitions

* `WeierstrassCurve.kodairaEncode`: an injection `KodairaSymbol → ℕ × ℕ`.

## Main results

* `WeierstrassCurve.instCountableKodairaSymbol`: Kodaira symbols are countable.
* `WeierstrassCurve.measurableSet_reductionDatum_fiber`: the fibres of the reduction datum `τ_p`
  are measurable.
* `WeierstrassCurve.tsum_deltaP_kodaira`: `∑'_{κ} δ_p((κ, t)) = δ_p(t)`.
* `WeierstrassCurve.tsum_deltaP`: `∑_{K ∈ 𝒦} δ_p(K) = 1`.
* `WeierstrassCurve.δ_one_add_tsum_deltaP_of_one_lt`: `δ_p(1) + ∑_{c(K) > 1} δ_p(K) = 1`.
* `WeierstrassCurve.localFactor_collapse`: the collapse identity.

## Implementation notes

The sum over `𝒦 ∖ 𝒦₀` is a `tsum` over the subtype `↥(𝒦₀ᶜ)`: its `δ_p`-support is infinite, so a
`finsum` would return its junk value `0`. The densities are coerced to `ℂ` by `ENNReal.toReal`
followed by `Complex.ofReal`, and `1 - δ_p(1)` is a subtraction in `ℂ`.
-/

@[expose] public section

open Function MeasureTheory BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex
  BSDTamagawa.LocalConstancy

namespace WeierstrassCurve

/-! ### `𝒦` is countable -/

/-- A constructor-and-argument encoding of Kodaira symbols as pairs of naturals: the constructor
index together with the `ℕ` argument of `Iₙ`/`Iₙ*` (and `0` for the symbols that take none). -/
def kodairaEncode : KodairaSymbol → ℕ × ℕ
  | .I n => (0, n)
  | .II => (1, 0)
  | .III => (2, 0)
  | .IV => (3, 0)
  | .I! n => (4, n)
  | .IV! => (5, 0)
  | .III! => (6, 0)
  | .II! => (7, 0)

/-- Distinct Kodaira symbols get distinct codes. -/
lemma kodairaEncode_injective : Injective kodairaEncode := by
  intro a b h; cases a <;> cases b <;> simp_all [kodairaEncode]

/-- **Kodaira symbols are countable**, hence so is the reduction datum `𝒦 = KodairaSymbol × ℕ`. -/
instance instCountableKodairaSymbol : Countable KodairaSymbol :=
  kodairaEncode_injective.countable

variable (p : ℕ) [Fact p.Prime]

/-! ### The fibres of the reduction datum are measurable -/

/-- Tate's algorithm at equal curves returns equal output. -/
private lemma run_congr_curve {W W' : WeierstrassCurve ℤ_[p]} (h : W = W')
    (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) :
    TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ
      = TateAlgorithm.run (W := W') PadicInt.uniformizer_ne_zero hΔ' := by
  subst h; rfl

/-- The reduction datum `strat` on the coefficient plane, evaluated at the coefficients of an
elliptic short model `W`, is the reduction datum of `W` computed by Tate's algorithm. -/
lemma strat_coeffs (W : ShortNF.Elliptic ℤ_[p]) :
    strat p (ShortNF.Elliptic.coeffs p W)
      = ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) := by
  simp only [strat, tauP, ShortNF.Elliptic.coeffs]
  rw [run_congr_curve p (ofShortNF_eq_self W.val.property) _ W.property]

/-- **The fibres of the reduction datum `τ_p` are measurable.** -/
lemma measurableSet_reductionDatum_fiber (K : KodairaSymbol × ℕ) :
    MeasurableSet {W : ShortNF.Elliptic ℤ_[p] |
      ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = K} := by
  have h : {W : ShortNF.Elliptic ℤ_[p] |
        ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = K}
      = ShortNF.Elliptic.coeffs p ⁻¹' (strat p ⁻¹' {K}) := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, strat_coeffs]
  rw [h]
  exact ShortNF.Elliptic.measurable_coeffs p (isLocallyConstant_strat p _).measurableSet

/-! ### The `𝒦`-to-scalar aggregation, and the two masses -/

/-- The `𝒦`-to-scalar aggregation: `δ_p(t) = ∑_{K ∈ 𝒦, c(K) = t} δ_p(K)`, written as a sum over the
Kodaira symbol at fixed Tamagawa number `t`. -/
@[bsd_tamagawa "T010a"]
theorem tsum_deltaP_kodaira (t : ℕ) : ∑' κ : KodairaSymbol, deltaP p (κ, t) = δ p t := by
  have hdisj : Pairwise (Disjoint on fun κ : KodairaSymbol =>
      {W : ShortNF.Elliptic ℤ_[p] |
        ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = (κ, t)}) := by
    intro κ κ' h
    simp only [Function.onFun, Set.disjoint_left, Set.mem_ofPred_eq]
    intro W hW hW'
    exact h (congrArg Prod.fst (hW.symm.trans hW'))
  have hunion : (⋃ κ : KodairaSymbol, {W : ShortNF.Elliptic ℤ_[p] |
      ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = (κ, t)})
      = {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = t} := by
    ext W
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨κ, -, h⟩; exact h
    · intro h; exact ⟨_, rfl, h⟩
  simp only [deltaP, δ]
  rw [← measure_iUnion hdisj fun κ => measurableSet_reductionDatum_fiber p (κ, t), hunion]

/-- **The reduction densities have total mass one:** `∑_{K ∈ 𝒦} δ_p(K) = 1`. -/
theorem tsum_deltaP : ∑' K : KodairaSymbol × ℕ, deltaP p K = 1 := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [tsum_deltaP_kodaira]
  exact tsum_δ p

/-- The mass carried by the nontrivial data, aggregated: `∑_{c(K) > 1} δ_p(K)` equals the scalar
tail `∑_{t > 1} δ_p(t)`. -/
theorem tsum_deltaP_of_one_lt :
    ∑' K : KodairaSymbol × ℕ, (if 1 < K.2 then deltaP p K else 0)
      = ∑' t : ℕ, (if 1 < t then δ p t else 0) := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun t => ?_
  by_cases h : 1 < t
  · simpa only [h, ite_true] using tsum_deltaP_kodaira p t
  · simp only [h, ite_false, tsum_zero]

/-- **The mass splitting:** `δ_p(1) + ∑_{K ∈ 𝒦, c(K) > 1} δ_p(K) = 1`. -/
theorem δ_one_add_tsum_deltaP_of_one_lt :
    δ p 1 + ∑' K : KodairaSymbol × ℕ, (if 1 < K.2 then deltaP p K else 0) = 1 := by
  have hsplit : ∀ t : ℕ,
      δ p t = (if 1 < t then 0 else δ p t) + (if 1 < t then δ p t else 0) := by
    intro t; by_cases h : 1 < t <;> simp [h]
  have hlow : ∑' t : ℕ, (if 1 < t then 0 else δ p t) = δ p 1 := by
    rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) fun b hb => ?_]
    · simp [δ_zero]
    · have hb' : 1 < b := by
        rcases Nat.lt_or_ge b 2 with h | h
        · interval_cases b <;> simp_all
        · omega
      simp [hb']
  rw [tsum_deltaP_of_one_lt]
  calc δ p 1 + ∑' t : ℕ, (if 1 < t then δ p t else 0)
      = ∑' t : ℕ, (if 1 < t then 0 else δ p t) + ∑' t : ℕ, (if 1 < t then δ p t else 0) := by
        rw [hlow]
    _ = ∑' t : ℕ, δ p t := by rw [← ENNReal.tsum_add]; exact (tsum_congr hsplit).symm
    _ = 1 := tsum_δ p

/-! ### Passage to `ℝ` and `ℂ`

`μ_p` is a probability measure, so every density is finite and `ENNReal.toReal` is lossless.
-/

/-- A reduction density is finite: it is the measure of a set for a probability measure. -/
lemma deltaP_ne_top (K : KodairaSymbol × ℕ) : deltaP p K ≠ ⊤ := by
  rw [deltaP]; exact measure_ne_top _ _

/-- A scalar density is finite, for the same reason. -/
lemma δ_ne_top (t : ℕ) : δ p t ≠ ⊤ := by
  rw [δ]; exact measure_ne_top _ _

/-- The nontrivial mass `∑_{c(K) > 1} δ_p(K)` is finite. -/
private lemma tsum_deltaP_of_one_lt_ne_top :
    ∑' K : KodairaSymbol × ℕ, (if 1 < K.2 then deltaP p K else 0) ≠ ⊤ := by
  intro h
  have hkey := δ_one_add_tsum_deltaP_of_one_lt p
  rw [h] at hkey
  simp at hkey

/-- The real-valued reduction densities sum to `1`. -/
lemma hasSum_deltaP_toReal :
    HasSum (fun K : KodairaSymbol × ℕ => (deltaP p K).toReal) 1 := by
  have hsummable : Summable fun K : KodairaSymbol × ℕ => (deltaP p K).toReal :=
    ENNReal.summable_toReal (by rw [tsum_deltaP]; exact ENNReal.one_ne_top)
  have hval : ∑' K : KodairaSymbol × ℕ, (deltaP p K).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (deltaP_ne_top p), tsum_deltaP]
    simp
  have h := hsummable.hasSum
  rwa [hval] at h

/-- The real-valued nontrivial mass is `1 - δ_p(1)`. -/
lemma hasSum_deltaP_toReal_of_one_lt :
    HasSum (fun K : KodairaSymbol × ℕ => if 1 < K.2 then (deltaP p K).toReal else 0)
      (1 - (δ p 1).toReal) := by
  have hne : ∀ K : KodairaSymbol × ℕ, (if 1 < K.2 then deltaP p K else 0) ≠ ⊤ := by
    intro K; split
    · exact deltaP_ne_top p K
    · exact ENNReal.zero_ne_top
  have hfun : (fun K : KodairaSymbol × ℕ => if 1 < K.2 then (deltaP p K).toReal else 0)
      = fun K : KodairaSymbol × ℕ => ((if 1 < K.2 then deltaP p K else 0)).toReal := by
    funext K; split <;> simp
  rw [hfun]
  have hsummable : Summable fun K : KodairaSymbol × ℕ =>
      ((if 1 < K.2 then deltaP p K else 0)).toReal :=
    ENNReal.summable_toReal (tsum_deltaP_of_one_lt_ne_top p)
  have hval : ∑' K : KodairaSymbol × ℕ, ((if 1 < K.2 then deltaP p K else 0)).toReal
      = 1 - (δ p 1).toReal := by
    rw [← ENNReal.tsum_toReal_eq hne]
    have h2 : (δ p 1).toReal
        + (∑' K : KodairaSymbol × ℕ, (if 1 < K.2 then deltaP p K else 0)).toReal = 1 := by
      rw [← ENNReal.toReal_add (δ_ne_top p 1) (tsum_deltaP_of_one_lt_ne_top p),
        δ_one_add_tsum_deltaP_of_one_lt]
      simp
    linarith
  have h := hsummable.hasSum
  rwa [hval] at h

/-! ### The local weight on the face `Λ = Π = ∅`, `w = 1`, `s = 0` -/

/-- **`Φ_p` on the face.** At `Λ = Π = ∅`, `s = 0`, `w = 1` the local weight is the two-valued
weight `u^{𝟙[c(K) > 1]}`. -/
lemma localWeight_face (K : KodairaSymbol × ℕ) (u : ℂ)
    (z : (∅ : Finset ℕ) → ℂ) (uΛ : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ) :
    localWeight ∅ ∅ K 0 u 1 z uΛ = if 1 < K.2 then u else 1 := by
  rw [localWeight]; simp [multiMonomial]

/-! ### The trivial stratum -/

/-- `𝒦₀ = {(I₀, 1), (I₁, 1)}` is finite. -/
lemma finite_K0 : K0.Finite := by
  rw [K0]; exact (Set.finite_singleton _).insert _

/-- A sum over the two-element index `↥𝒦₀` is the two-term sum. -/
lemma tsum_subtype_K0 {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (f : KodairaSymbol × ℕ → M) :
    ∑' K : ↥K0, f K = f (KodairaSymbol.I 0, 1) + f (KodairaSymbol.I 1, 1) := by
  have : Finite ↥K0 := finite_K0.to_subtype
  rw [tsum_eq_finsum (Set.toFinite _), finsum_set_coe_eq_finsum_mem (f := f) (s := K0), K0,
    finsum_mem_pair (show (KodairaSymbol.I 0, 1) ≠ (KodairaSymbol.I 1, 1) by simp)]

/-! ### The collapse -/

/-- For a prime `p` and every `u : ℂ`,
`β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ_p(K; 0, u, 1, ∅, ∅) = δ_p(1) + (1 - δ_p(1)) u`, with `β_p` the
trivial-datum mass, `δ_p(K)` the local reduction density, `δ_p(1)` the scalar local density and
`Φ_p` the local weight. The densities are coerced to `ℂ` by `ENNReal.toReal` followed by
`Complex.ofReal`. -/
@[bsd_tamagawa "T041f"]
theorem localFactor_collapse (u : ℂ) (z : (∅ : Finset ℕ) → ℂ)
    (uΛ : (∅ : Finset (KodairaSymbol × ℕ)) → ℂ) :
    ((β p).toReal : ℂ)
        + ∑' K : ↥(K0ᶜ : Set (KodairaSymbol × ℕ)),
            ((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
              * localWeight ∅ ∅ (K : KodairaSymbol × ℕ) 0 u 1 z uΛ
      = ((δ p 1).toReal : ℂ) + (1 - ((δ p 1).toReal : ℂ)) * u := by
  have h1 : HasSum (fun K : KodairaSymbol × ℕ => ((deltaP p K).toReal : ℂ)) 1 := by
    simpa [Function.comp_def] using
      (hasSum_deltaP_toReal p).map Complex.ofRealHom Complex.continuous_ofReal
  have h2 : HasSum
      (fun K : KodairaSymbol × ℕ => ((if 1 < K.2 then (deltaP p K).toReal else 0 : ℝ) : ℂ))
      ((1 - (δ p 1).toReal : ℝ) : ℂ) := by
    simpa [Function.comp_def] using
      (hasSum_deltaP_toReal_of_one_lt p).map Complex.ofRealHom Complex.continuous_ofReal
  have hterm : (fun K : KodairaSymbol × ℕ =>
        ((deltaP p K).toReal : ℂ) * localWeight ∅ ∅ K 0 u 1 z uΛ)
      = fun K : KodairaSymbol × ℕ => ((deltaP p K).toReal : ℂ)
          + (u - 1) * ((if 1 < K.2 then (deltaP p K).toReal else 0 : ℝ) : ℂ) := by
    funext K
    rw [localWeight_face]
    split <;> push_cast <;> ring
  have htot : HasSum (fun K : KodairaSymbol × ℕ =>
      ((deltaP p K).toReal : ℂ) * localWeight ∅ ∅ K 0 u 1 z uΛ)
      (1 + (u - 1) * ((1 - (δ p 1).toReal : ℝ) : ℂ)) := by
    rw [hterm]; exact h1.add (h2.mul_left _)
  have hK0 : ∑' K : ↥K0, (((deltaP p (K : KodairaSymbol × ℕ)).toReal : ℂ)
      * localWeight ∅ ∅ (K : KodairaSymbol × ℕ) 0 u 1 z uΛ) = ((β p).toReal : ℂ) := by
    rw [tsum_subtype_K0 (M := ℂ) fun K => ((deltaP p K).toReal : ℂ)
      * localWeight ∅ ∅ K 0 u 1 z uΛ]
    simp only [localWeight_face, lt_irrefl, ite_false, mul_one]
    rw [β_add, ENNReal.toReal_add (deltaP_ne_top p _) (deltaP_ne_top p _)]
    push_cast
    ring
  rw [← hK0, htot.summable.tsum_subtype_add_tsum_subtype_compl K0, htot.tsum_eq]
  push_cast
  ring

end WeierstrassCurve
