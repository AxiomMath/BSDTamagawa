/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityLargePrime

/-!
# The split-decorated multiplicative density

The density `WeierstrassCurve.deltaP` is indexed by the pair (Kodaira symbol, Tamagawa number),
which does not separate the split and non-split halves `I_n^sp`, `I_n^ns` of the multiplicative
stratum: at `n = 1, 2` both halves report the same pair, while at `n ≥ 3` the pair `(I_n, n)` names
the split half alone. This file refines the index by a split flag and evaluates the refinement
exactly: for every prime `p ≥ 5` and every `t ≥ 1`,

  `δ_p(I_t^sp) = δ_p(I_t^ns) = (p-1)²/(2p^{t+2}) · (1 - p⁻¹⁰)⁻¹`.

## Main definitions

* `WeierstrassCurve.iFineLocus`: the level-`t` multiplicative locus decorated by the split flag.
* `WeierstrassCurve.deltaPI`: the split-decorated density `δ_p(I_t^sp)`, `δ_p(I_t^ns)`.

## Main results

* `WeierstrassCurve.deltaPI_eq`: for every prime `p ≥ 5`, every `t ≥ 1` and both halves,
  `δ_p(I_t^sp) = δ_p(I_t^ns) = 2N²p^{-(t+2)}(1 - p⁻¹⁰)⁻¹`, where `2N = p - 1`.
* `WeierstrassCurve.deltaP_I_one_eq`: `δ_p((I₁, 1)) = 4N²p⁻³(1 - p⁻¹⁰)⁻¹`.

## Implementation notes

The two halves have equal mass because the twist `x ↦ (ν²a₄, ν³a₆)` by a quadratic non-residue `ν`
preserves Haar measure and exchanges them. This needs a non-residue, so it is an odd-`p` statement;
at `p = 2` the two halves have unequal mass, and everything here is stated at `p ≥ 5`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The decorated level-`t` locus -/

variable (p) in
/-- **The level-`t` multiplicative locus, decorated by the split flag**: `iSplitLocus p t`, where
`-c₆ = 864a₆` is a square mod `p`, at `sp = true`, and `iNonSplitLocus p t` at `sp = false`. -/
def iFineLocus (t : ℕ) : Bool → Set (ℤ_[p] × ℤ_[p])
  | true => iSplitLocus p t
  | false => iNonSplitLocus p t

/-- The split half of the decorated locus is `iSplitLocus p t`. -/
@[simp]
theorem iFineLocus_true (t : ℕ) : iFineLocus p t true = iSplitLocus p t := rfl

/-- The non-split half of the decorated locus is `iNonSplitLocus p t`. -/
@[simp]
theorem iFineLocus_false (t : ℕ) : iFineLocus p t false = iNonSplitLocus p t := rfl

/-- **The two halves have equal mass**, for every prime `p ≥ 5` and every `t ≥ 1`. -/
theorem volume_iFineLocus_false_eq (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (iFineLocus p t false) = volume (iFineLocus p t true) := by
  obtain ⟨ν, hν, hχ⟩ := exists_isUnit_quadraticChar_eq_neg_one hp
  rw [iFineLocus_true, iFineLocus_false, iNonSplitLocus_eq_preimage hp ht hν hχ]
  exact (measurePreserving_twistPlane hν).measure_preimage
    (measurableSet_iSplitLocus t).nullMeasurableSet

/-- **The exact mass of each half**: `2N²p^{-(t+2)}`, `N = |goodRes p|`, at every prime `p ≥ 5` and
every `t ≥ 1`. -/
theorem volume_iFineLocus_eq (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (sp : Bool) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (iFineLocus p t sp)
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 2) := by
  cases sp with
  | false => rw [volume_iFineLocus_false_eq hp ht]; exact volume_iSplitLocus hp ht
  | true => exact volume_iSplitLocus hp ht

/-! ### The split-decorated density -/

variable (p) in
/-- **The split-decorated multiplicative density** `δ_p(I_t^sp)` (at `sp = true`) and `δ_p(I_t^ns)`
(at `sp = false`): the mass of the decorated level-`t` locus times the factor `(1 - p⁻¹⁰)⁻¹`. -/
noncomputable def deltaPI (t : ℕ) (sp : Bool) : ℝ≥0∞ :=
  (volume : Measure (ℤ_[p] × ℤ_[p])) (iFineLocus p t sp) * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹

/-- For every prime `p ≥ 5`, every `t ≥ 1` and both halves,

  `δ_p(I_t^sp) = δ_p(I_t^ns) = 2N² p^{-(t+2)} (1 - p⁻¹⁰)⁻¹`,  `2N = p - 1`,

i.e. `(p-1)²/(2p^{t+2}) · (1 - p⁻¹⁰)⁻¹`. -/
@[bsd_tamagawa "T020b"]
theorem deltaPI_eq (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (sp : Bool) :
    deltaPI p t sp
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 2)
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaPI, volume_iFineLocus_eq hp ht]

/-! ### The `I₁` row -/

/-- **The level-1 multiplicative locus lies in the stratum `τ_p⁻¹((I₁, 1))`**, for every prime
`p ≥ 5`. -/
theorem iLocus_one_subset_stratFibre (hp : 5 ≤ p) :
    iLocus p 1 ⊆ stratFibre p (KodairaSymbol.I 1, 1) := by
  intro x hx
  have hUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_of_mem_iLocus hp hx
  have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((1 : ℕ) : ℕ∞) :=
    emultiplicity_Δ_of_mem_iLocus hp hx
  have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := not_dvd_c₄_of_mem_iLocus hp hx
  have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := dvd_Δ_of_emultiplicity_eq le_rfl hΔv
  have htoNat : (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat = 1 :=
    (toNat_emultiplicity_Δ_eq_iff hUp 1).2 hΔv
  have hκ : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
      = KodairaSymbol.I 1 := by
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄, htoNat]
  have hc : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 1 := by
    rw [run_tamagawaNumber_of_nodal hUp hpΔ hc₄, htoNat]
    split
    · rfl
    · rw [ite_eq_left odd_one]
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-- **The minimal part of the stratum `τ_p⁻¹((I₁, 1))` is the whole level-1 multiplicative locus**,
for every prime `p ≥ 5`:

  `τ_p⁻¹((I₁, 1)) ∖ σ_p(ℤ_p²) = {p ∤ a₄, v_p(4a₄³ + 27a₆²) = 1}`. -/
theorem stratFibre_diff_range_eq_iLocus_one (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.I 1, 1) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = iLocus p 1 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have h4 : ¬ (p : ℤ_[p]) ∣ x.1 := fun hd =>
      hxR (mem_range_of_mem_stratFibre_of_dvd_fst hp le_rfl hxF hd)
    have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
      rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
      exact h4
    have hs := (mem_stratFibre_iff hUp).1 hxF
    rw [strat] at hs
    have hκ : (run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I 1 := congrArg Prod.fst hs
    have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
      by_contra hnd
      rw [run_eq_of_not_dvd_Δ hUp hnd] at hκ
      exact absurd (KodairaSymbol.I.inj hκ) (by omega)
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄] at hκ
    have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((1 : ℕ) : ℕ∞) :=
      (toNat_emultiplicity_Δ_eq_iff hUp 1).1 (KodairaSymbol.I.inj hκ)
    rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add] at hΔv
    exact ⟨h4, hΔv⟩
  · intro x hx
    refine ⟨iLocus_one_subset_stratFibre hp hx, fun hr => ?_⟩
    exact hx.1 (dvd_trans (dvd_pow_self _ (by norm_num : 4 ≠ 0))
      (PadicInt.mem_range_scaleProdByPPow_iff.1 hr).1)

/-- **The density of `(I₁, 1)`**, for every prime `p ≥ 5`:

  `δ_p((I₁, 1)) = 4N² p⁻³ (1 - p⁻¹⁰)⁻¹`,  `2N = p - 1`,

i.e. `(p-1)²p⁷/(p¹⁰-1)`. -/
theorem deltaP_I_one_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.I 1, 1)
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 3
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_iLocus_one hp,
    volume_iLocus hp (by norm_num), one_sub_inv_eq hp]
  ring

end WeierstrassCurve
