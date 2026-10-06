/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityIVStar
public import BSDTamagawa.NumberTheory.SplitDecoratedDensity

/-!
# The fibre `{c = 1}` and the head density `δ_p(1)` for `p ≥ 5`

For a prime `p ≥ 5`, write `N = |goodRes p|`, so that `2N = p - 1`, and `T = (1 - p⁻¹⁰)⁻¹`. This
file shows that the Tamagawa number `1` is carried exactly by the Kodaira symbols `I₀`, the odd
`Iₙ`, `II`, `I₀*`, `IV`, `IV*` and `II*`, which gives the decomposition

  `δ_p(1) = δ_p((I₀,1)) + δ_p((II,1)) + δ_p((I₀*,1)) + δ_p((IV,1)) + δ_p((IV*,1)) + δ_p((II*,1))
            + ∑_{k ≥ 0} δ_p((I_{2k+1}, 1))`.

It computes the densities `δ_p((Iₙ, 1)) = 2N² p^{-(n+2)} T` of the non-split strata at odd `n ≥ 3`,
their sum over the odd multiplicative family, and `δ_p((II*, 1)) = 2N p⁻¹⁰ T`. Together with the
known densities of the other strata, this reduces the closed form `δ_p(1) = gotδ p 1` to the single
density `δ_p((I₀*, 1)) = ((p²-1)/3) p⁻⁷ T`.

## Main definitions

* `WeierstrassCurve.gotHeadOneEvaluated`: the sum, as a real number, of the densities of the strata
  `(I₀, 1)`, `(I₁, 1)`, `(Iₙ, 1)` for odd `n ≥ 3`, `(II, 1)`, `(IV, 1)` and `(IV*, 1)`.
* `WeierstrassCurve.gotIZeroStarOne`: `((p²-1)/3) p⁻⁷ T`.
* `WeierstrassCurve.gotIIStarOne`: `(p-1) p⁻¹⁰ T`.
* `WeierstrassCurve.stratMinimalIIstar`: the locus `{p⁴ ∣ a₄, v_p(a₆) = 5}`.

## Main results

* `WeierstrassCurve.deltaP_I_one_eq_of_odd`: `δ_p((Iₙ, 1)) = 2N² p^{-(n+2)} T` for odd `n ≥ 3`.
* `WeierstrassCurve.TateAlgorithm.run_kodairaSymbol_of_tamagawaNumber_eq_one`: the Kodaira symbols
  carrying the Tamagawa number `1`.
* `WeierstrassCurve.iUnion_stratFibre_one_eq`: the fibre `{c = 1}` as a union of strata.
* `WeierstrassCurve.δ_one_eq_add_tsum`: the decomposition of `δ_p(1)` above.
* `WeierstrassCurve.tsum_deltaP_I_odd_one_eq`:
  `∑_{k ≥ 0} δ_p((I_{2k+1}, 1)) = 4N²p⁻³T + 2N²p⁻⁵T(1 - p⁻²)⁻¹`.
* `WeierstrassCurve.gotHeadOneEvaluated_add_add_eq_gotδ_one`:
  `gotHeadOneEvaluated p + gotIZeroStarOne p + gotIIStarOne p = gotδ p 1`.
* `WeierstrassCurve.run_eq_IIstar_of_eq_pow_mul`: a short model with `p⁴ ∣ a₄`, `a₆ = p⁵u`, `p ∤ u`
  has reduction datum `(II*, 1)`.
* `WeierstrassCurve.deltaP_IIstar_one_eq`: `δ_p((II*, 1)) = 2N p⁻¹⁰ T`.
* `WeierstrassCurve.δ_one_eq_ofReal_gotδ_iff_IZeroStar_row`: `δ_p(1) = ENNReal.ofReal (gotδ p 1)`
  if and only if `δ_p((I₀*, 1)) = ENNReal.ofReal (((p²-1)/3)p⁻⁷T)`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The non-split odd `Iₙ` strata -/

/-- **A point of a stratum `τ_p⁻¹((Iₙ, c))` with `n ≥ 1` and `p ∣ a₄` is a `σ_p`-dilate**, for
every prime `p ≥ 5`. -/
theorem mem_range_of_mem_stratFibre_I_of_dvd_fst (hp : 5 ≤ p) {n c : ℕ} (hn : 1 ≤ n)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I n, c))
    (h4 : (p : ℤ_[p]) ∣ x.1) :
    x ∈ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
  have hstrat : strat p ⟨x, hUp⟩ = (KodairaSymbol.I n, c) := (mem_stratFibre_iff hUp).1 hx
  have hkod : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I n := by
    rw [strat] at hstrat
    exact congrArg Prod.fst hstrat
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
    rw [ofShortNF_c₄]
    exact h4.mul_left _
  have hd : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
    by_contra hnd
    rw [run_eq_of_not_dvd_Δ hUp hnd] at hkod
    exact absurd (KodairaSymbol.I.inj hkod) (by omega)
  obtain ⟨h4', h6'⟩ := TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I
    PadicInt.uniformizer_ne_zero hUp hd hc₄ hkod
  rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4'
  rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6'
  rw [PadicInt.mem_range_scaleProdByPPow_iff]
  exact ⟨h4', h6'⟩

/-- **The non-split level-`n` locus lies in the stratum `τ_p⁻¹((Iₙ, 1))` for odd `n`.** -/
theorem iNonSplitLocus_subset_stratFibre_one (hp : 5 ≤ p) {n : ℕ} (hodd : Odd n) :
    iNonSplitLocus p n ⊆ stratFibre p (KodairaSymbol.I n, 1) := by
  have hoddp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rintro x ⟨hxL, hns⟩
  have hUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_of_mem_iLocus hp hxL
  have hΔv := emultiplicity_Δ_of_mem_iLocus hp hxL
  have hc₄ := not_dvd_c₄_of_mem_iLocus hp hxL
  have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := dvd_Δ_of_emultiplicity_eq hodd.pos hΔv
  have htoNat : (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat = n :=
    (toNat_emultiplicity_Δ_eq_iff hUp n).2 hΔv
  have hnosplit : ¬ Step2.TangentSplits (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    intro hsplit
    have hsq := (Step2.tangentSplits_iff_isSquare_neg_c₆ hpΔ hc₄
      (not_dvd_two_of_odd hoddp)).1 hsplit
    rw [ofShortNF_c₆, show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 by ring,
      isSquare_mod_iff_isSquare_toZMod] at hsq
    exact hns hsq
  have hκ : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
      = KodairaSymbol.I n := by
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄, htoNat]
  have hc : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 1 := by
    rw [run_tamagawaNumber_of_nodal hUp hpΔ hc₄, htoNat, ite_eq_right hnosplit, ite_eq_left hodd]
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

/-- **The minimal part of the stratum `τ_p⁻¹((Iₙ, 1))` is the non-split level-`n` locus**, for
every prime `p ≥ 5` and every odd `n ≥ 3`:

  `τ_p⁻¹((Iₙ, 1)) ∖ σ_p(ℤ_p²) = {p ∤ a₄, v_p(4a₄³ + 27a₆²) = n, 864a₆ a non-square mod p}`.
-/
theorem stratFibre_diff_range_eq_iNonSplitLocus (hp : 5 ≤ p) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    stratFibre p (KodairaSymbol.I n, 1) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = iNonSplitLocus p n := by
  have hoddp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have h4 : ¬ (p : ℤ_[p]) ∣ x.1 := fun hd =>
      hxR (mem_range_of_mem_stratFibre_I_of_dvd_fst hp (by omega) hxF hd)
    have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
      rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
      exact h4
    have hs := (mem_stratFibre_iff hUp).1 hxF
    rw [strat] at hs
    have hκ : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
        = KodairaSymbol.I n := congrArg Prod.fst hs
    have hc : (run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).tamagawaNumber
        = 1 := congrArg Prod.snd hs
    have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
      by_contra hnd
      rw [run_eq_of_not_dvd_Δ hUp hnd] at hκ
      exact absurd (KodairaSymbol.I.inj hκ) (by omega)
    rw [run_kodairaSymbol_of_nodal hUp hpΔ hc₄] at hκ
    have hΔv : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((n : ℕ) : ℕ∞) :=
      (toNat_emultiplicity_Δ_eq_iff hUp n).1 (KodairaSymbol.I.inj hκ)
    have htoNat : (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat = n :=
      KodairaSymbol.I.inj hκ
    rw [run_tamagawaNumber_of_nodal hUp hpΔ hc₄, htoNat] at hc
    have hnosplit : ¬ Step2.TangentSplits (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
      intro hsplit
      rw [ite_eq_left hsplit] at hc
      omega
    have hns : ¬ IsSquare (PadicInt.toZMod (864 * x.2)) := by
      intro hsq
      refine hnosplit ((Step2.tangentSplits_iff_isSquare_neg_c₆ hpΔ hc₄
        (not_dvd_two_of_odd hoddp)).2 ?_)
      rw [ofShortNF_c₆, show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 from by ring,
        isSquare_mod_iff_isSquare_toZMod]
      exact hsq
    rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add] at hΔv
    exact ⟨⟨h4, hΔv⟩, hns⟩
  · intro x hx
    refine ⟨iNonSplitLocus_subset_stratFibre_one hp hodd hx, fun hr => ?_⟩
    exact hx.1.1 (dvd_trans (dvd_pow_self _ (by norm_num : 4 ≠ 0))
      (PadicInt.mem_range_scaleProdByPPow_iff.1 hr).1)

/-- **The densities of the non-split odd `Iₙ` strata**, for every prime `p ≥ 5` and every odd
`n ≥ 3`:

  `δ_p((Iₙ, 1)) = 2N² p^{-(n+2)} (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)²p^{8-n}/(2(p¹⁰-1))`. -/
theorem deltaP_I_one_eq_of_odd (hp : 5 ≤ p) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    deltaP p (KodairaSymbol.I n, 1)
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (n + 2)
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_iNonSplitLocus hp hn hodd,
    ← iFineLocus_false, volume_iFineLocus_eq hp (by omega)]

/-! ### Which Kodaira symbols can carry the Tamagawa number `1`

Step 2 reports `(Iₙ, if split then n else if Odd n then 1 else 2)`, so `c = 1` forces `n` to be
odd. The Tamagawa number `1` is carried by `I₀`, the odd `Iₙ`, `II`, `I₀*`, `IV`, `IV*` and `II*`,
and never by `III`, `III*` or `Iₙ*`. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Step 1 reports `(I₀, 1)`, one of the admitted symbols. -/
theorem Step1.kodairaSymbol_of_tamagawaNumber_eq_one
    (h : Step1.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  exact Or.inl rfl

/-- Step 2 reports `Iₙ`, and `c = 1` forces `n` to be odd. -/
theorem Step2.kodairaSymbol_of_tamagawaNumber_eq_one
    (h : Step2.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step1.kodairaSymbol_of_tamagawaNumber_eq_one h hc
  · have hb : ¬ (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W').b₂ := by
      intro hb'
      rw [ite_eq_left hb'] at h
      simp at h
    rw [ite_eq_right hb] at h
    obtain rfl := Except.error.inj h
    dsimp only at hc ⊢
    refine Or.inr (Or.inl ?_)
    split_ifs at hc with hsp hodd
    · exact ⟨0, by rw [hc]⟩
    · obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by rw [hk]⟩
    · simp at hc

/-- Step 3 reports `(II, 1)`. -/
theorem Step3.kodairaSymbol_of_tamagawaNumber_eq_one
    (h : Step3.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_of_tamagawaNumber_eq_one h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (Or.inr (Or.inl rfl))

/-- Step 4 reports `(III, 2)`, which `c = 1` excludes. -/
theorem Step4.kodairaSymbol_of_tamagawaNumber_eq_one
    (h : Step4.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_of_tamagawaNumber_eq_one h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- Step 5 reports `IV`, one of the admitted symbols. -/
theorem Step5.kodairaSymbol_of_tamagawaNumber_eq_one
    (h : Step5.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_of_tamagawaNumber_eq_one h hc
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- Step 6 reports `I₀*`, one of the admitted symbols. -/
theorem Step6.kodairaSymbol_of_tamagawaNumber_eq_one
    (h : Step6.run (p : ℤ_[p]) W = Except.error out) (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_of_tamagawaNumber_eq_one h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- Every answer of the `Iₙ*` subprocedure of Step 7 reports `4` or `2`, never `1`. -/
theorem Step7.subprocedure_tamagawaNumber_ne_one (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber ≠ 1 := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => dsimp only; split_ifs <;> simp
  | case3 => dsimp only; split_ifs <;> simp

/-- Step 7 answers inside its `Iₙ*` subprocedure, whose Tamagawa numbers are `4` and `2`. -/
theorem Step7.kodairaSymbol_of_tamagawaNumber_eq_one (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_of_tamagawaNumber_eq_one (heq.trans h) hc
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hc ?_
    apply Step7.subprocedure_tamagawaNumber_ne_one

/-- Step 8 reports `IV*`, one of the admitted symbols. -/
theorem Step8.kodairaSymbol_of_tamagawaNumber_eq_one (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_of_tamagawaNumber_eq_one hΔ h hc
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-- Step 9 reports `(III*, 2)`, which `c = 1` excludes. -/
theorem Step9.kodairaSymbol_of_tamagawaNumber_eq_one (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.kodairaSymbol_of_tamagawaNumber_eq_one hΔ h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hc

/-- Step 10 reports `(II*, 1)`, one of the admitted symbols. -/
theorem Step10.kodairaSymbol_of_tamagawaNumber_eq_one (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.kodairaSymbol_of_tamagawaNumber_eq_one hΔ h hc
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- **An answer of Tamagawa number `1` at Steps 1–11** has Kodaira symbol `I₀`, an odd `Iₙ`, `II`,
`I₀*`, `IV`, `IV*` or `II*`. -/
theorem Step11.kodairaSymbol_of_tamagawaNumber_eq_one (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hc : out.tamagawaNumber = 1) :
    out.kodairaSymbol = KodairaSymbol.I 0
      ∨ (∃ k : ℕ, out.kodairaSymbol = KodairaSymbol.I (2 * k + 1))
      ∨ out.kodairaSymbol = KodairaSymbol.II ∨ out.kodairaSymbol = KodairaSymbol.I! 0
      ∨ out.kodairaSymbol = KodairaSymbol.IV ∨ out.kodairaSymbol = KodairaSymbol.IV!
      ∨ out.kodairaSymbol = KodairaSymbol.II! := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.kodairaSymbol_of_tamagawaNumber_eq_one hΔ h hc
  · simp at h

/-- **Only `I₀`, the odd `Iₙ`, `II`, `I₀*`, `IV`, `IV*` and `II*` carry the Tamagawa number `1`**,
for every Weierstrass curve over `ℤ_p` with `Δ ≠ 0`. -/
theorem run_kodairaSymbol_of_tamagawaNumber_eq_one {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) :
    (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 →
      (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 0 ∨
        (∃ k : ℕ, (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
          = KodairaSymbol.I (2 * k + 1)) ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! 0 ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV! ∨
        (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II! := by
  induction W, hΔ using run.induct PadicInt.uniformizer_ne_zero with
  | case1 W hΔ out h =>
    intro hc
    rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ h] at hc ⊢
    exact Step11.kodairaSymbol_of_tamagawaNumber_eq_one hΔ h hc
  | case2 W hΔ W' h ih =>
    intro hc
    have hΔ' : W'.Δ ≠ 0 := fun h0 =>
      hΔ (by rw [← Step11.run_Δ PadicInt.uniformizer_ne_zero hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ h hΔ'] at hc ⊢
    exact ih hc

end TateAlgorithm

/-! ### The fibre `{c = 1}`, as seven families of strata -/

/-- **The fibre `{c = 1}` is exactly the union of the strata `(I₀, 1)`, `(II, 1)`, `(I₀*, 1)`,
`(IV, 1)`, `(IV*, 1)`, `(II*, 1)` and the odd multiplicative family `(I_{2k+1}, 1)`**, at every
prime. -/
theorem iUnion_stratFibre_one_eq :
    (⋃ κ : KodairaSymbol, stratFibre p (κ, 1))
      = stratFibre p (KodairaSymbol.I 0, 1) ∪ stratFibre p (KodairaSymbol.II, 1)
          ∪ stratFibre p (KodairaSymbol.I! 0, 1) ∪ stratFibre p (KodairaSymbol.IV, 1)
          ∪ stratFibre p (KodairaSymbol.IV!, 1) ∪ stratFibre p (KodairaSymbol.II!, 1)
        ∪ (⋃ k : ℕ, stratFibre p (KodairaSymbol.I (2 * k + 1), 1)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨κ, hxκ⟩ := Set.mem_iUnion.1 hx
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxκ
    have hs := (mem_stratFibre_iff hUp).1 hxκ
    rw [strat] at hs
    have hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 1 := congrArg Prod.snd hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = κ := congrArg Prod.fst hs
    rcases TateAlgorithm.run_kodairaSymbol_of_tamagawaNumber_eq_one hUp hc with
      h | ⟨k, h⟩ | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (by rw [hκ.symm.trans h] at hxκ; exact hxκ))))))
    · exact Or.inr (Set.mem_iUnion.2 ⟨k, by rw [hκ.symm.trans h] at hxκ; exact hxκ⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        (by rw [hκ.symm.trans h] at hxκ; exact hxκ))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        (by rw [hκ.symm.trans h] at hxκ; exact hxκ)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr
        (by rw [hκ.symm.trans h] at hxκ; exact hxκ))))
    · exact Or.inl (Or.inl (Or.inr (by rw [hκ.symm.trans h] at hxκ; exact hxκ)))
    · exact Or.inl (Or.inr (by rw [hκ.symm.trans h] at hxκ; exact hxκ))
  · refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_) ?_) ?_) ?_
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _
    · exact Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _
    · exact Set.iUnion_subset fun k => Set.subset_iUnion (fun κ => stratFibre p (κ, 1)) _

/-- The odd multiplicative part of the fibre `{c = 1}` is measurable, being a countable union of
open sets. -/
theorem measurableSet_iUnion_stratFibre_I_odd_one :
    MeasurableSet (⋃ k : ℕ, stratFibre p (KodairaSymbol.I (2 * k + 1), 1)) :=
  MeasurableSet.iUnion fun k =>
    (isOpen_stratFibre (p := p) (KodairaSymbol.I (2 * k + 1), 1)).measurableSet

/-- **The odd multiplicative part of `{c = 1}` has mass `∑_k δ_p((I_{2k+1}, 1))`.** -/
theorem volume_iUnion_stratFibre_I_odd_one :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (⋃ k : ℕ, stratFibre p (KodairaSymbol.I (2 * k + 1), 1))
      = ∑' k : ℕ, deltaP p (KodairaSymbol.I (2 * k + 1), 1) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : ℕ => stratFibre p (KodairaSymbol.I (2 * k + 1), 1))) := by
    intro i j hij
    refine disjoint_stratFibre_of_ne (fun h => hij ?_) 1 1
    have := KodairaSymbol.I.inj h
    omega
  rw [measure_iUnion hdisj fun k =>
    (isOpen_stratFibre (p := p) (KodairaSymbol.I (2 * k + 1), 1)).measurableSet]
  exact tsum_congr fun k => volume_stratFibre _

/-- The union of the six strata `(I₀, 1)`, `(II, 1)`, `(I₀*, 1)`, `(IV, 1)`, `(IV*, 1)`, `(II*, 1)`
has the sum of their masses. -/
private theorem volume_union_six_stratFibre_one :
    (volume : Measure (ℤ_[p] × ℤ_[p]))
        (stratFibre p (KodairaSymbol.I 0, 1) ∪ stratFibre p (KodairaSymbol.II, 1)
          ∪ stratFibre p (KodairaSymbol.I! 0, 1) ∪ stratFibre p (KodairaSymbol.IV, 1)
          ∪ stratFibre p (KodairaSymbol.IV!, 1) ∪ stratFibre p (KodairaSymbol.II!, 1))
      = deltaP p (KodairaSymbol.I 0, 1) + deltaP p (KodairaSymbol.II, 1)
        + deltaP p (KodairaSymbol.I! 0, 1) + deltaP p (KodairaSymbol.IV, 1)
        + deltaP p (KodairaSymbol.IV!, 1) + deltaP p (KodairaSymbol.II!, 1) := by
  have d01 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 0) (κ' := KodairaSymbol.II) (by simp) 1 1
  have d02 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 0) (κ' := KodairaSymbol.I! 0) (by simp) 1 1
  have d03 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 0) (κ' := KodairaSymbol.IV) (by simp) 1 1
  have d04 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 0) (κ' := KodairaSymbol.IV!) (by simp) 1 1
  have d05 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I 0) (κ' := KodairaSymbol.II!) (by simp) 1 1
  have d12 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.II) (κ' := KodairaSymbol.I! 0) (by simp) 1 1
  have d13 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.II) (κ' := KodairaSymbol.IV) (by simp) 1 1
  have d14 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.II) (κ' := KodairaSymbol.IV!) (by simp) 1 1
  have d15 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.II) (κ' := KodairaSymbol.II!) (by simp) 1 1
  have d23 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I! 0) (κ' := KodairaSymbol.IV) (by simp) 1 1
  have d24 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I! 0) (κ' := KodairaSymbol.IV!) (by simp) 1 1
  have d25 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.I! 0) (κ' := KodairaSymbol.II!) (by simp) 1 1
  have d34 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.IV) (κ' := KodairaSymbol.IV!) (by simp) 1 1
  have d35 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.IV) (κ' := KodairaSymbol.II!) (by simp) 1 1
  have d45 := disjoint_stratFibre_of_ne (p := p)
    (κ := KodairaSymbol.IV!) (κ' := KodairaSymbol.II!) (by simp) 1 1
  rw [measure_union ((((d05.union_left d15).union_left d25).union_left d35).union_left d45)
      (isOpen_stratFibre (p := p) (KodairaSymbol.II!, 1)).measurableSet,
    measure_union (((d04.union_left d14).union_left d24).union_left d34)
      (isOpen_stratFibre (p := p) (KodairaSymbol.IV!, 1)).measurableSet,
    measure_union ((d03.union_left d13).union_left d23)
      (isOpen_stratFibre (p := p) (KodairaSymbol.IV, 1)).measurableSet,
    measure_union (d02.union_left d12)
      (isOpen_stratFibre (p := p) (KodairaSymbol.I! 0, 1)).measurableSet,
    measure_union d01 (isOpen_stratFibre (p := p) (KodairaSymbol.II, 1)).measurableSet,
    volume_stratFibre, volume_stratFibre, volume_stratFibre, volume_stratFibre,
    volume_stratFibre, volume_stratFibre]

/-- **`δ_p(1)` as a sum of densities of strata**, at every prime:

  `δ_p(1) = δ_p((I₀,1)) + δ_p((II,1)) + δ_p((I₀*,1)) + δ_p((IV,1)) + δ_p((IV*,1)) + δ_p((II*,1))
            + ∑_{k ≥ 0} δ_p((I_{2k+1}, 1))`.
-/
theorem δ_one_eq_add_tsum :
    δ p 1 = deltaP p (KodairaSymbol.I 0, 1) + deltaP p (KodairaSymbol.II, 1)
        + deltaP p (KodairaSymbol.I! 0, 1) + deltaP p (KodairaSymbol.IV, 1)
        + deltaP p (KodairaSymbol.IV!, 1) + deltaP p (KodairaSymbol.II!, 1)
      + ∑' k : ℕ, deltaP p (KodairaSymbol.I (2 * k + 1), 1) := by
  have hO : ∀ κ : KodairaSymbol, (∀ k : ℕ, KodairaSymbol.I (2 * k + 1) ≠ κ) →
      Disjoint (stratFibre p (κ, 1))
        (⋃ k : ℕ, stratFibre p (KodairaSymbol.I (2 * k + 1), 1)) := fun κ h =>
    (Set.disjoint_iUnion_left.2 fun k => disjoint_stratFibre_of_ne (h k) 1 1).symm
  have e0 := hO (KodairaSymbol.I 0) fun k h => by have := KodairaSymbol.I.inj h; omega
  have e1 := hO KodairaSymbol.II fun k => by simp
  have e2 := hO (KodairaSymbol.I! 0) fun k => by simp
  have e3 := hO KodairaSymbol.IV fun k => by simp
  have e4 := hO KodairaSymbol.IV! fun k => by simp
  have e5 := hO KodairaSymbol.II! fun k => by simp
  rw [← volume_iUnion_stratFibre_kodaira (p := p) 1, iUnion_stratFibre_one_eq,
    measure_union (((((e0.union_left e1).union_left e2).union_left e3).union_left e4).union_left e5)
      measurableSet_iUnion_stratFibre_I_odd_one,
    volume_union_six_stratFibre_one, volume_iUnion_stratFibre_I_odd_one]

/-! ### The odd multiplicative family, summed -/

/-- **The odd multiplicative contribution to `δ_p(1)`**, for every prime `p ≥ 5`:

  `∑_{k ≥ 0} δ_p((I_{2k+1}, 1)) = 4N² p⁻³ T + 2N² p⁻⁵ T (1 - p⁻²)⁻¹`,   `T = (1 - p⁻¹⁰)⁻¹`,

where `2N = p - 1`. In closed form the total is `(p-1)p⁷/(p¹⁰-1) + (p-1)p⁷/(2(p+1)(p¹⁰-1))`. -/
theorem tsum_deltaP_I_odd_one_eq (hp : 5 ≤ p) :
    ∑' k : ℕ, deltaP p (KodairaSymbol.I (2 * k + 1), 1)
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 3
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
        + 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ * (1 - ((p : ℝ≥0∞)⁻¹) ^ 2)⁻¹ := by
  have h0 : deltaP p (KodairaSymbol.I (2 * 0 + 1), 1)
      = 4 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 3
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
    rw [show (2 * 0 + 1 : ℕ) = 1 from by norm_num]
    exact deltaP_I_one_eq hp
  have hstep : ∀ k : ℕ, deltaP p (KodairaSymbol.I (2 * (k + 1) + 1), 1)
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 5
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ * (((p : ℝ≥0∞)⁻¹) ^ 2) ^ k := by
    intro k
    rw [deltaP_I_one_eq_of_odd hp (by omega) ⟨k + 1, by ring⟩,
      show 2 * (k + 1) + 1 + 2 = 5 + 2 * k from by ring, pow_add, pow_mul]
    ring
  rw [tsum_eq_zero_add' ENNReal.summable, h0, tsum_congr hstep, ENNReal.tsum_mul_left,
    ENNReal.tsum_geometric]

/-! ### The three real closed forms -/

variable (p) in
/-- **The sum of six densities of strata in `{c = 1}`**, as a real number: `(I₀, 1)`, `(I₁, 1)`,
the non-split odd `(Iₙ, 1)` for `n ≥ 3`, `(II, 1)`, `(IV, 1)` and `(IV*, 1)`, each with the factor
`T = (1 - p⁻¹⁰)⁻¹`:

  `((p-1)/p + (p-1)²/p³ + (p-1)/(2p³(p+1)) + (p-1)/p³ + (p-1)/(2p⁵) + (p-1)/(2p⁸)) T`.

This is meaningful for `p ≥ 5`. -/
noncomputable def gotHeadOneEvaluated : ℝ :=
  (((p : ℝ) - 1) / (p : ℝ) + ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 3
      + ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 3 * ((p : ℝ) + 1)) + ((p : ℝ) - 1) / (p : ℝ) ^ 3
      + ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 5) + ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 8))
    * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

variable (p) in
/-- **The closed form of `δ_p((I₀*, 1))`** at `p ≥ 5`: `((p²-1)/3) p⁻⁷ (1 - p⁻¹⁰)⁻¹`.

The numerator is the number of depressed cubics `x³ + Ax + B` over `𝔽_p` with no root in `𝔽_p`. -/
noncomputable def gotIZeroStarOne : ℝ :=
  ((p : ℝ) ^ 2 - 1) / (3 * (p : ℝ) ^ 7) * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

variable (p) in
/-- **The closed form of `δ_p((II*, 1))`** at `p ≥ 5`: `(p-1) p⁻¹⁰ (1 - p⁻¹⁰)⁻¹`. -/
noncomputable def gotIIStarOne : ℝ :=
  ((p : ℝ) - 1) / (p : ℝ) ^ 10 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹

omit [Fact p.Prime] in
/-- `1 - p⁻ᵏ > 0` on `ℝ` for `p > 1` and `k ≠ 0`. -/
theorem one_sub_inv_pow_pos (hp : 1 < p) {k : ℕ} (hk : k ≠ 0) :
    (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ k :=
  sub_pos.2 (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)) hk)

/-- `(1 - x⁻ᵏ)⁻¹ = xᵏ / (xᵏ - 1)` for `x ≠ 0`. -/
theorem inv_one_sub_inv_pow_eq_div {x : ℝ} (hx : x ≠ 0) (k : ℕ) :
    (1 - x⁻¹ ^ k)⁻¹ = x ^ k / (x ^ k - 1) := by
  rw [← inv_div, inv_pow]
  congr 1
  field_simp

omit [Fact p.Prime] in
/-- `p⁻¹` on `ℝ≥0∞` is `ENNReal.ofReal` of its real counterpart, for `p ≠ 0`. -/
theorem inv_natCast_eq_ofReal (hp : 0 < p) : ((p : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp), ENNReal.ofReal_natCast]

omit [Fact p.Prime] in
/-- `1 - p⁻ᵏ` on `ℝ≥0∞` is `ENNReal.ofReal` of its real counterpart, for `p ≠ 0`. -/
theorem one_sub_inv_pow_eq_ofReal (hp : 0 < p) (k : ℕ) :
    (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ k = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ k) := by
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, inv_natCast_eq_ofReal hp,
    ← ENNReal.ofReal_pow (by positivity)]

/-- `|goodRes p| = (p - 1)/2` on `ℝ`, for every prime `p ≥ 5`. -/
theorem cast_card_goodRes_eq (hp : 5 ≤ p) :
    (((goodRes p).card : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
  have hcast : (p : ℝ) = 2 * (((goodRes p).card : ℕ) : ℝ) + 1 := by
    exact_mod_cast eq_two_mul_card_goodRes_add_one (p := p) hp
  linarith

omit [Fact p.Prime] in
/-- `(1 - p⁻¹⁰)⁻¹ > 0` on `ℝ` at `p ≥ 5`. -/
theorem inv_one_sub_inv_pow_ten_pos (hp : 5 ≤ p) : (0 : ℝ) < (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ :=
  inv_pos.2 (one_sub_inv_pow_pos (by omega) (by norm_num))

omit [Fact p.Prime] in
/-- `gotHeadOneEvaluated p` is nonnegative for `p ≥ 5`. -/
theorem gotHeadOneEvaluated_nonneg (hp : 5 ≤ p) : (0 : ℝ) ≤ gotHeadOneEvaluated p := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have h5 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [gotHeadOneEvaluated]
  refine mul_nonneg ?_ (inv_one_sub_inv_pow_ten_pos hp).le
  have e1 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) := div_nonneg hp1 h5.le
  have e2 : (0 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 3 := by positivity
  have e3 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 3 * ((p : ℝ) + 1)) :=
    div_nonneg hp1 (by positivity)
  have e4 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 3 := div_nonneg hp1 (by positivity)
  have e5 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 5) := div_nonneg hp1 (by positivity)
  have e6 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 8) := div_nonneg hp1 (by positivity)
  linarith

omit [Fact p.Prime] in
/-- The `(I₀*, 1)` closed form is nonnegative. -/
theorem gotIZeroStarOne_nonneg (hp : 5 ≤ p) : (0 : ℝ) ≤ gotIZeroStarOne p := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [gotIZeroStarOne]
  exact mul_nonneg (div_nonneg (by nlinarith) (by positivity))
    (inv_one_sub_inv_pow_ten_pos hp).le

omit [Fact p.Prime] in
/-- The `(II*, 1)` closed form is nonnegative. -/
theorem gotIIStarOne_nonneg (hp : 5 ≤ p) : (0 : ℝ) ≤ gotIIStarOne p := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [gotIIStarOne]
  exact mul_nonneg (div_nonneg (by linarith) (by positivity))
    (inv_one_sub_inv_pow_ten_pos hp).le

omit [Fact p.Prime] in
/-- **The closed forms of the strata in `{c = 1}` add up to `gotδ p 1`**, at every `p ≥ 5`:

  `gotHeadOneEvaluated p + gotIZeroStarOne p + gotIIStarOne p = gotδ p 1`.
-/
theorem gotHeadOneEvaluated_add_add_eq_gotδ_one (hp : 5 ≤ p) :
    gotHeadOneEvaluated p + gotIZeroStarOne p + gotIIStarOne p = gotδ p 1 := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hnep1 : (p : ℝ) + 1 ≠ 0 := by linarith
  have hne10 : (p : ℝ) ^ 10 - 1 ≠ 0 := by
    linarith [one_lt_pow₀ (by linarith : (1 : ℝ) < p) (by norm_num : 10 ≠ 0)]
  have hneQ : (p : ℝ) ^ 8 + (p : ℝ) ^ 6 + (p : ℝ) ^ 4 + (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  rw [gotHeadOneEvaluated, gotIZeroStarOne, gotIIStarOne, gotδ_one_of_five_le hp, gotD, gotQ,
    inv_one_sub_inv_pow_eq_div hne]
  field_simp
  ring

/-! ### `δ_p(1)` in terms of `δ_p((I₀*, 1))` and `δ_p((II*, 1))` -/

/-- **The six evaluated densities in `δ_p(1)` sum to `gotHeadOneEvaluated p`** on `ℝ`, for every
prime `p ≥ 5`, with `N = |goodRes p|` and `T = (1 - p⁻¹⁰)⁻¹`. -/
theorem gotI0Volume_add_rows_eq_gotHeadOneEvaluated (hp : 5 ≤ p) :
    gotI0Volume p + 2 * (((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 3 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
      + (((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 5 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
      + (((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 8 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
      + 4 * (((goodRes p).card : ℕ) : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 3 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
      + 2 * (((goodRes p).card : ℕ) : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 5 * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
        * (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
      = gotHeadOneEvaluated p := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hnep1 : (p : ℝ) + 1 ≠ 0 := by linarith
  have hne10 : (p : ℝ) ^ 10 - 1 ≠ 0 := by
    linarith [one_lt_pow₀ (by linarith : (1 : ℝ) < p) (by norm_num : 10 ≠ 0)]
  have hne2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [gotHeadOneEvaluated, gotI0Volume, cast_card_goodRes_eq hp, inv_one_sub_inv_pow_eq_div hne,
    inv_one_sub_inv_pow_eq_div hne]
  field_simp
  ring

/-- The six evaluated densities in `δ_p(1)`, each passed through `ENNReal.ofReal`, sum to
`ENNReal.ofReal (gotHeadOneEvaluated p)`, for every prime `p ≥ 5`. -/
theorem ofReal_add_rows_eq_ofReal_gotHeadOneEvaluated (hp : 5 ≤ p) :
    ENNReal.ofReal (gotI0Volume p)
        + ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 3
          * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
        + ENNReal.ofReal ((((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 5
          * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
        + ENNReal.ofReal ((((goodRes p).card : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ 8
          * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
        + ENNReal.ofReal (4 * (((goodRes p).card : ℕ) : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 3
          * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹)
        + ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 5
          * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ * (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹)
      = ENNReal.ofReal (gotHeadOneEvaluated p) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hTr := (inv_one_sub_inv_pow_ten_pos hp).le
  have hTr2 := (inv_pos.2 (one_sub_inv_pow_pos (p := p) (by omega) two_ne_zero)).le
  have ha0 : (0 : ℝ) ≤ gotI0Volume p := by
    rw [gotI0Volume]
    exact div_nonneg (mul_nonneg (by linarith) (by positivity))
      (by linarith [one_lt_pow₀ (by linarith : (1 : ℝ) < p) (by norm_num : 10 ≠ 0)])
  have ha1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (((goodRes p).card : ℕ) : ℝ)
    * ((p : ℝ)⁻¹) ^ 3) hTr
  have ha2 := mul_nonneg (by positivity : (0 : ℝ) ≤ (((goodRes p).card : ℕ) : ℝ)
    * ((p : ℝ)⁻¹) ^ 5) hTr
  have ha3 := mul_nonneg (by positivity : (0 : ℝ) ≤ (((goodRes p).card : ℕ) : ℝ)
    * ((p : ℝ)⁻¹) ^ 8) hTr
  have ha4 := mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (((goodRes p).card : ℕ) : ℝ) ^ 2
    * ((p : ℝ)⁻¹) ^ 3) hTr
  have ha5 := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2
    * (((goodRes p).card : ℕ) : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 5) hTr) hTr2
  have ha01 := add_nonneg ha0 ha1
  have ha02 := add_nonneg ha01 ha2
  have ha03 := add_nonneg ha02 ha3
  rw [← ENNReal.ofReal_add ha0 ha1, ← ENNReal.ofReal_add ha01 ha2, ← ENNReal.ofReal_add ha02 ha3,
    ← ENNReal.ofReal_add ha03 ha4, ← ENNReal.ofReal_add (add_nonneg ha03 ha4) ha5,
    gotI0Volume_add_rows_eq_gotHeadOneEvaluated hp]

/-- **`δ_p(1)` with six of its densities evaluated**, for every prime `p ≥ 5`:

  `δ_p(1) = gotHeadOneEvaluated p + δ_p((I₀*, 1)) + δ_p((II*, 1))`.
-/
theorem δ_one_eq_ofReal_add_two_rows (hp : 5 ≤ p) :
    δ p 1 = ENNReal.ofReal (gotHeadOneEvaluated p)
      + deltaP p (KodairaSymbol.I! 0, 1) + deltaP p (KodairaSymbol.II!, 1) := by
  have hp0 : 0 < p := by omega
  have hpos10 : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 := one_sub_inv_pow_pos (by omega) (by norm_num)
  have hpos2 : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 2 := one_sub_inv_pow_pos (by omega) (by norm_num)
  have hTr : (0 : ℝ) < (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹ := inv_pos.2 hpos10
  have hinvE := inv_natCast_eq_ofReal hp0
  have hten := one_sub_inv_pow_eq_ofReal hp0 10
  have htwo := one_sub_inv_pow_eq_ofReal hp0 2
  have key : ∀ (c : ℝ) (k : ℕ), 0 ≤ c →
      ENNReal.ofReal c * ((p : ℝ≥0∞)⁻¹) ^ k * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
        = ENNReal.ofReal (c * ((p : ℝ)⁻¹) ^ k * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹) := by
    intro c k hc
    rw [hten, ← ENNReal.ofReal_inv_of_pos hpos10, hinvE, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]
  have key2 : ∀ (c : ℝ) (k : ℕ), 0 ≤ c →
      ENNReal.ofReal c * ((p : ℝ≥0∞)⁻¹) ^ k * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
          * (1 - ((p : ℝ≥0∞)⁻¹) ^ 2)⁻¹
        = ENNReal.ofReal (c * ((p : ℝ)⁻¹) ^ k * (1 - ((p : ℝ)⁻¹) ^ 10)⁻¹
            * (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹) := by
    intro c k hc
    rw [key c k hc, htwo, ← ENNReal.ofReal_inv_of_pos hpos2,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc (by positivity)) hTr.le)]
  have hN : (((goodRes p).card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (((goodRes p).card : ℕ) : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have hc2N : (2 : ℝ≥0∞) * (((goodRes p).card : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have hc4N2 : (4 : ℝ≥0∞) * (((goodRes p).card : ℕ) : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (4 * (((goodRes p).card : ℕ) : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have hc2N2 : (2 : ℝ≥0∞) * (((goodRes p).card : ℕ) : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [δ_one_eq_add_tsum, deltaP_I0_eq_ofReal hp (stratScaleInvariant_of_five_le hp),
    deltaP_II_eq hp, hc2N, key _ 3 (by positivity),
    deltaP_IV_one_eq hp, hN, key _ 5 (by positivity),
    deltaP_IVstar_one_eq hp, hN, key _ 8 (by positivity),
    tsum_deltaP_I_odd_one_eq hp, hc4N2, key _ 3 (by positivity), hc2N2,
    key2 _ 5 (by positivity), ← ofReal_add_rows_eq_ofReal_gotHeadOneEvaluated hp]
  ring

/-- **The closed form of `δ_p(1)` is equivalent to closed forms of two densities**, for every prime
`p ≥ 5`:

  `δ_p(1) = ENNReal.ofReal (gotδ p 1)`  ↔  `δ_p((I₀*,1)) + δ_p((II*,1))
      = ENNReal.ofReal (((p²-1)/3)p⁻⁷T + (p-1)p⁻¹⁰T)`.
-/
theorem δ_one_eq_ofReal_gotδ_iff (hp : 5 ≤ p) :
    δ p 1 = ENNReal.ofReal (gotδ p 1) ↔
      deltaP p (KodairaSymbol.I! 0, 1) + deltaP p (KodairaSymbol.II!, 1)
        = ENNReal.ofReal (gotIZeroStarOne p + gotIIStarOne p) := by
  have hE : (0 : ℝ) ≤ gotHeadOneEvaluated p := gotHeadOneEvaluated_nonneg hp
  have h1 : (0 : ℝ) ≤ gotIZeroStarOne p := gotIZeroStarOne_nonneg hp
  have h2 : (0 : ℝ) ≤ gotIIStarOne p := gotIIStarOne_nonneg hp
  rw [δ_one_eq_ofReal_add_two_rows hp, add_assoc,
    ← gotHeadOneEvaluated_add_add_eq_gotδ_one hp, add_assoc,
    ENNReal.ofReal_add hE (add_nonneg h1 h2),
    ENNReal.add_right_inj ENNReal.ofReal_ne_top]

/-! ### Steps 9 and 10 read off `c₄` and `c₆`

The branch conditions of Steps 9 and 10 are conditions on the coefficients of a translate, pinned
only modulo `p`; each is equivalent to a condition on `c₄` or `c₆`, which no translation moves. -/

/-- `48` is a unit of `ℤ_p` at `p ≥ 5`. -/
theorem isUnit_fortyEight (hp : 5 ≤ p) : IsUnit (48 : ℤ_[p]) := by
  simpa using (isUnit_neg_fortyEight hp).neg

/-- **Step 9's branch condition is `p⁴ ∣ c₄`.** On a curve with `p ∣ a₁`, `p² ∣ a₂` and `p³ ∣ a₃`,
`p⁴ ∣ a₄` exactly when `p⁴ ∣ c₄`. -/
theorem pow_four_dvd_a₄_iff_pow_four_dvd_c₄ (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) ^ 2 * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 3 * A₃) :
    (p : ℤ_[p]) ^ 4 ∣ W.a₄ ↔ (p : ℤ_[p]) ^ 4 ∣ W.c₄ := by
  have hX : (p : ℤ_[p]) ^ 4 ∣ (p : ℤ_[p]) ^ 4 * ((A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * A₁ * A₃) :=
    dvd_mul_right _ _
  have hkey : W.c₄ = (p : ℤ_[p]) ^ 4 * ((A₁ ^ 2 + 4 * A₂) ^ 2 - 24 * A₁ * A₃) - 48 * W.a₄ := by
    rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h1, h2, h3]
    ring
  refine ⟨fun hd => ?_, fun hc => ?_⟩
  · rw [hkey]
    exact dvd_sub hX (hd.mul_left 48)
  · have hs : (p : ℤ_[p]) ^ 4 ∣ 48 * W.a₄ := by
      have hsub := dvd_sub hX hc
      rwa [hkey, sub_sub_cancel] at hsub
    rwa [(isUnit_fortyEight hp).dvd_mul_left] at hs

/-- **Step 10's branch condition is `p⁶ ∣ c₆`.** On a curve with `p ∣ a₁`, `p² ∣ a₂`, `p³ ∣ a₃` and
`p⁴ ∣ a₄`, `p⁶ ∣ a₆` exactly when `p⁶ ∣ c₆`. -/
theorem pow_six_dvd_a₆_iff_pow_six_dvd_c₆ (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    {A₁ A₂ A₃ A₄ : ℤ_[p]} (h1 : W.a₁ = (p : ℤ_[p]) * A₁) (h2 : W.a₂ = (p : ℤ_[p]) ^ 2 * A₂)
    (h3 : W.a₃ = (p : ℤ_[p]) ^ 3 * A₃) (h4 : W.a₄ = (p : ℤ_[p]) ^ 4 * A₄) :
    (p : ℤ_[p]) ^ 6 ∣ W.a₆ ↔ (p : ℤ_[p]) ^ 6 ∣ W.c₆ := by
  have hX : (p : ℤ_[p]) ^ 6 ∣ (p : ℤ_[p]) ^ 6 * (-((A₁ ^ 2 + 4 * A₂) ^ 3)
      + 36 * (A₁ ^ 2 + 4 * A₂) * (2 * A₄ + A₁ * A₃) - 216 * A₃ ^ 2) := dvd_mul_right _ _
  have hkey : W.c₆ = (p : ℤ_[p]) ^ 6 * (-((A₁ ^ 2 + 4 * A₂) ^ 3)
      + 36 * (A₁ ^ 2 + 4 * A₂) * (2 * A₄ + A₁ * A₃) - 216 * A₃ ^ 2) - 864 * W.a₆ := by
    rw [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      h1, h2, h3, h4]
    ring
  refine ⟨fun hd => ?_, fun hc => ?_⟩
  · rw [hkey]
    exact dvd_sub hX (hd.mul_left 864)
  · have hs : (p : ℤ_[p]) ^ 6 ∣ 864 * W.a₆ := by
      have hsub := dvd_sub hX hc
      rwa [hkey, sub_sub_cancel] at hsub
    rwa [(isUnit_eightSixFour hp).dvd_mul_left] at hs

/-- Step 8 succeeds, returning its translate, when its quadratic has a double root. -/
theorem step8_run_eq_ok_of_hasDoubleRoot {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W')
    (hq : (quadratic (p : ℤ_[p]) (Step8.translate (p : ℤ_[p]) W') 2).HasDoubleRoot) :
    Step8.run PadicInt.uniformizer_ne_zero hΔ
      = Except.ok (Step8.translate (p : ℤ_[p]) W') := by
  rw [Step8.run.eq_def, h7]
  simp only [except_ok_bind]
  exact ite_eq_left hq

/-- Step 9 succeeds, returning its translate, when `p⁴ ∣ a₄`. -/
theorem step9_run_eq_ok_of_dvd {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h8 : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W')
    (ha : (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p]) W').a₄) :
    Step9.run PadicInt.uniformizer_ne_zero hΔ
      = Except.ok (Step9.translate (p : ℤ_[p]) W') := by
  rw [Step9.run.eq_def, h8]
  simp only [except_ok_bind]
  exact ite_eq_left ha

/-- Step 10 answers `(II*, 1)` when `p⁶ ∤ a₆`. -/
theorem step10_run_eq_error_of_not_dvd {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h9 : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.ok W')
    (ha : ¬ (p : ℤ_[p]) ^ 6 ∣ W'.a₆) :
    Step10.run PadicInt.uniformizer_ne_zero hΔ
      = Except.error ⟨W', KodairaSymbol.II!, 1⟩ := by
  rw [Step10.run.eq_def, h9]
  simp only [except_ok_bind]
  exact ite_eq_right ha

/-- An answer of Step 10 is the answer of Step 11. -/
theorem step11_error_of_step10 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) {out : Output ℤ_[p]}
    (h10 : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  rw [Step11.run.eq_def, h10]; rfl

/-! ### Steps 5–10 run forwards -/

/-- **The forward run at `II*`, from the invariants.** For every prime `p ≥ 5`, a curve over `ℤ_p`
on which Steps 1–5 succeed and whose invariants satisfy `p⁴ ∣ c₄` and `v_p(c₆) = 5` has reduction
datum `(II*, 1)`. -/
theorem run_eq_IIstar_of_invariants (hp : 5 ≤ p) {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok W') (hc₄ : (p : ℤ_[p]) ^ 4 ∣ W.c₄)
    (hc₆ : (p : ℤ_[p]) ^ 5 ∣ W.c₆) (hc₆' : ¬ (p : ℤ_[p]) ^ 6 ∣ W.c₆) :
    (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II! ∧
      (TateAlgorithm.run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hv5 := Step5.run_hasValuation hϖ h5
  have hv6 := Step6.hasValuation_translate hϖ hv5
  have e₄ : (Step6.translate (p : ℤ_[p]) W').c₄ = W.c₄ := by
    rw [Step6.translate_c₄, Step5.run_c₄ h5]
  have e₆ : (Step6.translate (p : ℤ_[p]) W').c₆ = W.c₆ := by
    rw [Step6.translate_c₆, Step5.run_c₆ h5]
  obtain ⟨A₁, hA₁⟩ := hv6.a₁
  obtain ⟨A₂, hA₂⟩ := hv6.a₂
  obtain ⟨A₃, hA₃⟩ := hv6.a₃
  obtain ⟨A₄, hA₄⟩ := hv6.a₄
  obtain ⟨A₆, hA₆⟩ := hv6.a₆
  rw [pow_one] at hA₁ hA₂
  have ht : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasTripleRoot :=
    (hasTripleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆).2
      (by rw [e₄]; exact dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 4)) hc₄)
  have hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W') 1 1).HasDoubleRoot :=
    (hasDoubleRoot_cubic_iff hp hA₁ hA₂ hA₃ hA₄ hA₆ ht).2
      (by rw [e₆]; exact dvd_trans (pow_dvd_pow _ (by norm_num : 4 ≤ 5)) hc₆)
  have hs6 := step6_run_eq_ok_of_hasDoubleRoot h5 hd
  have hs7 := step7_run_eq_ok_of_hasTripleRoot hΔ hs6 ht
  have hv8 := Step8.hasValuation_translate hϖ hv6 hd ht
  obtain ⟨B₁, hB₁⟩ := hv8.a₁
  obtain ⟨B₂, hB₂⟩ := hv8.a₂
  obtain ⟨B₃, hB₃⟩ := hv8.a₃
  obtain ⟨B₄, hB₄⟩ := hv8.a₄
  obtain ⟨B₆, hB₆⟩ := hv8.a₆
  rw [pow_one] at hB₁
  have f₄ : (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')).c₄ = W.c₄ := by
    rw [Step8.translate_c₄, e₄]
  have f₆ : (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')).c₆ = W.c₆ := by
    rw [Step8.translate_c₆, e₆]
  have hq : (quadratic (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W')) 2).HasDoubleRoot := by
    rw [hasDoubleRoot_quadratic_two_iff hp hB₁ hB₂ hB₃ hB₄ hB₆, f₆]
    exact hc₆
  have hs8 := step8_run_eq_ok_of_hasDoubleRoot hΔ hs7 hq
  have hv9 := Step9.hasValuation_translate hϖ hv8 hq
  obtain ⟨C₁, hC₁⟩ := hv9.a₁
  obtain ⟨C₂, hC₂⟩ := hv9.a₂
  obtain ⟨C₃, hC₃⟩ := hv9.a₃
  rw [pow_one] at hC₁
  have g₄ : (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W'))).c₄ = W.c₄ := by
    rw [Step7.translateY_c₄, f₄]
  have g₆ : (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W'))).c₆ = W.c₆ := by
    rw [Step7.translateY_c₆, f₆]
  have ha₄ : (p : ℤ_[p]) ^ 4 ∣ (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W'))).a₄ := by
    rw [pow_four_dvd_a₄_iff_pow_four_dvd_c₄ hp hC₁ hC₂ hC₃, g₄]
    exact hc₄
  have hs9 := step9_run_eq_ok_of_dvd hΔ hs8 ha₄
  obtain ⟨C₄, hC₄⟩ := ha₄
  have ha₆ : ¬ (p : ℤ_[p]) ^ 6 ∣ (Step9.translate (p : ℤ_[p])
      (Step8.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) W'))).a₆ := by
    rw [pow_six_dvd_a₆_iff_pow_six_dvd_c₆ hp hC₁ hC₂ hC₃ hC₄, g₆]
    exact hc₆'
  have hs10 := step10_run_eq_error_of_not_dvd hΔ hs9 ha₆
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step10 hΔ hs10)]
  exact ⟨rfl, rfl⟩

/-- A short model with `p⁴ ∣ a₄` and `a₆ = p⁵u`, `p ∤ u`, satisfies `p¹¹ ∤ Δ`. -/
theorem not_pow_eleven_dvd_ofShortNF_Δ_of_IIstar (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (h4 : (p : ℤ_[p]) ^ 4 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 5 ∣ a₆) (h6' : ¬ (p : ℤ_[p]) ^ 6 ∣ a₆) :
    ¬ (p : ℤ_[p]) ^ 11 ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨b, rfl⟩ := h6
  intro hd
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left] at hd
  have h1 : (p : ℤ_[p]) ^ 11 ∣ 4 * ((p : ℤ_[p]) ^ 4 * c) ^ 3 :=
    ⟨4 * (p : ℤ_[p]) * c ^ 3, by ring⟩
  have h2 : (p : ℤ_[p]) ^ 11 ∣ (p : ℤ_[p]) ^ 10 * (27 * b ^ 2) := by
    have hs := dvd_sub hd h1
    rwa [show 4 * ((p : ℤ_[p]) ^ 4 * c) ^ 3 + 27 * ((p : ℤ_[p]) ^ 5 * b) ^ 2
      - 4 * ((p : ℤ_[p]) ^ 4 * c) ^ 3 = (p : ℤ_[p]) ^ 10 * (27 * b ^ 2) from by ring] at hs
  obtain ⟨z, hz⟩ := h2
  have h3 : (p : ℤ_[p]) ∣ 27 * b ^ 2 :=
    ⟨z, mul_left_cancel₀ (pow_ne_zero 10 PadicInt.uniformizer_ne_zero) (by rw [hz]; ring)⟩
  rw [(isUnit_twentySeven hp).dvd_mul_left] at h3
  exact h6' (by rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ]
                exact mul_dvd_mul_left _ (PadicInt.prime_p.dvd_of_dvd_pow h3))

/-- **The forward run at `II*` on the short plane.** For every prime `p ≥ 5`, a short model over
`ℤ_p` with `p⁴ ∣ a₄` and `a₆ = p⁵u`, `p ∤ u`, has reduction datum `(II*, 1)`. -/
theorem run_eq_IIstar_of_eq_pow_mul (hp : 5 ≤ p) {a₄ a₆ u : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ^ 4 ∣ a₄) (hu : ¬ (p : ℤ_[p]) ∣ u)
    (ha₆ : a₆ = (p : ℤ_[p]) ^ 5 * u) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II! ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h6 : (p : ℤ_[p]) ^ 5 ∣ a₆ := ⟨u, ha₆⟩
  have hs5 := step5_run_eq_ok_of_dvd hp (dvd_trans (pow_dvd_pow _ (by norm_num : 2 ≤ 4)) h4)
    (dvd_trans (pow_dvd_pow _ (by norm_num : 3 ≤ 5)) h6)
  refine run_eq_IIstar_of_invariants hp hΔ hs5 ?_ ?_ ?_
  · rw [ofShortNF_c₄]; exact h4.mul_left _
  · rw [ofShortNF_c₆]; exact h6.mul_left _
  · rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left, ha₆,
      show (6 : ℕ) = 5 + 1 from rfl, pow_succ_dvd_pow_mul hϖ]
    exact hu

/-! ### Only Step 10 answers `II*` -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- Steps 1–2 answer `Iₙ`, not `II*`. -/
theorem Step2.kodairaSymbol_ne_IIstar (h : Step2.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  obtain ⟨n, hn⟩ := Step2.exists_kodairaSymbol_eq_I h
  rw [hn]; simp

/-- Step 3 answers `II`, not `II*`. -/
theorem Step3.kodairaSymbol_ne_IIstar (h : Step3.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_ne_IIstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 4 answers `III`, not `II*`. -/
theorem Step4.kodairaSymbol_ne_IIstar (h : Step4.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_ne_IIstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 5 answers `IV`, not `II*`. -/
theorem Step5.kodairaSymbol_ne_IIstar (h : Step5.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_ne_IIstar h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 6 answers `I₀*`, not `II*`. -/
theorem Step6.kodairaSymbol_ne_IIstar (h : Step6.run (p : ℤ_[p]) W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_ne_IIstar h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- No answer of the `Iₙ*` subprocedure of Step 7 is `II*`. -/
theorem Step7.subprocedure_kodairaSymbol_ne_IIstar (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ (p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.II! := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 answers `Iₙ*`, not `II*`. -/
theorem Step7.kodairaSymbol_ne_IIstar (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_ne_IIstar (heq.trans h)
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    apply Step7.subprocedure_kodairaSymbol_ne_IIstar

/-- Step 8 answers `IV*`, not `II*`. -/
theorem Step8.kodairaSymbol_ne_IIstar (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_ne_IIstar hΔ h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 9 answers `III*`, not `II*`. -/
theorem Step9.kodairaSymbol_ne_IIstar (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.II! := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.kodairaSymbol_ne_IIstar hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- **Step 10's answer `II*` forces `p⁴ ∣ c₄`, `p⁵ ∣ c₆` and `p⁶ ∤ c₆`.** -/
theorem Step10.pow_dvd_c₄_c₆_of_eq_IIstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II!) :
    (p : ℤ_[p]) ^ 4 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 5 ∣ W.c₆ ∧ ¬ (p : ℤ_[p]) ^ 6 ∣ W.c₆ := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact absurd hκ (Step9.kodairaSymbol_ne_IIstar hΔ h)
  · have hv9 := Step9.run_hasValuation hϖ hΔ h'
    have e₄ : W'.c₄ = W.c₄ := Step9.run_c₄ hϖ hΔ h'
    have e₆ : W'.c₆ = W.c₆ := Step9.run_c₆ hϖ hΔ h'
    obtain ⟨C₁, hC₁⟩ := hv9.a₁
    obtain ⟨C₂, hC₂⟩ := hv9.a₂
    obtain ⟨C₃, hC₃⟩ := hv9.a₃
    obtain ⟨C₄, hC₄⟩ := hv9.a₄
    dsimp only at hC₁ hC₂ hC₃ hC₄
    rw [pow_one] at hC₁
    have hcon : ¬ (p : ℤ_[p]) ^ 6 ∣ W'.a₆ := by
      intro h6
      rw [ite_eq_left h6] at h
      simp at h
    refine ⟨e₄ ▸ hv9.c₄, e₆ ▸ hv9.c₆, ?_⟩
    rw [← e₆, ← pow_six_dvd_a₆_iff_pow_six_dvd_c₆ hp hC₁ hC₂ hC₃ hC₄]
    exact hcon

/-- **An answer of `II*` at Steps 1–11 forces `p⁴ ∣ c₄`, `p⁵ ∣ c₆` and `p⁶ ∤ c₆`**, i.e.
`v_p(a₄) ≥ 4` and `v_p(a₆) = 5` on the short plane. -/
theorem Step11.pow_dvd_c₄_c₆_of_eq_IIstar (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II!) :
    (p : ℤ_[p]) ^ 4 ∣ W.c₄ ∧ (p : ℤ_[p]) ^ 5 ∣ W.c₆ ∧ ¬ (p : ℤ_[p]) ^ 6 ∣ W.c₆ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.pow_dvd_c₄_c₆_of_eq_IIstar hp hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The density of the `II*` stratum -/

variable (p) in
/-- **The minimal `II*` locus**: `p⁴ ∣ a₄` and `v_p(a₆) = 5`. -/
noncomputable def stratMinimalIIstar : Set (ℤ_[p] × ℤ_[p]) :=
  ((Ideal.span {(p : ℤ_[p]) ^ 4} : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ
    {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = ((5 : ℕ) : ℕ∞)}

/-- A pair lies in the minimal `II*` locus iff `p⁴ ∣ a₄`, `p⁵ ∣ a₆` and `p⁶ ∤ a₆`. -/
theorem mem_stratMinimalIIstar_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ stratMinimalIIstar p ↔
      (p : ℤ_[p]) ^ 4 ∣ x.1 ∧ (p : ℤ_[p]) ^ 5 ∣ x.2 ∧ ¬ (p : ℤ_[p]) ^ 6 ∣ x.2 := by
  rw [stratMinimalIIstar, Set.mem_prod]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Set.mem_ofPred_eq,
    emultiplicity_eq_coe (n := 5)]

/-- **The mass of the minimal `II*` locus is `2N p⁻¹⁰`**, i.e. `(p-1)/p¹⁰`. -/
theorem volume_stratMinimalIIstar (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratMinimalIIstar p)
      = 2 * ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 10 := by
  rw [stratMinimalIIstar, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.measure_span_pPow' 4, PadicInt.volume_setOf_emultiplicity_eq, one_sub_inv_eq hp]
  ring

/-- **The minimal `II*` locus lies in the stratum `τ_p⁻¹((II*, 1))`.** -/
theorem stratMinimalIIstar_subset_stratFibre (hp : 5 ≤ p) :
    stratMinimalIIstar p ⊆ stratFibre p (KodairaSymbol.II!, 1) := by
  intro x hx
  obtain ⟨h4, h6, h6'⟩ := mem_stratMinimalIIstar_iff.1 hx
  obtain ⟨u, hu5⟩ := h6
  have hu : ¬ (p : ℤ_[p]) ∣ u := fun ⟨z, hz⟩ => h6' ⟨z, by rw [hu5, hz]; ring⟩
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_eleven_dvd_ofShortNF_Δ_of_IIstar hp h4 ⟨u, hu5⟩ h6' (h0 ▸ dvd_zero _)
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, hc⟩ := run_eq_IIstar_of_eq_pow_mul hp hΔ h4 hu hu5
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)

open scoped Classical in
/-- **The minimal part of the stratum `τ_p⁻¹((II*, 1))` is the minimal `II*` locus**, for every
prime `p ≥ 5`:

  `τ_p⁻¹((II*, 1)) ∖ σ_p(ℤ_p²) = {p⁴ ∣ a₄, v_p(a₆) = 5}`.
-/
theorem stratFibre_diff_range_eq_stratMinimalIIstar (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.II!, 1) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = stratMinimalIIstar p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have hs := (mem_stratFibre_iff hxUp).1 hxF
    rw [strat] at hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.II! := congrArg Prod.fst hs
    rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp with out' | W'
    · obtain ⟨h4, h6, h6'⟩ := TateAlgorithm.Step11.pow_dvd_c₄_c₆_of_eq_IIstar hp hxUp e
        (by rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
            exact hκ)
      rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4
      rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6
      rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6'
      exact mem_stratMinimalIIstar_iff.2 ⟨h4, h6, h6'⟩
    · refine absurd (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩) hxR
      · have hd : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
          ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hd
      · have hd : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
          ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hd
  · intro x hx
    obtain ⟨-, -, h6'⟩ := mem_stratMinimalIIstar_iff.1 hx
    refine ⟨stratMinimalIIstar_subset_stratFibre hp hx, fun hr => ?_⟩
    obtain ⟨-, h6r⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    exact h6' (dvd_trans (pow_dvd_pow _ (by norm_num : 6 ≤ 6)) h6r)

/-- **The density of the `II*` stratum**, for every prime `p ≥ 5`:

  `δ_p((II*, 1)) = 2N p⁻¹⁰ (1 - p⁻¹⁰)⁻¹`,   `2N = p - 1`,

i.e. `(p-1)/(p¹⁰-1)`. -/
theorem deltaP_IIstar_one_eq (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.II!, 1)
      = 2 * ((goodRes p).card : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 10
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [deltaP_eq_mul_inv_one_sub hp, stratFibre_diff_range_eq_stratMinimalIIstar hp,
    volume_stratMinimalIIstar hp]

/-- **The density of `(II*, 1)` in closed form**:
`δ_p((II*, 1)) = ENNReal.ofReal (gotIIStarOne p)`, i.e. `(p-1)/(p¹⁰-1)`, at every prime `p ≥ 5`. -/
theorem deltaP_IIstar_one_eq_ofReal (hp : 5 ≤ p) :
    deltaP p (KodairaSymbol.II!, 1) = ENNReal.ofReal (gotIIStarOne p) := by
  have hp0 : 0 < p := by omega
  have hc2N : (2 : ℝ≥0∞) * (((goodRes p).card : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (2 * (((goodRes p).card : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [deltaP_IIstar_one_eq hp, hc2N, one_sub_inv_pow_eq_ofReal hp0,
    ← ENNReal.ofReal_inv_of_pos (one_sub_inv_pow_pos (by omega) (by norm_num)),
    inv_natCast_eq_ofReal hp0, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hne : (p : ℝ) ≠ 0 := by positivity
  rw [gotIIStarOne, cast_card_goodRes_eq hp]
  field_simp

/-! ### `δ_p(1)` in terms of `δ_p((I₀*, 1))` -/

/-- **The closed form of `δ_p(1)` is equivalent to that of `δ_p((I₀*, 1))`**, for every prime
`p ≥ 5`:

  `δ_p(1) = ENNReal.ofReal (gotδ p 1)`  ↔  `δ_p((I₀*, 1)) = ENNReal.ofReal (((p²-1)/3)p⁻⁷T)`.
-/
theorem δ_one_eq_ofReal_gotδ_iff_IZeroStar_row (hp : 5 ≤ p) :
    δ p 1 = ENNReal.ofReal (gotδ p 1) ↔
      deltaP p (KodairaSymbol.I! 0, 1) = ENNReal.ofReal (gotIZeroStarOne p) := by
  rw [δ_one_eq_ofReal_gotδ_iff hp, deltaP_IIstar_one_eq_ofReal hp,
    ENNReal.ofReal_add (gotIZeroStarOne_nonneg hp) (gotIIStarOne_nonneg hp),
    ENNReal.add_left_inj ENNReal.ofReal_ne_top]

/-- **The closed form of `δ_p(1)` at `p ≥ 5`**, given
`δ_p((I₀*, 1)) = ENNReal.ofReal (gotIZeroStarOne p)`. -/
theorem δ_one_eq_ofReal_gotδ_of_IZeroStar_row (hp : 5 ≤ p)
    (hI0star : deltaP p (KodairaSymbol.I! 0, 1) = ENNReal.ofReal (gotIZeroStarOne p)) :
    δ p 1 = ENNReal.ofReal (gotδ p 1) :=
  (δ_one_eq_ofReal_gotδ_iff_IZeroStar_row hp).2 hI0star

end WeierstrassCurve
