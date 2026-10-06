/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarForwardRun

/-!
# The deep residue locus over the double-root residues lies in the `Iₙ*` family

For a prime `p ≥ 5`, every nonsingular point `(a₄, a₆) ∈ ℤ_p²` of the deep residue locus over the
double-root residues has reduction type `Iₘ*` for some `m ≥ 1`, and lies outside the image
`σ_p(ℤ_p²)` of `PadicInt.scaleProdByPPow 4 6`:

  `deepResidueLocus p (doubleRootResidues p) ∩ nonsingularLocus p
     ⊆ (⋃_{m ≥ 1} ⋃_{c} stratFibre p (Iₘ*, c)) ∖ σ_p(ℤ_p²)`.

The intersection with `nonsingularLocus p` cannot be dropped:
`deepResidueLocus p (doubleRootResidues p)` contains points with `Δ = 0`.

## Main results

* `deepResidueLocus_inter_nonsingularLocus_subset_iUnion_stratFibre`: every point of
  `deepResidueLocus p (doubleRootResidues p)` with nonzero discriminant lies on a stratum `Iₘ*`
  with `m ≥ 1` and outside `σ_p(ℤ_p²)`.
-/

open MeasureTheory

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy TateAlgorithm

/-- For `p ≥ 5`, every point of `deepResidueLocus p (doubleRootResidues p)` with nonzero
discriminant lies on a stratum `Iₘ*` with `m ≥ 1` and outside the image of
`PadicInt.scaleProdByPPow 4 6`. -/
theorem deepResidueLocus_inter_nonsingularLocus_subset_iUnion_stratFibre (hp : 5 ≤ p) :
    deepResidueLocus p (doubleRootResidues p) ∩ nonsingularLocus p
      ⊆ (⋃ m : ℕ, ⋃ c : ℕ, stratFibre p (KodairaSymbol.I! (m + 1), c)) \
          Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  rintro x ⟨hxL, hxU⟩
  obtain ⟨A, B, hx1, hx2, hmem⟩ := mem_deepResidueLocus_iff.1 hxL
  rw [doubleRootResidues, Finset.mem_filter] at hmem
  obtain ⟨hcusp, hAne⟩ := hmem
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := hxU
  have h5 := step5_run_eq_ok_of_dvd hp (⟨A, hx1⟩ : (p : ℤ_[p]) ^ 2 ∣ x.1)
    (⟨B, hx2⟩ : (p : ℤ_[p]) ^ 3 ∣ x.2)
  have hd : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2))) 1 1).HasDoubleRoot :=
    (step6_cubic_bridge hp hx1 hx2 h5).1.2 hcusp
  have h6 := step6_run_eq_ok_of_hasDoubleRoot h5 hd
  have hnt : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p])
      (Step2.translate (p : ℤ_[p]) (ofShortNF x.1 x.2))) 1 1).HasTripleRoot := by
    rw [hasTripleRoot_step6_cubic_iff_toZMod_eq_zero hp hx1 h5]
    exact hAne
  obtain ⟨out, h7, m, hm, hκ⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hnt
  have hrun := TateAlgorithm.run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  refine ⟨Set.mem_iUnion.2 ⟨m', Set.mem_iUnion.2
    ⟨(TateAlgorithm.run hϖ hΔ).tamagawaNumber, (mem_stratFibre_iff hxU).2 ?_⟩⟩, ?_⟩
  · rw [strat]
    exact Prod.ext (by rw [hrun]; exact hκ) rfl
  · intro hr
    obtain ⟨h4', -⟩ := PadicInt.mem_range_scaleProdByPPow_iff.1 hr
    obtain ⟨z, hz⟩ := h4'
    have hA : (p : ℤ_[p]) ∣ A := ⟨(p : ℤ_[p]) * z,
      mul_left_cancel₀ (pow_ne_zero 2 hϖ) (by rw [← hx1, hz]; ring)⟩
    rw [PadicInt.dvd_iff_toZMod_eq_zero] at hA
    exact hAne hA

end WeierstrassCurve
