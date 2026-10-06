/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarTamagawaTwoFour

/-!
# The `Iₘ*` strata with Tamagawa number `2` or `4`

For `p ≥ 5`, a point `x ∈ nonsingularLocus p` outside `σ_p(ℤ_p²)` whose curve `ofShortNF x.1 x.2`
has Kodaira symbol `Iₘ*` with `m ≥ 1` has Tamagawa number `2` or `4`. Consequently, outside
`σ_p(ℤ_p²)`, the union of the strata `(Iₘ*, c)` with `m ≥ 1` and `c ∈ {2, 4}` is the locus
`deepResidueLocus p (doubleRootResidues p) ∩ nonsingularLocus p`.

## Main results

* `run_tamagawaNumber_eq_two_or_four_of_kodairaSymbol_eq_Istar`: a point of `nonsingularLocus p`
  outside `σ_p(ℤ_p²)` with Kodaira symbol `Iₘ*`, `m ≠ 0`, has Tamagawa number `2` or `4`.
* `iUnion_stratFibre_Istar_pos_two_four_diff_range_eq`: the union of the strata `(Iₘ₊₁*, c)` over
  `m : ℕ` and `c ∈ {2, 4}`, minus `σ_p(ℤ_p²)`, equals
  `deepResidueLocus p (doubleRootResidues p) ∩ nonsingularLocus p`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open BSDTamagawa.LocalConstancy TateAlgorithm

/-- For `p ≥ 5`, if `x ∈ nonsingularLocus p` lies outside `σ_p(ℤ_p²)` and the curve
`ofShortNF x.1 x.2` has Kodaira symbol `Iₘ*` with `m ≠ 0`, then its Tamagawa number is `2` or
`4`. -/
theorem run_tamagawaNumber_eq_two_or_four_of_kodairaSymbol_eq_Istar (hp : 5 ≤ p)
    {x : ℤ_[p] × ℤ_[p]} (hxUp : x ∈ nonsingularLocus p)
    (hxR : x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]))
    {m : ℕ} (hm : m ≠ 0)
    (hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.I! m) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = 2 ∨
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = 4 := by
  rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp with out' | W'
  · have hκ' : out'.kodairaSymbol = KodairaSymbol.I! m := by
      rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
      exact hκ
    obtain ⟨h7, hne⟩ :=
      TateAlgorithm.Step11.stepSeven_subprocedure_of_kodairaSymbol_eq_Istar hxUp hm e hκ'
    obtain ⟨W'', h6ok, hnt⟩ := step6_ok_and_not_hasTripleRoot_of_step7_error hxUp h7 hne
    rw [TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
    exact Step7.run_error_tamagawaNumber_eq_two_or_four hxUp h6ok hnt h7
  · refine absurd (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩) hxR
    · have hdv : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
        ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hdv
    · have hdv : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
        ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hdv

/-- For `p ≥ 5`, the union of the strata `(Iₘ₊₁*, c)` over `m : ℕ` and `c ∈ {2, 4}`, minus
`σ_p(ℤ_p²)`, equals `deepResidueLocus p (doubleRootResidues p) ∩ nonsingularLocus p`. -/
theorem iUnion_stratFibre_Istar_pos_two_four_diff_range_eq (hp : 5 ≤ p) :
    (⋃ m : ℕ, ⋃ c ∈ ({2, 4} : Set ℕ), stratFibre p (KodairaSymbol.I! (m + 1), c)) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = deepResidueLocus p (doubleRootResidues p) ∩ nonsingularLocus p := by
  refine Set.Subset.antisymm (fun x hx => ⟨?_, ?_⟩) (fun x hx => ?_)
  · obtain ⟨hxu, hxR⟩ := hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hxu
    obtain ⟨c, -, hc⟩ := Set.mem_iUnion₂.1 hm
    exact stratFibre_Istar_pos_diff_range_subset hp (Nat.succ_ne_zero m) c ⟨hc, hxR⟩
  · obtain ⟨hxu, -⟩ := hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hxu
    obtain ⟨c, -, hc⟩ := Set.mem_iUnion₂.1 hm
    exact stratFibre_subset _ hc
  · obtain ⟨hmem, hxR⟩ :=
      deepResidueLocus_inter_nonsingularLocus_subset_iUnion_stratFibre hp hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hm
    have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hc
    have hs := (mem_stratFibre_iff hxUp).1 hc
    rw [strat] at hs
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.I! (m + 1) :=
      congrArg Prod.fst hs
    have hcv : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).tamagawaNumber = c := congrArg Prod.snd hs
    have h24 := run_tamagawaNumber_eq_two_or_four_of_kodairaSymbol_eq_Istar hp hxUp hxR
      (Nat.succ_ne_zero m) hκ
    rw [hcv] at h24
    refine ⟨Set.mem_iUnion.2 ⟨m, Set.mem_iUnion₂.2 ⟨c, ?_, hc⟩⟩, hxR⟩
    rcases h24 with h | h
    · exact h ▸ Set.mem_insert _ _
    · exact h ▸ Set.mem_insert_of_mem _ rfl

end WeierstrassCurve
