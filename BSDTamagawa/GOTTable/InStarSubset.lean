/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.HeadDensityInStarSource
public import BSDTamagawa.GOTTable.InStarStep7Shape

/-!
# A minimal `Iₘ*` stratum with `m ≥ 1` lies in `deepResidueLocus p (doubleRootResidues p)`

For a prime `p ≥ 5` and `m ≥ 1`, a short Weierstrass pair `(a₄, a₆) ∈ ℤ_p²` whose Tate algorithm
reports Kodaira symbol `Iₘ*`, and which is not in the image `σ_p(ℤ_p²)` of
`(a, b) ↦ (p⁴ a, p⁶ b)`, satisfies `p² ∣ a₄`, `p³ ∣ a₆`, and its residue pair
`(a₄ / p², a₆ / p³) mod p` lies in `doubleRootResidues p`:

  `stratFibre p (Iₘ*, c) ∖ σ_p(ℤ_p²) ⊆ deepResidueLocus p (doubleRootResidues p)`.

The inclusion holds for every Tamagawa number `c`.

## Main results

* `exists_step5_ok_of_step6_run_eq_ok`: if Step 6 of Tate's algorithm returns `ok`, then Step 5
  returned `ok` and Step 6's output is the translate of Step 5's.
* `stratFibre_Istar_pos_diff_range_subset`: for `m ≠ 0`, the stratum of `(Iₘ*, c)` minus the
  image of `σ_p` lies in `deepResidueLocus p (doubleRootResidues p)`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

open TateAlgorithm

open BSDTamagawa.LocalConstancy

/-- If `Step6.run` returns `ok W''`, then `Step5.run` returns `ok W₅` for some `W₅`, and `W''` is
`Step6.translate W₅`. -/
theorem exists_step5_ok_of_step6_run_eq_ok {W W'' : WeierstrassCurve ℤ_[p]}
    (h : Step6.run (p : ℤ_[p]) W = Except.ok W'') :
    ∃ W₅, Step5.run (p : ℤ_[p]) W = Except.ok W₅ ∧ W'' = Step6.translate (p : ℤ_[p]) W₅ := by
  rw [Step6.run.eq_def] at h
  rcases Except.bind_eq_ok_iff.mp h with ⟨W₅, h5, h6⟩
  refine ⟨W₅, h5, ?_⟩
  split_ifs at h6
  exact (Except.ok.inj h6).symm

/-- For `p ≥ 5`, `m ≠ 0` and any `c`, the stratum of `(Iₘ*, c)` minus the image of
`scaleProdByPPow 4 6` lies in `deepResidueLocus p (doubleRootResidues p)`. -/
theorem stratFibre_Istar_pos_diff_range_subset (hp : 5 ≤ p) {m : ℕ} (hm : m ≠ 0) (c : ℕ) :
    stratFibre p (KodairaSymbol.I! m, c) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      ⊆ deepResidueLocus p (doubleRootResidues p) := by
  rintro x ⟨hxF, hxR⟩
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  have hs := (mem_stratFibre_iff hxUp).1 hxF
  rw [strat] at hs
  have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.I! m :=
    congrArg Prod.fst hs
  have h4 : (p : ℤ_[p]) ^ 2 ∣ x.1 := by
    have hd := (pow_dvd_of_mem_stratFibre_additive hp hxF).1
    simpa only [KodairaSymbol.additiveC₄Level] using hd
  have h6' : (p : ℤ_[p]) ^ 3 ∣ x.2 := by
    have hd := (pow_dvd_of_mem_stratFibre_additive hp hxF).2
    simpa only [KodairaSymbol.additiveC₆Level] using hd
  obtain ⟨A, hx1⟩ := h4
  obtain ⟨B, hx2⟩ := h6'
  refine mem_deepResidueLocus_iff.2 ⟨A, B, hx1, hx2, ?_⟩
  rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp with out' | W'
  · have hκ' : out'.kodairaSymbol = KodairaSymbol.I! m := by
      rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
      exact hκ
    obtain ⟨h7, hne⟩ :=
      TateAlgorithm.Step11.stepSeven_subprocedure_of_kodairaSymbol_eq_Istar hxUp hm e hκ'
    obtain ⟨W'', h6ok, hnt⟩ := step6_ok_and_not_hasTripleRoot_of_step7_error hxUp h7 hne
    have hdr := TateAlgorithm.Step6.run_hasDoubleRoot h6ok
    obtain ⟨W₅, h5, rfl⟩ := exists_step5_ok_of_step6_run_eq_ok h6ok
    exact (hasDoubleRoot_and_not_hasTripleRoot_iff_mem_doubleRootResidues hp hx1 hx2 h5).1
      ⟨hdr, hnt⟩
  · refine absurd (PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨?_, ?_⟩) hxR
    · have hdv : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
        ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hdv
    · have hdv : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
        ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
      rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hdv

end WeierstrassCurve
