/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowLowerBoundThree
public import BSDTamagawa.NumberTheory.TailConstantThree

/-!
# Family B at `p = 3`: the masses of the level shells

Family B at `p = 3` consists of the short models with `a₄ = 27α`, `a₆ = 27β`, `3 ∤ α` and
`27 ∣ 4α³ + β²`. Its level is `n := v₃(4α³ + β²) − 3 ≥ 0`, and Tate's algorithm on it answers

* `n = 0`: `(I₀, 1)`;
* `n ≥ 1`, `β ≡ 2 (mod 3)` (split): `(Iₙ, n)`;
* `n ≥ 1`, `β ≡ 1 (mod 3)` (non-split): `(Iₙ, 1)` for odd `n` and `(Iₙ, 2)` for even `n`.

The level-`n` shell has mass `4 · 3^{−(n+11)}` and each of its halves `β ≡ r (mod 3)`, `r ≠ 0`, has
mass `2 · 3^{−(n+11)}`: over `α ≡ 2 (mod 3)` (a set of mass `3⁻¹`) the slice is the union of two
balls around the roots `±ν` of `−4α³`, of total mass `2(1 − 3⁻¹)3^{−(n+3)}`, the residue condition
keeps one of them, and the dilation `(α, β) ↦ (27α, 27β)` costs `3⁻⁶`. Assuming these answers
(`ForwardRun`), the shells lie in the minimal parts of the rows `t = 1, …, 4`, and the `t = 1` row
gives a lower bound for `δ₃(1)`.

## Main definitions

* `WeierstrassCurve.FamilyBThree.cyl`: the cylinder of Family B (eighteen classes of `(α, β)`
  modulo `27`, dilated by `(27, 27)`).
* `WeierstrassCurve.FamilyBThree.ForwardRun`: the three answers of Tate's algorithm on Family B, as
  a `Prop`-valued structure.
* `WeierstrassCurve.FamilyBThree.shell`, `WeierstrassCurve.FamilyBThree.half`,
  `WeierstrassCurve.FamilyBThree.splitShell`, `WeierstrassCurve.FamilyBThree.nonSplitShell`,
  `WeierstrassCurve.FamilyBThree.iZeroDescentLocus`, `WeierstrassCurve.FamilyBThree.nonSplitOdd`,
  `WeierstrassCurve.FamilyBThree.nonSplitEven`: the level shells, their halves and their unions.
* `WeierstrassCurve.FamilyBThree.rowOneFamilyB`, `WeierstrassCurve.FamilyBThree.rowTwoFamilyB`,
  `WeierstrassCurve.FamilyBThree.rowThreeFamilyB`, `WeierstrassCurve.FamilyBThree.rowFourFamilyB`:
  the four row sets.

## Main results

* `WeierstrassCurve.FamilyBThree.exists_form_of_mem_shell`,
  `WeierstrassCurve.FamilyBThree.exists_form_of_mem_half`: the algebraic shape `a₄ = 27α`,
  `a₆ = 27β`, `3 ∤ α`, `3^{n+3} ∣ 4α³ + β²`, `3^{n+4} ∤ 4α³ + β²` (and `β mod 3`) of a point of a
  shell; `WeierstrassCurve.FamilyBThree.Δ_ne_zero_of_form`: such points are nonsingular.
* `WeierstrassCurve.FamilyBThree.disjoint_shell_of_ne`,
  `WeierstrassCurve.FamilyBThree.disjoint_half_of_ne`,
  `WeierstrassCurve.FamilyBThree.disjoint_splitShell_nonSplitShell`: the disjointness of the
  pieces.
* `WeierstrassCurve.FamilyBThree.volume_shell`, `WeierstrassCurve.FamilyBThree.volume_splitShell`,
  `WeierstrassCurve.FamilyBThree.volume_nonSplitShell`,
  `WeierstrassCurve.FamilyBThree.volume_nonSplitOdd`,
  `WeierstrassCurve.FamilyBThree.volume_nonSplitEven`: the masses.
* `WeierstrassCurve.FamilyBThree.le_δ_one`: assuming `ForwardRun`, `65/2125728 ≤ δ₃(1)`.
-/

open scoped ENNReal
open MeasureTheory Set

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction BSDTamagawa.HeadDensityTwoBound
  TateAlgorithm

namespace FamilyBThree

/-! ### The cylinder: eighteen classes of `(α, β)` modulo `27` -/

/-- **The residue condition cutting out Family B at `3`**, on the pair `(α, β)` where
`(a₄, a₆) = (27α, 27β)`: `3 ∤ α` and `4α³ + β² = 0` in `ZMod 27`. -/
abbrev CylRes (c : ZMod (3 ^ 3) × ZMod (3 ^ 3)) : Prop :=
  (ZMod.cast c.1 : ZMod 3) ≠ 0 ∧ 4 * c.1 ^ 3 + c.2 ^ 2 = 0

/-- The classes of `(α, β)` modulo `27` cutting out Family B at `3`, as the graph of `CylRes`. -/
noncomputable def cylResidues : Finset (ZMod (3 ^ 3) × ZMod (3 ^ 3)) :=
  Finset.univ.filter CylRes

/-- A class `c` lies in `cylResidues` exactly when it satisfies `CylRes`. -/
theorem mem_cylResidues_iff (c : ZMod (3 ^ 3) × ZMod (3 ^ 3)) : c ∈ cylResidues ↔ CylRes c := by
  simp [cylResidues]

/-- **The Family B cylinder of the coefficient plane at `3`**: the image under
`(α, β) ↦ (27α, 27β)` of the eighteen-class cylinder modulo `27`. -/
noncomputable def cyl : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.scaleProdByPPow 3 3 ''
    (PadicInt.redPairPow 3 3 ⁻¹' (cylResidues : Set (ZMod (3 ^ 3) × ZMod (3 ^ 3))))

/-- `18 · 3⁻⁶ = 18/729 = 2/81` in `ℝ≥0∞`. -/
theorem eighteen_mul_inv_pow_six_eq :
    ((18 : ℕ) : ℝ≥0∞) * ((((3 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 3) = 2 / 81 := by
  rw [show ((18 : ℕ) : ℝ≥0∞) = 18 by norm_num, show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num,
    ← ENNReal.inv_pow, show ((3 : ℝ≥0∞)) ^ (2 * 3) = 729 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### The forward run -/

/-- **The answers of Tate's algorithm on Family B at `p = 3`**: on a nonsingular point of the
cylinder with `a₄ = 27α`, `a₆ = 27β`,

* level `0` (`3⁴ ∤ 4α³ + β²`) answers `(I₀, 1)`;
* level `n ≥ 1` with `β ≡ 2 (mod 3)` answers `(Iₙ, n)`;
* level `n ≥ 1` with `β ≡ 1 (mod 3)` answers `(Iₙ, 1)` for odd `n` and `(Iₙ, 2)` for even `n`. -/
structure ForwardRun : Prop where
  run_eq_I_zero_of_level_zero : ∀ {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0),
    x ∈ cyl → ∀ {α β : ℤ_[3]}, x.1 = 27 * α → x.2 = 27 * β →
      ¬ ((3 : ℕ) : ℤ_[3]) ^ 4 ∣ 4 * α ^ 3 + β ^ 2 →
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 0 ∧
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1
  run_eq_I_of_split : ∀ {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0),
    x ∈ cyl → ∀ {α β : ℤ_[3]}, x.1 = 27 * α → x.2 = 27 * β → ∀ {n : ℕ}, 1 ≤ n →
      ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2 →
      ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2 →
      PadicInt.toZMod β = 2 →
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I n ∧
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = n
  run_eq_I_of_nonsplit : ∀ {x : ℤ_[3] × ℤ_[3]} (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0),
    x ∈ cyl → ∀ {α β : ℤ_[3]}, x.1 = 27 * α → x.2 = 27 * β → ∀ {n : ℕ}, 1 ≤ n →
      ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2 →
      ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2 →
      PadicInt.toZMod β = 1 →
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I n ∧
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = if Odd n then 1 else 2

/-! ### The shells and their halves, as sets -/

/-- **The level-`n` shell in `(α, β)`-coordinates**: `3 ∤ α` and `v₃(4α³ + β²) = n + 3`, the latter
read as `β ∈ sqLevelSet (−4α³) (n + 3)` since `β² − (−4α³) = 4α³ + β²`. -/
def preShell (n : ℕ) : Set (ℤ_[3] × ℤ_[3]) :=
  {y | ¬ ((3 : ℕ) : ℤ_[3]) ∣ y.1} ∩ {y | y.2 ∈ PadicInt.sqLevelSet (-4 * y.1 ^ 3) (n + 3)}

/-- The residue class `β ≡ r (mod 3)` of the second coordinate. -/
def sndResidue (r : ZMod 3) : Set (ℤ_[3] × ℤ_[3]) := Prod.snd ⁻¹' (PadicInt.toZMod ⁻¹' {r})

/-- **The level-`n` shell of Family B**: the points `(27α, 27β)` with `3 ∤ α` and
`v₃(4α³ + β²) = n + 3`. -/
noncomputable def shell (n : ℕ) : Set (ℤ_[3] × ℤ_[3]) := PadicInt.scaleProdByPPow 3 3 '' preShell n

/-- The half of the level-`n` shell on which `β ≡ r (mod 3)`. -/
noncomputable def half (r : ZMod 3) (n : ℕ) : Set (ℤ_[3] × ℤ_[3]) :=
  PadicInt.scaleProdByPPow 3 3 '' (preShell n ∩ sndResidue r)

/-- **The split half of the level-`n` shell**: `β ≡ 2 (mod 3)`. -/
noncomputable def splitShell (n : ℕ) : Set (ℤ_[3] × ℤ_[3]) := half 2 n

/-- **The non-split half of the level-`n` shell**: `β ≡ 1 (mod 3)`. -/
noncomputable def nonSplitShell (n : ℕ) : Set (ℤ_[3] × ℤ_[3]) := half 1 n

/-- **The level-`0` shell**, where the descended model has good reduction: `(I₀, 1)`. -/
noncomputable def iZeroDescentLocus : Set (ℤ_[3] × ℤ_[3]) := shell 0

/-- **The non-split shells at odd levels**, all with Tamagawa number `1`. -/
noncomputable def nonSplitOdd : Set (ℤ_[3] × ℤ_[3]) := ⋃ j : ℕ, nonSplitShell (2 * j + 1)

/-- **The non-split shells at even levels `≥ 2`**, all with Tamagawa number `2`. -/
noncomputable def nonSplitEven : Set (ℤ_[3] × ℤ_[3]) := ⋃ j : ℕ, nonSplitShell (2 * j + 2)

/-! ### Measurability -/

/-- The level-`n` shell `preShell n` in `(α, β)`-coordinates is measurable. -/
theorem measurableSet_preShell (n : ℕ) : MeasurableSet (preShell n) := by
  refine MeasurableSet.inter ?_ ?_
  · have h : {y : ℤ_[3] × ℤ_[3] | ¬ ((3 : ℕ) : ℤ_[3]) ∣ y.1}
        = Prod.fst ⁻¹' (PadicInt.toZMod ⁻¹' {(0 : ZMod 3)})ᶜ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [PadicInt.dvd_iff_toZMod_eq_zero]
    rw [h]
    exact (PadicInt.measurableSet_preimage_toZMod 0).compl.preimage measurable_fst
  · have h : {y : ℤ_[3] × ℤ_[3] | y.2 ∈ PadicInt.sqLevelSet (-4 * y.1 ^ 3) (n + 3)}
        = (fun y : ℤ_[3] × ℤ_[3] => y.2 ^ 2 - (-4 * y.1 ^ 3)) ⁻¹'
            {z : ℤ_[3] | emultiplicity ((3 : ℕ) : ℤ_[3]) z = ((n + 3 : ℕ) : ℕ∞)} := by
      ext y
      exact Iff.rfl
    rw [h]
    exact (PadicInt.measurableSet_setOf_emultiplicity_eq (n + 3)).preimage
      ((continuous_snd.pow 2).sub (continuous_const.mul (continuous_fst.pow 3))).measurable

/-- The residue class `{β ≡ r (mod 3)}` of the second coordinate is measurable. -/
theorem measurableSet_sndResidue (r : ZMod 3) : MeasurableSet (sndResidue r) :=
  (PadicInt.measurableSet_preimage_toZMod r).preimage measurable_snd

/-- The level-`n` shell of Family B is measurable. -/
theorem measurableSet_shell (n : ℕ) : MeasurableSet (shell n) :=
  (PadicInt.measurableEmbedding_scaleProdByPPow 3 3).measurableSet_image.2
    (measurableSet_preShell n)

/-- The half of the level-`n` shell on which `β ≡ r (mod 3)` is measurable. -/
theorem measurableSet_half (r : ZMod 3) (n : ℕ) : MeasurableSet (half r n) :=
  (PadicInt.measurableEmbedding_scaleProdByPPow 3 3).measurableSet_image.2
    ((measurableSet_preShell n).inter (measurableSet_sndResidue r))

/-- The split half of the level-`n` shell is measurable. -/
theorem measurableSet_splitShell (n : ℕ) : MeasurableSet (splitShell n) := measurableSet_half 2 n

/-- The non-split half of the level-`n` shell is measurable. -/
theorem measurableSet_nonSplitShell (n : ℕ) : MeasurableSet (nonSplitShell n) :=
  measurableSet_half 1 n

/-- The level-`0` shell is measurable. -/
theorem measurableSet_iZeroDescentLocus : MeasurableSet iZeroDescentLocus := measurableSet_shell 0

/-- The union of the non-split shells at odd levels is measurable. -/
theorem measurableSet_nonSplitOdd : MeasurableSet nonSplitOdd :=
  MeasurableSet.iUnion fun j => measurableSet_nonSplitShell (2 * j + 1)

/-- The union of the non-split shells at even levels `≥ 2` is measurable. -/
theorem measurableSet_nonSplitEven : MeasurableSet nonSplitEven :=
  MeasurableSet.iUnion fun j => measurableSet_nonSplitShell (2 * j + 2)

/-! ### Inclusions and disjointness -/

/-- Each half of the level-`n` shell is contained in the shell. -/
theorem half_subset_shell (r : ZMod 3) (n : ℕ) : half r n ⊆ shell n :=
  Set.image_mono Set.inter_subset_left

/-- The split half of the level-`n` shell is contained in the shell. -/
theorem splitShell_subset_shell (n : ℕ) : splitShell n ⊆ shell n := half_subset_shell 2 n

/-- The non-split half of the level-`n` shell is contained in the shell. -/
theorem nonSplitShell_subset_shell (n : ℕ) : nonSplitShell n ⊆ shell n := half_subset_shell 1 n

/-- Shells at distinct levels are disjoint: the valuation `v₃(4α³ + β²)` is exact. -/
theorem disjoint_preShell_of_ne {m n : ℕ} (h : m ≠ n) : Disjoint (preShell m) (preShell n) := by
  rw [Set.disjoint_left]
  rintro y ⟨-, hm⟩ ⟨-, hn⟩
  have hm' : emultiplicity ((3 : ℕ) : ℤ_[3]) (y.2 ^ 2 - (-4 * y.1 ^ 3)) = ((m + 3 : ℕ) : ℕ∞) := hm
  have hn' : emultiplicity ((3 : ℕ) : ℤ_[3]) (y.2 ^ 2 - (-4 * y.1 ^ 3)) = ((n + 3 : ℕ) : ℕ∞) := hn
  rw [hm'] at hn'
  have h3 : m + 3 = n + 3 := by exact_mod_cast hn'
  omega

/-- Shells of Family B at distinct levels are disjoint. -/
theorem disjoint_shell_of_ne {m n : ℕ} (h : m ≠ n) : Disjoint (shell m) (shell n) :=
  (Set.disjoint_image_iff (PadicInt.measurableEmbedding_scaleProdByPPow 3 3).injective).2
    (disjoint_preShell_of_ne h)

/-- Halves of shells at distinct levels are disjoint, whatever their residues. -/
theorem disjoint_half_of_ne (r r' : ZMod 3) {m n : ℕ} (h : m ≠ n) :
    Disjoint (half r m) (half r' n) :=
  (disjoint_shell_of_ne h).mono (half_subset_shell r m) (half_subset_shell r' n)

/-- The two halves of one shell are disjoint, by `β mod 3`. -/
theorem disjoint_half_of_ne_residue {r r' : ZMod 3} (h : r ≠ r') (n : ℕ) :
    Disjoint (half r n) (half r' n) := by
  refine (Set.disjoint_image_iff
    (PadicInt.measurableEmbedding_scaleProdByPPow 3 3).injective).2 ?_
  rw [Set.disjoint_left]
  rintro y ⟨-, hr⟩ ⟨-, hr'⟩
  have h1 : PadicInt.toZMod y.2 = r := hr
  have h2 : PadicInt.toZMod y.2 = r' := hr'
  exact h (h1.symm.trans h2)

/-- Non-split halves of shells at distinct levels are disjoint. -/
theorem disjoint_nonSplitShell_of_ne {m n : ℕ} (h : m ≠ n) :
    Disjoint (nonSplitShell m) (nonSplitShell n) := disjoint_half_of_ne 1 1 h

/-- A split half and a non-split half are disjoint, at any two levels. -/
theorem disjoint_splitShell_nonSplitShell (m n : ℕ) :
    Disjoint (splitShell m) (nonSplitShell n) := by
  by_cases h : m = n
  · subst h
    exact disjoint_half_of_ne_residue (by decide) m
  · exact disjoint_half_of_ne 2 1 h

/-- The level-`0` shell is disjoint from the non-split shells at odd levels. -/
theorem disjoint_iZeroDescentLocus_nonSplitOdd : Disjoint iZeroDescentLocus nonSplitOdd :=
  Set.disjoint_iUnion_right.2 fun j =>
    (disjoint_shell_of_ne (by omega)).mono_right (nonSplitShell_subset_shell (2 * j + 1))

/-- The level-`0` shell is disjoint from the split half of the level-`1` shell. -/
theorem disjoint_iZeroDescentLocus_splitShell_one : Disjoint iZeroDescentLocus (splitShell 1) :=
  (disjoint_shell_of_ne (by omega)).mono_right (splitShell_subset_shell 1)

/-- The non-split shells at odd levels are disjoint from the split half of the level-`1` shell. -/
theorem disjoint_nonSplitOdd_splitShell_one : Disjoint nonSplitOdd (splitShell 1) :=
  Set.disjoint_iUnion_left.2 fun j =>
    (disjoint_splitShell_nonSplitShell 1 (2 * j + 1)).symm

/-- The non-split shells at even levels `≥ 2` are disjoint from the split half of the level-`2`
shell. -/
theorem disjoint_nonSplitEven_splitShell_two : Disjoint nonSplitEven (splitShell 2) :=
  Set.disjoint_iUnion_left.2 fun j =>
    (disjoint_splitShell_nonSplitShell 2 (2 * j + 2)).symm

/-! ### The algebraic shape of a point, and its nonsingularity -/

/-- The first coordinate of the dilation `(α, β) ↦ (27α, 27β)`. -/
theorem scaleProdByPPow_fst (α β : ℤ_[3]) :
    (PadicInt.scaleProdByPPow 3 3 (α, β)).1 = 27 * α := by
  rw [PadicInt.scaleProdByPPow, Prod.map_fst, PadicInt.scaleByPPow]
  norm_num

/-- The second coordinate of the dilation `(α, β) ↦ (27α, 27β)`. -/
theorem scaleProdByPPow_snd (α β : ℤ_[3]) :
    (PadicInt.scaleProdByPPow 3 3 (α, β)).2 = 27 * β := by
  rw [PadicInt.scaleProdByPPow, Prod.map_snd, PadicInt.scaleByPPow]
  norm_num

/-- Membership of `preShell n`, in divisibility form: `3 ∤ α`, `3^{n+3} ∣ 4α³ + β²` and
`3^{n+4} ∤ 4α³ + β²`. -/
theorem form_of_mem_preShell {n : ℕ} {α β : ℤ_[3]} (h : (α, β) ∈ preShell n) :
    ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧ ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2 ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2 := by
  obtain ⟨hα, hv⟩ := h
  have hv' : emultiplicity ((3 : ℕ) : ℤ_[3]) (β ^ 2 - (-4 * α ^ 3)) = ((n + 3 : ℕ) : ℕ∞) := hv
  rw [show β ^ 2 - (-4 * α ^ 3) = 4 * α ^ 3 + β ^ 2 by ring, emultiplicity_eq_coe] at hv'
  refine ⟨hα, hv'.1, ?_⟩
  have h2 := hv'.2
  rwa [show n + 3 + 1 = n + 4 by omega] at h2

/-- **The algebraic shape of a point of the level-`n` shell**: `a₄ = 27α`, `a₆ = 27β`, `3 ∤ α`,
`3^{n+3} ∣ 4α³ + β²` and `3^{n+4} ∤ 4α³ + β²`. -/
theorem exists_form_of_mem_shell {n : ℕ} {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ shell n) :
    ∃ α β : ℤ_[3], x.1 = 27 * α ∧ x.2 = 27 * β ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧
      ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2 ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2 := by
  obtain ⟨⟨α, β⟩, hy, rfl⟩ := hx
  obtain ⟨hα, hlev, hlev'⟩ := form_of_mem_preShell hy
  exact ⟨α, β, scaleProdByPPow_fst α β, scaleProdByPPow_snd α β, hα, hlev, hlev'⟩

/-- **The algebraic shape of a point of a half**: that of `exists_form_of_mem_shell`, together with
`β ≡ r (mod 3)`. -/
theorem exists_form_of_mem_half {r : ZMod 3} {n : ℕ} {x : ℤ_[3] × ℤ_[3]} (hx : x ∈ half r n) :
    ∃ α β : ℤ_[3], x.1 = 27 * α ∧ x.2 = 27 * β ∧ ¬ ((3 : ℕ) : ℤ_[3]) ∣ α ∧
      ((3 : ℕ) : ℤ_[3]) ^ (n + 3) ∣ 4 * α ^ 3 + β ^ 2 ∧
      ¬ ((3 : ℕ) : ℤ_[3]) ^ (n + 4) ∣ 4 * α ^ 3 + β ^ 2 ∧ PadicInt.toZMod β = r := by
  obtain ⟨⟨α, β⟩, ⟨hy, hr⟩, rfl⟩ := hx
  obtain ⟨hα, hlev, hlev'⟩ := form_of_mem_preShell hy
  exact ⟨α, β, scaleProdByPPow_fst α β, scaleProdByPPow_snd α β, hα, hlev, hlev', hr⟩

/-- A quantity not divisible by a power of `3` is nonzero. -/
theorem ne_zero_of_not_pow_dvd {k : ℕ} {y : ℤ_[3]} (h : ¬ ((3 : ℕ) : ℤ_[3]) ^ k ∣ y) : y ≠ 0 :=
  fun h0 => h (h0 ▸ dvd_zero _)

/-- **Points of exact level are nonsingular.** With `a₄ = 27α`, `a₆ = 27β` the discriminant is
`Δ = −16 · 27³ · (4α³ + β²)`, which is nonzero when `4α³ + β² ≠ 0`. -/
theorem Δ_ne_zero_of_form {x : ℤ_[3] × ℤ_[3]} {α β : ℤ_[3]} (h₄ : x.1 = 27 * α)
    (h₆ : x.2 = 27 * β) (hne : 4 * α ^ 3 + β ^ 2 ≠ 0) : (ofShortNF x.1 x.2).Δ ≠ 0 := by
  rw [ofShortNF_Δ, h₄, h₆]
  intro h
  apply hne
  have h' : (-16 * 27 ^ 3 : ℤ_[3]) * (4 * α ^ 3 + β ^ 2) = 0 := by rw [← h]; ring
  exact (mul_eq_zero.1 h').resolve_left (by norm_num)

/-- **Minimality.** `v₃(a₄) = 3` on every shell, so `3⁴ ∤ a₄` and no point is a
`(3⁴, 3⁶)`-dilate. -/
theorem notMem_range_of_form {x : ℤ_[3] × ℤ_[3]} {α : ℤ_[3]} (h₄ : x.1 = 27 * α)
    (hα : ¬ ((3 : ℕ) : ℤ_[3]) ∣ α) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => hα ?_
  rw [h₄] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c, mul_left_cancel₀ (by norm_num : (27 : ℤ_[3]) ≠ 0) ?_⟩
  rw [hc]
  push_cast
  ring

/-! ### The shells lie in the cylinder -/

/-- **Every shell lies in the cylinder**: `3 ∤ α` gives the unit clause, and `v₃(4α³ + β²) ≥ 3`
gives the vanishing in `ZMod 27`. -/
theorem shell_subset_cyl (n : ℕ) : shell n ⊆ cyl := by
  rintro x ⟨⟨α, β⟩, hy, rfl⟩
  obtain ⟨hα, hlev, -⟩ := form_of_mem_preShell hy
  refine ⟨(α, β), ?_, rfl⟩
  rw [Set.mem_preimage, Finset.mem_coe, mem_cylResidues_iff]
  change CylRes (PadicInt.toZModPow 3 α, PadicInt.toZModPow 3 β)
  refine ⟨fun h => hα ?_, ?_⟩
  · have h1 : (ZMod.cast (PadicInt.toZModPow 3 α) : ZMod (3 ^ 1)) = PadicInt.toZModPow 1 α :=
      PadicInt.cast_toZModPow 1 3 (by norm_num) α
    have h0 : (ZMod.cast (PadicInt.toZModPow 3 α) : ZMod (3 ^ 1)) = 0 := by simpa using h
    have h3 := PadicInt.pow_dvd_iff_toZModPow_eq_zero.2 (h1.symm.trans h0)
    rwa [pow_one] at h3
  · have hd : ((3 : ℕ) : ℤ_[3]) ^ 3 ∣ 4 * α ^ 3 + β ^ 2 :=
      dvd_trans (pow_dvd_pow _ (by omega : 3 ≤ n + 3)) hlev
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_add, map_mul, map_pow, map_pow,
      map_ofNat] at hd
    exact hd

/-- Every half of every shell lies in the cylinder. -/
theorem half_subset_cyl (r : ZMod 3) (n : ℕ) : half r n ⊆ cyl :=
  (half_subset_shell r n).trans (shell_subset_cyl n)

/-! ### The masses: one `a₄`-slice at a time

Over `α` the slice of `preShell n` is empty unless `α` is a unit with `−4α³` a square — which is
`α ≡ 2 (mod 3)` — and then it is the square level set `sqLevelSet (−4α³) (n + 3)`. -/

/-- The slice of `preShell n` over a multiple `a` of `3` is empty. -/
theorem preimage_preShell_of_dvd {n : ℕ} {a : ℤ_[3]} (ha : ((3 : ℕ) : ℤ_[3]) ∣ a) :
    Prod.mk a ⁻¹' preShell n = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hb => hb.1 ha

/-- The slice of `preShell n` over `a` with `3 ∤ a` is the square level set
`sqLevelSet (−4a³) (n + 3)`. -/
theorem preimage_preShell_of_not_dvd {n : ℕ} {a : ℤ_[3]} (ha : ¬ ((3 : ℕ) : ℤ_[3]) ∣ a) :
    Prod.mk a ⁻¹' preShell n = PadicInt.sqLevelSet (-4 * a ^ 3) (n + 3) := by
  ext b
  exact ⟨fun hb => hb.2, fun hb => ⟨ha, hb⟩⟩

/-- The slice of `sndResidue r` over any `a` is the residue class `{β ≡ r (mod 3)}`. -/
theorem preimage_sndResidue (r : ZMod 3) (a : ℤ_[3]) :
    Prod.mk a ⁻¹' sndResidue r = PadicInt.toZMod ⁻¹' {r} := rfl

/-- A residue of `2` is impossible for a multiple of `3`. -/
theorem notMem_residue_two_of_dvd {a : ℤ_[3]} (ha : ((3 : ℕ) : ℤ_[3]) ∣ a) :
    a ∉ PadicInt.toZMod ⁻¹' {(2 : ZMod 3)} := by
  intro h
  have h0 : PadicInt.toZMod a = 0 := PadicInt.dvd_iff_toZMod_eq_zero.1 ha
  have h2 : PadicInt.toZMod a = 2 := h
  rw [h0] at h2
  exact absurd h2 (by decide)

/-- For a unit `α` with `−4α³` a square, `α ≡ 2 (mod 3)`. -/
theorem mem_residue_two_of_isSquare {a : ℤ_[3]} (hau : IsUnit a)
    (hsq : IsSquare (-4 * a ^ 3 : ℤ_[3])) : a ∈ PadicInt.toZMod ⁻¹' {(2 : ZMod 3)} :=
  (isSquare_neg_four_mul_cube_iff_three rfl hau).1 hsq

/-- For a unit `α` with `−4α³` not a square, `α ≢ 2 (mod 3)`. -/
theorem notMem_residue_two_of_not_isSquare {a : ℤ_[3]} (hau : IsUnit a)
    (hsq : ¬ IsSquare (-4 * a ^ 3 : ℤ_[3])) : a ∉ PadicInt.toZMod ⁻¹' {(2 : ZMod 3)} :=
  fun h => hsq ((isSquare_neg_four_mul_cube_iff_three rfl hau).2 h)

/-- **The mass of an `a₄`-slice of the level-`n` shell**: `2(1 − 3⁻¹)3^{−(n+3)}` on the residue
class `α ≡ 2 (mod 3)` and `0` elsewhere. -/
theorem volume_slice_preShell (n : ℕ) (a : ℤ_[3]) :
    (volume : Measure ℤ_[3]) (Prod.mk a ⁻¹' preShell n)
      = (PadicInt.toZMod ⁻¹' {(2 : ZMod 3)}).indicator
          (fun _ => 2 * (1 - ((3 : ℕ) : ℝ≥0∞)⁻¹) * (((3 : ℕ) : ℝ≥0∞)⁻¹) ^ (n + 3)) a := by
  have hodd : Odd 3 := by decide
  by_cases ha : ((3 : ℕ) : ℤ_[3]) ∣ a
  · rw [preimage_preShell_of_dvd ha, measure_empty,
      Set.indicator_of_notMem (notMem_residue_two_of_dvd ha)]
  · rw [preimage_preShell_of_not_dvd ha]
    have hau : IsUnit a := isUnit_of_not_dvd ha
    have hunit : IsUnit (-4 * a ^ 3 : ℤ_[3]) := (PadicInt.isUnit_neg_four hodd).mul (hau.pow 3)
    by_cases hsq : IsSquare (-4 * a ^ 3 : ℤ_[3])
    · rw [PadicInt.measure_sqLevelSet_of_isSquare hodd hunit hsq (by omega : 1 ≤ n + 3),
        Set.indicator_of_mem (mem_residue_two_of_isSquare hau hsq)]
    · rw [PadicInt.sqLevelSet_eq_empty_of_not_isSquare hodd hunit hsq (by omega : 1 ≤ n + 3),
        measure_empty, Set.indicator_of_notMem (notMem_residue_two_of_not_isSquare hau hsq)]

/-- The residue class `{β | β ≡ r (mod 3)}` is constant on residue classes modulo `3`. -/
theorem residue_congr (r : ZMod 3) : ∀ y z : ℤ_[3], ((3 : ℕ) : ℤ_[3]) ∣ y - z →
    (y ∈ PadicInt.toZMod ⁻¹' {r} ↔ z ∈ PadicInt.toZMod ⁻¹' {r}) := by
  intro y z h
  rw [PadicInt.dvd_iff_toZMod_eq_zero, map_sub, sub_eq_zero] at h
  simp only [Set.mem_preimage, Set.mem_singleton_iff, h]

/-- In `ZMod 3`, for a nonzero `x` and a nonzero `r`, exactly one of `x`, `−x` equals `r`. -/
theorem zmod_three_eq_or_neg_eq :
    ∀ x r : ZMod 3, x ≠ 0 → r ≠ 0 → (x = r ∧ -x ≠ r) ∨ (x ≠ r ∧ -x = r) := by
  decide

/-- **A residue condition `β ≡ r (mod 3)` with `r ≠ 0` keeps exactly one of the two roots
`±s`.** -/
theorem unique_root_residue {r : ZMod 3} (hr : r ≠ 0) {s : ℤ_[3]} (hs : IsUnit s) :
    (s ∈ PadicInt.toZMod ⁻¹' {r} ∧ -s ∉ PadicInt.toZMod ⁻¹' {r}) ∨
      (s ∉ PadicInt.toZMod ⁻¹' {r} ∧ -s ∈ PadicInt.toZMod ⁻¹' {r}) := by
  have hs0 : PadicInt.toZMod s ≠ 0 := fun h =>
    PadicInt.dvd_iff_not_isUnit.1 (PadicInt.dvd_iff_toZMod_eq_zero.2 h) hs
  simp only [Set.mem_preimage, Set.mem_singleton_iff, map_neg]
  exact zmod_three_eq_or_neg_eq _ _ hs0 hr

/-- **The mass of an `a₄`-slice of a half**: `(1 − 3⁻¹)3^{−(n+3)}` on `α ≡ 2 (mod 3)`, `0`
elsewhere — one ball of the two. -/
theorem volume_slice_preHalf {r : ZMod 3} (hr : r ≠ 0) (n : ℕ) (a : ℤ_[3]) :
    (volume : Measure ℤ_[3]) (Prod.mk a ⁻¹' (preShell n ∩ sndResidue r))
      = (PadicInt.toZMod ⁻¹' {(2 : ZMod 3)}).indicator
          (fun _ => (1 - ((3 : ℕ) : ℝ≥0∞)⁻¹) * (((3 : ℕ) : ℝ≥0∞)⁻¹) ^ (n + 3)) a := by
  have hodd : Odd 3 := by decide
  rw [Set.preimage_inter, preimage_sndResidue]
  by_cases ha : ((3 : ℕ) : ℤ_[3]) ∣ a
  · rw [preimage_preShell_of_dvd ha, Set.empty_inter, measure_empty,
      Set.indicator_of_notMem (notMem_residue_two_of_dvd ha)]
  · rw [preimage_preShell_of_not_dvd ha]
    have hau : IsUnit a := isUnit_of_not_dvd ha
    have hunit : IsUnit (-4 * a ^ 3 : ℤ_[3]) := (PadicInt.isUnit_neg_four hodd).mul (hau.pow 3)
    by_cases hsq : IsSquare (-4 * a ^ 3 : ℤ_[3])
    · obtain ⟨s, hs⟩ := hsq
      have hsu : IsUnit s := by rw [hs] at hunit; exact (IsUnit.mul_iff.mp hunit).1
      rw [PadicInt.volume_sqLevelSet_inter_of_unique_root hodd hunit hs (residue_congr r)
          (unique_root_residue hr hsu) (by omega : 1 ≤ n + 3),
        Set.indicator_of_mem (mem_residue_two_of_isSquare hau ⟨s, hs⟩)]
    · rw [PadicInt.sqLevelSet_eq_empty_of_not_isSquare hodd hunit hsq (by omega : 1 ≤ n + 3),
        Set.empty_inter, measure_empty,
        Set.indicator_of_notMem (notMem_residue_two_of_not_isSquare hau hsq)]

/-- The mass of `preShell n`: the slice constant times the mass `3⁻¹` of `{α ≡ 2 (mod 3)}`. -/
theorem volume_preShell (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (preShell n)
      = 2 * (1 - ((3 : ℕ) : ℝ≥0∞)⁻¹) * (((3 : ℕ) : ℝ≥0∞)⁻¹) ^ (n + 3)
          * ((3 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_preShell n),
    lintegral_congr (volume_slice_preShell n),
    lintegral_indicator_const (PadicInt.measurableSet_preimage_toZMod 2),
    PadicInt.volume_preimage_toZMod]

/-- The mass of a half of `preShell n`. -/
theorem volume_preHalf {r : ZMod 3} (hr : r ≠ 0) (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (preShell n ∩ sndResidue r)
      = (1 - ((3 : ℕ) : ℝ≥0∞)⁻¹) * (((3 : ℕ) : ℝ≥0∞)⁻¹) ^ (n + 3) * ((3 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply ((measurableSet_preShell n).inter (measurableSet_sndResidue r)),
    lintegral_congr (volume_slice_preHalf hr n),
    lintegral_indicator_const (PadicInt.measurableSet_preimage_toZMod 2),
    PadicInt.volume_preimage_toZMod]

/-- `1 − 3⁻¹ = 2 · 3⁻¹` in `ℝ≥0∞`. -/
theorem one_sub_inv_three_eq :
    (1 : ℝ≥0∞) - ((3 : ℕ) : ℝ≥0∞)⁻¹ = 2 * ((3 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  rw [show (2 : ℝ≥0∞) * ((3 : ℕ) : ℝ≥0∞)⁻¹ + ((3 : ℕ) : ℝ≥0∞)⁻¹
      = 3 * ((3 : ℕ) : ℝ≥0∞)⁻¹ from by ring]
  norm_num
  exact (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm

/-- **The mass of the level-`n` shell is `4 · 3^{−(n+11)}`.** -/
theorem volume_shell (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (shell n) = 4 * ((3 : ℝ≥0∞)⁻¹) ^ (n + 11) := by
  rw [shell, PadicInt.measure_image_scaleProdByPPow, volume_preShell,
    show ((3 : ℕ) + (3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num,
    PadicInt.zpow_neg_natCast_eq_inv_pow, one_sub_inv_three_eq,
    show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num, show n + 11 = 6 + (n + 3) + 1 + 1 by omega]
  ring

/-- **The mass of a half of the level-`n` shell is `2 · 3^{−(n+11)}`**, for `r ≠ 0`. -/
theorem volume_half {r : ZMod 3} (hr : r ≠ 0) (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (half r n) = 2 * ((3 : ℝ≥0∞)⁻¹) ^ (n + 11) := by
  rw [half, PadicInt.measure_image_scaleProdByPPow, volume_preHalf hr,
    show ((3 : ℕ) + (3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num,
    PadicInt.zpow_neg_natCast_eq_inv_pow, one_sub_inv_three_eq,
    show ((3 : ℕ) : ℝ≥0∞) = 3 by norm_num, show n + 11 = 6 + (n + 3) + 1 + 1 by omega]
  ring

/-- The split half of the level-`n` shell has mass `2 · 3^{−(n+11)}`. -/
theorem volume_splitShell (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (splitShell n) = 2 * ((3 : ℝ≥0∞)⁻¹) ^ (n + 11) :=
  volume_half (by decide) n

/-- The non-split half of the level-`n` shell has mass `2 · 3^{−(n+11)}`. -/
theorem volume_nonSplitShell (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (nonSplitShell n) = 2 * ((3 : ℝ≥0∞)⁻¹) ^ (n + 11) :=
  volume_half (by decide) n

/-- `c · (3⁻¹)ᵏ = c / 3ᵏ` in `ℝ≥0∞`. -/
theorem mul_inv_pow_eq_div (c : ℝ≥0∞) (k : ℕ) : c * ((3 : ℝ≥0∞)⁻¹) ^ k = c / 3 ^ k := by
  rw [← ENNReal.inv_pow, div_eq_mul_inv]

/-- The level-`n` shell has mass `4/3^{n+11}`. -/
theorem volume_shell_div (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (shell n) = 4 / 3 ^ (n + 11) := by
  rw [volume_shell, mul_inv_pow_eq_div]

/-- The split half of the level-`n` shell has mass `2/3^{n+11}`. -/
theorem volume_splitShell_div (n : ℕ) :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (splitShell n) = 2 / 3 ^ (n + 11) := by
  rw [volume_splitShell, mul_inv_pow_eq_div]

/-- **The level-`0` shell has mass `4/3¹¹ = 4/177147`.** -/
theorem volume_iZeroDescentLocus :
    (volume : Measure (ℤ_[3] × ℤ_[3])) iZeroDescentLocus = 4 / 177147 := by
  rw [iZeroDescentLocus, volume_shell_div, show (3 : ℝ≥0∞) ^ (0 + 11) = 177147 by norm_num]

/-- The split half of the level-`1` shell has mass `2/3¹² = 2/531441`. -/
theorem volume_splitShell_one :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (splitShell 1) = 2 / 531441 := by
  rw [volume_splitShell_div, show (3 : ℝ≥0∞) ^ (1 + 11) = 531441 by norm_num]

/-- The split half of the level-`2` shell has mass `2/3¹³ = 2/1594323`. -/
theorem volume_splitShell_two :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (splitShell 2) = 2 / 1594323 := by
  rw [volume_splitShell_div, show (3 : ℝ≥0∞) ^ (2 + 11) = 1594323 by norm_num]

/-- The split half of the level-`3` shell has mass `2/3¹⁴ = 2/4782969`. -/
theorem volume_splitShell_three :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (splitShell 3) = 2 / 4782969 := by
  rw [volume_splitShell_div, show (3 : ℝ≥0∞) ^ (3 + 11) = 4782969 by norm_num]

/-- The split half of the level-`4` shell has mass `2/3¹⁵ = 2/14348907`. -/
theorem volume_splitShell_four :
    (volume : Measure (ℤ_[3] × ℤ_[3])) (splitShell 4) = 2 / 14348907 := by
  rw [volume_splitShell_div, show (3 : ℝ≥0∞) ^ (4 + 11) = 14348907 by norm_num]

/-! ### The geometric sums over the odd and the even non-split levels -/

/-- `∑_{j ≥ 0} 9^{-j} = 9/8` in `ℝ≥0∞`. -/
theorem tsum_inv_pow_ninth : ∑' j : ℕ, ((9 : ℝ≥0∞)⁻¹) ^ j = 9 / 8 := by
  have h1 : (1 : ℝ≥0∞) - (9 : ℝ≥0∞)⁻¹ = 8 / 9 := by
    refine ENNReal.sub_eq_of_eq_add (by simp) ?_
    rw [ENNReal.div_eq_inv_mul,
      show (9 : ℝ≥0∞)⁻¹ * 8 + (9 : ℝ≥0∞)⁻¹ = (9 : ℝ≥0∞)⁻¹ * 9 from by ring]
    exact (ENNReal.inv_mul_cancel (by norm_num) (by norm_num)).symm
  have h2 : ((8 : ℝ≥0∞) / 9)⁻¹ = 9 / 8 := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      inv_inv, ENNReal.div_eq_inv_mul]
    ring
  rw [ENNReal.tsum_geometric, h1, h2]

/-- `(3⁻¹)^{2j+k} = (3⁻¹)^k · (9⁻¹)^j`. -/
theorem inv_pow_two_mul_add (j k : ℕ) :
    ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + k) = ((3 : ℝ≥0∞)⁻¹) ^ k * ((9 : ℝ≥0∞)⁻¹) ^ j := by
  rw [pow_add, pow_mul, show ((3 : ℝ≥0∞)⁻¹) ^ 2 = (9 : ℝ≥0∞)⁻¹ from by
    rw [← ENNReal.inv_pow]; norm_num]
  ring

/-- **`∑_{j ≥ 0} 2 · 3^{−(2j+12)} = 1/236196`**: the total mass of the non-split shells at odd
levels, `2 · 3⁻¹² · 9/8`. -/
theorem tsum_two_mul_inv_pow_odd_levels :
    ∑' j : ℕ, 2 * ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + 12) = 1 / 236196 := by
  have hterm : ∀ j : ℕ, 2 * ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + 12)
      = 2 * ((3 : ℝ≥0∞)⁻¹) ^ 12 * ((9 : ℝ≥0∞)⁻¹) ^ j := fun j => by
    rw [inv_pow_two_mul_add, mul_assoc]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_inv_pow_ninth, mul_inv_pow_eq_div,
    show (3 : ℝ≥0∞) ^ 12 = 531441 by norm_num, enn_div_mul_div (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞) * 9 = 18 by norm_num, show (531441 : ℝ≥0∞) * 8 = 4251528 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **`∑_{j ≥ 0} 2 · 3^{−(2j+13)} = 1/708588`**: the total mass of the non-split shells at even
levels `≥ 2`, `2 · 3⁻¹³ · 9/8`. -/
theorem tsum_two_mul_inv_pow_even_levels :
    ∑' j : ℕ, 2 * ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + 13) = 1 / 708588 := by
  have hterm : ∀ j : ℕ, 2 * ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + 13)
      = 2 * ((3 : ℝ≥0∞)⁻¹) ^ 13 * ((9 : ℝ≥0∞)⁻¹) ^ j := fun j => by
    rw [inv_pow_two_mul_add, mul_assoc]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_inv_pow_ninth, mul_inv_pow_eq_div,
    show (3 : ℝ≥0∞) ^ 13 = 1594323 by norm_num, enn_div_mul_div (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞) * 9 = 18 by norm_num, show (1594323 : ℝ≥0∞) * 8 = 12754584 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The non-split shells at odd levels have total mass `1/236196`.** -/
theorem volume_nonSplitOdd : (volume : Measure (ℤ_[3] × ℤ_[3])) nonSplitOdd = 1 / 236196 := by
  have hv : ∀ j : ℕ, (volume : Measure (ℤ_[3] × ℤ_[3])) (nonSplitShell (2 * j + 1))
      = 2 * ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + 12) := fun j => by
    rw [volume_nonSplitShell, show 2 * j + 1 + 11 = 2 * j + 12 by omega]
  rw [nonSplitOdd, measure_iUnion (fun i j hij => disjoint_nonSplitShell_of_ne (by omega))
      fun j => measurableSet_nonSplitShell (2 * j + 1),
    tsum_congr hv, tsum_two_mul_inv_pow_odd_levels]

/-- **The non-split shells at even levels `≥ 2` have total mass `1/708588`.** -/
theorem volume_nonSplitEven : (volume : Measure (ℤ_[3] × ℤ_[3])) nonSplitEven = 1 / 708588 := by
  have hv : ∀ j : ℕ, (volume : Measure (ℤ_[3] × ℤ_[3])) (nonSplitShell (2 * j + 2))
      = 2 * ((3 : ℝ≥0∞)⁻¹) ^ (2 * j + 13) := fun j => by
    rw [volume_nonSplitShell, show 2 * j + 2 + 11 = 2 * j + 13 by omega]
  rw [nonSplitEven, measure_iUnion (fun i j hij => disjoint_nonSplitShell_of_ne (by omega))
      fun j => measurableSet_nonSplitShell (2 * j + 2),
    tsum_congr hv, tsum_two_mul_inv_pow_even_levels]

/-! ### The shells lie in the minimal parts of their rows, assuming the forward run -/

/-- The minimal part of the `t`-row at `p = 3`: the `t`-fibre, any Kodaira symbol, with the
`(3⁴, 3⁶)`-dilates removed. -/
abbrev headMinimal (t : ℕ) : Set (ℤ_[3] × ℤ_[3]) :=
  (⋃ κ : KodairaSymbol, stratFibre 3 (κ, t)) \
    Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[3] × ℤ_[3] → ℤ_[3] × ℤ_[3])

/-- **The level-`0` shell lies in the minimal part of row `t = 1`**, at the symbol `I₀`. -/
theorem iZeroDescentLocus_subset_headMinimal (hrun : ForwardRun) :
    iZeroDescentLocus ⊆ headMinimal 1 := by
  refine subset_headMinimal_at_three (κ := KodairaSymbol.I 0) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨α, β, h₄, h₆, -, -, hlev'⟩ := exists_form_of_mem_shell hx
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_form h₄ h₆ (ne_zero_of_not_pow_dvd hlev')
    obtain ⟨hks, ht⟩ :=
      hrun.run_eq_I_zero_of_level_zero hΔ (shell_subset_cyl 0 hx) h₄ h₆ hlev'
    refine (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_
    rw [strat]
    exact Prod.ext hks ht
  · obtain ⟨α, β, h₄, -, hα, -, -⟩ := exists_form_of_mem_shell hx
    exact notMem_range_of_form h₄ hα

/-- **The split half of the level-`n` shell lies in the minimal part of row `t = n`**, for `n ≥ 1`,
at the symbol `Iₙ`. -/
theorem splitShell_subset_headMinimal (hrun : ForwardRun) {n : ℕ} (hn : 1 ≤ n) :
    splitShell n ⊆ headMinimal n := by
  refine subset_headMinimal_at_three (κ := KodairaSymbol.I n) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨α, β, h₄, h₆, -, hlev, hlev', hβ⟩ := exists_form_of_mem_half hx
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_form h₄ h₆ (ne_zero_of_not_pow_dvd hlev')
    obtain ⟨hks, ht⟩ :=
      hrun.run_eq_I_of_split hΔ (half_subset_cyl 2 n hx) h₄ h₆ hn hlev hlev' hβ
    refine (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_
    rw [strat]
    exact Prod.ext hks ht
  · obtain ⟨α, β, h₄, -, hα, -, -, -⟩ := exists_form_of_mem_half hx
    exact notMem_range_of_form h₄ hα

/-- **A non-split shell at an odd level lies in the minimal part of row `t = 1`.** -/
theorem nonSplitShell_odd_subset_headMinimal (hrun : ForwardRun) (j : ℕ) :
    nonSplitShell (2 * j + 1) ⊆ headMinimal 1 := by
  refine subset_headMinimal_at_three (κ := KodairaSymbol.I (2 * j + 1)) (fun x hx => ?_)
    (fun x hx => ?_)
  · obtain ⟨α, β, h₄, h₆, -, hlev, hlev', hβ⟩ := exists_form_of_mem_half hx
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_form h₄ h₆ (ne_zero_of_not_pow_dvd hlev')
    obtain ⟨hks, ht⟩ := hrun.run_eq_I_of_nonsplit hΔ (half_subset_cyl 1 _ hx) h₄ h₆
      (by omega : 1 ≤ 2 * j + 1) hlev hlev' hβ
    rw [ite_eq_left (by rw [Nat.odd_iff]; omega)] at ht
    refine (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_
    rw [strat]
    exact Prod.ext hks ht
  · obtain ⟨α, β, h₄, -, hα, -, -, -⟩ := exists_form_of_mem_half hx
    exact notMem_range_of_form h₄ hα

/-- **A non-split shell at an even level `≥ 2` lies in the minimal part of row `t = 2`.** -/
theorem nonSplitShell_even_subset_headMinimal (hrun : ForwardRun) (j : ℕ) :
    nonSplitShell (2 * j + 2) ⊆ headMinimal 2 := by
  refine subset_headMinimal_at_three (κ := KodairaSymbol.I (2 * j + 2)) (fun x hx => ?_)
    (fun x hx => ?_)
  · obtain ⟨α, β, h₄, h₆, -, hlev, hlev', hβ⟩ := exists_form_of_mem_half hx
    have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_form h₄ h₆ (ne_zero_of_not_pow_dvd hlev')
    obtain ⟨hks, ht⟩ := hrun.run_eq_I_of_nonsplit hΔ (half_subset_cyl 1 _ hx) h₄ h₆
      (by omega : 1 ≤ 2 * j + 2) hlev hlev' hβ
    rw [ite_eq_right (by rw [Nat.odd_iff]; omega)] at ht
    refine (mem_stratFibre_iff (hΔ : x ∈ nonsingularLocus 3)).2 ?_
    rw [strat]
    exact Prod.ext hks ht
  · obtain ⟨α, β, h₄, -, hα, -, -, -⟩ := exists_form_of_mem_half hx
    exact notMem_range_of_form h₄ hα

/-- **The non-split shells at odd levels lie in the minimal part of row `t = 1`**, assuming
`ForwardRun`. -/
theorem nonSplitOdd_subset_headMinimal (hrun : ForwardRun) : nonSplitOdd ⊆ headMinimal 1 :=
  Set.iUnion_subset fun j => nonSplitShell_odd_subset_headMinimal hrun j

/-- **The non-split shells at even levels `≥ 2` lie in the minimal part of row `t = 2`**, assuming
`ForwardRun`. -/
theorem nonSplitEven_subset_headMinimal (hrun : ForwardRun) : nonSplitEven ⊆ headMinimal 2 :=
  Set.iUnion_subset fun j => nonSplitShell_even_subset_headMinimal hrun j

/-! ### The four row sets, their masses, and the row-`1` contribution -/

/-- **Family B's row `t = 1` set**: the level-`0` shell, the odd non-split shells, and the split
shell at level `1`. -/
noncomputable def rowOneFamilyB : Set (ℤ_[3] × ℤ_[3]) :=
  iZeroDescentLocus ∪ nonSplitOdd ∪ splitShell 1

/-- **Family B's row `t = 2` set**: the even non-split shells and the split shell at level `2`. -/
noncomputable def rowTwoFamilyB : Set (ℤ_[3] × ℤ_[3]) := nonSplitEven ∪ splitShell 2

/-- **Family B's row `t = 3` set**: the split shell at level `3`. -/
noncomputable def rowThreeFamilyB : Set (ℤ_[3] × ℤ_[3]) := splitShell 3

/-- **Family B's row `t = 4` set**: the split shell at level `4`. -/
noncomputable def rowFourFamilyB : Set (ℤ_[3] × ℤ_[3]) := splitShell 4

/-- Family B's row `t = 1` set is measurable. -/
theorem measurableSet_rowOneFamilyB : MeasurableSet rowOneFamilyB :=
  (measurableSet_iZeroDescentLocus.union measurableSet_nonSplitOdd).union
    (measurableSet_splitShell 1)

/-- Family B's row `t = 2` set is measurable. -/
theorem measurableSet_rowTwoFamilyB : MeasurableSet rowTwoFamilyB :=
  measurableSet_nonSplitEven.union (measurableSet_splitShell 2)

/-- Family B's row `t = 3` set is measurable. -/
theorem measurableSet_rowThreeFamilyB : MeasurableSet rowThreeFamilyB := measurableSet_splitShell 3

/-- Family B's row `t = 4` set is measurable. -/
theorem measurableSet_rowFourFamilyB : MeasurableSet rowFourFamilyB := measurableSet_splitShell 4

/-- **Row `t = 1` has mass `4/177147 + 1/236196 + 2/531441 = 65/2125764`.** -/
theorem volume_rowOneFamilyB :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowOneFamilyB = 65 / 2125764 := by
  rw [rowOneFamilyB, measure_union (Set.disjoint_union_left.2
      ⟨disjoint_iZeroDescentLocus_splitShell_one, disjoint_nonSplitOdd_splitShell_one⟩)
      (measurableSet_splitShell 1),
    measure_union disjoint_iZeroDescentLocus_nonSplitOdd measurableSet_nonSplitOdd,
    volume_iZeroDescentLocus, volume_nonSplitOdd, volume_splitShell_one,
    show (4 : ℝ≥0∞) / 177147 = 48 / 2125764 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (1 : ℝ≥0∞) / 236196 = 9 / 2125764 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞) / 531441 = 8 / 2125764 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    show (48 : ℝ≥0∞) + 9 + 8 = 65 by norm_num]

/-- **Row `t = 2` has mass `1/708588 + 2/1594323 = 17/6377292`.** -/
theorem volume_rowTwoFamilyB :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowTwoFamilyB = 17 / 6377292 := by
  rw [rowTwoFamilyB,
    measure_union disjoint_nonSplitEven_splitShell_two (measurableSet_splitShell 2),
    volume_nonSplitEven, volume_splitShell_two,
    show (1 : ℝ≥0∞) / 708588 = 9 / 6377292 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞) / 1594323 = 8 / 6377292 from
      enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ENNReal.div_add_div_same, show (9 : ℝ≥0∞) + 8 = 17 by norm_num]

/-- **Row `t = 3` has mass `2/4782969`.** -/
theorem volume_rowThreeFamilyB :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowThreeFamilyB = 2 / 4782969 := volume_splitShell_three

/-- **Row `t = 4` has mass `2/14348907`.** -/
theorem volume_rowFourFamilyB :
    (volume : Measure (ℤ_[3] × ℤ_[3])) rowFourFamilyB = 2 / 14348907 := volume_splitShell_four

/-- Family B's row `t = 1` set lies in the minimal part of row `t = 1`, assuming `ForwardRun`. -/
theorem rowOneFamilyB_subset_headMinimal (hrun : ForwardRun) : rowOneFamilyB ⊆ headMinimal 1 :=
  Set.union_subset (Set.union_subset (iZeroDescentLocus_subset_headMinimal hrun)
    (nonSplitOdd_subset_headMinimal hrun)) (splitShell_subset_headMinimal hrun le_rfl)

/-- Family B's row `t = 2` set lies in the minimal part of row `t = 2`, assuming `ForwardRun`. -/
theorem rowTwoFamilyB_subset_headMinimal (hrun : ForwardRun) : rowTwoFamilyB ⊆ headMinimal 2 :=
  Set.union_subset (nonSplitEven_subset_headMinimal hrun)
    (splitShell_subset_headMinimal hrun (by norm_num))

/-- Family B's row `t = 3` set lies in the minimal part of row `t = 3`, assuming `ForwardRun`. -/
theorem rowThreeFamilyB_subset_headMinimal (hrun : ForwardRun) :
    rowThreeFamilyB ⊆ headMinimal 3 :=
  splitShell_subset_headMinimal hrun (by norm_num)

/-- Family B's row `t = 4` set lies in the minimal part of row `t = 4`, assuming `ForwardRun`. -/
theorem rowFourFamilyB_subset_headMinimal (hrun : ForwardRun) :
    rowFourFamilyB ⊆ headMinimal 4 :=
  splitShell_subset_headMinimal hrun (by norm_num)

/-- **Row `t = 1`: `65/2125728 ≤ δ₃(1)` from Family B**, assuming `ForwardRun`. The mass
`65/2125764` times the storey factor `59049/59048`. -/
theorem le_δ_one (hrun : ForwardRun) : (65 : ℝ≥0∞) / 2125728 ≤ δ 3 1 := by
  refine le_trans (le_of_eq ?_) (le_δ_at_three_of_subset (rowOneFamilyB_subset_headMinimal hrun))
  rw [volume_rowOneFamilyB, enn_div_mul_div (by norm_num) (by norm_num)]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end FamilyBThree

end WeierstrassCurve

end
