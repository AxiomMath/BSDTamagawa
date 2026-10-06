/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# Equidistribution of coefficient pairs by residue

For every `M ≥ 1` and every `A ⊆ (ℤ/Mℤ)²`, the natural density of integer coefficient pairs
`(a₄, a₆)` giving a nonsingular short Weierstrass curve of bounded height whose reduction mod `M`
lies in `A` equals `|A| / M²`: `N_A(X) / N(X) → |A| / M²` as `X → ∞`
(`tendsto_restrictedCount_div_Ncount`), with `N(X)` the total count
`WeierstrassCurve.integralShortNFCount` and `N_A(X)` the residue-restricted count
`restrictedCount`.

## The argument

The height condition `Ht(a₄, a₆) = max{4|a₄|³, 27 a₆²} ≤ X` is, for `0 ≤ X`, exactly membership in
the integer box `B(X) = [-a₄Bound X, a₄Bound X] × [-a₆Bound X, a₆Bound X]` (`mem_heightBox_iff`),
where `a₄Bound X = ⌊(X/4)^{1/3}⌋` and `a₆Bound X = ⌊(X/27)^{1/2}⌋`. Writing `S` for the singular
locus `4a₄³ + 27a₆² = 0` and `P(X) = #B(X) = (2 a₄Bound X + 1)(2 a₆Bound X + 1)` (`boxSize`),
`N(X) = P(X) - #(B(X) ∩ S)` and `N_A(X) = #{p ∈ B(X) : p̄ ∈ A} - #(B(X) ∩ S ∩ A)`. Then:

* `#(B(X) ∩ S) ≤ 2(2 a₄Bound X + 1)` (`card_singular_box_le`), since `27 a₆² = -4 a₄³` has at most
  two integer solutions `a₆` for each `a₄`. As `a₆Bound X → ∞` this is `o(P(X))`
  (`tendsto_singular_ratio_zero`), so `N(X) / P(X) → 1`.
* Each residue class meets a symmetric interval `[-K, K]` in `(2K+1)/M + O(1)` points
  (`abs_card_residueClass_Icc_sub_le_one`); the box count factors over the two coordinates, so
  `#{p ∈ B(X) : p̄ ∈ A} = (|A|/M²) P(X) + O(a₄Bound X + a₆Bound X)`
  (`abs_card_heightBox_residue_sub_le`), whence `N_A(X) / P(X) → |A|/M²`.
* Dividing the two limits gives the theorem.
-/

@[expose] public section

namespace WeierstrassCurve

/-! ### The congruence-restricted counting functions -/

/-- The congruence-restricted count `N_A(X)`: the number of integer coefficient pairs `(a₄, a₆)` of
height at most `X` with `E(a₄, a₆)` nonsingular whose reduction `(a₄ mod M, a₆ mod M)` lies in
`A ⊆ (ℤ/Mℤ)²`. -/
noncomputable def restrictedCount (M : ℕ) (A : Set (ZMod M × ZMod M)) (X : ℝ) : ℕ :=
  {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧ (ofShortNF p.1 p.2).Δ ≠ 0 ∧
    ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A}.ncard

/-! ### Unfolding lemmas for the discriminant and the height -/

/-- The discriminant of `E(a₄, a₆)` equals `-16 (4 a₄³ + 27 a₆²)`. -/
theorem ofShortNF_Δ_eq (a₄ a₆ : ℤ) :
    (ofShortNF a₄ a₆).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := ofShortNF_Δ a₄ a₆

/-- The naive height of `E(a₄, a₆)` equals `max {4 |a₄|³, 27 a₆²}`. -/
theorem integralShortNFHeight_eq (a₄ a₆ : ℤ) :
    integralShortNFHeight a₄ a₆ = max (4 * (a₄.natAbs : ℤ) ^ 3) (27 * a₆ ^ 2) := rfl

/-! ### The coordinate bounds `a₄Bound` and `a₆Bound` -/

open Filter Topology

/-- Upper bound for `|a₄|`: the largest `n` with `4 n³ ≤ X`. -/
noncomputable def a₄Bound (X : ℝ) : ℕ := ⌊(X / 4) ^ ((1 : ℝ) / 3)⌋₊

/-- Upper bound for `|a₆|`: the largest `n` with `27 n² ≤ X`. -/
noncomputable def a₆Bound (X : ℝ) : ℕ := ⌊(X / 27) ^ ((1 : ℝ) / 2)⌋₊

/-- For `X ≥ 0`, `4 n³ ≤ X ↔ n ≤ a₄Bound X`. -/
theorem natAbs_a4_iff {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    (4 * (n : ℝ) ^ 3 ≤ X) ↔ n ≤ a₄Bound X := by
  rw [a₄Bound, one_div, Nat.le_floor_iff (by positivity),
    Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num),
    le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
  rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast, mul_comm]

/-- For `X ≥ 0`, `27 n² ≤ X ↔ n ≤ a₆Bound X`. -/
theorem natAbs_a6_iff {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    (27 * (n : ℝ) ^ 2 ≤ X) ↔ n ≤ a₆Bound X := by
  rw [a₆Bound, one_div, Nat.le_floor_iff (by positivity),
    Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num),
    le_div_iff₀ (by norm_num : (0:ℝ) < 27)]
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, mul_comm]

/-! ### The height box -/

/-- Membership in the symmetric integer interval `[-K, K]` is exactly `|n| ≤ K`. -/
theorem mem_Icc_iff_natAbs_le (n : ℤ) (K : ℕ) :
    n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ↔ n.natAbs ≤ K := by
  rw [Finset.mem_Icc]; omega

/-- For `0 ≤ X`, `Ht(a₄, a₆) ≤ X` if and only if `|a₄| ≤ a₄Bound X` and `|a₆| ≤ a₆Bound X`. -/
theorem height_le_iff_natAbs_le {X : ℝ} (hX : 0 ≤ X) (p : ℤ × ℤ) :
    ((integralShortNFHeight p.1 p.2 : ℝ) ≤ X) ↔
      (p.1.natAbs ≤ a₄Bound X ∧ p.2.natAbs ≤ a₆Bound X) := by
  rw [integralShortNFHeight_eq]
  push_cast
  rw [max_le_iff, ← natAbs_a4_iff hX p.1.natAbs, ← natAbs_a6_iff hX p.2.natAbs,
    Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, sq_abs]

/-- `Δ(E(a₄, a₆)) ≠ 0 ↔ 4 a₄³ + 27 a₆² ≠ 0`. -/
theorem ofShortNF_Δ_ne_zero_iff (a₄ a₆ : ℤ) :
    (ofShortNF a₄ a₆).Δ ≠ 0 ↔ 4 * a₄ ^ 3 + 27 * a₆ ^ 2 ≠ 0 := by
  rw [ofShortNF_Δ_eq, ne_eq, ne_eq, not_iff_not, mul_eq_zero]
  simp

/-- The integer box `[-a₄Bound X, a₄Bound X] × [-a₆Bound X, a₆Bound X]` cut out by the height
bound. -/
noncomputable def heightBox (X : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(a₄Bound X : ℤ)) (a₄Bound X) ×ˢ Finset.Icc (-(a₆Bound X : ℤ)) (a₆Bound X)

/-- `heightBox` unfolded to the product of the two symmetric intervals. -/
theorem heightBox_def (X : ℝ) :
    heightBox X =
      Finset.Icc (-(a₄Bound X : ℤ)) (a₄Bound X) ×ˢ Finset.Icc (-(a₆Bound X : ℤ)) (a₆Bound X) :=
  rfl

/-- For `0 ≤ X`, `Ht(a₄, a₆) ≤ X` if and only if `(a₄, a₆) ∈ heightBox X`. -/
theorem mem_heightBox_iff {X : ℝ} (hX : 0 ≤ X) (p : ℤ × ℤ) :
    p ∈ heightBox X ↔ (integralShortNFHeight p.1 p.2 : ℝ) ≤ X := by
  rw [heightBox_def, Finset.mem_product, mem_Icc_iff_natAbs_le, mem_Icc_iff_natAbs_le,
    height_le_iff_natAbs_le hX]

/-- The number of lattice points in `heightBox X`. -/
theorem heightBox_card (X : ℝ) :
    (heightBox X).card = (2 * a₄Bound X + 1) * (2 * a₆Bound X + 1) := by
  rw [heightBox_def, Finset.card_product, Int.card_Icc, Int.card_Icc]
  congr 1 <;> omega

/-! ### Size estimates for `a₄Bound` and `a₆Bound`: `a₄Bound X ≍ X^{1/3}` and
`a₆Bound X ≍ X^{1/2}` -/

/-- If `c = b ^ n` with `b ≥ 0` and `r = 1 / n`, then `c ^ r = b`. -/
theorem rpow_one_div_of_eq_pow {b c r : ℝ} (n : ℕ) (hn : n ≠ 0) (hb : 0 ≤ b)
    (hc : c = b ^ n) (hr : r = 1 / (n : ℝ)) : c ^ r = b := by
  subst hc; subst hr; rw [one_div, Real.pow_rpow_inv_natCast hb hn]

/-- `1 ≤ a₄Bound X` once `4 ≤ X`. -/
theorem one_le_a₄Bound {X : ℝ} (hX : 4 ≤ X) : 1 ≤ a₄Bound X := by
  refine (Nat.one_le_floor_iff _).mpr ?_
  calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by simp
    _ ≤ (X / 4) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)

/-- `1 ≤ a₆Bound X` once `27 ≤ X`. -/
theorem one_le_a₆Bound {X : ℝ} (hX : 27 ≤ X) : 1 ≤ a₆Bound X := by
  refine (Nat.one_le_floor_iff _).mpr ?_
  calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := by simp
    _ ≤ (X / 27) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)

/-- `a₆Bound X = 0` below the threshold `X < 27`. -/
theorem a₆Bound_eq_zero_of_lt {X : ℝ} (hX0 : 0 ≤ X) (hX : X < 27) : a₆Bound X = 0 := by
  rw [a₆Bound, Nat.floor_eq_zero]
  exact Real.rpow_lt_one (by positivity) (by linarith) (by norm_num)

/-- `a₄Bound X = 1` on the intermediate range `4 ≤ X < 27`. -/
theorem a₄Bound_eq_one_of_lt {X : ℝ} (hX : 4 ≤ X) (hX27 : X < 27) : a₄Bound X = 1 := by
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 :=
    rpow_one_div_of_eq_pow 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlo : (1 : ℝ) ≤ (X / 4) ^ ((1 : ℝ) / 3) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by simp
      _ ≤ (X / 4) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hhi : (X / 4) ^ ((1 : ℝ) / 3) < 2 := by
    calc (X / 4) ^ ((1 : ℝ) / 3) < (8 : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.rpow_lt_rpow (by positivity) (by linarith) (by norm_num)
      _ = 2 := h8
  rw [a₄Bound, Nat.floor_eq_iff (by linarith)]
  exact ⟨by exact_mod_cast hlo, by push_cast; linarith⟩

/-- Upper bound `a₄Bound X ≤ X^{1/3}`. -/
theorem a₄Bound_le_rpow {X : ℝ} (hX : 0 ≤ X) : (a₄Bound X : ℝ) ≤ X ^ ((1 : ℝ) / 3) := by
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hXn : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hX _
  calc (a₄Bound X : ℝ) ≤ (X / 4) ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
    _ = X ^ ((1 : ℝ) / 3) / (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.div_rpow hX (by norm_num) _
    _ ≤ X ^ ((1 : ℝ) / 3) := by rw [div_le_iff₀ (by linarith)]; nlinarith

/-- Upper bound `a₆Bound X ≤ X^{1/2}`. -/
theorem a₆Bound_le_rpow {X : ℝ} (hX : 0 ≤ X) : (a₆Bound X : ℝ) ≤ X ^ ((1 : ℝ) / 2) := by
  have h27 : (1 : ℝ) ≤ (27 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hXn : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hX _
  calc (a₆Bound X : ℝ) ≤ (X / 27) ^ ((1 : ℝ) / 2) := Nat.floor_le (by positivity)
    _ = X ^ ((1 : ℝ) / 2) / (27 : ℝ) ^ ((1 : ℝ) / 2) := Real.div_rpow hX (by norm_num) _
    _ ≤ X ^ ((1 : ℝ) / 2) := by rw [div_le_iff₀ (by linarith)]; nlinarith

/-- Lower bound `X^{1/3} / 4 ≤ a₄Bound X` for `4 ≤ X`. -/
theorem rpow_div_le_a₄Bound {X : ℝ} (hX : 4 ≤ X) : X ^ ((1 : ℝ) / 3) / 4 ≤ (a₄Bound X : ℝ) := by
  rw [a₄Bound]
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hX0 _
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have h4le2 : (4 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 :=
    (Real.rpow_le_rpow (by norm_num) (by norm_num : (4 : ℝ) ≤ 8) (by norm_num)).trans_eq
      (rpow_one_div_of_eq_pow 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  set t := (X / 4) ^ ((1 : ℝ) / 3) with ht
  have htge : X ^ ((1 : ℝ) / 3) / 2 ≤ t := by
    rw [ht, Real.div_rpow hX0 (by norm_num : (0:ℝ) ≤ 4),
      div_le_div_iff₀ (by norm_num) h4pos]
    nlinarith [hXpos, h4le2]
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by simp
      _ ≤ (X / 4) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hfl : t / 2 < (⌊t⌋₊ : ℝ) := Nat.div_two_lt_floor ht1
  linarith

/-- Lower bound `X^{1/2} / 12 ≤ a₆Bound X` for `27 ≤ X`. -/
theorem rpow_div_le_a₆Bound {X : ℝ} (hX : 27 ≤ X) : X ^ ((1 : ℝ) / 2) / 12 ≤ (a₆Bound X : ℝ) := by
  rw [a₆Bound]
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hX0 _
  have h27pos : (0 : ℝ) < (27 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h27le6 : (27 : ℝ) ^ ((1 : ℝ) / 2) ≤ 6 :=
    (Real.rpow_le_rpow (by norm_num) (by norm_num : (27 : ℝ) ≤ 36) (by norm_num)).trans_eq
      (rpow_one_div_of_eq_pow 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  set t := (X / 27) ^ ((1 : ℝ) / 2) with ht
  have htge : X ^ ((1 : ℝ) / 2) / 6 ≤ t := by
    rw [ht, Real.div_rpow hX0 (by norm_num : (0:ℝ) ≤ 27),
      div_le_div_iff₀ (by norm_num) h27pos]
    nlinarith [hXpos, h27le6]
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := by simp
      _ ≤ (X / 27) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hfl : t / 2 < (⌊t⌋₊ : ℝ) := Nat.div_two_lt_floor ht1
  linarith

/-! ### Box reformulation of the two counting functions -/

/-- For `0 ≤ X`, `N(X)` is the number of points of `heightBox X` with `4 a₄³ + 27 a₆² ≠ 0`. -/
theorem Ncount_eq_box_card (X : ℝ) (hX : 0 ≤ X) :
    (integralShortNFCount X : ℝ) =
      ((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)).card := by
  have hset : {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧
        (ofShortNF p.1 p.2).Δ ≠ 0}
      = ↑((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_filter]
    rw [← mem_heightBox_iff hX p, ofShortNF_Δ_ne_zero_iff]
  unfold integralShortNFCount integralShortNFFamily
  simp only [Set.mem_ofPred_eq]
  rw [hset, Set.ncard_coe_finset]

/-- For `0 ≤ X`, `N_A(X)` is the number of points of `heightBox X` with `4 a₄³ + 27 a₆² ≠ 0` and
`(a₄ mod M, a₆ mod M) ∈ A`. -/
theorem restrictedCount_eq_box_card (M : ℕ) (A : Finset (ZMod M × ZMod M)) (X : ℝ)
    (hX : 0 ≤ X) :
    (restrictedCount M (A : Set (ZMod M × ZMod M)) X : ℝ) =
      ((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0 ∧
          ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card := by
  have hset : {p : ℤ × ℤ | (integralShortNFHeight p.1 p.2 : ℝ) ≤ X ∧
        (ofShortNF p.1 p.2).Δ ≠ 0 ∧
        ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ (A : Set (ZMod M × ZMod M))}
      = ↑((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0 ∧
          ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_coe]
    rw [← mem_heightBox_iff hX p, ofShortNF_Δ_ne_zero_iff]
  rw [restrictedCount, hset, Set.ncard_coe_finset]

/-! ### Residue equidistribution in a box -/

/-- For `M ≥ 1` and a residue `r : ZMod M`, the number of integers `n ∈ [-K, K]` with `n ≡ r`
differs from `(2K+1)/M` by at most `1`. -/
theorem abs_card_residueClass_Icc_sub_le_one (M : ℕ) (hM : 1 ≤ M) (r : ZMod M) (K : ℕ) :
    |(((Finset.Icc (-(K : ℤ)) K).filter (fun n : ℤ => ((n : ZMod M) = r))).card : ℝ)
        - (2 * K + 1) / M| ≤ 1 := by
  have hM0 : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hMQ : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  have hNZ : NeZero M := ⟨by omega⟩
  set v : ℤ := (r.val : ℤ) with hv
  have hrv : ((v : ZMod M)) = r := by
    rw [hv]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
  have hpred : ∀ n : ℤ, ((n : ZMod M) = r) ↔ n ≡ v [ZMOD (M : ℤ)] := fun n => by
    rw [← hrv, ZMod.intCast_eq_intCast_iff]
  have hIcc : (Finset.Icc (-(K : ℤ)) K) = Finset.Ico (-(K : ℤ)) (K + 1) := by
    rw [← Finset.Ico_succ_right_eq_Icc]; rfl
  have hfeq : ((Finset.Icc (-(K : ℤ)) K).filter (fun n : ℤ => ((n : ZMod M) = r))).card
      = ((Finset.Ico (-(K : ℤ)) (K + 1)).filter
          (fun n : ℤ => n ≡ v [ZMOD (M : ℤ)])).card := by
    rw [hIcc]
    exact congrArg Finset.card (Finset.filter_congr fun n _ => hpred n)
  rw [hfeq]
  have hcard := Int.Ico_filter_modEq_card (-(K : ℤ)) (K + 1) hM0 v
  set x : ℚ := ((K : ℚ) + 1 - (v : ℚ)) / (M : ℚ) with hx
  set y : ℚ := ((-(K : ℚ)) - (v : ℚ)) / (M : ℚ) with hy
  have hcard' :
      (({x ∈ Finset.Ico (-(K : ℤ)) (K + 1) | x ≡ v [ZMOD (M : ℤ)]}).card : ℤ)
        = max (⌈x⌉ - ⌈y⌉) 0 := by
    rw [hcard]; push_cast [hx, hy]; ring_nf
  have hcle : ⌈y⌉ ≤ ⌈x⌉ := Int.ceil_le_ceil <| by
    rw [hx, hy, div_le_div_iff_of_pos_right hMQ]
    have : (0 : ℚ) ≤ 2 * K + 1 := by positivity
    linarith
  have hNvalR : (((Finset.Ico (-(K : ℤ)) (K + 1)).filter
      (fun n : ℤ => n ≡ v [ZMOD (M : ℤ)])).card : ℝ)
      = ((⌈x⌉ : ℝ) - (⌈y⌉ : ℝ)) := by
    have : (((Finset.Ico (-(K : ℤ)) (K + 1)).filter
        (fun n : ℤ => n ≡ v [ZMOD (M : ℤ)])).card : ℤ) = ⌈x⌉ - ⌈y⌉ := by
      rw [hcard', max_eq_left (by omega)]
    exact_mod_cast this
  rw [hNvalR]
  have hx1 : ((x : ℚ) : ℝ) ≤ (⌈x⌉ : ℝ) := by exact_mod_cast Int.le_ceil x
  have hx2 : (⌈x⌉ : ℝ) < ((x : ℚ) : ℝ) + 1 := by exact_mod_cast Int.ceil_lt_add_one x
  have hy1 : ((y : ℚ) : ℝ) ≤ (⌈y⌉ : ℝ) := by exact_mod_cast Int.le_ceil y
  have hy2 : (⌈y⌉ : ℝ) < ((y : ℚ) : ℝ) + 1 := by exact_mod_cast Int.ceil_lt_add_one y
  have hxy2 : ((x : ℚ) : ℝ) - ((y : ℚ) : ℝ) = (2 * (K : ℝ) + 1) / (M : ℝ) := by
    rw [hx, hy]; push_cast; ring
  rw [abs_le]
  constructor <;> linarith

/-- For `M ≥ 1` and `A : Finset (ZMod M × ZMod M)`, the number of points of the height box whose
residue lies in `A` differs from `(|A|/M²)(2 a₄Bound X + 1)(2 a₆Bound X + 1)` by at most
`|A| ((2 a₄Bound X + 1) + (2 a₆Bound X + 1) + 1)`. -/
theorem abs_card_heightBox_residue_sub_le (M : ℕ) (hM : 1 ≤ M)
    (A : Finset (ZMod M × ZMod M)) (X : ℝ) :
    |(((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card : ℝ)
        - ((A.card : ℝ) / (M : ℝ) ^ 2) * ((2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1))|
      ≤ (A.card : ℝ) * ((2 * (a₄Bound X : ℝ) + 1) + (2 * (a₆Bound X : ℝ) + 1) + 1) := by
  classical
  rw [heightBox_def]
  set IA := Finset.Icc (-(a₄Bound X : ℤ)) (a₄Bound X) with hIA
  set IB := Finset.Icc (-(a₆Bound X : ℤ)) (a₆Bound X) with hIB
  set f : ℤ × ℤ → ZMod M × ZMod M := fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) with hf
  set Na : ZMod M → ℝ :=
    fun c => ((IA.filter (fun a : ℤ => (a : ZMod M) = c)).card : ℝ) with hNa
  set Nb : ZMod M → ℝ :=
    fun c => ((IB.filter (fun b : ℤ => (b : ZMod M) = c)).card : ℝ) with hNb
  set α : ℝ := (2 * (a₄Bound X : ℝ) + 1) / (M : ℝ) with hα
  set β : ℝ := (2 * (a₆Bound X : ℝ) + 1) / (M : ℝ) with hβ
  have hstep1 : (((IA ×ˢ IB).filter (fun p => f p ∈ A)).card : ℝ)
      = ∑ c ∈ A, (Na c.1 * Nb c.2) := by
    have hfib := Finset.sum_card_fiberwise_eq_card_filter (IA ×ˢ IB) A f
    rw [← hfib]
    push_cast
    apply Finset.sum_congr rfl
    intro c _
    have hfiber : ((IA ×ˢ IB).filter (fun p => f p = c)).card
        = (IA.filter (fun a : ℤ => (a : ZMod M) = c.1)).card
          * (IB.filter (fun b : ℤ => (b : ZMod M) = c.2)).card := by
      rw [← Finset.card_product]
      rw [← Finset.filter_product (fun a : ℤ => (a : ZMod M) = c.1)
            (fun b : ℤ => (b : ZMod M) = c.2)]
      exact congrArg Finset.card
        (Finset.filter_congr fun p _ => by rw [hf]; simp only [Prod.ext_iff])
    rw [hfiber]
    push_cast
    rw [hNa, hNb]
  rw [hstep1]
  have habs : |(∑ c ∈ A, Na c.1 * Nb c.2) - ∑ c ∈ A, α * β|
      ≤ ∑ c ∈ A, (α + β + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum
    intro c _
    have hNb0 : 0 ≤ Nb c.2 := by rw [hNb]; positivity
    have hα0 : 0 ≤ α := by rw [hα]; positivity
    have ha1 : |Na c.1 - α| ≤ 1 := by
      have := abs_card_residueClass_Icc_sub_le_one M hM c.1 (a₄Bound X)
      rw [hNa, hα]
      convert this using 2
    have hb1 : |Nb c.2 - β| ≤ 1 := by
      have := abs_card_residueClass_Icc_sub_le_one M hM c.2 (a₆Bound X)
      rw [hNb, hβ]
      convert this using 2
    have hbbound : Nb c.2 ≤ β + 1 := by linarith [(abs_le.mp hb1).2]
    have ht1 : |(Na c.1 - α) * Nb c.2| ≤ 1 * (β + 1) := by
      rw [abs_mul, abs_of_nonneg hNb0]
      exact mul_le_mul ha1 hbbound hNb0 zero_le_one
    have ht2 : |α * (Nb c.2 - β)| ≤ α * 1 := by
      rw [abs_mul, abs_of_nonneg hα0]
      exact mul_le_mul_of_nonneg_left hb1 hα0
    calc |Na c.1 * Nb c.2 - α * β|
        = |(Na c.1 - α) * Nb c.2 + α * (Nb c.2 - β)| := by congr 1; ring
      _ ≤ |(Na c.1 - α) * Nb c.2| + |α * (Nb c.2 - β)| := abs_add_le _ _
      _ ≤ 1 * (β + 1) + α * 1 := add_le_add ht1 ht2
      _ = α + β + 1 := by ring
  have hsumαβ : (∑ _c ∈ A, α * β) = (A.card : ℝ) * (α * β) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hαβeq : (A.card : ℝ) / (M : ℝ) ^ 2 * ((2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1))
      = (A.card : ℝ) * (α * β) := by
    rw [hα, hβ]
    field_simp
  rw [hαβeq, ← hsumαβ]
  have hαle : α ≤ 2 * (a₄Bound X : ℝ) + 1 := by
    rw [hα]
    apply div_le_self (by positivity)
    exact_mod_cast hM
  have hβle : β ≤ 2 * (a₆Bound X : ℝ) + 1 := by
    rw [hβ]
    apply div_le_self (by positivity)
    exact_mod_cast hM
  calc |(∑ c ∈ A, Na c.1 * Nb c.2) - ∑ _c ∈ A, α * β|
      ≤ ∑ _c ∈ A, (α + β + 1) := habs
    _ = (A.card : ℝ) * (α + β + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A.card : ℝ) * ((2 * (a₄Bound X : ℝ) + 1) + (2 * (a₆Bound X : ℝ) + 1) + 1) := by gcongr

/-! ### Negligibility of the singular locus -/

/-- In the integer box `[-Ka, Ka] × [-Kb, Kb]` at most `2(2 Ka + 1)` points lie on the singular
locus `4 a₄³ + 27 a₆² = 0`. -/
theorem card_singular_box_le (Ka Kb : ℕ) :
    ((((Finset.Icc (-(Ka : ℤ)) (Ka : ℤ)) ×ˢ (Finset.Icc (-(Kb : ℤ)) (Kb : ℤ))).filter
        (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)).card : ℝ)
      ≤ 2 * (2 * Ka + 1) := by
  set s := (((Finset.Icc (-(Ka : ℤ)) (Ka : ℤ)) ×ˢ (Finset.Icc (-(Kb : ℤ)) (Kb : ℤ))).filter
        (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)) with hs
  set t := Finset.Icc (-(Ka : ℤ)) (Ka : ℤ) with ht
  have hmaps : ∀ p ∈ s, p.1 ∈ t := by
    intro p hp
    rw [hs, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  have hfiber : ∀ b ∈ t, (s.filter (fun p => p.1 = b)).card ≤ 2 := by
    intro b _
    rcases (s.filter (fun p => p.1 = b)).eq_empty_or_nonempty with he | ⟨q, hq⟩
    · rw [he]; simp
    · rw [Finset.mem_filter, hs, Finset.mem_filter] at hq
      obtain ⟨⟨_, hqeq⟩, hqb⟩ := hq
      have hsub :
          (s.filter (fun p => p.1 = b)) ⊆ ({(b, q.2), (b, -q.2)} : Finset (ℤ × ℤ)) := by
        intro p hp
        rw [Finset.mem_filter, hs, Finset.mem_filter] at hp
        obtain ⟨⟨_, hpeq⟩, hpb⟩ := hp
        rw [(hpb : p.1 = b)] at hpeq
        rw [(hqb : q.1 = b)] at hqeq
        have hfac : (p.2 - q.2) * (p.2 + q.2) = 0 := by linarith
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        rcases mul_eq_zero.mp hfac with h | h
        · exact Or.inl ⟨hpb, by linarith⟩
        · exact Or.inr ⟨hpb, by linarith⟩
      calc (s.filter (fun p => p.1 = b)).card
          ≤ ({(b, q.2), (b, -q.2)} : Finset (ℤ × ℤ)).card := Finset.card_le_card hsub
        _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hmain : s.card ≤ 2 * t.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfiber
  have htcard : t.card = 2 * Ka + 1 := by
    rw [ht, Int.card_Icc]
    omega
  have : s.card ≤ 2 * (2 * Ka + 1) := htcard ▸ hmain
  exact_mod_cast this

/-- `card_singular_box_le` specialised to the height box. -/
theorem singularCard_heightBox_le (X : ℝ) :
    (((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)).card : ℝ)
      ≤ 2 * (2 * (a₄Bound X : ℝ) + 1) := by
  rw [heightBox_def]
  exact_mod_cast card_singular_box_le (a₄Bound X) (a₆Bound X)

/-! ### Limits -/

/-- `a₄Bound X → ∞` as `X → ∞`. -/
theorem a₄Bound_atTop : Filter.Tendsto a₄Bound Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp <| (tendsto_rpow_atTop (by norm_num)).comp <|
    Filter.Tendsto.atTop_div_const (by norm_num) Filter.tendsto_id

/-- `a₆Bound X → ∞` as `X → ∞`. -/
theorem a₆Bound_atTop : Filter.Tendsto a₆Bound Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp <| (tendsto_rpow_atTop (by norm_num)).comp <|
    Filter.Tendsto.atTop_div_const (by norm_num) Filter.tendsto_id

/-- The box size `P(X) = (2 a₄Bound X + 1)(2 a₆Bound X + 1)`, as a real number. -/
noncomputable def boxSize (X : ℝ) : ℝ := (2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1)

/-- The box size is always positive. -/
theorem boxSize_pos (X : ℝ) : 0 < boxSize X := by rw [boxSize]; positivity

/-- The height box has exactly `boxSize X` lattice points. -/
theorem card_heightBox_eq_boxSize (X : ℝ) : ((heightBox X).card : ℝ) = boxSize X := by
  rw [heightBox_card, boxSize]; push_cast; ring

/-- `(a₄Bound X : ℝ) → ∞` as `X → ∞`. -/
theorem a₄Bound_real_atTop :
    Filter.Tendsto (fun X => (a₄Bound X : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.comp a₄Bound_atTop

/-- `(a₆Bound X : ℝ) → ∞` as `X → ∞`. -/
theorem a₆Bound_real_atTop :
    Filter.Tendsto (fun X => (a₆Bound X : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.comp a₆Bound_atTop

/-- The `a₄`-side length `2 a₄Bound X + 1` of the height box tends to infinity. -/
theorem a₄Bound_boxDim_atTop :
    Filter.Tendsto (fun X => 2 * (a₄Bound X : ℝ) + 1) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_add_const_right _ 1
    (Filter.Tendsto.const_mul_atTop (by norm_num) a₄Bound_real_atTop)

/-- The `a₆`-side length `2 a₆Bound X + 1` of the height box tends to infinity. -/
theorem a₆Bound_boxDim_atTop :
    Filter.Tendsto (fun X => 2 * (a₆Bound X : ℝ) + 1) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_add_const_right _ 1
    (Filter.Tendsto.const_mul_atTop (by norm_num) a₆Bound_real_atTop)

/-- For `0 ≤ X`, `N(X)` is `boxSize X` minus the number of box points on `4a₄³ + 27a₆² = 0`. -/
theorem Ncount_eq_boxSize_sub_singular {X : ℝ} (hX : 0 ≤ X) :
    (integralShortNFCount X : ℝ) = boxSize X -
      (((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)).card : ℝ) := by
  have hadd := Finset.card_filter_add_card_filter_not (s := heightBox X)
    (p := fun p : ℤ × ℤ => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)
  have hnegeq :
      ((heightBox X).filter (fun p => ¬ (4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)))
        = ((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)) :=
    Finset.filter_congr fun p _ => by simp only [ne_eq, not_not]
  rw [hnegeq] at hadd
  have haddR :
      (((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)).card : ℝ)
        + (((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)).card : ℝ)
        = ((heightBox X).card : ℝ) := by exact_mod_cast hadd
  rw [Ncount_eq_box_card X hX, ← card_heightBox_eq_boxSize X]
  linarith

/-- For `0 ≤ X`, `N_A(X)` is the number of box points with residue in `A` minus the number of those
on `4a₄³ + 27a₆² = 0`. -/
theorem restrictedCount_eq_sub_singular {M : ℕ} (A : Finset (ZMod M × ZMod M)) {X : ℝ}
    (hX : 0 ≤ X) :
    (restrictedCount M (A : Set (ZMod M × ZMod M)) X : ℝ)
      = (((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card : ℝ)
        - (((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0 ∧
            ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card : ℝ) := by
  rw [restrictedCount_eq_box_card M A X hX]
  have hadd :
      (((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).filter
          (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)).card
        + (((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).filter
          (fun p => ¬ (4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0))).card
        = ((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card :=
    Finset.card_filter_add_card_filter_not _
  have hfilt1 :
      (((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).filter
          (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0))
        = ((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0 ∧
            ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun p _ => by tauto
  have hfilt2 :
      (((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).filter
          (fun p => ¬ (4 * p.1 ^ 3 + 27 * p.2 ^ 2 ≠ 0)))
        = ((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0 ∧
            ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun p _ => by simp only [ne_eq, not_not]; tauto
  rw [hfilt1, hfilt2] at hadd
  push_cast [← hadd]
  ring

/-- Any nonnegative `T X ≤ 2 (2 a₄Bound X + 1)` satisfies `T X / boxSize X → 0`. -/
theorem tendsto_singular_ratio_zero (T : ℝ → ℝ) (hT0 : ∀ X, 0 ≤ T X)
    (hTle : ∀ X, T X ≤ 2 * (2 * (a₄Bound X : ℝ) + 1)) :
    Filter.Tendsto (fun X => T X / boxSize X) Filter.atTop (nhds 0) := by
  have htend0 : Filter.Tendsto (fun X => 2 / (2 * (a₆Bound X : ℝ) + 1)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds a₆Bound_boxDim_atTop
  refine squeeze_zero (fun X => div_nonneg (hT0 X) (boxSize_pos X).le) (fun X => ?_) htend0
  rw [boxSize, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hTle X, (by positivity : (0:ℝ) ≤ 2 * (a₄Bound X : ℝ) + 1),
    (by positivity : (0:ℝ) ≤ 2 * (a₆Bound X : ℝ) + 1)]

/-- `N(X) / boxSize X → 1` as `X → ∞`. -/
theorem tendsto_Ncount_div_boxSize :
    Filter.Tendsto (fun X => (integralShortNFCount X : ℝ) / boxSize X)
      Filter.atTop (nhds 1) := by
  have hStend : Filter.Tendsto
      (fun X => (((heightBox X).filter
        (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)).card : ℝ) / boxSize X)
      Filter.atTop (nhds 0) :=
    tendsto_singular_ratio_zero _ (fun _ => Nat.cast_nonneg _) singularCard_heightBox_le
  have hmain : Filter.Tendsto
      (fun X => 1 - (((heightBox X).filter
        (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0)).card : ℝ) / boxSize X)
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hStend
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with X hX
  rw [Ncount_eq_boxSize_sub_singular hX, sub_div, div_self (boxSize_pos X).ne']

/-- For `M ≥ 1`, `N_A(X) / boxSize X → |A|/M²` as `X → ∞`. -/
theorem tendsto_restrictedCount_div_boxSize (M : ℕ) (hM : 1 ≤ M)
    (A : Finset (ZMod M × ZMod M)) :
    Filter.Tendsto
      (fun X => (restrictedCount M (A : Set (ZMod M × ZMod M)) X : ℝ) / boxSize X)
      Filter.atTop (nhds ((A.card : ℝ) / (M : ℝ) ^ 2)) := by
  set R : ℝ → ℝ := fun X =>
    (((heightBox X).filter (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card : ℝ) with hR
  set SR : ℝ → ℝ := fun X =>
    (((heightBox X).filter (fun p => 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0 ∧
      ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card : ℝ) with hSR
  have hN := fun (X : ℝ) (hX : 0 ≤ X) => restrictedCount_eq_sub_singular A hX
  have hSRtend : Filter.Tendsto (fun X => SR X / boxSize X) Filter.atTop (nhds 0) := by
    refine tendsto_singular_ratio_zero SR (fun X => Nat.cast_nonneg _) (fun X => ?_)
    refine le_trans ?_ (singularCard_heightBox_le X)
    rw [hSR]
    refine Nat.cast_le.mpr (Finset.card_le_card fun p hp => ?_)
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hRerr : ∀ X : ℝ,
      |R X / boxSize X - (A.card : ℝ) / (M : ℝ) ^ 2|
        ≤ (A.card : ℝ) * (2 / (2 * (a₆Bound X : ℝ) + 1) + 2 / (2 * (a₄Bound X : ℝ) + 1)
            + 1 / (2 * (a₆Bound X : ℝ) + 1)) := by
    intro X
    have hBR := abs_card_heightBox_residue_sub_le M hM A X
    have hBReq : (((heightBox X).filter
        (fun p => ((p.1 : ZMod M), (p.2 : ZMod M)) ∈ A)).card : ℝ) = R X := by rw [hR]
    rw [hBReq] at hBR
    have hbs : boxSize X = (2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1) := rfl
    have hcast : R X / boxSize X - (A.card : ℝ) / (M : ℝ) ^ 2
        = (R X - (A.card : ℝ) / (M : ℝ) ^ 2 * boxSize X) / boxSize X := by
      rw [sub_div, mul_div_assoc, div_self (boxSize_pos X).ne', mul_one]
    rw [hcast, abs_div, abs_of_pos (boxSize_pos X), hbs, div_le_iff₀ (by positivity)]
    calc |R X - (A.card : ℝ) / (M : ℝ) ^ 2 *
          ((2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1))|
        ≤ (A.card : ℝ) * ((2 * (a₄Bound X : ℝ) + 1) + (2 * (a₆Bound X : ℝ) + 1) + 1) := hBR
      _ ≤ (A.card : ℝ) * (2 / (2 * (a₆Bound X : ℝ) + 1) + 2 / (2 * (a₄Bound X : ℝ) + 1)
            + 1 / (2 * (a₆Bound X : ℝ) + 1)) *
            ((2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1)) := by
          have hLa : (0 : ℝ) < 2 * (a₄Bound X : ℝ) + 1 := by positivity
          have hLb : (0 : ℝ) < 2 * (a₆Bound X : ℝ) + 1 := by positivity
          have hexp : (2 / (2 * (a₆Bound X : ℝ) + 1) + 2 / (2 * (a₄Bound X : ℝ) + 1)
              + 1 / (2 * (a₆Bound X : ℝ) + 1)) *
              ((2 * (a₄Bound X : ℝ) + 1) * (2 * (a₆Bound X : ℝ) + 1))
              = 2 * (2 * (a₄Bound X : ℝ) + 1) + 2 * (2 * (a₆Bound X : ℝ) + 1)
                + (2 * (a₄Bound X : ℝ) + 1) := by
            field_simp
          rw [mul_assoc, hexp]
          exact mul_le_mul_of_nonneg_left (by nlinarith [hLa, hLb]) (by positivity)
  have hErrTend : Filter.Tendsto
      (fun X => (A.card : ℝ) * (2 / (2 * (a₆Bound X : ℝ) + 1) + 2 / (2 * (a₄Bound X : ℝ) + 1)
        + 1 / (2 * (a₆Bound X : ℝ) + 1))) Filter.atTop (nhds 0) := by
    have t1 : Filter.Tendsto (fun X => (2 : ℝ) / (2 * (a₆Bound X : ℝ) + 1)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds a₆Bound_boxDim_atTop
    have t2 : Filter.Tendsto (fun X => (2 : ℝ) / (2 * (a₄Bound X : ℝ) + 1)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds a₄Bound_boxDim_atTop
    have t3 : Filter.Tendsto (fun X => (1 : ℝ) / (2 * (a₆Bound X : ℝ) + 1)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds a₆Bound_boxDim_atTop
    simpa using (((t1.add t2).add t3).const_mul (A.card : ℝ))
  have hRtend : Filter.Tendsto (fun X => R X / boxSize X) Filter.atTop
      (nhds ((A.card : ℝ) / (M : ℝ) ^ 2)) := by
    have hRdiff : Filter.Tendsto
        (fun X => R X / boxSize X - (A.card : ℝ) / (M : ℝ) ^ 2) Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero (fun X => abs_nonneg _) hRerr hErrTend
    have h := hRdiff.add (tendsto_const_nhds (x := (A.card : ℝ) / (M : ℝ) ^ 2))
    rw [zero_add] at h
    exact h.congr fun X => by ring
  have hmain : Filter.Tendsto (fun X => R X / boxSize X - SR X / boxSize X) Filter.atTop
      (nhds ((A.card : ℝ) / (M : ℝ) ^ 2)) := by
    simpa using hRtend.sub hSRtend
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with X hX
  rw [hN X hX, sub_div]

/-- For every `M ≥ 1` and every `A ⊆ (ℤ/Mℤ)²`, `N_A(X) / N(X) → |A| / M²` as `X → ∞`. -/
@[bsd_tamagawa "T029"]
theorem tendsto_restrictedCount_div_Ncount (M : ℕ) (hM : 1 ≤ M)
    (A : Finset (ZMod M × ZMod M)) :
    Filter.Tendsto (fun X => (restrictedCount M (A : Set (ZMod M × ZMod M)) X : ℝ) /
        (integralShortNFCount X : ℝ))
      Filter.atTop (nhds ((A.card : ℝ) / (M : ℝ) ^ 2)) := by
  have hcomb := (tendsto_restrictedCount_div_boxSize M hM A).div
    tendsto_Ncount_div_boxSize (by norm_num)
  rw [div_one] at hcomb
  exact hcomb.congr fun X => div_div_div_cancel_right₀ (boxSize_pos X).ne' _ _

end WeierstrassCurve
