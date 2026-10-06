/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildInStarLowAtTwo

/-!
# One additive offset in `a₆` exchanges Tamagawa `2` with Tamagawa `4` at `p = 2`

Let `W` be a curve entering Step 7's subprocedure at level `n` with the algorithm's loop
invariant, and let `W'` be `W` with `ϖ ^ v` added to `a₆` and nothing else changed. When `v` is
the `a₆` index the loop's exit test reads, that is, when the loop's answer on `W` is `Iₘ*` with
`v = m + 3`, the two runs report the same Kodaira symbol and opposite Tamagawa numbers:

  `(subprocedure W').tamagawaNumber = 4 ↔ (subprocedure W).tamagawaNumber = 2`.

In the Weierstrass transformation law with `u = 1`,

  `(C • W).a₆ = W.a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁`,

the old `a₆` enters only the new `a₆`, with coefficient `1`, so an offset in `a₆` alone is
preserved by any change of variables applied to both curves. The loop's substitutions depend on
`a₆` only through digits strictly below `v` before the exit, so both curves receive the same
substitutions. At `p = 2` every branch test of the loop is the vanishing of a linear coefficient,
which the offset does not touch, while at the exit the offset adds `1` to the constant term of the
tested polynomial; a record `⟨0, 1, 1, d⟩` over `𝔽_2` has a root exactly when `d = 0`, and both
exits report `4` if there is a root and `2` otherwise.

The hypothesis `v = m + 3` is sharp: for `v` above the exit index the two Tamagawa numbers are
equal, and for `v` below it the Kodaira symbol changes.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.FlipOffset`, with `Step7.FlipOffset.smul`,
  `Step7.FlipOffset.of_translateY` and `Step7.FlipOffset.of_translateX`: the relation "`W'` is `W`
  with `δ` added to `a₆`" and its preservation by each of the loop's two changes of variables.
* `WeierstrassCurve.TateAlgorithm.Step7.hasDoubleRoot_iff_c_eq_zero_two`: at `p = 2` both of the
  loop's branch tests are the vanishing of the linear coefficient.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_exists_kodairaSymbol_two_mul_le`: the loop
  entered at level `n` reports `Iₘ*` with `2 * n ≤ m + 3`.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_flip`: same Kodaira symbol, and Tamagawa
  number `4` for one curve exactly when `2` for the other.
-/

@[expose] public section

open CommRing Ideal

universe u

namespace WeierstrassCurve

open TateAlgorithm

/-! ### Adding `ϖ ^ k` to a coefficient moves one residue digit -/

section Digits

variable {R : Type u} [CommRing R] [NoZeroDivisors R] {ϖ : R}

/-- `div (ϖ ^ k) (ϖ ^ k) = 1`: the exact quotient of a nonzero element by itself. -/
theorem Flip.div_pow_self (hϖ : ϖ ≠ 0) (k : ℕ) : div ((ϖ : R) ^ k) (ϖ ^ k) = 1 :=
  mul_left_cancel₀ (pow_ne_zero k hϖ) <| by
    rw [mul_div (pow_ne_zero k hϖ) dvd_rfl, mul_one]

/-- **Adding `ϖ ^ k` bumps the `k`-th residue digit by one.** -/
theorem Flip.mod_div_add_pow (hϖ : ϖ ≠ 0) {x : R} {k : ℕ} (hx : ϖ ^ k ∣ x) :
    mod ϖ (div (x + ϖ ^ k) (ϖ ^ k)) = mod ϖ (div x (ϖ ^ k)) + 1 := by
  rw [div_add (pow_ne_zero k hϖ) hx dvd_rfl, Flip.div_pow_self hϖ, map_add, map_one]

/-- **Adding `ϖ ^ v` leaves every residue digit below `v` unchanged.** -/
theorem Flip.mod_div_add_pow_of_lt (hϖ : ϖ ≠ 0) {x : R} {k v : ℕ} (hx : ϖ ^ k ∣ x) (hkv : k < v) :
    mod ϖ (div (x + ϖ ^ v) (ϖ ^ k)) = mod ϖ (div x (ϖ ^ k)) :=
  mod_div_eq_of_pow_succ_dvd_sub hϖ (hx.add (pow_dvd_pow ϖ hkv.le)) hx <| by
    rw [add_sub_cancel_left]
    exact pow_dvd_pow ϖ hkv

end Digits

/-! ### The offset relation, and its invariance under the loop's changes of variables -/

namespace TateAlgorithm

namespace Step7

section Offset

variable {R : Type u} [CommRing R] {ϖ δ : R} [(span {ϖ}).IsMaximal] {n : ℕ}
  {W W' : WeierstrassCurve R}

variable (δ W W') in
/-- **`W'` is `W` with `δ` added to `a₆` and nothing else changed.** -/
structure FlipOffset : Prop where
  /-- The `a₁` coefficients agree. -/
  a₁ : W'.a₁ = W.a₁
  /-- The `a₂` coefficients agree. -/
  a₂ : W'.a₂ = W.a₂
  /-- The `a₃` coefficients agree. -/
  a₃ : W'.a₃ = W.a₃
  /-- The `a₄` coefficients agree. -/
  a₄ : W'.a₄ = W.a₄
  /-- The `a₆` coefficients differ by exactly `δ`. -/
  a₆ : W'.a₆ = W.a₆ + δ

/-- **A change of variables with `u = 1` preserves the offset relation, with the same `δ`.** In the
Weierstrass transformation law the old `a₆` enters only the new `a₆`, and there with coefficient
`1`; every other new coefficient is a function of `a₁, a₂, a₃, a₄` alone. -/
theorem FlipOffset.smul (h : FlipOffset δ W W') (r s t : R) :
    FlipOffset δ ((VariableChange.mk 1 r s t) • W) ((VariableChange.mk 1 r s t) • W') where
  a₁ := by simp [variableChange_a₁, h.a₁]
  a₂ := by simp [variableChange_a₂, h.a₁, h.a₂]
  a₃ := by simp [variableChange_a₃, h.a₁, h.a₃]
  a₄ := by simp [variableChange_a₄, h.a₁, h.a₂, h.a₃, h.a₄]
  a₆ := by
    simp only [variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, h.a₁, h.a₂, h.a₃,
      h.a₄, h.a₆]
    ring

/-- **The offset survives the loop's `Y`-translation** once the two curves present the same
level-`n` quadratic. -/
theorem FlipOffset.of_translateY (h : FlipOffset δ W W') (ht : tY ϖ W n = tY ϖ W' n) :
    FlipOffset δ (translateY ϖ W n) (translateY ϖ W' n) := by
  unfold translateY
  rw [ht]
  exact h.smul _ _ _

/-- **The offset survives the loop's `X`-translation** once the two curves present the same
level-`n` cubic. -/
theorem FlipOffset.of_translateX (h : FlipOffset δ W W') (hr : rX ϖ W n = rX ϖ W' n) :
    FlipOffset δ (translateX ϖ W n) (translateX ϖ W' n) := by
  unfold translateX
  rw [hr]
  exact h.smul _ _ _

end Offset

end Step7

end TateAlgorithm

/-! ### The branch tests and the exit test of the loop, at the even prime -/

variable {p : ℕ} [Fact p.Prime]

/-- **At `p = 2` a `HasDoubleRoot` test on a record with no cubic term and unit quadratic term is
the vanishing of the linear coefficient.** The test reads `c ^ 2 = 4 * d`; on the residue field of
`ℤ_2` one has `4 = 0` and `y ^ 2 = y`, so it is `c = 0`. In particular it does not involve `d`. -/
theorem TateAlgorithm.Step7.hasDoubleRoot_iff_c_eq_zero_two (hp2 : p = 2)
    {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})} (ha : P.a = 0) (hb : P.b = 1) :
    P.HasDoubleRoot ↔ P.c = 0 := by
  rw [Cubic.hasDoubleRoot_of_b_eq_one ha hb, residue_four_eq_zero_two hp2, zero_mul,
    residue_sq_eq_self_two hp2]

/-- **The level-`n` cubic of Step 7's loop is monic in its quadratic term at `p = 2`.** That
coefficient is the residue of `a₂ / ϖ`, which is nonzero because `¬ ϖ ^ 2 ∣ a₂`, and the residue
field of `ℤ_2` has only `0` and `1`. -/
theorem TateAlgorithm.Step7.cubic_b_eq_one_two (hp2 : p = 2) {V : WeierstrassCurve ℤ_[p]}
    (a : ℤ_[p]) (n : ℕ) (ha₂ : (p : ℤ_[p]) ∣ V.a₂) (ha₂' : ¬(p : ℤ_[p]) ^ 2 ∣ V.a₂) :
    (cubic (p : ℤ_[p]) V a n).b = 1 := by
  refine (Step2.residue_eq_zero_or_one_of_eq_two hp2 _).resolve_left fun h => ha₂' ?_
  rw [show (cubic (p : ℤ_[p]) V a n).b = mod (p : ℤ_[p]) (div V.a₂ (p : ℤ_[p])) from rfl,
    mod_eq_zero] at h
  exact sq_dvd.mpr ⟨ha₂, h⟩

open scoped Classical in
/-- **The exit test at `p = 2`.** A record `⟨0, 1, 1, d⟩` over the residue field of `ℤ_2` has a
nonempty root `Finset` exactly when `d = 0`: squaring is the identity there, so `x ^ 2 + x = 0` for
every `x` and the polynomial takes the single value `d`. -/
theorem Flip.card_roots_pos_iff_d_two (hp2 : p = 2) {P : Cubic (ℤ_[p] ⧸ span {(p : ℤ_[p])})}
    (ha : P.a = 0) (hb : P.b = 1) (hc : P.c = 1) : 0 < P.roots.toFinset.card ↔ P.d = 0 := by
  obtain ⟨a, b, c, d⟩ := P
  obtain rfl : a = 0 := ha
  obtain rfl : b = 1 := hb
  obtain rfl : c = 1 := hc
  exact card_roots_toFinset_pos_iff_cubic_two hp2 d

/-- **Bumping the exit test's constant digit by one exchanges the two Tamagawa values.** With
`d = 0` the root count is positive and the answer is `4`, with `d = 1` it is zero and the answer is
`2`, and over `𝔽_2` the two digits are exchanged by `d ↦ d + 1`. -/
theorem Flip.exit_flip_two (hp2 : p = 2) (d : ℤ_[p] ⧸ span {(p : ℤ_[p])})
    [Decidable (d = 0)] [Decidable (d + 1 = 0)] :
    ((if d + 1 = 0 then (4 : ℕ) else 2) = 4 ↔ (if d = 0 then (4 : ℕ) else 2) = 2) := by
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  have key : d + 1 = 0 ↔ ¬(d = 0) := by
    rcases Step2.residue_eq_zero_or_one_of_eq_two hp2 d with h | h
    · rw [h, zero_add]
      exact ⟨fun hc => absurd hc one_ne_zero, fun hc => absurd rfl hc⟩
    · rw [h]
      exact ⟨fun _ hc => one_ne_zero hc, fun _ => by linear_combination h2⟩
  by_cases hd : d = 0
  · rw [ite_eq_right fun hc => key.mp hc hd, ite_eq_left hd]
    norm_num
  · rw [ite_eq_left (key.mpr hd), ite_eq_right hd]
    norm_num

namespace TateAlgorithm

variable {W W' : WeierstrassCurve ℤ_[p]}

/-! ### The reported index is bounded below by the level -/

/-- **The loop entered at level `n` reports `Iₘ*` with `2 * n ≤ m + 3`.** The odd exit at level `k`
reports `I!(2k−3)` and the even exit `I!(2k−2)`, so the reported index is at least `2k − 3` at the
level `k ≥ n` at which the loop exits. -/
theorem Step7.subprocedure_exists_kodairaSymbol_two_mul_le (hϖ : (p : ℤ_[p]) ≠ 0) (hΔ : W.Δ ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬(p : ℤ_[p]) ^ 2 ∣ W.a₂) :
    ∃ m, (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = KodairaSymbol.I! m ∧
      2 * n ≤ m + 3 := by
  fun_induction Step7.subprocedure with
  | case1 =>
    rename_i ih
    exact ih.imp fun m h => ⟨h.1, by omega⟩
  | case2 => exact ⟨_, rfl, by omega⟩
  | case3 => exact ⟨_, rfl, by omega⟩

/-! ### The flip -/

open scoped Classical in
/-- **One additive offset in `a₆`, at the index the exit test reads, exchanges Tamagawa `2` with
Tamagawa `4` and leaves the Kodaira symbol alone.**

`W'` is `W` with `ϖ ^ v` added to `a₆` and nothing else changed, both curves carry the valuation
data of the loop invariant at level `n`, and `v = m + 3` where `Iₘ*` is the symbol the loop
reports on `W`, so that the offset sits exactly at the `a₆` index the exit test consults. Then the
loop reports `Iₘ*` on `W'` too, and the two Tamagawa numbers are opposite. This version carries the
extra hypothesis `2 * n ≤ v`. -/
theorem Step7.subprocedure_flip_of_two_mul_le (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {v m : ℕ} {W W' : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (hW' : HasValuation (p : ℤ_[p]) W' ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬(p : ℤ_[p]) ^ 2 ∣ W.a₂) (ha₂' : ¬(p : ℤ_[p]) ^ 2 ∣ W'.a₂)
    (hoff : Step7.FlipOffset ((p : ℤ_[p]) ^ v) W W')
    (hm : (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = KodairaSymbol.I! m)
    (hv : v = m + 3) (hvn : 2 * n ≤ v) :
    (Step7.subprocedure hϖ hΔ' hn hW' ha₂').kodairaSymbol = KodairaSymbol.I! m ∧
      ((Step7.subprocedure hϖ hΔ' hn hW' ha₂').tamagawaNumber = 4 ↔
        (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 2) := by
  have h2 := Step2.residue_two_eq_zero_of_eq_two (p := p) hp2
  have ha₆ : (p : ℤ_[p]) ^ (2 * n) ∣ W.a₆ := hW.a₆
  have hqc : (quadratic (p : ℤ_[p]) W' n).c = (quadratic (p : ℤ_[p]) W n).c := by
    simp only [quadratic, hoff.a₃]
  have hYiff : (quadratic (p : ℤ_[p]) W' n).HasDoubleRoot
      ↔ (quadratic (p : ℤ_[p]) W n).HasDoubleRoot := by
    rw [Step7.hasDoubleRoot_iff_c_eq_zero_two hp2 rfl rfl,
      Step7.hasDoubleRoot_iff_c_eq_zero_two hp2 rfl rfl, hqc]
  by_cases hY : (quadratic (p : ℤ_[p]) W n).HasDoubleRoot
  · have hY' : (quadratic (p : ℤ_[p]) W' n).HasDoubleRoot := hYiff.mpr hY
    have hqeq : 2 * n + 1 ≤ v →
        quadratic (p : ℤ_[p]) W n = quadratic (p : ℤ_[p]) W' n := fun hle => by
      simp only [quadratic, hoff.a₃, hoff.a₆]
      rw [Flip.mod_div_add_pow_of_lt hϖ ha₆ (by omega)]
    have hvY := Step7.hasValuation_translateY hn hϖ hW hY
    have hvY' := Step7.hasValuation_translateY hn hϖ hW' hY'
    have ha₂Y : ¬(p : ℤ_[p]) ^ 2 ∣ (Step7.translateY (p : ℤ_[p]) W n).a₂ :=
      Step7.not_dvd_translateY_a₂ n ha₂
    have ha₂Y' : ¬(p : ℤ_[p]) ^ 2 ∣ (Step7.translateY (p : ℤ_[p]) W' n).a₂ :=
      Step7.not_dvd_translateY_a₂ n ha₂'
    have hdY : (p : ℤ_[p]) ∣ (Step7.translateY (p : ℤ_[p]) W n).a₂ := by
      have h := hvY.a₂; rwa [pow_one] at h
    have hdY' : (p : ℤ_[p]) ∣ (Step7.translateY (p : ℤ_[p]) W' n).a₂ := by
      have h := hvY'.a₂; rwa [pow_one] at h
    have ha₆Y : (p : ℤ_[p]) ^ (2 * n + 1) ∣ (Step7.translateY (p : ℤ_[p]) W n).a₆ := hvY.a₆
    have hbY := Step7.cubic_b_eq_one_two hp2 (V := Step7.translateY (p : ℤ_[p]) W n) 0 n hdY ha₂Y
    have hbY' := Step7.cubic_b_eq_one_two hp2 (V := Step7.translateY (p : ℤ_[p]) W' n) 0 n hdY'
      ha₂Y'
    have hoffY : 2 * n + 1 ≤ v → Step7.FlipOffset ((p : ℤ_[p]) ^ v)
        (Step7.translateY (p : ℤ_[p]) W n) (Step7.translateY (p : ℤ_[p]) W' n) := fun hle =>
      hoff.of_translateY <| Step7.tY_eq_of_quadratic_eq (hqeq hle)
    have hXc : 2 * n + 1 ≤ v →
        (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) 0 n).c
          = (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) 0 n).c := fun hle => by
      simp only [cubic, (hoffY hle).a₄]
    have hXiff : 2 * n + 1 ≤ v →
        ((cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) 0 n).HasDoubleRoot
          ↔ (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) 0 n).HasDoubleRoot) := fun hle =>
      by
        rw [Step7.hasDoubleRoot_iff_c_eq_zero_two hp2 rfl hbY',
          Step7.hasDoubleRoot_iff_c_eq_zero_two hp2 rfl hbY, hXc hle]
    by_cases hX : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) 0 n).HasDoubleRoot
    · have ha₂X : ¬(p : ℤ_[p]) ^ 2 ∣
          (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) n).a₂ :=
        Step7.not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y
      have hvX := Step7.hasValuation_translateX hn hϖ hvY ha₂Y hX
      have hΔX : (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) n).Δ ≠ 0 := by
        rw [Step7.translateX_Δ, Step7.translateY_Δ]; exact hΔ
      have hrec := Step7.subprocedure_eq_subprocedure hϖ hΔ hn hW ha₂ hY hX hΔX
        (Nat.le_succ_of_le hn) hvX ha₂X
      rw [hrec] at hm
      obtain ⟨m', hm', hle'⟩ := Step7.subprocedure_exists_kodairaSymbol_two_mul_le hϖ hΔX
        (Nat.le_succ_of_le hn) hvX ha₂X
      obtain rfl : m' = m := KodairaSymbol.I!.inj (hm'.symm.trans hm)
      have hv2 : 2 * n + 2 ≤ v := by omega
      have hX' : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) 0 n).HasDoubleRoot :=
        (hXiff (by omega)).mpr hX
      have ha₂X' : ¬(p : ℤ_[p]) ^ 2 ∣
          (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) n).a₂ :=
        Step7.not_dvd_translateX_a₂ hn hϖ hvY'.a₂ ha₂Y'
      have hvX' := Step7.hasValuation_translateX hn hϖ hvY' ha₂Y' hX'
      have hΔX' : (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) n).Δ ≠ 0 := by
        rw [Step7.translateX_Δ, Step7.translateY_Δ]; exact hΔ'
      have hoffX : Step7.FlipOffset ((p : ℤ_[p]) ^ v)
          (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) n)
          (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) n) := by
        refine (hoffY (by omega)).of_translateX (Step7.rX_eq_of_cubic_eq ?_)
        simp only [cubic, (hoffY (by omega)).a₂, (hoffY (by omega)).a₄, (hoffY (by omega)).a₆]
        rw [Flip.mod_div_add_pow_of_lt hϖ ha₆Y (by omega)]
      rw [hrec, Step7.subprocedure_eq_subprocedure hϖ hΔ' hn hW' ha₂' hY' hX' hΔX'
        (Nat.le_succ_of_le hn) hvX' ha₂X']
      exact Step7.subprocedure_flip_of_two_mul_le hp2 hϖ hΔX hΔX' (Nat.le_succ_of_le hn)
        hvX hvX' ha₂X ha₂X' hoffX hm hv (by omega)
    · rw [Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX] at hm
      obtain rfl : 2 * n - 2 = m := KodairaSymbol.I!.inj hm
      have hv1 : v = 2 * n + 1 := by omega
      have hX' : ¬(cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) 0 n).HasDoubleRoot :=
        fun h => hX ((hXiff (by omega)).mp h)
      have hc : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) 0 n).c = 1 :=
        (Step2.residue_eq_zero_or_one_of_eq_two hp2 _).resolve_left fun h =>
          hX ((Step7.hasDoubleRoot_iff_c_eq_zero_two hp2 rfl hbY).mpr h)
      have hc' : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) 0 n).c = 1 := by
        rw [hXc (by omega), hc]
      have hd : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W' n) 0 n).d
          = (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p]) W n) 0 n).d + 1 := by
        simp only [cubic, (hoffY (by omega)).a₆]
        rw [show v = 2 * n + 1 from hv1, Flip.mod_div_add_pow hϖ ha₆Y]
      rw [Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX,
        Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ' hn hW' ha₂' hY' hX']
      refine ⟨rfl, ?_⟩
      rw [if_congr (Flip.card_roots_pos_iff_d_two hp2 rfl hbY' hc') rfl rfl,
        if_congr (Flip.card_roots_pos_iff_d_two hp2 rfl hbY hc) rfl rfl, hd]
      exact Flip.exit_flip_two hp2 _
  · rw [Step7.subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY] at hm
    obtain rfl : 2 * n - 3 = m := KodairaSymbol.I!.inj hm
    have hv0 : v = 2 * n := by omega
    have hc : (quadratic (p : ℤ_[p]) W n).c = 1 :=
      (Step2.residue_eq_zero_or_one_of_eq_two hp2 _).resolve_left fun h =>
        hY ((Step7.hasDoubleRoot_iff_c_eq_zero_two hp2 rfl rfl).mpr h)
    have hc' : (quadratic (p : ℤ_[p]) W' n).c = 1 := by rw [hqc, hc]
    have hd : (quadratic (p : ℤ_[p]) W' n).d = (quadratic (p : ℤ_[p]) W n).d + 1 := by
      simp only [quadratic, hoff.a₆]
      rw [show v = 2 * n from hv0, Flip.mod_div_add_pow hϖ ha₆]
      linear_combination -h2
    rw [Step7.subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY,
      Step7.subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ' hn hW' ha₂' fun h => hY (hYiff.mp h)]
    refine ⟨rfl, ?_⟩
    rw [if_congr (Flip.card_roots_pos_iff_d_two hp2 rfl rfl hc') rfl rfl,
      if_congr (Flip.card_roots_pos_iff_d_two hp2 rfl rfl hc) rfl rfl, hd]
    exact Flip.exit_flip_two hp2 _
termination_by v - n
decreasing_by omega

/-- **The flip.** At `p = 2`, if `W'` is `W` with `ϖ ^ v` added to `a₆` and nothing else changed,
both carry the loop invariant at level `n`, and the loop reports `Iₘ*` on `W` with `v = m + 3`,
then it reports `Iₘ*` on `W'` too, and the Tamagawa number on `W'` is `4` exactly when the one on
`W` is `2`. -/
theorem Step7.subprocedure_flip (hp2 : p = 2) (hϖ : (p : ℤ_[p]) ≠ 0)
    {v m : ℕ} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}
    (hW : HasValuation (p : ℤ_[p]) W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (hW' : HasValuation (p : ℤ_[p]) W' ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬(p : ℤ_[p]) ^ 2 ∣ W.a₂) (ha₂' : ¬(p : ℤ_[p]) ^ 2 ∣ W'.a₂)
    (hoff : Step7.FlipOffset ((p : ℤ_[p]) ^ v) W W')
    (hm : (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol = KodairaSymbol.I! m)
    (hv : v = m + 3) :
    (Step7.subprocedure hϖ hΔ' hn hW' ha₂').kodairaSymbol = KodairaSymbol.I! m ∧
      ((Step7.subprocedure hϖ hΔ' hn hW' ha₂').tamagawaNumber = 4 ↔
        (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber = 2) := by
  obtain ⟨m', hm', hle⟩ := Step7.subprocedure_exists_kodairaSymbol_two_mul_le hϖ hΔ hn hW ha₂
  obtain rfl : m' = m := KodairaSymbol.I!.inj (hm'.symm.trans hm)
  exact Step7.subprocedure_flip_of_two_mul_le hp2 hϖ hΔ hΔ' hn hW hW' ha₂ ha₂' hoff hm hv
    (by omega)

end TateAlgorithm

end WeierstrassCurve

end
