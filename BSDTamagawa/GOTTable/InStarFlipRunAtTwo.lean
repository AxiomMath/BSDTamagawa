/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarFlipAtTwo

/-!
# The `a₆` offset that exchanges Tamagawa `2` with `4` survives Steps 1–7 of Tate's algorithm

At `p = 2`, two curves entering Step 7's loop that differ only by `ϖ ^ v` in `a₆`, with `v = m + 3`
where `Iₘ*` is the reported symbol, receive the same Kodaira symbol and exchanged Tamagawa numbers
`2` and `4`. This file transfers that statement to `TateAlgorithm.run` on the input curves, in
particular to `ofShortNF a₄ a₆` and `ofShortNF a₄ (a₆ + ϖ ^ v)`.

Every change of variables Tate's algorithm performs before Step 8 has `u = 1`, and such a change of
variables preserves the offset relation with the same offset. It remains that both curves receive
the same substitution at each step: Step 2's substitution depends only on the reduction modulo `ϖ`,
Step 6's on residues that an offset divisible by `ϖ ^ 3` does not reach, and Step 7's outer
translation on `cubic ϖ · 1 1`, which an offset divisible by `ϖ ^ 4` does not reach. The branch
tests of Steps 1–6 agree because the offset is a congruence to depth `4`. The depth `4 ≤ v` is not
an extra hypothesis: entry into Step 7's loop at level `2` forces `4 ≤ m + 3 = v`.

## Main results

* `WeierstrassCurve.Flip.congrDepth_of_offset`, `Flip.mod_div_add_of_pow_succ_dvd` and
  `Flip.cubic_eq_of_offset`: the offset relation read as a congruence, the digit statement for a
  general offset, and equality of the cubics `cubic ϖ · a n` of the two curves.
* `WeierstrassCurve.TateAlgorithm.Step7.FlipOffset.of_step2_translate`,
  `…of_step6_translate` and `…of_step7_translate`: the offset relation survives the substitutions
  of Steps 2, 6 and 7.
* `WeierstrassCurve.FlipRun.step5_run_eq_ok_of_offset`: Steps 1–5 traverse on the second curve as
  soon as they traverse on the first, and hand on the Step-2 translate of the second.
* `WeierstrassCurve.FlipRun.run_flip`: given the Step 1–6 entry data for the first curve,
  `TateAlgorithm.run` reports the same Kodaira symbol on both and exchanges `4` with `2`.
* `WeierstrassCurve.FlipRun.run_flip_ofShortNF`: the same for the short models
  `ofShortNF a₄ a₆` and `ofShortNF a₄ (a₆ + ϖ ^ v)`.
-/

@[expose] public section

open CommRing Ideal

universe u

namespace WeierstrassCurve

open TateAlgorithm

/-! ### The offset relation as a congruence, and the residues it cannot reach -/

section General

variable {R : Type u} [CommRing R] {ϖ δ : R} {W W' : WeierstrassCurve R}

/-- **An offset divisible by `ϖ ^ n` is a congruence to depth `n`.** Four of the five coefficients
agree and the fifth differs by `δ`. -/
theorem Flip.congrDepth_of_offset [(span {ϖ}).IsMaximal] {n : ℕ}
    (h : Step7.FlipOffset δ W W') (hδ : ϖ ^ n ∣ δ) : CongrDepth ϖ n W W' := by
  have hzero : ∀ x : R, ϖ ^ n ∣ x - x := fun x => by rw [sub_self]; exact dvd_zero _
  rw [congrDepth_iff_sub_mem]
  refine ⟨mem_span_singleton.mpr ?_, mem_span_singleton.mpr ?_, mem_span_singleton.mpr ?_,
    mem_span_singleton.mpr ?_, mem_span_singleton.mpr ?_⟩
  · rw [h.a₁]; exact hzero _
  · rw [h.a₂]; exact hzero _
  · rw [h.a₃]; exact hzero _
  · rw [h.a₄]; exact hzero _
  · rw [h.a₆, show W.a₆ - (W.a₆ + δ) = -δ from by ring]
    exact dvd_neg.mpr hδ

variable [NoZeroDivisors R]

/-- **A residue digit at index `k` does not see an offset divisible by `ϖ ^ (k + 1)`.** -/
theorem Flip.mod_div_add_of_pow_succ_dvd (hϖ : ϖ ≠ 0) {x : R} {k : ℕ} (hx : ϖ ^ k ∣ x)
    (hδ : ϖ ^ (k + 1) ∣ δ) : mod ϖ (div (x + δ) (ϖ ^ k)) = mod ϖ (div x (ϖ ^ k)) :=
  mod_div_eq_of_pow_succ_dvd_sub hϖ (hx.add ((pow_dvd_pow ϖ (Nat.le_succ k)).trans hδ)) hx <| by
    rw [add_sub_cancel_left]
    exact hδ

/-- **Two curves related by a deep enough offset present the same cubic.** `cubic ϖ · a n` reads
`a₂ / ϖ`, `a₄ / ϖ ^ (n + 1)` and `a₆ / ϖ ^ (2 * n + 1)`; the relation leaves the first two equal,
and the third does not see an offset divisible by `ϖ ^ (2 * n + 2)`. -/
theorem Flip.cubic_eq_of_offset (hϖ : ϖ ≠ 0) (h : Step7.FlipOffset δ W W') (a : R) (n : ℕ)
    (ha₆ : ϖ ^ (2 * n + 1) ∣ W.a₆) (hδ : ϖ ^ (2 * n + 2) ∣ δ) :
    cubic ϖ W a n = cubic ϖ W' a n := by
  simp only [cubic, h.a₂, h.a₄, h.a₆]
  rw [Flip.mod_div_add_of_pow_succ_dvd hϖ ha₆ hδ]

end General

/-! ### The offset survives the substitutions of Steps 2, 6 and 7 -/

namespace TateAlgorithm

namespace Step7

variable {R : Type u} [CommRing R] {ϖ δ : R} [(span {ϖ}).IsMaximal]
  {W W' : WeierstrassCurve R}

/-- **Step 2's substitution preserves the offset once `ϖ ∣ δ`.** Step 2 translates the singular
point of the mod-`ϖ` reduction to the origin, and that substitution is a function of the reduction
alone. An offset divisible by `ϖ` leaves the reduction unchanged, so the two curves receive the
same substitution `⟨1, r, 0, t⟩`. -/
theorem FlipOffset.of_step2_translate [PerfectField (R ⧸ span {ϖ})] (h : FlipOffset δ W W')
    (hδ : ϖ ∣ δ) (hΔ : ϖ ∣ W.Δ) (hΔ' : ϖ ∣ W'.Δ) :
    FlipOffset δ (Step2.translate ϖ W) (Step2.translate ϖ W') := by
  have hmap : W.map (mod ϖ) = W'.map (mod ϖ) :=
    (congrDepth_one_iff_map_mod_eq ϖ W W').mp
      (Flip.congrDepth_of_offset h (by rwa [pow_one]))
  rw [Step2.translate_eq_smul ϖ hΔ, Step2.translate_eq_smul ϖ hΔ',
    Step2.translateVariableChange_eq_of_map_mod_eq ϖ hmap hΔ hΔ']
  exact h.smul _ _ _

variable [NoZeroDivisors R]

/-- **Step 6's substitution preserves the offset once `ϖ ^ 3 ∣ δ`.** Step 6 applies
`⟨1, 0, s, ϖ t⟩`, where `Step6.s` is a function of `mod ϖ a₁` and `mod ϖ a₂`, which the relation
leaves equal, and `Step6.t` of `mod ϖ (a₃ / ϖ)` and `mod ϖ (a₆ / ϖ ^ 2)`. Only the last of these
can feel the offset, and it cannot once the offset is divisible by `ϖ ^ 3`. -/
theorem FlipOffset.of_step6_translate (hϖ : ϖ ≠ 0) (h : FlipOffset δ W W')
    (ha₆ : ϖ ^ 2 ∣ W.a₆) (hδ : ϖ ^ 3 ∣ δ) :
    FlipOffset δ (Step6.translate ϖ W) (Step6.translate ϖ W') := by
  have hs : Step6.s ϖ W = Step6.s ϖ W' :=
    Step6.s_eq_of_mod_eq ϖ (by rw [h.a₁]) (by rw [h.a₂])
  have ht : Step6.t ϖ W = Step6.t ϖ W' :=
    Step6.t_eq_of_mod_div_eq ϖ (by rw [h.a₃]) <| by
      rw [h.a₆, Flip.mod_div_add_of_pow_succ_dvd hϖ ha₆ hδ]
  unfold Step6.translate
  rw [hs, ht]
  exact h.smul _ _ _

/-- **Step 7's outer translate preserves the offset once `ϖ ^ 4 ∣ δ`.** The substitution is
`⟨1, ϖ r, 0, 0⟩` with `Step7.r` a function of `cubic ϖ · 1 1` alone, whose deepest coefficient is
`mod ϖ (a₆ / ϖ ^ 3)`. -/
theorem FlipOffset.of_step7_translate (hϖ : ϖ ≠ 0) (h : FlipOffset δ W W')
    (ha₆ : ϖ ^ 3 ∣ W.a₆) (hδ : ϖ ^ 4 ∣ δ) :
    FlipOffset δ (Step7.translate ϖ W) (Step7.translate ϖ W') := by
  have hr : Step7.r ϖ W = Step7.r ϖ W' :=
    Step7.r_eq_of_cubic_eq (Flip.cubic_eq_of_offset hϖ h 1 1
      (show ϖ ^ (2 * 1 + 1) ∣ W.a₆ from ha₆) (show ϖ ^ (2 * 1 + 2) ∣ δ from hδ))
  unfold Step7.translate
  rw [hr]
  exact h.smul _ _ _

end Step7

end TateAlgorithm

/-! ### Steps 1–5 traverse on the offset curve as soon as they traverse on the original -/

namespace FlipRun

variable {p : ℕ} [Fact p.Prime] {W W' c : WeierstrassCurve ℤ_[p]}

/-- **The curve Steps 1–5 hand on is the Step-2 translate of the input.** Steps 1, 3, 4 and 5 pass
the curve through unchanged, so the only substitution performed before Step 6 is Step 2's. -/
theorem step5_run_ok_eq_translate (h : Step5.run (p : ℤ_[p]) W = Except.ok c) :
    c = Step2.translate (p : ℤ_[p]) W := by
  rw [Step5.run.eq_def] at h
  obtain ⟨c₄, h₄, h₅⟩ := Except.bind_eq_ok_iff.mp h
  split_ifs at h₅
  obtain rfl := Except.ok.inj h₅
  rw [Step4.run.eq_def] at h₄
  obtain ⟨c₃, h₃, h₄'⟩ := Except.bind_eq_ok_iff.mp h₄
  split_ifs at h₄'
  obtain rfl := Except.ok.inj h₄'
  rw [Step3.run.eq_def] at h₃
  obtain ⟨c₂, h₂, h₃'⟩ := Except.bind_eq_ok_iff.mp h₃
  split_ifs at h₃'
  obtain rfl := Except.ok.inj h₃'
  rw [Step2.run.eq_def] at h₂
  obtain ⟨c₁, h₁, h₂'⟩ := Except.bind_eq_ok_iff.mp h₂
  split_ifs at h₂'
  obtain rfl := Step1.run_weierstrassCurve h₁
  exact (Except.ok.inj h₂').symm

/-- **The five tests of Steps 1–5, run forwards from the branch data.** Steps 1–5 test
`ϖ ∣ Δ` on the input and then `ϖ ∣ b₂`, `ϖ ^ 2 ∣ a₆`, `ϖ ^ 3 ∣ b₈`, `ϖ ^ 3 ∣ b₆` on the Step-2
translate; nothing else is inspected and no further substitution is made. -/
theorem step5_run_eq_ok_of_tests (hΔ : (p : ℤ_[p]) ∣ W.Δ)
    (hb₂ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂)
    (ha₆ : (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) W).a₆)
    (hb₈ : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) W).b₈)
    (hb₆ : (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) W).b₆) :
    Step5.run (p : ℤ_[p]) W = Except.ok (Step2.translate (p : ℤ_[p]) W) := by
  classical
  have h₂ : Step2.run (p : ℤ_[p]) W = Except.ok (Step2.translate (p : ℤ_[p]) W) := by
    rw [Step2.run_eq_of_dvd_Δ (p : ℤ_[p]) hΔ]
    exact ite_eq_left hb₂
  have h₃ : Step3.run (p : ℤ_[p]) W = Except.ok (Step2.translate (p : ℤ_[p]) W) := by
    rw [Step3.run.eq_def, h₂]
    simp only [except_ok_bind]
    exact ite_eq_left ha₆
  have h₄ : Step4.run (p : ℤ_[p]) W = Except.ok (Step2.translate (p : ℤ_[p]) W) := by
    rw [Step4.run.eq_def, h₃]
    simp only [except_ok_bind]
    exact ite_eq_left hb₈
  rw [Step5.run.eq_def, h₄]
  simp only [except_ok_bind]
  exact ite_eq_left hb₆

/-- **Steps 1–5 traverse on the offset curve too, and hand on its Step-2 translate.** Every test of
Steps 1–5 is a divisibility of a coefficient or of a derived quantity of the input or of its Step-2
translate, and an offset divisible by `ϖ ^ 4` is a congruence to depth `4`. -/
theorem step5_run_eq_ok_of_offset {δ : ℤ_[p]} (hoff : Step7.FlipOffset δ W W')
    (hδ : (p : ℤ_[p]) ^ 4 ∣ δ) (h5 : Step5.run (p : ℤ_[p]) W = Except.ok c) :
    Step5.run (p : ℤ_[p]) W' = Except.ok (Step2.translate (p : ℤ_[p]) W') := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain rfl := step5_run_ok_eq_translate h5
  have hval := Step5.run_hasValuation hϖ h5
  have hΔ : (p : ℤ_[p]) ∣ W.Δ := by
    rw [← Step5.run_Δ h5]
    exact (dvd_pow_self _ (by norm_num : 5 ≠ 0)).trans hval.Δ
  have hδ1 : (p : ℤ_[p]) ∣ δ := (dvd_pow_self _ (by norm_num : 4 ≠ 0)).trans hδ
  have hcong1 : CongrDepth (p : ℤ_[p]) 1 W W' :=
    Flip.congrDepth_of_offset hoff (by rwa [pow_one])
  have hΔ' : (p : ℤ_[p]) ∣ W'.Δ := hcong1.dvd_Δ_iff.mp hΔ
  have hoff2 : Step7.FlipOffset δ (Step2.translate (p : ℤ_[p]) W)
      (Step2.translate (p : ℤ_[p]) W') := hoff.of_step2_translate hδ1 hΔ hΔ'
  have hcong : CongrDepth (p : ℤ_[p]) 4 (Step2.translate (p : ℤ_[p]) W)
      (Step2.translate (p : ℤ_[p]) W') := Flip.congrDepth_of_offset hoff2 hδ
  refine step5_run_eq_ok_of_tests hΔ' ?_ ?_ ?_ ?_
  · have hb₂ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂ := by
      have h := hval.b₂; rwa [pow_one] at h
    exact (hcong.mono (by norm_num)).dvd_b₂_iff.mp hb₂
  · exact (dvd_iff_dvd_of_dvd_sub (hcong.pow_dvd_a₆_sub (by norm_num))).mp hval.a₆
  · exact (hcong.pow_dvd_b₈_iff (by norm_num)).mp hval.b₈
  · exact (hcong.pow_dvd_b₆_iff (by norm_num)).mp hval.b₆

end FlipRun

/-! ### The flip at `TateAlgorithm.run` -/

variable {p : ℕ} [Fact p.Prime]

namespace FlipRun

open scoped Classical in
/-- **The flip, at `TateAlgorithm.run`.**

`W'` is `W` with `ϖ ^ v` added to `a₆` and nothing else changed; on `W` Steps 1–5 traverse and
Step 6's cubic has a double but not a triple root, so Step 7 enters its subprocedure at level `2`;
and `v = m + 3` where `Iₘ*` is the symbol `run` reports on `W`. Then `run` reports `Iₘ*` on `W'`
too, and the two Tamagawa numbers are exchanged. No separate depth hypothesis on `v` is needed:
entry at level `2` forces `4 ≤ m + 3 = v`. -/
theorem run_flip (hp2 : p = 2) {v m : ℕ} {W W' V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (hoff : Step7.FlipOffset ((p : ℤ_[p]) ^ v) W W')
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hm : (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol
      = KodairaSymbol.I! m) (hv : v = m + 3) :
    (TateAlgorithm.run (W := W') PadicInt.uniformizer_ne_zero hΔ').kodairaSymbol
        = KodairaSymbol.I! m ∧
      ((TateAlgorithm.run (W := W') PadicInt.uniformizer_ne_zero hΔ').tamagawaNumber = 4 ↔
        (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2) := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain rfl := step5_run_ok_eq_translate h5
  have hval5 := Step5.run_hasValuation hϖ h5
  have h6 : Step6.run (p : ℤ_[p]) W
      = Except.ok (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)) := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_left hdbl
  have hval6 := Step6.run_hasValuation hϖ h6
  have hΔc : (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W))).Δ ≠ 0 := by
    rw [Step7.translate_Δ, Step6.run_Δ h6]; exact hΔ
  have hvc := Step7.hasValuation_translate hϖ hval6 hdbl hntr
  have ha₂c := Step7.not_dvd_translate_a₂ hϖ hval6.a₂ hdbl hntr
  have hrun : TateAlgorithm.run (W := W) hϖ hΔ = Step7.subprocedure hϖ hΔc le_rfl hvc ha₂c :=
    run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ
      (Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h6 hntr hΔc hvc ha₂c))
  rw [hrun] at hm
  obtain ⟨m', hm', hle⟩ :=
    Step7.subprocedure_exists_kodairaSymbol_two_mul_le hϖ hΔc le_rfl hvc ha₂c
  obtain rfl : m' = m := KodairaSymbol.I!.inj (hm'.symm.trans hm)
  have hδ4 : (p : ℤ_[p]) ^ 4 ∣ (p : ℤ_[p]) ^ v := pow_dvd_pow _ (by omega)
  have h5' : Step5.run (p : ℤ_[p]) W' = Except.ok (Step2.translate (p : ℤ_[p]) W') :=
    step5_run_eq_ok_of_offset hoff hδ4 h5
  have hval5' := Step5.run_hasValuation hϖ h5'
  have hΔd : (p : ℤ_[p]) ∣ W.Δ := by
    rw [← Step5.run_Δ h5]
    exact (dvd_pow_self _ (by norm_num : 5 ≠ 0)).trans hval5.Δ
  have hΔd' : (p : ℤ_[p]) ∣ W'.Δ := by
    rw [← Step5.run_Δ h5']
    exact (dvd_pow_self _ (by norm_num : 5 ≠ 0)).trans hval5'.Δ
  have hoff2 : Step7.FlipOffset ((p : ℤ_[p]) ^ v) (Step2.translate (p : ℤ_[p]) W)
      (Step2.translate (p : ℤ_[p]) W') :=
    hoff.of_step2_translate ((dvd_pow_self _ (by norm_num : 4 ≠ 0)).trans hδ4) hΔd hΔd'
  have hoff6 : Step7.FlipOffset ((p : ℤ_[p]) ^ v)
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W))
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W')) :=
    hoff2.of_step6_translate hϖ hval5.a₆ ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans hδ4)
  have hcub : cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)) 1 1
      = cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W')) 1 1 :=
    Flip.cubic_eq_of_offset hϖ hoff6 1 1 (show (p : ℤ_[p]) ^ (2 * 1 + 1) ∣ _ from hval6.a₆)
      (show (p : ℤ_[p]) ^ (2 * 1 + 2) ∣ _ from hδ4)
  have hdbl' : (cubic (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W')) 1 1).HasDoubleRoot :=
    hcub ▸ hdbl
  have hntr' : ¬ (cubic (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W')) 1 1).HasTripleRoot :=
    hcub ▸ hntr
  have h6' : Step6.run (p : ℤ_[p]) W'
      = Except.ok (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W')) := by
    rw [Step6.run.eq_def, h5']
    simp only [except_ok_bind]
    exact ite_eq_left hdbl'
  have hval6' := Step6.run_hasValuation hϖ h6'
  have hoff7 : Step7.FlipOffset ((p : ℤ_[p]) ^ v)
      (Step7.translate (p : ℤ_[p])
        (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W)))
      (Step7.translate (p : ℤ_[p])
        (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W'))) :=
    hoff6.of_step7_translate hϖ hval6.a₆ hδ4
  have hΔc' : (Step7.translate (p : ℤ_[p])
      (Step6.translate (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) W'))).Δ ≠ 0 := by
    rw [Step7.translate_Δ, Step6.run_Δ h6']; exact hΔ'
  have hvc' := Step7.hasValuation_translate hϖ hval6' hdbl' hntr'
  have ha₂c' := Step7.not_dvd_translate_a₂ hϖ hval6'.a₂ hdbl' hntr'
  have hrun' : TateAlgorithm.run (W := W') hϖ hΔ' = Step7.subprocedure hϖ hΔc' le_rfl hvc' ha₂c' :=
    run_eq_of_step11_error hϖ hΔ' (step11_error_of_step7 hΔ'
      (Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ' h6' hntr' hΔc' hvc' ha₂c'))
  rw [hrun, hrun']
  exact Step7.subprocedure_flip hp2 hϖ hΔc hΔc' le_rfl hvc hvc' ha₂c ha₂c' hoff7 hm hv

/-- **The flip on short models.** At `p = 2`, `ofShortNF a₄ (a₆ + ϖ ^ v)` is `ofShortNF a₄ a₆`
with `ϖ ^ v` added to `a₆`. If on `ofShortNF a₄ a₆` Steps 1–5 traverse and Step 6's cubic has a
double but not a triple root, and `v = m + 3` where `Iₘ*` is the symbol `run` reports, then `run`
reports `Iₘ*` on both short models and exchanges Tamagawa `4` with `2`. -/
theorem run_flip_ofShortNF (hp2 : p = 2) {v m : ℕ} {a₄ a₆ : ℤ_[p]} {V : WeierstrassCurve ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (hΔ' : (ofShortNF a₄ (a₆ + (p : ℤ_[p]) ^ v)).Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hm : (TateAlgorithm.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m) (hv : v = m + 3) :
    (TateAlgorithm.run (W := ofShortNF a₄ (a₆ + (p : ℤ_[p]) ^ v))
        PadicInt.uniformizer_ne_zero hΔ').kodairaSymbol = KodairaSymbol.I! m ∧
      ((TateAlgorithm.run (W := ofShortNF a₄ (a₆ + (p : ℤ_[p]) ^ v))
          PadicInt.uniformizer_ne_zero hΔ').tamagawaNumber = 4 ↔
        (TateAlgorithm.run (W := ofShortNF a₄ a₆)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2) :=
  run_flip hp2 hΔ hΔ' ⟨rfl, rfl, rfl, rfl, rfl⟩ h5 hdbl hntr hm hv

end FlipRun

end WeierstrassCurve

end
