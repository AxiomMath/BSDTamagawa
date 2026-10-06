/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.EllipticCurve.Tate.Algorithm

/-!
# Positivity of the Tamagawa number computed by Tate's algorithm

Tate's algorithm always returns a positive Tamagawa number: `0 < (run hϖ hΔ).tamagawaNumber`.
Eleven of the twelve `Output` construction sites of the algorithm are syntactically positive; the
twelfth is Step 2's `Iₙ`, whose Tamagawa number on the split branch is `n = v_ϖ(Δ)`, positive
because Step 1 has already forced `ϖ ∣ Δ`.

## Main results

* `Except.bind_eq_error_iff`: a bind of `Except` is an `error` exactly when the first computation
  errored, or it succeeded and the continuation errored.
* `WeierstrassCurve.TateAlgorithm.Step1.pos`, …, `Step11.pos`: if step `k` terminates with output
  `out`, then `0 < out.tamagawaNumber`.
* `WeierstrassCurve.TateAlgorithm.run_tamagawaNumber_pos`: the Tamagawa number returned by Tate's
  algorithm is positive.

## Implementation notes

Each step has type `Step_k.run : Except (Output R) (WeierstrassCurve R)`: `Except.ok W'` means
"continue with the curve `W'`", and `Except.error out` means "terminate with the answer `out`". So
every statement about the answer is a statement about the `error` branch. The top-level
`run hϖ hΔ : Output R` recurses on `ok` and returns on `error`.
-/

@[expose] public section

universe u

/-! ### The `error` branch of `Except.bind` -/

namespace Except

/-- A monadic bind of `Except` is an `error` exactly when either the first computation already
errored, or it succeeded and the continuation errored. This is the `error` counterpart of
`Except.bind_eq_ok_iff`. -/
lemma bind_eq_error_iff {ε α β : Type u} {x : Except ε α} {f : α → Except ε β} {e : ε} :
    x >>= f = error e ↔ x = error e ∨ ∃ a, x = ok a ∧ f a = error e := by
  cases x <;> simp [Bind.bind, Except.bind]

end Except

/-- If `ϖ` generates a proper ideal of a Noetherian domain and `ϖ ∣ x` with `x ≠ 0`, then the
multiplicity of `ϖ` in `x` is nonzero and finite, so its `ℕ`-truncation is positive. -/
lemma toNat_emultiplicity_pos {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {ϖ x : R} (hspan : Ideal.span {ϖ} ≠ ⊤) (hx : x ≠ 0) (hd : ϖ ∣ x) :
    0 < (emultiplicity ϖ x).toNat := by
  have hfin : emultiplicity ϖ x ≠ ⊤ := by
    rwa [Ne, emultiplicity_of_span_ne_top hspan]
  have h1 : (1 : ℕ∞) ≤ emultiplicity ϖ x := by
    simpa using le_emultiplicity_of_pow_dvd (k := 1) (by simpa using hd)
  have h2 := ENat.toNat_le_toNat h1 hfin
  rw [ENat.toNat_one] at h2
  omega

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R}

/-! ### Steps 1–6 -/

omit [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}] in
/-- Step 1 terminates only with good reduction `I₀`, of Tamagawa number `1`. -/
lemma Step1.pos (h : Step1.run ϖ W = Except.error out) : 0 < out.tamagawaNumber := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  exact Nat.one_pos

variable [IsNoetherianRing R] [IsDomain R]

/-- Step 2 terminates with multiplicative reduction `Iₙ`, of Tamagawa number `n`, `1` or `2`. This
is the only step whose positivity has content: `n = v_ϖ(Δ)` is positive because Step 1 has already
established `ϖ ∣ Δ`, and finite because `Δ ≠ 0`. -/
lemma Step2.pos (hΔ : W.Δ ≠ 0) (h : Step2.run ϖ W = Except.error out) :
    0 < out.tamagawaNumber := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step1.pos h
  · have hdvd : ϖ ∣ W.Δ := Step1.run_Δ h'
    have hn : 0 < (emultiplicity ϖ W.Δ).toNat :=
      toNat_emultiplicity_pos (IsMaximal.ne_top inferInstance) hΔ hdvd
    rw [Step1.run_weierstrassCurve h'] at h
    by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W).b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      rw [Step2.translate_Δ]
      split_ifs
      · exact hn
      · exact Nat.one_pos
      · exact Nat.zero_lt_two

/-- Step 3 terminates only with additive reduction `II`, of Tamagawa number `1`. -/
lemma Step3.pos (hΔ : W.Δ ≠ 0) (h : Step3.run ϖ W = Except.error out) :
    0 < out.tamagawaNumber := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.pos hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Nat.one_pos

/-- Step 4 terminates only with additive reduction `III`, of Tamagawa number `2`. -/
lemma Step4.pos (hΔ : W.Δ ≠ 0) (h : Step4.run ϖ W = Except.error out) :
    0 < out.tamagawaNumber := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.pos hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Nat.zero_lt_two

/-- Step 5 terminates only with additive reduction `IV`, of Tamagawa number `3` or `1`. -/
lemma Step5.pos (hΔ : W.Δ ≠ 0) (h : Step5.run ϖ W = Except.error out) :
    0 < out.tamagawaNumber := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.pos hΔ h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Nat.succ_pos _

/-- Step 6 terminates only with additive reduction `I₀*`, of Tamagawa number `1 + #roots`. -/
lemma Step6.pos (hΔ : W.Δ ≠ 0) (h : Step6.run ϖ W = Except.error out) :
    0 < out.tamagawaNumber := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.pos hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)

/-! ### Step 7 and its `Iₙ*` subprocedure -/

/-- Every output of the `Iₙ*` subprocedure of Step 7 has positive Tamagawa number (it is `4` or
`2`). -/
lemma Step7.subprocedure_pos (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) :
    0 < (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => split_ifs <;> exact Nat.succ_pos _
  | case3 => split_ifs <;> exact Nat.succ_pos _

/-- An error output of Step 7 (an earlier termination, or type `Iₙ*`) has positive Tamagawa
number. -/
lemma Step7.pos (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (h : Step7.run hϖ hΔ = Except.error out) :
    0 < out.tamagawaNumber := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.pos hΔ (heq.trans h)
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact Step7.subprocedure_pos ..

/-! ### Steps 8–11 -/

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- Step 8 terminates only with additive reduction `IV*`, of Tamagawa number `3` or `1`. -/
lemma Step8.pos (h : Step8.run hϖ hΔ = Except.error out) : 0 < out.tamagawaNumber := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.pos hϖ hΔ h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Nat.succ_pos _

/-- Step 9 terminates only with additive reduction `III*`, of Tamagawa number `2`. -/
lemma Step9.pos (h : Step9.run hϖ hΔ = Except.error out) : 0 < out.tamagawaNumber := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.pos hϖ hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Nat.zero_lt_two

/-- Step 10 terminates only with additive reduction `II*`, of Tamagawa number `1`. -/
lemma Step10.pos (h : Step10.run hϖ hΔ = Except.error out) : 0 < out.tamagawaNumber := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.pos hϖ hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Nat.one_pos

/-- Step 11 never terminates on its own — it only minimalizes the curve — so an error there is an
error inherited from Step 10. -/
lemma Step11.pos (h : Step11.run hϖ hΔ = Except.error out) : 0 < out.tamagawaNumber := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.pos hϖ hΔ h
  · simp at h

/-! ### The top-level algorithm -/

/-- If Step 11 errors with `out`, then `run` returns `out`. -/
lemma run_eq_of_step11_error (h : Step11.run hϖ hΔ = Except.error out) : run hϖ hΔ = out := by
  rw [run.eq_def]
  split
  next out' heq => exact (Except.error.inj (h.symm.trans heq)).symm
  next W' heq => exact absurd (h.symm.trans heq) (by simp)

/-- If Step 11 returns the minimalized curve `W'`, then `run` equals `run` on `W'`. Which proof of
`W'.Δ ≠ 0` is used is irrelevant. -/
lemma run_eq_of_step11_ok {W' : WeierstrassCurve R} (h : Step11.run hϖ hΔ = Except.ok W')
    (hΔ' : W'.Δ ≠ 0) : run hϖ hΔ = run hϖ hΔ' := by
  rw [run.eq_def]
  split
  next out' heq => exact absurd (h.symm.trans heq) (by simp)
  next W'' heq => obtain rfl := Except.ok.inj (h.symm.trans heq); rfl

/-- **Positivity of the Tamagawa number.** Tate's algorithm always returns a positive Tamagawa
number: it terminates at one of the twelve `Output` construction sites, each of which reports a
positive number of components. -/
theorem run_tamagawaNumber_pos : 0 < (run hϖ hΔ).tamagawaNumber := by
  induction W, hΔ using run.induct hϖ with
  | case1 W hΔ out h => rw [run_eq_of_step11_error hϖ hΔ h]; exact Step11.pos hϖ hΔ h
  | case2 W hΔ W' h ih =>
    have hΔ' : W'.Δ ≠ 0 := fun h0 ↦ hΔ (by rw [← Step11.run_Δ hϖ hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok hϖ hΔ h hΔ']
    exact ih

end WeierstrassCurve.TateAlgorithm
