/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TateCongruenceStep6

/-!
# Finite determination of Step 7 of Tate's algorithm

Step 7 of Tate's algorithm runs Step 6 and, if Step 6 continues with a curve `c`, continues with
`c` itself when the cubic `cubic ϖ c 1 1` has a triple root. Otherwise it translates the double
root of that cubic to the origin and enters the loop `Step7.subprocedure`, which at level `n`
alternately translates the double root of the quadratic `quadratic ϖ · n` to `Y = 0` and the double
root of the cubic `cubic ϖ · 0 n` to `X = 0`, and terminates with Kodaira symbol `Iₙ*` as soon as
one of these double roots fails to exist. We show that Step 7 is determined by the coefficients of
the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`; in particular, the loop is determined by a congruence at
a depth that does not grow with the number of iterations. Here `Except.ok c` means that the
algorithm continues with `c`, and `Except.error o` that it terminates with answer `o`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step7.r_eq_of_cubic_eq`,
  `WeierstrassCurve.TateAlgorithm.Step7.tY_eq_of_quadratic_eq`,
  `WeierstrassCurve.TateAlgorithm.Step7.rX_eq_of_cubic_eq`: the three roots that Step 7 extracts
  over the residue field are functions of the relevant cubic or quadratic alone.
* `WeierstrassCurve.TateAlgorithm.Step7.translate_congrDepth`,
  `WeierstrassCurve.TateAlgorithm.Step7.translateY_congrDepth`,
  `WeierstrassCurve.TateAlgorithm.Step7.translateX_congrDepth`: each of the three changes of
  variables of Step 7 substitutes congruent curves by congruent curves.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_eq_of_not_hasDoubleRoot`,
  `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic`,
  `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_eq_subprocedure`: the three outcomes of one
  iteration of `Step7.subprocedure`.
* `WeierstrassCurve.TateAlgorithm.Step7.subprocedure_eq_of_congrDepth`: two curves congruent to
  depth `d` which enter the loop at the same level `n`, with the valuation data of the loop
  invariant, produce answers with the same Kodaira symbol and the same local Tamagawa number,
  provided `2 * n + 2 ≤ d` and `v_ϖ(Δ) ≤ d`.
* `WeierstrassCurve.TateAlgorithm.Step7.run_eq_of_step6_error`,
  `WeierstrassCurve.TateAlgorithm.Step7.run_eq_of_step6_ok_of_hasTripleRoot`,
  `WeierstrassCurve.TateAlgorithm.Step7.run_eq_of_step6_ok_of_not_hasTripleRoot`: `Step7.run` in
  terms of the outcome of Step 6.
* `WeierstrassCurve.TateAlgorithm.Step7.six_le_multiplicity_Δ`: if Step 6 continues on `W`, then
  `v_ϖ(W.Δ) ≥ 6`.
* `WeierstrassCurve.TateAlgorithm.Step7.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 7 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.
-/

@[expose] public section

universe u

open CommRing Ideal

variable {R : Type u} [CommRing R]

namespace WeierstrassCurve

variable {ϖ : R} {d n : ℕ} {W W' : WeierstrassCurve R}

namespace TateAlgorithm

namespace Step7

variable [(span {ϖ}).IsMaximal]

/-! ### The three changes of variables of Step 7

Step 7 and its subprocedure translate three different roots to the origin: the double root `X = r`
of `cubic ϖ W 1 1` (`Step7.translate`), the double root `Y = t` of `quadratic ϖ W n`
(`Step7.translateY`), and the double root `X = r` of `cubic ϖ W 0 n` (`Step7.translateX`). -/

/-- The scalar `Step7.r` is a function of the cubic `cubic ϖ W 1 1` alone. -/
theorem r_eq_of_cubic_eq (hc : cubic ϖ W 1 1 = cubic ϖ W' 1 1) : r ϖ W = r ϖ W' := by
  unfold r
  congr 1
  split_ifs with h2
  · rw [hc]
  · rw [hc]

/-- The scalar `Step7.tY` is a function of the quadratic `quadratic ϖ W n` alone. -/
theorem tY_eq_of_quadratic_eq (hq : quadratic ϖ W n = quadratic ϖ W' n) :
    tY ϖ W n = tY ϖ W' n := by
  unfold tY
  congr 1
  split_ifs with h2
  · rw [hq]
  · rw [hq]

/-- The scalar `Step7.rX` is a function of the cubic `cubic ϖ W 1 n` alone. -/
theorem rX_eq_of_cubic_eq (hc : cubic ϖ W 1 n = cubic ϖ W' 1 n) : rX ϖ W n = rX ϖ W' n := by
  unfold rX
  congr 1
  split_ifs with h2
  · rw [hc]
  · rw [hc]

/-- Step 7's outer change of variables preserves congruence to any depth. -/
theorem translate_congrDepth (hr : r ϖ W = r ϖ W') (h : CongrDepth ϖ d W W') :
    CongrDepth ϖ d (translate ϖ W) (translate ϖ W') := by
  unfold translate
  rw [hr]
  exact h.smul _

/-- The `Y`-translation of Step 7's subprocedure preserves congruence to any depth. -/
theorem translateY_congrDepth (ht : tY ϖ W n = tY ϖ W' n) (h : CongrDepth ϖ d W W') :
    CongrDepth ϖ d (translateY ϖ W n) (translateY ϖ W' n) := by
  unfold translateY
  rw [ht]
  exact h.smul _

/-- The `X`-translation of Step 7's subprocedure preserves congruence to any depth. -/
theorem translateX_congrDepth (ht : rX ϖ W n = rX ϖ W' n) (h : CongrDepth ϖ d W W') :
    CongrDepth ϖ d (translateX ϖ W n) (translateX ϖ W' n) := by
  unfold translateX
  rw [ht]
  exact h.smul _

variable [PerfectField (R ⧸ span {ϖ})] [IsDomain R] [IsNoetherianRing R]
  {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ}

/-! ### The branch structure of Step 7's subprocedure

At level `n`, either the quadratic has no double root (terminate with `I*_{2n-3}`), or it has one
but the cubic does not (terminate with `I*_{2n-2}`), or both do (recurse at level `n + 1`). -/

section Subprocedure

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (hn : 2 ≤ n)
  (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
  (ha₂ : ¬ϖ ^ 2 ∣ W.a₂)

open scoped Classical in
/-- Unfolding of Step 7's subprocedure when the quadratic `quadratic ϖ W n` has no double root: the
loop terminates with Kodaira symbol `I*_{2n-3}` and local Tamagawa number `4` or `2` according as
that quadratic has a root over the residue field or not. -/
theorem subprocedure_eq_of_not_hasDoubleRoot (hY : ¬(quadratic ϖ W n).HasDoubleRoot) :
    subprocedure hϖ hΔ hn hW ha₂ =
      ⟨W, .I! (2 * n - 3), if 0 < (quadratic ϖ W n).roots.toFinset.card then 4 else 2⟩ := by
  rw [subprocedure.eq_def, dite_eq_right hY]

open scoped Classical in
/-- Unfolding of Step 7's subprocedure when the quadratic has a double root but the cubic
`cubic ϖ (translateY ϖ W n) 0 n` does not: the loop terminates with Kodaira symbol `I*_{2n-2}` and
local Tamagawa number `4` or `2` according as that cubic has a root over the residue field or
not. -/
theorem subprocedure_eq_of_not_hasDoubleRoot_cubic (hY : (quadratic ϖ W n).HasDoubleRoot)
    (hX : ¬(cubic ϖ (translateY ϖ W n) 0 n).HasDoubleRoot) :
    subprocedure hϖ hΔ hn hW ha₂ =
      ⟨translateY ϖ W n, .I! (2 * n - 2),
        if 0 < (cubic ϖ (translateY ϖ W n) 0 n).roots.toFinset.card then 4 else 2⟩ := by
  rw [subprocedure.eq_def, dite_eq_left hY]
  dsimp only
  rw [dite_eq_right hX]

/-- Unfolding of Step 7's subprocedure when both double roots exist: the loop performs both
translations and recurses at level `n + 1`. -/
theorem subprocedure_eq_subprocedure (hY : (quadratic ϖ W n).HasDoubleRoot)
    (hX : (cubic ϖ (translateY ϖ W n) 0 n).HasDoubleRoot)
    (hΔ' : (translateX ϖ (translateY ϖ W n) n).Δ ≠ 0) (hn' : 2 ≤ n + 1)
    (hW' : HasValuation ϖ (translateX ϖ (translateY ϖ W n) n)
      ⟨1, 1, n + 1, n + 2, 2 * n + 2, 1, n + 2, 2 * n + 2, 2 * n + 3, 2, 3, 2 * n + 5⟩)
    (ha₂' : ¬ϖ ^ 2 ∣ (translateX ϖ (translateY ϖ W n) n).a₂) :
    subprocedure hϖ hΔ hn hW ha₂ = subprocedure hϖ hΔ' hn' hW' ha₂' := by
  rw [subprocedure.eq_def, dite_eq_left hY]
  dsimp only
  rw [dite_eq_left hX]

end Subprocedure

/-! ### Finite determination of Step 7's subprocedure -/

/-- **The loop of Step 7 is determined by a congruence at a depth that does not grow with the
number of iterations.**

Let `W` and `W'` be congruent to depth `d`, both carrying the valuation data that the algorithm's
loop invariant records at level `n`, and suppose the depth budget `d` covers the current level
(`2 * n + 2 ≤ d`) and is at least the discriminant valuation (`v_ϖ(W.Δ) ≤ d`). Then the loop
returns the same Kodaira symbol and the same local Tamagawa number on both curves. -/
theorem subprocedure_eq_of_congrDepth (hϖ : ϖ ≠ 0) {d n : ℕ} {W W' : WeierstrassCurve R}
    {b₂ b₄ b₆ b₈ c₄ c₆ Δv : ℕ} (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (hn : 2 ≤ n)
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (hW' : HasValuation ϖ W' ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δv⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) (ha₂' : ¬ϖ ^ 2 ∣ W'.a₂) (h : CongrDepth ϖ d W W')
    (hd : 2 * n + 2 ≤ d) (hdm : multiplicity ϖ W.Δ ≤ d) :
    (subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol
        = (subprocedure hϖ hΔ' hn hW' ha₂').kodairaSymbol ∧
      (subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber
        = (subprocedure hϖ hΔ' hn hW' ha₂').tamagawaNumber := by
  have hq : quadratic ϖ W n = quadratic ϖ W' n :=
    quadratic_eq_of_congrDepth hϖ h (m := n) (by omega) hW.a₃ hW.a₆
  by_cases hY : (quadratic ϖ W n).HasDoubleRoot
  · have hY' : (quadratic ϖ W' n).HasDoubleRoot := hq ▸ hY
    have hY₁ : CongrDepth ϖ d (translateY ϖ W n) (translateY ϖ W' n) :=
      translateY_congrDepth (tY_eq_of_quadratic_eq hq) h
    have hvY := hasValuation_translateY hn hϖ hW hY
    have hvY' := hasValuation_translateY hn hϖ hW' hY'
    have hcub : ∀ a : R, cubic ϖ (translateY ϖ W n) a n = cubic ϖ (translateY ϖ W' n) a n :=
      fun a => cubic_eq_of_congrDepth hϖ hY₁ (a := a) (by omega) hvY.a₂ hvY.a₄ hvY.a₆
    by_cases hX : (cubic ϖ (translateY ϖ W n) 0 n).HasDoubleRoot
    · have hX' : (cubic ϖ (translateY ϖ W' n) 0 n).HasDoubleRoot := hcub 0 ▸ hX
      have ha₂Y : ¬ϖ ^ 2 ∣ (translateY ϖ W n).a₂ := not_dvd_translateY_a₂ n ha₂
      have ha₂Y' : ¬ϖ ^ 2 ∣ (translateY ϖ W' n).a₂ := not_dvd_translateY_a₂ n ha₂'
      have hvX := hasValuation_translateX hn hϖ hvY ha₂Y hX
      have hvX' := hasValuation_translateX hn hϖ hvY' ha₂Y' hX'
      have hΔX : (translateX ϖ (translateY ϖ W n) n).Δ ≠ 0 := by
        rw [translateX_Δ, translateY_Δ]; exact hΔ
      have hΔX' : (translateX ϖ (translateY ϖ W' n) n).Δ ≠ 0 := by
        rw [translateX_Δ, translateY_Δ]; exact hΔ'
      have hX₁ : CongrDepth ϖ d (translateX ϖ (translateY ϖ W n) n)
          (translateX ϖ (translateY ϖ W' n) n) :=
        translateX_congrDepth (rX_eq_of_cubic_eq (hcub 1)) hY₁
      have hΔ₅ : 2 * n + 5 ≤ multiplicity ϖ W.Δ := by
        refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
        have hdvd := hvX.Δ
        rwa [translateX_Δ, translateY_Δ] at hdvd
      have hdmX : multiplicity ϖ (translateX ϖ (translateY ϖ W n) n).Δ ≤ d := by
        rw [translateX_Δ, translateY_Δ]; exact hdm
      rw [subprocedure_eq_subprocedure hϖ hΔ hn hW ha₂ hY hX hΔX (by omega) hvX
        (not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y),
        subprocedure_eq_subprocedure hϖ hΔ' hn hW' ha₂' hY' hX' hΔX' (by omega) hvX'
        (not_dvd_translateX_a₂ hn hϖ hvY'.a₂ ha₂Y')]
      exact subprocedure_eq_of_congrDepth hϖ hΔX hΔX' (by omega) hvX hvX'
        (not_dvd_translateX_a₂ hn hϖ hvY.a₂ ha₂Y) (not_dvd_translateX_a₂ hn hϖ hvY'.a₂ ha₂Y')
        hX₁ (by omega) hdmX
    · rw [subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ hn hW ha₂ hY hX,
        subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔ' hn hW' ha₂' hY'
          fun hc => hX (hcub 0 ▸ hc)]
      exact ⟨rfl, by rw [hcub 0]⟩
  · rw [subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ hn hW ha₂ hY,
      subprocedure_eq_of_not_hasDoubleRoot hϖ hΔ' hn hW' ha₂' fun hc => hY (hq ▸ hc)]
    exact ⟨rfl, by rw [hq]⟩
termination_by d - n
decreasing_by omega

/-! ### The branch structure of Step 7

Either Step 6 terminates, or Step 6 continues and the cubic `cubic ϖ · 1 1` has a triple root, or
Step 6 continues and that cubic does not have a triple root. -/

section Run

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- Unfolding of Step 7 in the case where Step 6 terminates: Step 7 passes the answer through
unchanged. -/
theorem run_eq_of_step6_error {o : Output R} (h6 : Step6.run ϖ W = .error o) :
    run hϖ hΔ = .error o := by
  rw [run.eq_def]
  split <;> rename_i x heq
  · rw [h6] at heq
    cases heq
    rfl
  · rw [h6] at heq
    exact absurd heq (by simp)

/-- Unfolding of Step 7 in the case where Step 6 continues with `c` and the cubic `cubic ϖ c 1 1`
has a triple root: Step 7 hands `c` itself on to Step 8, performing no change of variables. -/
theorem run_eq_of_step6_ok_of_hasTripleRoot {c : WeierstrassCurve R}
    (h6 : Step6.run ϖ W = .ok c) (htr : (cubic ϖ c 1 1).HasTripleRoot) : run hϖ hΔ = .ok c := by
  rw [run.eq_def]
  split <;> rename_i x heq
  · rw [h6] at heq
    exact absurd heq (by simp)
  · rw [h6] at heq
    cases heq
    rw [dite_eq_left htr]

/-- Unfolding of Step 7 in the case where Step 6 continues with `c` and the cubic `cubic ϖ c 1 1`
has a double but not a triple root: Step 7 translates the double root to the origin and terminates
with the answer computed by its subprocedure, entered at level `2`. -/
theorem run_eq_of_step6_ok_of_not_hasTripleRoot {c : WeierstrassCurve R}
    (h6 : Step6.run ϖ W = .ok c) (htr : ¬(cubic ϖ c 1 1).HasTripleRoot)
    (hΔc : (translate ϖ c).Δ ≠ 0)
    (hvc : HasValuation ϖ (translate ϖ c) ⟨1, 1, 2, 3, 4, 1, 3, 4, 5, 2, 3, 7⟩)
    (ha₂c : ¬ϖ ^ 2 ∣ (translate ϖ c).a₂) :
    run hϖ hΔ = .error (subprocedure hϖ hΔc le_rfl hvc ha₂c) := by
  rw [run.eq_def]
  split <;> rename_i x heq
  · rw [h6] at heq
    exact absurd heq (by simp)
  · rw [h6] at heq
    cases heq
    rw [dite_eq_right htr]

end Run

/-! ### Finite determination of Step 7 -/

/-- If `ϖ ≠ 0` and Step 6 continues on a curve `W` with `W.Δ ≠ 0`, then `v_ϖ(W.Δ) ≥ 6`. -/
theorem six_le_multiplicity_Δ (hϖ : ϖ ≠ 0) {W c : WeierstrassCurve R} (hΔ : W.Δ ≠ 0)
    (h6 : Step6.run ϖ W = .ok c) : 6 ≤ multiplicity ϖ W.Δ := by
  refine (FiniteMultiplicity.of_span_isMaximal ϖ hΔ).le_multiplicity_of_pow_dvd ?_
  rw [← Step6.run_Δ h6]
  exact (Step6.run_hasValuation hϖ h6).Δ

/-- **Step 7 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

1. `Step7.run hϖ hΔ` and `Step7.run hϖ hΔ'` have the same `Except.isOk` flag.
2. If both terminate (`Except.error`), the two answers have the same Kodaira symbol and the same
   local Tamagawa number.
3. If both continue (`Except.ok`), the two curves returned are congruent to depth `v_ϖ(W.Δ)`. -/
theorem finite_determination (hϖ : ϖ ≠ 0) {W W' : WeierstrassCurve R} (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W') :
    ((run hϖ hΔ).isOk = (run hϖ hΔ').isOk) ∧
    (∀ o o' : Output R, run hϖ hΔ = .error o → run hϖ hΔ' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve R, run hϖ hΔ = .ok c → run hϖ hΔ' = .ok c' →
      CongrDepth ϖ (multiplicity ϖ W.Δ) c c') := by
  obtain ⟨hbranch, herror, hcont⟩ := Step6.finite_determination ϖ hΔ h
  cases h₆ : Step6.run ϖ W with
  | error o =>
    cases h₆' : Step6.run ϖ W' with
    | error o' =>
      rw [run_eq_of_step6_error hϖ hΔ h₆, run_eq_of_step6_error hϖ hΔ' h₆']
      refine ⟨rfl, fun p p' hp hp' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at hp hp'
      subst hp; subst hp'
      exact herror o o' h₆ h₆'
    | ok c' => rw [h₆, h₆'] at hbranch; exact Bool.noConfusion hbranch
  | ok c =>
    cases h₆' : Step6.run ϖ W' with
    | error o' => rw [h₆, h₆'] at hbranch; exact Bool.noConfusion hbranch
    | ok c' =>
      have hcong : CongrDepth ϖ (multiplicity ϖ W.Δ) c c' := hcont c c' h₆ h₆'
      have hle : 6 ≤ multiplicity ϖ W.Δ := six_le_multiplicity_Δ hϖ hΔ h₆
      have hvc := Step6.run_hasValuation hϖ h₆
      have hvc' := Step6.run_hasValuation hϖ h₆'
      have hdr := Step6.run_hasDoubleRoot h₆
      have hdr' := Step6.run_hasDoubleRoot h₆'
      have hcub : cubic ϖ c 1 1 = cubic ϖ c' 1 1 :=
        cubic_eq_of_congrDepth hϖ hcong (m := 1) (by omega) hvc.a₂ hvc.a₄ hvc.a₆
      by_cases htr : (cubic ϖ c 1 1).HasTripleRoot
      · rw [run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ h₆ htr,
          run_eq_of_step6_ok_of_hasTripleRoot hϖ hΔ' h₆' (hcub ▸ htr)]
        refine ⟨rfl, fun p p' hp _ => absurd hp (by simp), fun e e' he he' => ?_⟩
        rw [Except.ok.injEq] at he he'
        subst he; subst he'
        exact hcong
      · have htr' : ¬(cubic ϖ c' 1 1).HasTripleRoot := fun hc => htr (hcub ▸ hc)
        have hΔc : (translate ϖ c).Δ ≠ 0 := by rw [translate_Δ, Step6.run_Δ h₆]; exact hΔ
        have hΔc' : (translate ϖ c').Δ ≠ 0 := by rw [translate_Δ, Step6.run_Δ h₆']; exact hΔ'
        have hvT := hasValuation_translate hϖ hvc hdr htr
        have hvT' := hasValuation_translate hϖ hvc' hdr' htr'
        have ha₂T := not_dvd_translate_a₂ hϖ hvc.a₂ hdr htr
        have ha₂T' := not_dvd_translate_a₂ hϖ hvc'.a₂ hdr' htr'
        have hcongT : CongrDepth ϖ (multiplicity ϖ W.Δ) (translate ϖ c) (translate ϖ c') :=
          translate_congrDepth (r_eq_of_cubic_eq hcub) hcong
        have hdm : multiplicity ϖ (translate ϖ c).Δ ≤ multiplicity ϖ W.Δ := by
          rw [translate_Δ, Step6.run_Δ h₆]
        rw [run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h₆ htr hΔc hvT ha₂T,
          run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ' h₆' htr' hΔc' hvT' ha₂T']
        refine ⟨rfl, fun p p' hp hp' => ?_, fun e e' he _ => absurd he (by simp)⟩
        rw [Except.error.injEq] at hp hp'
        subst hp; subst hp'
        exact subprocedure_eq_of_congrDepth hϖ hΔc hΔc' le_rfl hvT hvT' ha₂T ha₂T' hcongT
          (by omega) hdm

end Step7

end TateAlgorithm

end WeierstrassCurve
