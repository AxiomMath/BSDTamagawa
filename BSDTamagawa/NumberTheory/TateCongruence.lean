/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.EllipticCurve.Tate.Algorithm

/-!
# Congruence of Weierstrass curves and finite determination of Tate's algorithm

Two Weierstrass curves over `R` whose coefficients agree modulo `ϖ ^ n` are run by Tate's algorithm
in lockstep for as long as the algorithm only inspects the coefficients modulo `ϖ ^ n`. This file
defines the congruence relation `WeierstrassCurve.CongrDepth`, develops its API, and proves that
the output of Step 2 of Tate's algorithm is determined by the coefficients of the input curve
modulo `ϖ ^ (v_ϖ(Δ) + 1)`.

## Main definitions

* `WeierstrassCurve.CongrDepth ϖ n W W'`: `W` and `W'` are congruent to depth `n`, i.e. they have
  the same reduction modulo `ϖ ^ n`.
* `WeierstrassCurve.TateAlgorithm.Step2.translateVariableChange`: the change of variables applied
  by Step 2.

## Main results

* `WeierstrassCurve.congrDepth_iff_sub_mem`: `CongrDepth ϖ n W W'` holds iff the five Weierstrass
  coefficients of `W` and `W'` differ by elements of `(ϖ ^ n)`.
* `WeierstrassCurve.TateAlgorithm.Step2.run_eq_of_dvd_Δ`,
  `WeierstrassCurve.TateAlgorithm.Step2.run_eq_of_not_dvd_Δ`: the two unfoldings of `Step2.run`.
* `WeierstrassCurve.TateAlgorithm.Step2.finite_determination`: if `W` and `W'` are congruent to
  depth `v_ϖ(W.Δ) + 1`, then Step 2 takes the same branch on both, returns the same Kodaira symbol
  and the same local Tamagawa number when it terminates, and returns curves congruent to depth
  `v_ϖ(W.Δ)` when it continues.

## Implementation notes

Each step of Tate's algorithm has type `Except (Output R) (WeierstrassCurve R)`: `Except.ok W'`
means that the curve `W'` is handed to the next step, and `Except.error out` means that the
algorithm terminates with answer `out`.

`CongrDepth` is defined as equality of the two reductions `W.map (Ideal.Quotient.mk (ϖ ^ n))`, so
that its compatibility with the derived quantities and with changes of variables follows from
`WeierstrassCurve.map_b₂`, …, `WeierstrassCurve.map_variableChange`.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

/-! ### Multiplicity and congruences -/

/-- If `r - s` is divisible by `p ^ n` and `p` divides `r` fewer than `n` times, then `p` divides
`s` exactly as often as it divides `r`. -/
theorem emultiplicity_eq_of_pow_dvd_sub {p r s : R} {n : ℕ}
    (hn : emultiplicity p r < n) (h : p ^ n ∣ r - s) :
    emultiplicity p s = emultiplicity p r := by
  have hlt : emultiplicity p r < emultiplicity p (r - s) :=
    hn.trans_le (le_emultiplicity_of_pow_dvd h)
  have hsub := emultiplicity_sub_of_gt hlt
  rwa [show r - s - r = -s by ring, emultiplicity_neg] at hsub

/-- Every nonzero element of a Noetherian domain has finite `ϖ`-adic multiplicity as soon as `(ϖ)`
is a maximal ideal. -/
theorem FiniteMultiplicity.of_span_isMaximal [IsDomain R] [IsNoetherianRing R] (ϖ : R)
    [hϖ : (Ideal.span {ϖ}).IsMaximal] {r : R} (hr : r ≠ 0) : FiniteMultiplicity ϖ r :=
  (FiniteMultiplicity.span_ne_top hϖ.ne_top).mpr hr

namespace WeierstrassCurve

/-! ### Congruence to a given depth -/

/-- Two Weierstrass curves are **congruent to depth `n`** (with respect to `ϖ`) when they have the
same reduction modulo `ϖ ^ n`, i.e. when their five Weierstrass coefficients differ by elements of
the ideal `(ϖ ^ n)`. -/
def CongrDepth (ϖ : R) (n : ℕ) (W W' : WeierstrassCurve R) : Prop :=
  W.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ n}))
    = W'.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ n}))

variable {ϖ : R} {m n : ℕ} {W W' W'' : WeierstrassCurve R}

/-- Congruence to depth `n` holds precisely when the five Weierstrass coefficients differ by
elements of `(ϖ ^ n)`. -/
theorem congrDepth_iff_sub_mem (ϖ : R) (n : ℕ) (W W' : WeierstrassCurve R) :
    CongrDepth ϖ n W W' ↔
      W.a₁ - W'.a₁ ∈ Ideal.span {ϖ ^ n} ∧
      W.a₂ - W'.a₂ ∈ Ideal.span {ϖ ^ n} ∧
      W.a₃ - W'.a₃ ∈ Ideal.span {ϖ ^ n} ∧
      W.a₄ - W'.a₄ ∈ Ideal.span {ϖ ^ n} ∧
      W.a₆ - W'.a₆ ∈ Ideal.span {ϖ ^ n} := by
  simp only [CongrDepth, WeierstrassCurve.ext_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    Ideal.Quotient.eq]

/-- Congruence to depth `1` says exactly that the two curves have the same reduction modulo `ϖ`, in
the form `CommRing.mod ϖ`. -/
theorem congrDepth_one_iff_map_mod_eq (ϖ : R) (W W' : WeierstrassCurve R) :
    CongrDepth ϖ 1 W W' ↔ W.map (CommRing.mod ϖ) = W'.map (CommRing.mod ϖ) := by
  simp only [congrDepth_iff_sub_mem, pow_one, WeierstrassCurve.ext_iff, map_a₁, map_a₂, map_a₃,
    map_a₄, map_a₆, CommRing.mod, Ideal.Quotient.eq]

namespace CongrDepth

/-- Congruence to depth `n` is reflexive. -/
@[refl]
theorem refl (ϖ : R) (n : ℕ) (W : WeierstrassCurve R) : CongrDepth ϖ n W W := rfl

/-- Congruence to depth `n` is symmetric. -/
@[symm]
theorem symm (h : CongrDepth ϖ n W W') : CongrDepth ϖ n W' W := Eq.symm h

/-- Congruence to depth `n` is transitive. -/
@[trans]
theorem trans (h : CongrDepth ϖ n W W') (h' : CongrDepth ϖ n W' W'') : CongrDepth ϖ n W W'' :=
  Eq.trans h h'

/-- Congruence is monotone in the depth: a congruence to depth `n` implies one to depth `m ≤ n`. -/
theorem mono (h : CongrDepth ϖ n W W') (hmn : m ≤ n) : CongrDepth ϖ m W W' := by
  have hle : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ m} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn)
  rw [congrDepth_iff_sub_mem] at h ⊢
  exact ⟨hle h.1, hle h.2.1, hle h.2.2.1, hle h.2.2.2.1, hle h.2.2.2.2⟩

/-- Curves congruent to depth `n` have `b₂` congruent to depth `n`. -/
theorem b₂_sub_mem (h : CongrDepth ϖ n W W') : W.b₂ - W'.b₂ ∈ Ideal.span {ϖ ^ n} :=
  Ideal.Quotient.eq.mp <| by rw [← map_b₂, ← map_b₂, h]

/-- Curves congruent to depth `n` have `b₆` congruent to depth `n`. -/
theorem b₆_sub_mem (h : CongrDepth ϖ n W W') : W.b₆ - W'.b₆ ∈ Ideal.span {ϖ ^ n} :=
  Ideal.Quotient.eq.mp <| by rw [← map_b₆, ← map_b₆, h]

/-- Curves congruent to depth `n` have `b₈` congruent to depth `n`. -/
theorem b₈_sub_mem (h : CongrDepth ϖ n W W') : W.b₈ - W'.b₈ ∈ Ideal.span {ϖ ^ n} :=
  Ideal.Quotient.eq.mp <| by rw [← map_b₈, ← map_b₈, h]

/-- Curves congruent to depth `n` have discriminants congruent to depth `n`. -/
theorem Δ_sub_mem (h : CongrDepth ϖ n W W') : W.Δ - W'.Δ ∈ Ideal.span {ϖ ^ n} :=
  Ideal.Quotient.eq.mp <| by rw [← map_Δ, ← map_Δ, h]

/-- Curves congruent to depth `1` pass the divisibility test `ϖ ∣ b₂` of Step 2 together. -/
theorem dvd_b₂_iff (h : CongrDepth ϖ 1 W W') : ϖ ∣ W.b₂ ↔ ϖ ∣ W'.b₂ := by
  have hb := h.b₂_sub_mem
  rw [pow_one, Ideal.mem_span_singleton] at hb
  exact dvd_iff_dvd_of_dvd_sub hb

/-- Curves congruent to depth `1` pass the divisibility test `ϖ ∣ Δ` of Step 1 together. -/
theorem dvd_Δ_iff (h : CongrDepth ϖ 1 W W') : ϖ ∣ W.Δ ↔ ϖ ∣ W'.Δ := by
  have hΔ := h.Δ_sub_mem
  rw [pow_one, Ideal.mem_span_singleton] at hΔ
  exact dvd_iff_dvd_of_dvd_sub hΔ

/-- Applying one and the same change of variables to two curves congruent to depth `n` yields
curves congruent to depth `n`. -/
theorem smul (h : CongrDepth ϖ n W W') (C : VariableChange R) :
    CongrDepth ϖ n (C • W) (C • W') := by
  simp only [CongrDepth] at h
  simp only [CongrDepth, ← map_variableChange, h]

/-- A congruence to depth strictly greater than `v_ϖ(W.Δ)` pins down the multiplicity of the
discriminant exactly. -/
theorem emultiplicity_Δ_eq (h : CongrDepth ϖ n W W') (hn : emultiplicity ϖ W.Δ < n) :
    emultiplicity ϖ W'.Δ = emultiplicity ϖ W.Δ :=
  emultiplicity_eq_of_pow_dvd_sub hn (Ideal.mem_span_singleton.mp h.Δ_sub_mem)

end CongrDepth

namespace TateAlgorithm.Step2

/-! ### The change of variables performed by Step 2 -/

variable (ϖ : R) [(Ideal.span {ϖ}).IsMaximal] [PerfectField (R ⧸ Ideal.span {ϖ})]

/-- The change of variables performed by Step 2 of Tate's algorithm: it translates the singular
point of the mod-`ϖ` reduction to the origin, with `u = 1` and `s = 0`. -/
noncomputable def translateVariableChange {W : WeierstrassCurve R} (hΔ : ϖ ∣ W.Δ) :
    VariableChange R :=
  ⟨1, (singularPoint hΔ).x.out, 0, (singularPoint hΔ).y.out⟩

/-- Once Step 1 has established `ϖ ∣ Δ`, `Step2.translate` is the action of the change
of variables `Step2.translateVariableChange`. -/
theorem translate_eq_smul {W : WeierstrassCurve R} (hΔ : ϖ ∣ W.Δ) :
    translate ϖ W = translateVariableChange ϖ hΔ • W := by
  unfold translate translateVariableChange
  rw [dite_eq_left hΔ]

/-- The change of variables performed by Step 2 depends only on the reduction of the curve modulo
`ϖ`: two curves with the same reduction are translated by the same substitution. -/
theorem translateVariableChange_eq_of_map_mod_eq {W W' : WeierstrassCurve R}
    (hmap : W.map (CommRing.mod ϖ) = W'.map (CommRing.mod ϖ)) (hΔ : ϖ ∣ W.Δ) (hΔ' : ϖ ∣ W'.Δ) :
    translateVariableChange ϖ hΔ = translateVariableChange ϖ hΔ' := by
  have hsp : HEq (singularPoint hΔ) (singularPoint hΔ') := by
    have htype : Affine.SingularPoint (W.map (CommRing.mod ϖ))
        = Affine.SingularPoint (W'.map (CommRing.mod ϖ)) := by rw [hmap]
    have hΔ0 : (W.map (CommRing.mod ϖ)).Δ = 0 := by
      rw [WeierstrassCurve.map_Δ, CommRing.mod, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact hΔ
    have : Unique (Affine.SingularPoint (W.map (CommRing.mod ϖ))) :=
      Affine.SingularPoint.unique hΔ0
    exact Subsingleton.helim htype _ _
  unfold translateVariableChange
  have hx : (singularPoint hΔ).x = (singularPoint hΔ').x := by congr 1
  have hy : (singularPoint hΔ).y = (singularPoint hΔ').y := by congr 1
  rw [hx, hy]

/-- Step 2's translation preserves congruence: if two curves have the same reduction modulo `ϖ` and
are congruent to depth `n`, their Step-2 translates are congruent to depth `n`. -/
theorem translate_congrDepth {n : ℕ} {W W' : WeierstrassCurve R} (h₁ : CongrDepth ϖ 1 W W')
    (h : CongrDepth ϖ n W W') : CongrDepth ϖ n (translate ϖ W) (translate ϖ W') := by
  by_cases hΔ : ϖ ∣ W.Δ
  · have hΔ' : ϖ ∣ W'.Δ := h₁.dvd_Δ_iff.mp hΔ
    have hvc : translateVariableChange ϖ hΔ = translateVariableChange ϖ hΔ' :=
      translateVariableChange_eq_of_map_mod_eq ϖ
        ((congrDepth_one_iff_map_mod_eq ϖ W W').mp h₁) hΔ hΔ'
    rw [translate_eq_smul ϖ hΔ, translate_eq_smul ϖ hΔ', hvc]
    exact h.smul _
  · have hΔ' : ¬ ϖ ∣ W'.Δ := fun hc => hΔ (h₁.dvd_Δ_iff.mpr hc)
    unfold translate
    rw [dite_eq_right hΔ, dite_eq_right hΔ']
    exact h

/-! ### The branch structure of Step 2 -/

open scoped Classical in
open Polynomial in
/-- Unfolding of Step 2 in the case `ϖ ∣ Δ`, where Step 1 continues: Step 2 translates the
singular point to the origin and then tests `ϖ ∣ b₂`, continuing (`Except.ok`) in the additive
case and terminating (`Except.error`) with Kodaira symbol `Iₙ`, `n = v_ϖ(Δ)`, in the
multiplicative case. -/
theorem run_eq_of_dvd_Δ {W : WeierstrassCurve R} (hΔ : ϖ ∣ W.Δ) :
    run ϖ W =
      if ϖ ∣ (translate ϖ W).b₂ then .ok (translate ϖ W)
      else
        .error
          { weierstrassCurve := translate ϖ W
            kodairaSymbol := .I (emultiplicity ϖ (translate ϖ W).Δ).toNat
            tamagawaNumber :=
              if ((X ^ 2 + C (translate ϖ W).a₁ * X - C (translate ϖ W).a₂).map
                  (CommRing.mod ϖ)).Splits then (emultiplicity ϖ (translate ϖ W).Δ).toNat
              else if Odd (emultiplicity ϖ (translate ϖ W).Δ).toNat then 1 else 2 } := by
  rw [run.eq_def, Step1.run.eq_def, ite_eq_left hΔ]
  rfl

/-- Unfolding of Step 2 in the case `ϖ ∤ Δ`, where Step 1 already terminates: the curve has good
reduction, the Kodaira symbol is `I₀` and the local Tamagawa number is `1`. -/
theorem run_eq_of_not_dvd_Δ {W : WeierstrassCurve R} (hΔ : ¬ ϖ ∣ W.Δ) :
    run ϖ W = .error ⟨W, .I 0, 1⟩ := by
  rw [run.eq_def, Step1.run.eq_def, ite_eq_right hΔ]
  rfl

/-! ### Finite determination of Step 2 -/

open scoped Classical in
open Polynomial in
/-- **Step 2 of Tate's algorithm is determined by the input curve modulo `ϖ ^ (v_ϖ(Δ) + 1)`.**

Let `W` be a Weierstrass curve with `W.Δ ≠ 0` and let `W'` be congruent to `W` to depth
`v_ϖ(W.Δ) + 1`. Then:

* `Step2.run ϖ W` and `Step2.run ϖ W'` lie in the same branch (their `Except.isOk` flags agree).
* If both terminate (`Except.error`), the two answers have the same Kodaira symbol and the same
  local Tamagawa number.
* If both continue (`Except.ok`), the two curves handed to Step 3 are congruent to depth
  `v_ϖ(W.Δ)`. -/
theorem finite_determination [IsDomain R] [IsNoetherianRing R] {W W' : WeierstrassCurve R}
    (hΔ : W.Δ ≠ 0) (h : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) W W') :
    ((run ϖ W).isOk = (run ϖ W').isOk) ∧
    (∀ o o' : Output R, run ϖ W = .error o → run ϖ W' = .error o' →
      o.kodairaSymbol = o'.kodairaSymbol ∧ o.tamagawaNumber = o'.tamagawaNumber) ∧
    (∀ c c' : WeierstrassCurve R, run ϖ W = .ok c → run ϖ W' = .ok c' →
      CongrDepth ϖ (multiplicity ϖ W.Δ) c c') := by
  have h₁ : CongrDepth ϖ 1 W W' := h.mono (by omega)
  by_cases hdvd : ϖ ∣ W.Δ
  · have hdvd' : ϖ ∣ W'.Δ := h₁.dvd_Δ_iff.mp hdvd
    have htr : CongrDepth ϖ (multiplicity ϖ W.Δ + 1) (translate ϖ W) (translate ϖ W') :=
      translate_congrDepth ϖ h₁ h
    have htr₁ : CongrDepth ϖ 1 (translate ϖ W) (translate ϖ W') := htr.mono (by omega)
    have hmap : (translate ϖ W).map (CommRing.mod ϖ) = (translate ϖ W').map (CommRing.mod ϖ) :=
      (congrDepth_one_iff_map_mod_eq ϖ _ _).mp htr₁
    have hfin : FiniteMultiplicity ϖ W.Δ := FiniteMultiplicity.of_span_isMaximal ϖ hΔ
    have hemul : emultiplicity ϖ (translate ϖ W').Δ = emultiplicity ϖ (translate ϖ W).Δ := by
      rw [translate_Δ, translate_Δ]
      refine h.emultiplicity_Δ_eq ?_
      rw [hfin.emultiplicity_eq_multiplicity]
      exact_mod_cast Nat.lt_succ_self _
    have hnat : (emultiplicity ϖ (translate ϖ W).Δ).toNat
        = (emultiplicity ϖ (translate ϖ W').Δ).toNat := by rw [hemul]
    have ha₁ : CommRing.mod ϖ (translate ϖ W).a₁ = CommRing.mod ϖ (translate ϖ W').a₁ := by
      rw [← map_a₁, ← map_a₁, hmap]
    have ha₂ : CommRing.mod ϖ (translate ϖ W).a₂ = CommRing.mod ϖ (translate ϖ W').a₂ := by
      rw [← map_a₂, ← map_a₂, hmap]
    have hpoly :
        (X ^ 2 + C (translate ϖ W).a₁ * X - C (translate ϖ W).a₂).map (CommRing.mod ϖ)
          = (X ^ 2 + C (translate ϖ W').a₁ * X - C (translate ϖ W').a₂).map (CommRing.mod ϖ) := by
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, ha₁, ha₂]
    rw [run_eq_of_dvd_Δ ϖ hdvd, run_eq_of_dvd_Δ ϖ hdvd']
    by_cases hb₂ : ϖ ∣ (translate ϖ W).b₂
    · rw [ite_eq_left hb₂, ite_eq_left (htr₁.dvd_b₂_iff.mp hb₂)]
      refine ⟨rfl, fun o o' ho _ => absurd ho (by simp), fun c c' hc hc' => ?_⟩
      rw [Except.ok.injEq] at hc hc'
      subst hc; subst hc'
      exact htr.mono (by omega)
    · rw [ite_eq_right hb₂, ite_eq_right fun hc => hb₂ (htr₁.dvd_b₂_iff.mpr hc)]
      refine ⟨rfl, fun o o' ho ho' => ?_, fun c c' hc _ => absurd hc (by simp)⟩
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      exact ⟨by simp only [KodairaSymbol.I.injEq]; exact hnat, by rw [hpoly, hnat]⟩
  · have hdvd' : ¬ ϖ ∣ W'.Δ := fun hc => hdvd (h₁.dvd_Δ_iff.mpr hc)
    rw [run_eq_of_not_dvd_Δ ϖ hdvd, run_eq_of_not_dvd_Δ ϖ hdvd']
    refine ⟨rfl, ?_, ?_⟩
    · intro o o' ho ho'
      rw [Except.error.injEq] at ho ho'
      subst ho; subst ho'
      exact ⟨rfl, rfl⟩
    · intro c c' hc
      exact absurd hc (by simp)

end TateAlgorithm.Step2

end WeierstrassCurve
