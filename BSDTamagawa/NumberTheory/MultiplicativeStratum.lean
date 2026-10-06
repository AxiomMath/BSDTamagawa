/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.PadicHaar
public import BSDTamagawa.NumberTheory.ReductionValuation
public import BSDTamagawa.NumberTheory.TateCongruence

/-!
# The level-`t` split-multiplicative stratum

For a *nodal* model `W` over `ℤ_p` — one with `p ∣ Δ` and `p ∤ c₄` — Tate's algorithm terminates
at Step 2, and this file reads off its output at arbitrary discriminant depth. For `t ≥ 3`, the
split-multiplicative reduction datum of the Tate output is characterised by

  datum `(I_t, t)`  ↔  the tangent quadratic splits over the residue field and `v_p(Δ) = t`.

At an odd prime the splitting condition is equivalent to `-c₆` being a square in the residue field.

## Main definitions

* `WeierstrassCurve.TateAlgorithm.Step2.TangentSplits`: the tangent quadratic `Y² + a₁Y - a₂` of
  the Step-2 translate splits over the residue field.

## Main results

* `WeierstrassCurve.run_eq_step2_output_of_nodal`: at a nodal model the Tate output is
  `⟨translate, I_n, if TangentSplits then n else if Odd n then 1 else 2⟩` with `n = v_p(Δ)`.
* `WeierstrassCurve.run_kodaira_tamagawa_of_tangentSplits`: a nodal, split model with
  `v_p(Δ) = t ≥ 1` has reduction datum `(I_t, t)`.
* `WeierstrassCurve.run_kodaira_tamagawa_eq_iff_of_nodal`: for a nodal model and `t ≥ 3`, the
  reduction datum is `(I_t, t)` iff `v_p(Δ) = t` and the tangent quadratic splits.
* `WeierstrassCurve.TateAlgorithm.Step2.tangentSplits_iff_isSquare_neg_c₆`: away from residue
  characteristic `2`, the tangent quadratic of a nodal model splits iff `-c₆` is a square in the
  residue field.
* `WeierstrassCurve.run_kodaira_tamagawa_eq_iff_isSquare`: at an odd prime, for a nodal model and
  `t ≥ 3`, the reduction datum is `(I_t, t)` iff `v_p(Δ) = t` and `-c₆` is a square modulo `p`.

## Implementation notes

The non-split branch of Step 2 reports `(I_t, 1)` or `(I_t, 2)`, which coincide with `(I_t, t)` at
`t = 1` and `t = 2`; hence the hypothesis `t ≥ 3`.

The hypothesis `p ∤ c₄` cannot be dropped: Step 11 divides a non-minimal model by `ϖ^12`, so for
instance `(p⁴a₄, p⁶a₆)` has `v_p(Δ) = 12 + v_p(Δ(a₄, a₆))` and the same reduction datum as
`(a₄, a₆)`. The characterisation is therefore one of the nodal part `τ_p⁻¹(I_t, t) ∩ {p ∤ c₄}` of
the stratum.
-/

@[expose] public section

universe u

namespace WeierstrassCurve.TateAlgorithm.Step2

open Ideal Polynomial

variable {R : Type u} [CommRing R] (ϖ : R) [(span {ϖ}).IsMaximal]
  [PerfectField (R ⧸ span {ϖ})] (W : WeierstrassCurve R)

/-- **The split test of Step 2 of Tate's algorithm**: the tangent quadratic `Y² + a₁Y - a₂` of the
Step-2 translate of `W`, read over the residue field `R ⧸ (ϖ)`, splits.

At a node the two branches of the special fibre have tangent directions given by the roots of this
quadratic, so it splits exactly when both branches are defined over the residue field — the
classical *split multiplicative* condition. Here `a₂` is the coefficient of the translate, in
which the singular point has been moved to the origin. -/
def TangentSplits : Prop :=
  ((X ^ 2 + C (translate ϖ W).a₁ * X - C (translate ϖ W).a₂).map (CommRing.mod ϖ)).Splits

/-! ### The split test as a square test -/

/-- **Completing the square.** Over a field in which `2 ≠ 0`, the monic quadratic `Y² + aY - b` has
a root exactly when its discriminant `a² + 4b` is a square. -/
lemma exists_sq_add_mul_sub_eq_zero_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (a b : K) :
    (∃ y : K, y ^ 2 + a * y - b = 0) ↔ IsSquare (a ^ 2 + 4 * b) :=
  ⟨fun ⟨y, hy⟩ => ⟨2 * y + a, by linear_combination -4 * hy⟩,
    fun ⟨s, hs⟩ => ⟨(s - a) / 2, by field_simp; linear_combination -hs⟩⟩

/-- **A nonzero element of a field is a square exactly when its cube is.** -/
lemma isSquare_pow_three_iff {K : Type*} [Field K] {y : K} (hy : y ≠ 0) :
    IsSquare (y ^ 3) ↔ IsSquare y :=
  ⟨fun ⟨r, hr⟩ => ⟨r / y, by field_simp; linear_combination hr⟩,
    fun ⟨s, hs⟩ => ⟨s ^ 3, by rw [hs]; ring⟩⟩

section Criterion

variable {ϖ : R} [(span {ϖ}).IsMaximal] [PerfectField (R ⧸ span {ϖ})] {W : WeierstrassCurve R}

open CommRing

/-- The tangent quadratic splits exactly when it has a root in the residue field. -/
lemma tangentSplits_iff_exists_root :
    TangentSplits ϖ W ↔ ∃ y : R ⧸ span {ϖ},
      y ^ 2 + mod ϖ (translate ϖ W).a₁ * y - mod ϖ (translate ϖ W).a₂ = 0 := by
  set a := mod ϖ (translate ϖ W).a₁ with ha
  set b := mod ϖ (translate ϖ W).a₂ with hb
  have hmap : ((X ^ 2 + C (translate ϖ W).a₁ * X - C (translate ϖ W).a₂ : R[X]).map (mod ϖ))
      = X ^ 2 + C a * X - C b := by
    simp [ha, hb]
  have hdeg : ((X : (R ⧸ span {ϖ})[X]) ^ 2 + C a * X - C b).natDegree = 2 := by
    have h : (X : (R ⧸ span {ϖ})[X]) ^ 2 + C a * X - C b = C 1 * X ^ 2 + C a * X + C (-b) := by
      rw [map_neg, C_1, one_mul]
      ring
    rw [h, natDegree_quadratic one_ne_zero]
  have heval : ∀ y : R ⧸ span {ϖ},
      ((X : (R ⧸ span {ϖ})[X]) ^ 2 + C a * X - C b).eval y = y ^ 2 + a * y - b :=
    fun y => by simp
  rw [TangentSplits, hmap]
  refine ⟨fun hf => ?_, fun ⟨y, hy⟩ =>
    Polynomial.Splits.of_natDegree_eq_two hdeg (by rwa [heval])⟩
  obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero (hf.roots_ne_zero (by simp [hdeg]))
  exact ⟨y, heval y ▸ (Polynomial.mem_roots'.1 hy).2⟩

/-- Away from residue characteristic `2`, the tangent quadratic splits exactly when the
translate's `b₂ = a₁² + 4a₂` is a square in the residue field. -/
lemma tangentSplits_iff_isSquare_b₂ (h2 : ¬ ϖ ∣ (2 : R)) :
    TangentSplits ϖ W ↔ IsSquare (mod ϖ (translate ϖ W).b₂) := by
  have h2' : (2 : R ⧸ span {ϖ}) ≠ 0 := by
    rwa [show (2 : R ⧸ span {ϖ}) = mod ϖ 2 by simp only [map_ofNat], Ne, mod_eq_zero]
  have hb : (mod ϖ (translate ϖ W).a₁) ^ 2 + 4 * mod ϖ (translate ϖ W).a₂
      = mod ϖ (translate ϖ W).b₂ := by
    rw [WeierstrassCurve.b₂]
    simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [tangentSplits_iff_exists_root, exists_sq_add_mul_sub_eq_zero_iff h2', hb]

/-- At a nodal model, `ϖ` does not divide the translate's `b₂`. -/
lemma not_dvd_translate_b₂ (hΔ : ϖ ∣ W.Δ) (hc₄ : ¬ ϖ ∣ W.c₄) : ¬ ϖ ∣ (translate ϖ W).b₂ := by
  have hb₄ : ϖ ∣ (translate ϖ W).b₄ := by simpa using (hasValuation_translate hΔ).b₄
  intro h
  refine hc₄ (translate_c₄ ϖ W ▸ ?_)
  rw [WeierstrassCurve.c₄]
  exact dvd_sub (dvd_pow h two_ne_zero) (hb₄.mul_left 24)

/-- **Split multiplicative iff `-c₆` is a square.** At a nodal model away from residue
characteristic `2`, the tangent quadratic splits exactly when `-c₆` is a square in the residue
field. -/
theorem tangentSplits_iff_isSquare_neg_c₆ (hΔ : ϖ ∣ W.Δ) (hc₄ : ¬ ϖ ∣ W.c₄)
    (h2 : ¬ ϖ ∣ (2 : R)) : TangentSplits ϖ W ↔ IsSquare (mod ϖ (-W.c₆)) := by
  have hv := hasValuation_translate hΔ
  have hb₄ : mod ϖ (translate ϖ W).b₄ = 0 := (mod_eq_zero ..).2 (by simpa using hv.b₄)
  have hb₆ : mod ϖ (translate ϖ W).b₆ = 0 := (mod_eq_zero ..).2 (by simpa using hv.b₆)
  have hb₂ : mod ϖ (translate ϖ W).b₂ ≠ 0 :=
    fun h => not_dvd_translate_b₂ hΔ hc₄ ((mod_eq_zero ..).1 h)
  have hc : mod ϖ (-W.c₆) = (mod ϖ (translate ϖ W).b₂) ^ 3 := by
    rw [← translate_c₆ ϖ W, WeierstrassCurve.c₆]
    simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat, hb₄, hb₆]
    ring
  rw [tangentSplits_iff_isSquare_b₂ h2, hc, isSquare_pow_three_iff hb₂]

end Criterion

end WeierstrassCurve.TateAlgorithm.Step2

namespace WeierstrassCurve

open TateAlgorithm Polynomial

variable {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℤ_[p]}

/-! ### Nodal reduction forces termination at Step 2 -/

/-- **A nodal model terminates at Step 2.** If `p ∤ c₄` then Step 2 of Tate's algorithm returns
a final output. -/
lemma exists_step2_error_of_not_dvd_c₄ (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) :
    ∃ out, Step2.run (p : ℤ_[p]) W = Except.error out := by
  rcases he : Step2.run (p : ℤ_[p]) W with out | W'
  · exact ⟨out, rfl⟩
  · exact absurd (Step2.run_c₄ he ▸ (pow_one (p : ℤ_[p]) ▸ (Step2.run_hasValuation he).c₄)) hc₄

/-- **Good reduction is read off Step 1.** If `p ∤ Δ` then Tate's algorithm terminates immediately
with the good-reduction datum `(I₀, 1)`. -/
lemma run_eq_of_not_dvd_Δ (hΔ : W.Δ ≠ 0) (hnd : ¬ (p : ℤ_[p]) ∣ W.Δ) :
    run PadicInt.uniformizer_ne_zero hΔ = ⟨W, KodairaSymbol.I 0, 1⟩ := by
  have hs1 : Step1.run (p : ℤ_[p]) W = Except.error ⟨W, .I 0, 1⟩ := by
    rw [Step1.run.eq_def]; exact ite_eq_right hnd
  exact run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ
    (step11_error_of_step2 hΔ (step2_error_of_step1 hs1))

/-! ### The Tate output at a nodal model -/

open scoped Classical in
/-- **The Tate output at a nodal model is Step 2's output, at every depth.** If `p ∣ Δ` and
`p ∤ c₄` then

  `run W = ⟨translate ϖ W, I_n, if TangentSplits then n else if Odd n then 1 else 2⟩`,
  `n = v_p(Δ)`. -/
theorem run_eq_step2_output_of_nodal (hΔ : W.Δ ≠ 0) (hpΔ : (p : ℤ_[p]) ∣ W.Δ)
    (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) :
    run PadicInt.uniformizer_ne_zero hΔ =
      ⟨Step2.translate (p : ℤ_[p]) W,
        KodairaSymbol.I (emultiplicity (p : ℤ_[p]) W.Δ).toNat,
        if Step2.TangentSplits (p : ℤ_[p]) W then (emultiplicity (p : ℤ_[p]) W.Δ).toNat
          else if Odd (emultiplicity (p : ℤ_[p]) W.Δ).toNat then 1 else 2⟩ := by
  have hs1 : Step1.run (p : ℤ_[p]) W = Except.ok W := by
    rw [Step1.run.eq_def]; exact ite_eq_left hpΔ
  obtain ⟨out, hs2⟩ := exists_step2_error_of_not_dvd_c₄ hc₄
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step2 hΔ hs2)]
  rw [Step2.run.eq_def, hs1] at hs2
  simp only [except_ok_bind] at hs2
  by_cases hb : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂
  · rw [ite_eq_left hb] at hs2; exact absurd hs2 (by simp)
  · rw [ite_eq_right hb] at hs2
    obtain rfl := Except.error.inj hs2
    simp only [Step2.translate_Δ]
    rfl

/-- **The Kodaira symbol at a nodal model** is `I_{v_p(Δ)}`. -/
theorem run_kodairaSymbol_of_nodal (hΔ : W.Δ ≠ 0) (hpΔ : (p : ℤ_[p]) ∣ W.Δ)
    (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) :
    (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol =
      KodairaSymbol.I (emultiplicity (p : ℤ_[p]) W.Δ).toNat := by
  rw [run_eq_step2_output_of_nodal hΔ hpΔ hc₄]

open scoped Classical in
/-- **The Tamagawa number at a nodal model** is `v_p(Δ)` on the split branch and `1` or `2`
otherwise, according as `v_p(Δ)` is odd or even. -/
theorem run_tamagawaNumber_of_nodal (hΔ : W.Δ ≠ 0) (hpΔ : (p : ℤ_[p]) ∣ W.Δ)
    (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) :
    (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber =
      if Step2.TangentSplits (p : ℤ_[p]) W then (emultiplicity (p : ℤ_[p]) W.Δ).toNat
        else if Odd (emultiplicity (p : ℤ_[p]) W.Δ).toNat then 1 else 2 := by
  rw [run_eq_step2_output_of_nodal hΔ hpΔ hc₄]

/-! ### The valuation of `Δ` in `ℕ` and in `ℕ∞` -/

/-- For a nonsingular model, `(emultiplicity p Δ).toNat = t` iff `v_p(Δ) = t` in `ℕ∞`. -/
lemma toNat_emultiplicity_Δ_eq_iff (hΔ : W.Δ ≠ 0) (t : ℕ) :
    (emultiplicity (p : ℤ_[p]) W.Δ).toNat = t ↔ emultiplicity (p : ℤ_[p]) W.Δ = (t : ℕ∞) := by
  have hf : FiniteMultiplicity (p : ℤ_[p]) W.Δ :=
    FiniteMultiplicity.of_span_isMaximal (p : ℤ_[p]) hΔ
  rw [hf.emultiplicity_eq_multiplicity]
  simp

/-- A model with `v_p(Δ) = t` and `t ≥ 1` has `p ∣ Δ`. -/
lemma dvd_Δ_of_emultiplicity_eq {t : ℕ} (ht : 1 ≤ t)
    (hn : emultiplicity (p : ℤ_[p]) W.Δ = (t : ℕ∞)) : (p : ℤ_[p]) ∣ W.Δ := by
  have h := pow_dvd_of_le_emultiplicity (a := (p : ℤ_[p])) (b := W.Δ) (k := 1)
    (by rw [hn]; exact_mod_cast ht)
  rwa [pow_one] at h

/-! ### The split-multiplicative datum `(I_t, t)` -/

/-- A nodal model whose tangent quadratic splits and whose discriminant has valuation `t ≥ 1` has
reduction datum `(I_t, t)`. -/
theorem run_kodaira_tamagawa_of_tangentSplits (hΔ : W.Δ ≠ 0) (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄)
    {t : ℕ} (ht : 1 ≤ t) (hn : emultiplicity (p : ℤ_[p]) W.Δ = (t : ℕ∞))
    (hsplit : Step2.TangentSplits (p : ℤ_[p]) W) :
    (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I t ∧
      (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = t := by
  have hpΔ : (p : ℤ_[p]) ∣ W.Δ := dvd_Δ_of_emultiplicity_eq ht hn
  have hnt : (emultiplicity (p : ℤ_[p]) W.Δ).toNat = t := (toNat_emultiplicity_Δ_eq_iff hΔ t).2 hn
  refine ⟨by rw [run_kodairaSymbol_of_nodal hΔ hpΔ hc₄, hnt], ?_⟩
  rw [run_tamagawaNumber_of_nodal hΔ hpΔ hc₄, hnt]
  exact ite_eq_left hsplit

/-- For a model over `ℤ_p` with `p ∤ c₄` and `t ≥ 3`:

  `τ_p(W) = (I_t, t)`  ↔  `v_p(Δ) = t` and the tangent quadratic splits over the residue field. -/
@[bsd_tamagawa "T021e"]
theorem run_kodaira_tamagawa_eq_iff_of_nodal (hΔ : W.Δ ≠ 0) (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄)
    {t : ℕ} (ht : 3 ≤ t) :
    ((run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I t ∧
        (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = t) ↔
      emultiplicity (p : ℤ_[p]) W.Δ = (t : ℕ∞) ∧ Step2.TangentSplits (p : ℤ_[p]) W := by
  refine ⟨fun ⟨hκ, hc⟩ => ?_, fun ⟨hn, hsplit⟩ =>
    run_kodaira_tamagawa_of_tangentSplits hΔ hc₄ (by omega) hn hsplit⟩
  have hpΔ : (p : ℤ_[p]) ∣ W.Δ := by
    by_contra hnd
    rw [run_eq_of_not_dvd_Δ hΔ hnd] at hκ
    exact absurd (KodairaSymbol.I.inj hκ) (by omega)
  have hnt : (emultiplicity (p : ℤ_[p]) W.Δ).toNat = t := by
    rw [run_kodairaSymbol_of_nodal hΔ hpΔ hc₄] at hκ
    exact KodairaSymbol.I.inj hκ
  refine ⟨(toNat_emultiplicity_Δ_eq_iff hΔ t).1 hnt, ?_⟩
  rw [run_tamagawaNumber_of_nodal hΔ hpΔ hc₄, hnt] at hc
  by_contra hsplit
  rw [ite_eq_right hsplit] at hc
  split_ifs at hc <;> omega

/-! ### The invariant form of the split test -/

/-- At an odd prime, `p ∤ 2` in `ℤ_p`. -/
lemma not_dvd_two_of_odd (hp : Odd p) : ¬ (p : ℤ_[p]) ∣ (2 : ℤ_[p]) :=
  fun h => PadicInt.p_nonunit (isUnit_of_dvd_unit h (PadicInt.isUnit_two hp))

/-- At an odd prime `p`, for a model over `ℤ_p` with `p ∤ c₄` and `t ≥ 3`:

  `τ_p(W) = (I_t, t)`  ↔  `v_p(Δ) = t` and `-c₆` is a square in the residue field. -/
@[bsd_tamagawa "T021e"]
theorem run_kodaira_tamagawa_eq_iff_isSquare (hp : Odd p) (hΔ : W.Δ ≠ 0)
    (hc₄ : ¬ (p : ℤ_[p]) ∣ W.c₄) {t : ℕ} (ht : 3 ≤ t) :
    ((run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I t ∧
        (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = t) ↔
      emultiplicity (p : ℤ_[p]) W.Δ = (t : ℕ∞) ∧
        IsSquare (CommRing.mod (p : ℤ_[p]) (-W.c₆)) := by
  rw [run_kodaira_tamagawa_eq_iff_of_nodal hΔ hc₄ ht]
  refine and_congr_right fun hn => ?_
  exact Step2.tangentSplits_iff_isSquare_neg_c₆ (dvd_Δ_of_emultiplicity_eq (by omega) hn) hc₄
    (not_dvd_two_of_odd hp)

end WeierstrassCurve
