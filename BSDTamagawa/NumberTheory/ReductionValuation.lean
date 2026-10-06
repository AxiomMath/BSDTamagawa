/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TatePositivity

/-!
# Trivial reduction type at discriminant valuation at most one

For a Weierstrass curve over `ℤ_p` with `Δ ≠ 0`, if `p² ∤ Δ` then Tate's algorithm terminates at
Step 1 (good reduction `I₀`) or Step 2 (multiplicative reduction `I₁`), in both cases with Tamagawa
number `1`, so the reduction datum lies in the trivial set `𝒦₀`. Contrapositively, a reduction type
outside `𝒦₀` forces `p² ∣ Δ`. No minimality hypothesis is needed. The converse fails for
non-minimal models: `a₄ = p⁴`, `a₆ = p⁶` gives `I₀` with `v_p(Δ) = 12`.

## Main results

* `pow_dvd_ofShortNF_Δ_iff`: `pⁿ` divides the discriminant over `ℤ_p` iff it does over `ℤ`.
* `step11_error_of_step2`: a terminating output of Step 2 is the output of Step 11.
* `run_kodairaSymbol_tamagawaNumber_of_not_sq_dvd`: if `p² ∤ Δ`, the output of Tate's algorithm is
  `(I₀, 1)` or `(I₁, 1)`.
* `run_mem_K0_of_not_sq_dvd`: if `p² ∤ Δ`, the output of Tate's algorithm lies in `𝒦₀`.
* `tauZ_mem_K0_of_not_sq_dvd`: if `p² ∤ Δ(a₄, a₆)` over `ℤ`, then `τ_p(a₄, a₆) ∈ 𝒦₀`.
-/

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-- For integers `a₄`, `a₆`, `pⁿ ∣ Δ(E(a₄, a₆))` over `ℤ_p` iff `pⁿ ∣ Δ(E(a₄, a₆))` over `ℤ`. -/
lemma pow_dvd_ofShortNF_Δ_iff (a₄ a₆ : ℤ) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ (ofShortNF (a₄ : ℤ_[p]) (a₆ : ℤ_[p])).Δ ↔
      (p ^ n : ℤ) ∣ (ofShortNF a₄ a₆).Δ := by
  rw [ofShortNF_Δ_intCast]
  exact_mod_cast PadicInt.pow_p_dvd_int_iff n ((ofShortNF a₄ a₆).Δ)

/-- Monadic bind of `Except` on a success value: `ok a >>= f = f a`. -/
lemma except_ok_bind.{u} {ε α β : Type u} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- If Step 1 of Tate's algorithm terminates with output `out`, so does Step 2. -/
lemma step2_error_of_step1 {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}
    (s1 : Step1.run (p : ℤ_[p]) W = Except.error out) :
    Step2.run (p : ℤ_[p]) W = Except.error out := by
  rw [Step2.run.eq_def, s1]
  rfl

/-- If Step 2 of Tate's algorithm terminates with output `out`, so does Step 11. -/
lemma step11_error_of_step2 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    {out : Output ℤ_[p]} (s2 : Step2.run (p : ℤ_[p]) W = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  have h6 : Step6.run (p : ℤ_[p]) W = Except.error out := by
    rw [Step6.run.eq_def, Step5.run.eq_def, Step4.run.eq_def, Step3.run.eq_def, s2]
    rfl
  have h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step7.run.eq_def]
    split
    next out' heq => exact (h6.symm.trans heq).symm
    next W' heq => exact absurd (h6.symm.trans heq) (by simp)
  rw [Step11.run.eq_def, Step10.run.eq_def, Step9.run.eq_def, Step8.run.eq_def, h7]
  rfl

/-- If `p² ∤ Δ` (equivalently `v_p(Δ) ≤ 1`), the output of Tate's algorithm has Kodaira symbol
`I₀` and Tamagawa number `1` (good reduction) or Kodaira symbol `I₁` and Tamagawa number `1`
(multiplicative reduction). -/
lemma run_kodairaSymbol_tamagawaNumber_of_not_sq_dvd {W : WeierstrassCurve ℤ_[p]}
    (hΔ : W.Δ ≠ 0) (hnd : ¬ (p : ℤ_[p]) ^ 2 ∣ W.Δ) :
    (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 0 ∧
        (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 ∨
      (run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 1 ∧
        (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  by_cases hΔdvd : (p : ℤ_[p]) ∣ W.Δ
  · right
    have hs1 : Step1.run (p : ℤ_[p]) W = Except.ok W := by
      rw [Step1.run.eq_def]
      exact ite_eq_left hΔdvd
    obtain ⟨out, hs2⟩ : ∃ out, Step2.run (p : ℤ_[p]) W = Except.error out := by
      rcases he : Step2.run (p : ℤ_[p]) W with out | W'
      · exact ⟨out, rfl⟩
      · exact absurd (Step2.run_Δ he ▸ (Step2.run_hasValuation he).Δ) hnd
    rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step2 hΔ hs2)]
    rw [Step2.run.eq_def, hs1] at hs2
    simp only [except_ok_bind] at hs2
    by_cases hb : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₂
    · rw [ite_eq_left hb] at hs2
      exact absurd hs2 (by simp)
    · rw [ite_eq_right hb] at hs2
      obtain rfl := Except.error.inj hs2
      have hn1 : emultiplicity (p : ℤ_[p]) W.Δ = 1 := by
        simpa using
          emultiplicity_eq_of_dvd_of_not_dvd (k := 1) (by simpa using hΔdvd) (by simpa using hnd)
      exact ⟨by simp [hn1], by simp [hn1, odd_one]⟩
  · left
    have hs1 : Step1.run (p : ℤ_[p]) W = Except.error ⟨W, .I 0, 1⟩ := by
      rw [Step1.run.eq_def]
      exact ite_eq_right hΔdvd
    rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ
      (step11_error_of_step2 hΔ (step2_error_of_step1 hs1))]
    exact ⟨rfl, rfl⟩

/-- If `p² ∤ Δ`, the pair (Kodaira symbol, Tamagawa number) of the output of Tate's algorithm lies
in the trivial set `𝒦₀`. -/
@[bsd_tamagawa "T018i"]
lemma run_mem_K0_of_not_sq_dvd {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (hnd : ¬ (p : ℤ_[p]) ^ 2 ∣ W.Δ) :
    ((run PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol,
      (run PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber) ∈ K0 := by
  rcases run_kodairaSymbol_tamagawaNumber_of_not_sq_dvd hΔ hnd with h | h <;> simp [K0, h.1, h.2]

/-- If `p² ∤ Δ(E(a₄, a₆))` over `ℤ`, the pair (Kodaira symbol, Tamagawa number) of `τ_p(a₄, a₆)`
lies in the trivial set `𝒦₀`. -/
lemma tauZ_mem_K0_of_not_sq_dvd (p : ℕ) [Fact p.Prime] (a₄ a₆ : ℤ)
    (hnd : ¬ (p ^ 2 : ℤ) ∣ (ofShortNF a₄ a₆).Δ) :
    ((tauZ p a₄ a₆).kodairaSymbol, (tauZ p a₄ a₆).tamagawaNumber) ∈ K0 := by
  have hΔℤ : (ofShortNF a₄ a₆).Δ ≠ 0 := fun h => hnd (h ▸ dvd_zero _)
  rw [tauZ, dite_eq_left hΔℤ]
  exact run_mem_K0_of_not_sq_dvd _ (mt (pow_dvd_ofShortNF_Δ_iff a₄ a₆ 2).mp hnd)

end WeierstrassCurve
