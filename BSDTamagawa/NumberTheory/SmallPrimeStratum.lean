/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.SmallPrimeTailDecay
public import BSDTamagawa.NumberTheory.TateTailLaw

/-!
# The split-multiplicative stratum at `p = 2, 3`

If Tate's algorithm answers `I_n` with `n ≥ 1` on a Weierstrass model, then the number `r` of
Step-11 passes it made satisfies `v_ϖ(c₄) = 4r` and `v_ϖ(Δ) = n + 12r`, with no minimality
hypothesis and no hypothesis on the residue characteristic. On the short plane, where `c₄ = -48a₄`
and `Δ = -16(4a₄³ + 27a₆²)`, this pins the valuations of `a₄`, `a₆` and `Δ` at every point of the
stratum `τ_p⁻¹((I_t, t))` at `p = 2` and `p = 3`.

## Main results

* `WeierstrassCurve.TateAlgorithm.exists_pass_count_of_run_kodairaSymbol_eq_I`: if Tate's algorithm
  answers `I_n` with `n ≥ 1`, then for some `r`, `v_ϖ(c₄) = 4r` and `v_ϖ(Δ) = n + 12r`.
* `WeierstrassCurve.exists_emultiplicity_of_mem_stratFibre_three`: at `p = 3`, every point of
  `τ_3⁻¹((I_t, t))` with `t ≥ 5` satisfies, for some `s`, `v₃(a₄) = 4s + 3`, `v₃(a₆) = 6s + 3` and
  `v₃(Δ) = t + 12s + 12`.
* `WeierstrassCurve.exists_emultiplicity_of_mem_stratFibre_two`: at `p = 2`, likewise
  `v₂(a₄) = 4s`, `v₂(a₆) = 6s + 1` and `v₂(Δ) = t + 12s + 12`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

universe u

/-! ### The exact Step-11 pass count of an `I_n` answer -/

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R} {n : ℕ}

omit [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}] in
/-- **Step 1** reports `(I₀, 1)`, so it never reports an `I_n` with `n ≥ 1`. -/
lemma Step1.nodal_of_kodairaSymbol_eq_I (h : Step1.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  obtain rfl : (0 : ℕ) = n := KodairaSymbol.I.inj hn
  exact absurd h1 (by norm_num)

/-- **Step 2** reports `I_n` with `n ≥ 1` only on a model with `ϖ ∤ c₄`, and then `n = v_ϖ(Δ)`. -/
lemma Step2.nodal_of_kodairaSymbol_eq_I (h : Step2.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step1.nodal_of_kodairaSymbol_eq_I h hn h1
  · rw [Step1.run_weierstrassCurve h'] at h
    by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W).b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      have hΔdvd : ϖ ∣ W.Δ := Step1.run_Δ h'
      refine ⟨fun hc₄ => hb₂ (Step2.dvd_translate_b₂_of_dvd_c₄ hΔdvd hc₄), ?_⟩
      have hcast : KodairaSymbol.I ((emultiplicity ϖ (Step2.translate ϖ W).Δ).toNat)
          = KodairaSymbol.I n := hn
      have htoNat : (emultiplicity ϖ W.Δ).toNat = n := by
        rw [← Step2.translate_Δ (ϖ := ϖ) (W := W)]
        exact KodairaSymbol.I.inj hcast
      have hne : emultiplicity ϖ W.Δ ≠ ⊤ := by
        intro htop
        rw [htop, ENat.toNat_top] at htoNat
        omega
      rw [← htoNat, ENat.natCast_toNat hne]

/-- **Step 3** reports `II`, never an `I_n`. -/
lemma Step3.nodal_of_kodairaSymbol_eq_I (h : Step3.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.nodal_of_kodairaSymbol_eq_I h hn h1
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 4** reports `III`, never an `I_n`. -/
lemma Step4.nodal_of_kodairaSymbol_eq_I (h : Step4.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.nodal_of_kodairaSymbol_eq_I h hn h1
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 5** reports `IV`, never an `I_n`. -/
lemma Step5.nodal_of_kodairaSymbol_eq_I (h : Step5.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.nodal_of_kodairaSymbol_eq_I h hn h1
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hn

/-- **Step 6** reports `I₀*`, which is `KodairaSymbol.I! 0` and never an `I_n`. -/
lemma Step6.nodal_of_kodairaSymbol_eq_I (h : Step6.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.nodal_of_kodairaSymbol_eq_I h hn h1
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

variable [IsNoetherianRing R] [IsDomain R] (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- **Step 7** never reports an `I_n` with `n ≥ 1`: an error there is inherited from an earlier
step or comes from its `I_n*` subprocedure. -/
lemma Step7.nodal_of_kodairaSymbol_eq_I (h : Step7.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.nodal_of_kodairaSymbol_eq_I (heq.trans h) hn h1
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hn ?_
    apply Step7.subprocedure_ne_I

/-- **Step 8** reports `IV*`, never an `I_n`. -/
lemma Step8.nodal_of_kodairaSymbol_eq_I (h : Step8.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.nodal_of_kodairaSymbol_eq_I hϖ hΔ h hn h1
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hn

/-- **Step 9** reports `III*`, never an `I_n`. -/
lemma Step9.nodal_of_kodairaSymbol_eq_I (h : Step9.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.nodal_of_kodairaSymbol_eq_I hϖ hΔ h hn h1
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 10** reports `II*`, never an `I_n`. -/
lemma Step10.nodal_of_kodairaSymbol_eq_I (h : Step10.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.nodal_of_kodairaSymbol_eq_I hϖ hΔ h hn h1
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 11** constructs no output, so an error there is inherited from Step 10. -/
lemma Step11.nodal_of_kodairaSymbol_eq_I (h : Step11.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) (h1 : 1 ≤ n) :
    ¬ ϖ ∣ W.c₄ ∧ emultiplicity ϖ W.Δ = (n : ℕ∞) := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.nodal_of_kodairaSymbol_eq_I hϖ hΔ h hn h1
  · simp at h

/-- For every `n ≥ 1`, an `I_n` answer of `run` has `v_ϖ(c₄) = 4r` and `v_ϖ(Δ) = n + 12r` for some
`r`. -/
theorem run_exists_pass_count_forall :
    ∀ n : ℕ, 1 ≤ n → (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I n →
      ∃ r : ℕ, emultiplicity ϖ W.c₄ = ((4 * r : ℕ) : ℕ∞) ∧
        emultiplicity ϖ W.Δ = ((n + 12 * r : ℕ) : ℕ∞) := by
  induction W, hΔ using run.induct hϖ with
  | case1 W hΔ out h =>
    intro n h1 hn
    rw [run_eq_of_step11_error hϖ hΔ h] at hn
    obtain ⟨hc₄, hΔv⟩ := Step11.nodal_of_kodairaSymbol_eq_I hϖ hΔ h hn h1
    exact ⟨0, by simpa using emultiplicity_eq_zero.2 hc₄, by simpa using hΔv⟩
  | case2 W hΔ W' h ih =>
    intro n h1 hn
    have hΔ' : W'.Δ ≠ 0 := fun h0 ↦ hΔ (by rw [← Step11.run_Δ hϖ hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok hϖ hΔ h hΔ'] at hn
    obtain ⟨r, hc, hd⟩ := ih n h1 hn
    have hprime : Prime ϖ := Ideal.IsMaximal.prime hϖ
    refine ⟨r + 1, ?_, ?_⟩
    · rw [← Step11.run_c₄ hϖ hΔ h, emultiplicity_mul hprime,
        emultiplicity_pow_self_of_prime hprime, hc]
      push_cast
      ring
    · rw [← Step11.run_Δ hϖ hΔ h, emultiplicity_mul hprime,
        emultiplicity_pow_self_of_prime hprime, hd]
      push_cast
      ring

/-- **The exact Step-11 pass count of an `I_n` answer.** If Tate's algorithm answers `I_n` with
`n ≥ 1` on a model `W`, then for some `r`

  `v_ϖ(c₄(W)) = 4r`  and  `v_ϖ(Δ(W)) = n + 12r`. -/
theorem exists_pass_count_of_run_kodairaSymbol_eq_I {n : ℕ} (h1 : 1 ≤ n)
    (hn : (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I n) :
    ∃ r : ℕ, emultiplicity ϖ W.c₄ = ((4 * r : ℕ) : ℕ∞) ∧
      emultiplicity ϖ W.Δ = ((n + 12 * r : ℕ) : ℕ∞) :=
  run_exists_pass_count_forall hϖ hΔ n h1 hn

end WeierstrassCurve.TateAlgorithm

/-! ### Valuation bookkeeping -/

namespace ENat

/-- From `k + m = n` in `ℕ∞` with `k`, `n` natural numbers, `m` is a natural number too. -/
theorem exists_natCast_of_add_eq {k n : ℕ} {m : ℕ∞} (h : (k : ℕ∞) + m = (n : ℕ∞)) :
    ∃ j : ℕ, m = (j : ℕ∞) ∧ k + j = n := by
  have hm : m ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at h
    exact (ENat.natCast_ne_top n) h.symm
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hm
  refine ⟨j, hj.symm, ?_⟩
  rw [← hj] at h
  exact_mod_cast h

/-- From `k + b·m = n` in `ℕ∞` with `k`, `b ≠ 0`, `n` natural numbers, `m` is a natural number. -/
theorem exists_natCast_of_add_mul_eq {k b n : ℕ} (hb : b ≠ 0) {m : ℕ∞}
    (h : (k : ℕ∞) + (b : ℕ∞) * m = (n : ℕ∞)) : ∃ j : ℕ, m = (j : ℕ∞) ∧ k + b * j = n := by
  have hm : m ≠ ⊤ := by
    intro htop
    rw [htop, ENat.mul_top (by exact_mod_cast hb), add_top] at h
    exact (ENat.natCast_ne_top n) h.symm
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hm
  refine ⟨j, hj.symm, ?_⟩
  rw [← hj] at h
  exact_mod_cast h

end ENat

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- `v_p(p^k · u · y) = k + v_p(y)` for a unit `u`. -/
theorem emultiplicity_pow_mul_unit_mul (k : ℕ) {u : ℤ_[p]} (hu : IsUnit u) (y : ℤ_[p]) :
    emultiplicity (p : ℤ_[p]) ((p : ℤ_[p]) ^ k * (u * y))
      = (k : ℕ∞) + emultiplicity (p : ℤ_[p]) y := by
  rw [emultiplicity_mul prime_p, emultiplicity_pow_self_of_prime prime_p,
    emultiplicity_mul prime_p, emultiplicity_eq_zero_of_isUnit hu, zero_add]

/-- `v_p(p^k · u) = k` for a unit `u`. -/
theorem emultiplicity_pow_mul_unit (k : ℕ) {u : ℤ_[p]} (hu : IsUnit u) :
    emultiplicity (p : ℤ_[p]) ((p : ℤ_[p]) ^ k * u) = (k : ℕ∞) := by
  rw [emultiplicity_mul prime_p, emultiplicity_pow_self_of_prime prime_p,
    emultiplicity_eq_zero_of_isUnit hu, add_zero]

/-- **The ultrametric step.** If `v_p(x) = k`, `v_p(x + y) = n` and `k < n`, then `v_p(y) = k`. -/
theorem emultiplicity_eq_of_lt_of_add_eq {x y : ℤ_[p]} {k n : ℕ}
    (hx : emultiplicity (p : ℤ_[p]) x = (k : ℕ∞))
    (hs : emultiplicity (p : ℤ_[p]) (x + y) = (n : ℕ∞)) (hkn : k < n) :
    emultiplicity (p : ℤ_[p]) y = (k : ℕ∞) := by
  by_contra hne
  have hne' : emultiplicity (p : ℤ_[p]) x ≠ emultiplicity (p : ℤ_[p]) y := by
    rw [hx]
    exact fun h => hne h.symm
  rw [emultiplicity_add_eq_min hne', hx] at hs
  have hle : ((n : ℕ∞)) ≤ (k : ℕ∞) := by
    rw [← hs]
    exact min_le_left _ _
  exact absurd (by exact_mod_cast hle : n ≤ k) (by omega)

end PadicInt

/-! ### The stratum at `p = 2` and `p = 3` -/

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-- The Kodaira symbol of Tate's algorithm on the short model of a point of `τ_p⁻¹((I_t, t))` is
`I_t`. -/
theorem run_kodairaSymbol_of_mem_stratFibre {t : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hUp : x ∈ nonsingularLocus p)
    (hx : x ∈ stratFibre p (KodairaSymbol.I t, t)) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hUp).kodairaSymbol
      = KodairaSymbol.I t := by
  have hstrat : strat p ⟨x, hUp⟩ = (KodairaSymbol.I t, t) := (mem_stratFibre_iff hUp).1 hx
  rw [strat] at hstrat
  exact congrArg Prod.fst hstrat

/-- **The pass count on the coefficient plane.** For `t ≥ 1`, every point of `τ_p⁻¹((I_t, t))`
satisfies `v_p(c₄) = 4r` and `v_p(Δ) = t + 12r` for some `r`, at every prime. -/
theorem exists_emultiplicity_c₄_Δ_of_mem_stratFibre {t : ℕ} (ht : 1 ≤ t) {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ stratFibre p (KodairaSymbol.I t, t)) :
    ∃ r : ℕ, emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).c₄ = ((4 * r : ℕ) : ℕ∞) ∧
      emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((t + 12 * r : ℕ) : ℕ∞) :=
  TateAlgorithm.exists_pass_count_of_run_kodairaSymbol_eq_I PadicInt.uniformizer_ne_zero
    (stratFibre_subset _ hx) ht
    (run_kodairaSymbol_of_mem_stratFibre (stratFibre_subset _ hx) hx)

/-- **Where the stratum sits at `p = 3`.** Every point of `τ_3⁻¹((I_t, t))` with `t ≥ 5` satisfies,
for some `s`,

  `v₃(a₄) = 4s + 3`,  `v₃(a₆) = 6s + 3`,  `v₃(Δ) = t + 12s + 12`. -/
theorem exists_emultiplicity_of_mem_stratFibre_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I t, t)) :
    ∃ s : ℕ, emultiplicity (p : ℤ_[p]) x.1 = ((4 * s + 3 : ℕ) : ℕ∞) ∧
      emultiplicity (p : ℤ_[p]) x.2 = ((6 * s + 3 : ℕ) : ℕ∞) ∧
      emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((t + 12 * s + 12 : ℕ) : ℕ∞) := by
  have hodd : Odd p := hp3 ▸ (by decide : Odd 3)
  have h16 : IsUnit (-16 : ℤ_[p]) := PadicInt.isUnit_neg_sixteen hodd
  have h4u : IsUnit (4 : ℤ_[p]) := by simpa using (PadicInt.isUnit_neg_four hodd).neg
  obtain ⟨r, hc₄, hΔ⟩ := exists_emultiplicity_c₄_Δ_of_mem_stratFibre (by omega : 1 ≤ t) hx
  have hc₄' : (1 : ℕ∞) + emultiplicity (p : ℤ_[p]) x.1 = ((4 * r : ℕ) : ℕ∞) := by
    rw [← hc₄, ofShortNF_c₄,
      show -(48 : ℤ_[p]) * x.1 = (p : ℤ_[p]) ^ 1 * (-16 * x.1) by subst hp3; push_cast; ring,
      PadicInt.emultiplicity_pow_mul_unit_mul 1 h16]
    norm_num
  obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 1) (n := 4 * r) (by
    exact_mod_cast hc₄')
  have hr1 : 1 ≤ r := by omega
  refine ⟨r - 1, ?_, ?_, ?_⟩
  · rw [hj, show j = 4 * (r - 1) + 3 by omega]
  · have hsum : emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2)
        = ((t + 12 * r : ℕ) : ℕ∞) := by
      rw [← hΔ, ofShortNF_Δ,
        show (-16 : ℤ_[p]) * (4 * x.1 ^ 3 + 27 * x.2 ^ 2)
          = (p : ℤ_[p]) ^ 0 * (-16 * (4 * x.1 ^ 3 + 27 * x.2 ^ 2)) by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 0 h16]
      norm_num
    have hcube : emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3) = ((12 * r - 3 : ℕ) : ℕ∞) := by
      rw [show (4 : ℤ_[p]) * x.1 ^ 3 = (p : ℤ_[p]) ^ 0 * (4 * x.1 ^ 3) by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 0 h4u, emultiplicity_pow PadicInt.prime_p, hj]
      have : 3 * j = 12 * r - 3 := by omega
      push_cast [← this]
      ring
    have h27 : emultiplicity (p : ℤ_[p]) (27 * x.2 ^ 2) = ((12 * r - 3 : ℕ) : ℕ∞) :=
      PadicInt.emultiplicity_eq_of_lt_of_add_eq hcube hsum (by omega)
    have h27' : emultiplicity (p : ℤ_[p]) (27 * x.2 ^ 2)
        = ((3 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) * emultiplicity (p : ℤ_[p]) x.2 := by
      rw [show (27 : ℤ_[p]) * x.2 ^ 2 = (p : ℤ_[p]) ^ 3 * (1 * x.2 ^ 2) by
          subst hp3; push_cast; ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 3 isUnit_one, emultiplicity_pow PadicInt.prime_p]
    obtain ⟨i, hi, hir⟩ := ENat.exists_natCast_of_add_mul_eq (k := 3) (b := 2)
      (n := 12 * r - 3) two_ne_zero (h27'.symm.trans h27)
    rw [hi, show i = 6 * (r - 1) + 3 by omega]
  · rw [hΔ, show t + 12 * r = t + 12 * (r - 1) + 12 by omega]

/-- **Where the stratum sits at `p = 2`.** Every point of `τ_2⁻¹((I_t, t))` with `t ≥ 5` satisfies,
for some `s`,

  `v₂(a₄) = 4s`,  `v₂(a₆) = 6s + 1`,  `v₂(Δ) = t + 12s + 12`. -/
theorem exists_emultiplicity_of_mem_stratFibre_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I t, t)) :
    ∃ s : ℕ, emultiplicity (p : ℤ_[p]) x.1 = ((4 * s : ℕ) : ℕ∞) ∧
      emultiplicity (p : ℤ_[p]) x.2 = ((6 * s + 1 : ℕ) : ℕ∞) ∧
      emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((t + 12 * s + 12 : ℕ) : ℕ∞) := by
  have h3 : IsUnit (-3 : ℤ_[p]) := by
    have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 3) (by rw [hp2]; norm_num)
    simpa using h.neg
  have h27 : IsUnit (27 : ℤ_[p]) := by
    have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 27) (by rw [hp2]; norm_num)
    simpa using h
  have hm1 : IsUnit (-1 : ℤ_[p]) := (isUnit_one (M := ℤ_[p])).neg
  obtain ⟨r, hc₄, hΔ⟩ := exists_emultiplicity_c₄_Δ_of_mem_stratFibre (by omega : 1 ≤ t) hx
  have hc₄' : ((4 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) x.1 = ((4 * r : ℕ) : ℕ∞) := by
    rw [← hc₄, ofShortNF_c₄,
      show -(48 : ℤ_[p]) * x.1 = (p : ℤ_[p]) ^ 4 * (-3 * x.1) by subst hp2; push_cast; ring,
      PadicInt.emultiplicity_pow_mul_unit_mul 4 h3]
  obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 4) (n := 4 * r) hc₄'
  have hr1 : 1 ≤ r := by omega
  refine ⟨r - 1, ?_, ?_, ?_⟩
  · rw [hj, show j = 4 * (r - 1) by omega]
  · have hsum : emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2)
        = ((t + 12 * r - 4 : ℕ) : ℕ∞) := by
      have hkey : ((4 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2)
          = ((t + 12 * r : ℕ) : ℕ∞) := by
        rw [← hΔ, ofShortNF_Δ,
          show (-16 : ℤ_[p]) * (4 * x.1 ^ 3 + 27 * x.2 ^ 2)
            = (p : ℤ_[p]) ^ 4 * (-1 * (4 * x.1 ^ 3 + 27 * x.2 ^ 2)) by
              subst hp2; push_cast; ring,
          PadicInt.emultiplicity_pow_mul_unit_mul 4 hm1]
      obtain ⟨l, hl, hlr⟩ := ENat.exists_natCast_of_add_eq (k := 4) (n := t + 12 * r) hkey
      rw [hl, show l = t + 12 * r - 4 by omega]
    have hcube : emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3) = ((12 * r - 10 : ℕ) : ℕ∞) := by
      rw [show (4 : ℤ_[p]) * x.1 ^ 3 = (p : ℤ_[p]) ^ 2 * (1 * x.1 ^ 3) by
          subst hp2; push_cast; ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 2 isUnit_one, emultiplicity_pow PadicInt.prime_p,
        hj]
      have : 2 + 3 * j = 12 * r - 10 := by omega
      push_cast [← this]
      ring
    have h27sq : emultiplicity (p : ℤ_[p]) (27 * x.2 ^ 2) = ((12 * r - 10 : ℕ) : ℕ∞) :=
      PadicInt.emultiplicity_eq_of_lt_of_add_eq hcube hsum (by omega)
    have h27' : emultiplicity (p : ℤ_[p]) (27 * x.2 ^ 2)
        = ((0 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) * emultiplicity (p : ℤ_[p]) x.2 := by
      rw [show (27 : ℤ_[p]) * x.2 ^ 2 = (p : ℤ_[p]) ^ 0 * (27 * x.2 ^ 2) by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 0 h27, emultiplicity_pow PadicInt.prime_p]
    obtain ⟨i, hi, hir⟩ := ENat.exists_natCast_of_add_mul_eq (k := 0) (b := 2)
      (n := 12 * r - 10) two_ne_zero (h27'.symm.trans h27sq)
    rw [hi, show i = 6 * (r - 1) + 1 by omega]
  · rw [hΔ, show t + 12 * r = t + 12 * (r - 1) + 12 by omega]

end WeierstrassCurve
