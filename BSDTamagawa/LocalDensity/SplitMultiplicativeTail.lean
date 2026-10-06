/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.DegreeBound

/-!
# Split-multiplicative description of the tail

For a prime `p` and a local Tamagawa number `t ≥ 5`, the fibre of the reduction datum over `t` is
the single split-multiplicative stratum:

  `τ_p⁻¹({K ∈ 𝒦 : c(K) = t}) = τ_p⁻¹((I_t, t))`   for `t ≥ 5`.

Every output of Tate's algorithm has Kodaira symbol `I_c` or Tamagawa number `c ≤ 4`. The only
unbounded Tamagawa number occurs at Step 2, on the split multiplicative branch, where the datum is
`(I_n, n)`; non-split `I_n` has `c ∈ {1, 2}`. Among the additive terminal states, the only bound
with content is at Step 6 (`I₀*`), where `c = 1 + #{distinct roots of a cubic over 𝔽_p} ≤ 4`. The
threshold `5` is sharp, since the `Iₙ*` strata attain `c = 4`.

## Main results

* `WeierstrassCurve.TateAlgorithm.run_tail_dichotomy`: every output of Tate's algorithm satisfies
  `κ = I_c` or `c ≤ 4`.
* `WeierstrassCurve.tauP_preimage_tamagawaNumber`: `{W : c(τ_p(W)) = t} = τ_p⁻¹((I_t, t))` for
  `t ≥ 5`.
* `WeierstrassCurve.iUnion_stratFibre_eq_stratFibre`: `⋃_κ τ_p⁻¹(κ, t) = τ_p⁻¹(I_t, t)` on the
  coefficient plane, for `t ≥ 5`.
* `WeierstrassCurve.δ_eq_deltaP_I`: `δ_p(t) = δ_p((I_t, t))` for `t ≥ 5`.

## Implementation notes

`KodairaSymbol` has no split field; the splitness of a multiplicative fibre is carried by the pair
`(κ, c)`, so "the reduction datum is `(I_t, t)`" is the assertion that the fibre is split
multiplicative of type `I_t`.
-/

@[expose] public section

universe u

open MeasureTheory

/-! ### The tail dichotomy at every terminal state of Tate's algorithm -/

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R}

omit [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}] in
/-- An output of Step 1 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`: it is good reduction
`(I₀, 1)`. -/
lemma Step1.tail_dichotomy (h : Step1.run ϖ W = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  exact Or.inr (by norm_num)

/-- An output of Step 2 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`: it is multiplicative
reduction `Iₙ`, with `c = n` if the tangent quadratic at the node splits over the residue field and
`c ∈ {1, 2}` otherwise. -/
lemma Step2.tail_dichotomy (h : Step2.run ϖ W = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step1.tail_dichotomy h
  · rw [Step1.run_weierstrassCurve h'] at h
    by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W).b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (by norm_num)
      · exact Or.inr (by norm_num)

/-- An output of Steps 1–3 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 3 itself
outputs `II` with `c = 1`. -/
lemma Step3.tail_dichotomy (h : Step3.run ϖ W = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.tail_dichotomy h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (by norm_num)

/-- An output of Steps 1–4 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 4 itself
outputs `III` with `c = 2`. -/
lemma Step4.tail_dichotomy (h : Step4.run ϖ W = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.tail_dichotomy h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (by norm_num)

/-- An output of Steps 1–5 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 5 itself
outputs `IV` with `c ∈ {1, 3}`. -/
lemma Step5.tail_dichotomy (h : Step5.run ϖ W = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.tail_dichotomy h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Or.inr (by norm_num)

/-- An output of Steps 1–6 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 6 itself
outputs `I₀*` with `c = 1 + #{distinct roots of a cubic over R ⧸ (ϖ)} ≤ 4`. -/
lemma Step6.tail_dichotomy (h : Step6.run ϖ W = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.tail_dichotomy h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    classical
    exact Or.inr (Nat.add_le_add_left Cubic.card_roots_le 1)

variable [IsNoetherianRing R] [IsDomain R]

/-- Every output of the `Iₙ*` subprocedure of Step 7 has Tamagawa number at most `4`. -/
lemma Step7.subprocedure_tail_dichotomy (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol
        = KodairaSymbol.I (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber ∨
      (Step7.subprocedure hϖ hΔ hn hW ha₂).tamagawaNumber ≤ 4 := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => exact Or.inr (by split_ifs <;> norm_num)
  | case3 => exact Or.inr (by split_ifs <;> norm_num)

/-- An output of Steps 1–7 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`. -/
lemma Step7.tail_dichotomy (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (h : Step7.run hϖ hΔ = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.tail_dichotomy (heq.trans h)
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact Step7.subprocedure_tail_dichotomy ..

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- An output of Steps 1–8 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 8 itself
outputs `IV*` with `c ∈ {1, 3}`. -/
lemma Step8.tail_dichotomy (h : Step8.run hϖ hΔ = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.tail_dichotomy hϖ hΔ h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact Or.inr (by norm_num)

/-- An output of Steps 1–9 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 9 itself
outputs `III*` with `c = 2`. -/
lemma Step9.tail_dichotomy (h : Step9.run hϖ hΔ = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.tail_dichotomy hϖ hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (by norm_num)

/-- An output of Steps 1–10 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 10 itself
outputs `II*` with `c = 1`. -/
lemma Step10.tail_dichotomy (h : Step10.run hϖ hΔ = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.tail_dichotomy hϖ hΔ h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    exact Or.inr (by norm_num)

/-- An output of Steps 1–11 of Tate's algorithm satisfies `κ = I_c` or `c ≤ 4`; Step 11 itself
produces no output. -/
lemma Step11.tail_dichotomy (h : Step11.run hϖ hΔ = Except.error out) :
    out.kodairaSymbol = KodairaSymbol.I out.tamagawaNumber ∨ out.tamagawaNumber ≤ 4 := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.tail_dichotomy hϖ hΔ h
  · simp at h

/-- Every output of Tate's algorithm either has Kodaira symbol `I_c`, i.e. is the
split-multiplicative datum `(I_c, c)`, or has Tamagawa number `c ≤ 4`. -/
theorem run_tail_dichotomy :
    (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I (run hϖ hΔ).tamagawaNumber ∨
      (run hϖ hΔ).tamagawaNumber ≤ 4 := by
  induction W, hΔ using run.induct hϖ with
  | case1 W hΔ out h => rw [run_eq_of_step11_error hϖ hΔ h]; exact Step11.tail_dichotomy hϖ hΔ h
  | case2 W hΔ W' h ih =>
    have hΔ' : W'.Δ ≠ 0 := fun h0 ↦ hΔ (by rw [← Step11.run_Δ hϖ hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok hϖ hΔ h hΔ']
    exact ih

/-- If Tate's algorithm reports a Tamagawa number `c ≥ 5`, its Kodaira symbol is `I_c`. -/
theorem run_kodairaSymbol_eq_I_of_five_le (h5 : 5 ≤ (run hϖ hΔ).tamagawaNumber) :
    (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I (run hϖ hΔ).tamagawaNumber := by
  rcases run_tail_dichotomy hϖ hΔ with h | h
  · exact h
  · omega

end WeierstrassCurve.TateAlgorithm

/-! ### The tail on the space of models and on the coefficient plane -/

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-- If the local Tamagawa number `c` of a nonsingular short model over `ℤ_p` is at least `5`, its
Kodaira symbol is `I_c`. -/
theorem tauP_kodairaSymbol_eq_I_of_five_le {W : ShortNF.Elliptic ℤ_[p]}
    (h5 : 5 ≤ (tauP p W).tamagawaNumber) :
    (tauP p W).kodairaSymbol = KodairaSymbol.I (tauP p W).tamagawaNumber :=
  TateAlgorithm.run_kodairaSymbol_eq_I_of_five_le PadicInt.uniformizer_ne_zero W.property h5

/-- For `t ≥ 5` the fibre of the local Tamagawa number over `t` is the single reduction-datum fibre
`τ_p⁻¹((I_t, t))`: `{W : c(τ_p(W)) = t} = τ_p⁻¹((I_t, t))`. -/
@[bsd_tamagawa "T021b"]
theorem tauP_preimage_tamagawaNumber {t : ℕ} (ht : 5 ≤ t) :
    {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = t}
      = {W : ShortNF.Elliptic ℤ_[p] |
          ((tauP p W).kodairaSymbol, (tauP p W).tamagawaNumber) = (KodairaSymbol.I t, t)} := by
  ext W
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  rw [← h]
  exact tauP_kodairaSymbol_eq_I_of_five_le (by rw [h]; exact ht)

/-- At a point of the coefficient plane with Tamagawa number `c ≥ 5`, the reduction datum is
`(I_c, c)`. -/
theorem strat_eq_I_of_five_le {x : ↥(nonsingularLocus p)} (ht : 5 ≤ (strat p x).2) :
    strat p x = (KodairaSymbol.I (strat p x).2, (strat p x).2) :=
  Prod.ext (TateAlgorithm.run_kodairaSymbol_eq_I_of_five_le PadicInt.uniformizer_ne_zero
    x.property ht) rfl

/-- For `t ≥ 5` the union over the Kodaira symbol of the strata `τ_p⁻¹(κ, t)` on the coefficient
plane is its single `κ = I_t` term: `⋃_κ τ_p⁻¹(κ, t) = τ_p⁻¹(I_t, t)`. -/
@[bsd_tamagawa "T021b"]
theorem iUnion_stratFibre_eq_stratFibre {t : ℕ} (ht : 5 ≤ t) :
    (⋃ κ : KodairaSymbol, stratFibre p (κ, t)) = stratFibre p (KodairaSymbol.I t, t) := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun κ x hx => ?_)
    (Set.subset_iUnion (fun κ : KodairaSymbol => stratFibre p (κ, t)) (KodairaSymbol.I t))
  have hU : x ∈ nonsingularLocus p := stratFibre_subset _ hx
  have h2 : (strat p ⟨x, hU⟩).2 = t := by rw [(mem_stratFibre_iff hU).1 hx]
  exact (mem_stratFibre_iff hU).2 (by rw [strat_eq_I_of_five_le (h2 ▸ ht), h2])

/-- For `t ≥ 5`, `δ_p(t) = δ_p((I_t, t))`. -/
theorem δ_eq_deltaP_I {t : ℕ} (ht : 5 ≤ t) : δ p t = deltaP p (KodairaSymbol.I t, t) := by
  rw [← volume_iUnion_stratFibre_kodaira t, iUnion_stratFibre_eq_stratFibre ht, volume_stratFibre]

end WeierstrassCurve
