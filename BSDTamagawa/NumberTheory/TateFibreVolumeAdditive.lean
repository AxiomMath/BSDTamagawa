/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.TateFibreVolume

/-!
# The additive strata of the Tate fibre: valuation levels and minimal loci

Table 5 of Griffin–Ono–Tsai assigns a `p`-adic Haar mass `δ_p(K)` to each reduction datum
`K = (Kodaira symbol, Tamagawa number)` of short Weierstrass models over `ℤ_p`. For every prime
`p ≥ 5` this file describes the additive strata `τ_p⁻¹(K)` by congruences from above, and exhibits
explicit loci, of known mass, inside the `(II, 1)` and `(III, 2)` strata.

For each Kodaira symbol `κ`, Tate's algorithm forces `ϖ^i ∣ c₄` and `ϖ^j ∣ c₆` with the exponents
`(i, j)` = (`additiveC₄Level κ`, `additiveC₆Level κ`):

| `κ` | `Iₙ` | `II` | `III` | `IV` | `I₀*` | `Iₙ*` | `IV*` | `III*` | `II*` |
|-----|------|------|-------|------|-------|-------|-------|--------|-------|
| `i` | 0    | 1    | 1     | 2    | 2     | 2     | 2     | 3      | 4     |
| `j` | 0    | 1    | 2     | 2    | 3     | 3     | 3     | 4      | 5     |

On the short plane at `p ≥ 5`, where `c₄ = -48a₄` and `c₆ = -864a₆`, this says that every pair in
the stratum `τ_p⁻¹(K)` has `p^i ∣ a₄` and `p^j ∣ a₆`. To run the algorithm forward on explicit
loci, the branch conditions of Steps 3, 4 and 5, which concern the translated curve, are expressed
through `c₄` and `c₆`, which no translation changes.

## Main definitions

* `WeierstrassCurve.KodairaSymbol.additiveC₄Level`,
  `WeierstrassCurve.KodairaSymbol.additiveC₆Level`: the exponents `i` and `j` of the table above.
* `WeierstrassCurve.stratMinimalII`, `WeierstrassCurve.stratMinimalIII`: the minimal loci
  `{p ∣ a₄} × {v_p(a₆) = 1}` and `{v_p(a₄) = 1} × {p² ∣ a₆}`.

## Main results

* `WeierstrassCurve.TateAlgorithm.pow_dvd_c₄_c₆_run`: for every Weierstrass curve with `Δ ≠ 0`,
  `ϖ^i ∣ c₄` and `ϖ^j ∣ c₆`, where `(i, j)` are the levels of the Kodaira symbol returned by Tate's
  algorithm.
* `WeierstrassCurve.pow_dvd_of_mem_stratFibre_additive`: for `p ≥ 5`, every pair in the stratum
  `τ_p⁻¹(K)` has `p^i ∣ a₄` and `p^j ∣ a₆`.
* `WeierstrassCurve.TateAlgorithm.Step2.dvd_translate_b₂`,
  `WeierstrassCurve.sq_dvd_translate_a₆_iff_sq_dvd_c₆`, `WeierstrassCurve.cb_dvd_b₈_iff_sq_dvd_c₄`,
  `WeierstrassCurve.cb_dvd_b₆_iff_cb_dvd_c₆`: the branch conditions of Steps 2–5 in terms of `c₄`
  and `c₆`.
* `WeierstrassCurve.run_eq_II_of_dvd_of_not_sq_dvd`,
  `WeierstrassCurve.run_eq_III_of_emultiplicity_eq_one`,
  `WeierstrassCurve.run_kodairaSymbol_eq_IV_of_emultiplicity_eq_two`: the reduction data on the
  minimal `II` and `III` loci, and the Kodaira symbol `IV` when `p² ∣ a₄` and `v_p(a₆) = 2`.
* `WeierstrassCurve.stratMinimalII_subset_stratFibre`,
  `WeierstrassCurve.stratMinimalIII_subset_stratFibre`: the minimal loci lie in the `(II, 1)` and
  `(III, 2)` strata.
* `WeierstrassCurve.stratFibre_II_subset_union`: the `(II, 1)` stratum lies in the minimal `II`
  locus together with the range of the weight-`(4, 6)` dilation.

## Implementation notes

The only `ℝ≥0∞` subtraction is `1 - p^{-1}`, whose subtrahend is at most `1`; it appears only in
the masses of the minimal loci.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

universe u

/-! ### The valuation levels of a Kodaira symbol

For each Kodaira symbol these are the exponents `(i, j)` such that an answer of that symbol forces
`ϖ^i ∣ c₄` and `ϖ^j ∣ c₆`. The multiplicative symbols `Iₙ` get `(0, 0)`. -/

namespace WeierstrassCurve.KodairaSymbol

/-- The exponent `i` with which a Kodaira symbol forces `ϖ^i ∣ c₄`. -/
def additiveC₄Level : KodairaSymbol → ℕ
  | .I _ => 0
  | .II => 1
  | .III => 1
  | .IV => 2
  | .I! _ => 2
  | .IV! => 2
  | .III! => 3
  | .II! => 4

/-- The exponent `j` with which a Kodaira symbol forces `ϖ^j ∣ c₆`. -/
def additiveC₆Level : KodairaSymbol → ℕ
  | .I _ => 0
  | .II => 1
  | .III => 2
  | .IV => 2
  | .I! _ => 3
  | .IV! => 3
  | .III! => 4
  | .II! => 5

/-- No symbol demands more than `ϖ⁴ ∣ c₄`. -/
lemma additiveC₄Level_le_four (κ : KodairaSymbol) : κ.additiveC₄Level ≤ 4 := by
  cases κ <;> simp [additiveC₄Level]

/-- No symbol demands more than `ϖ⁶ ∣ c₆`. -/
lemma additiveC₆Level_le_six (κ : KodairaSymbol) : κ.additiveC₆Level ≤ 6 := by
  cases κ <;> simp [additiveC₆Level]

end WeierstrassCurve.KodairaSymbol

/-! ### The valuations of `c₄` and `c₆` forced by each step's answer -/

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R}

omit [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}] in
/-- Step 1 answers `I₀`, whose levels are `(0, 0)`. -/
lemma Step1.pow_dvd_c₄_c₆ (h : Step1.run ϖ W = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  exact ⟨by simp [KodairaSymbol.additiveC₄Level], by simp [KodairaSymbol.additiveC₆Level]⟩

variable [IsNoetherianRing R] [IsDomain R]

omit [IsNoetherianRing R] [IsDomain R] in
/-- **Step 2's answer is always some `Iₙ`.** -/
lemma Step2.exists_kodairaSymbol_eq_I (h : Step2.run ϖ W = Except.error out) :
    ∃ n : ℕ, out.kodairaSymbol = KodairaSymbol.I n := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · rw [Step1.run.eq_def] at h
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact ⟨0, rfl⟩
  · by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W').b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      exact ⟨_, rfl⟩

omit [IsNoetherianRing R] [IsDomain R] in
/-- Step 2 answers `Iₙ`, whose levels are `(0, 0)`. -/
lemma Step2.pow_dvd_c₄_c₆ (h : Step2.run ϖ W = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step1.pow_dvd_c₄_c₆ h
  · by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W').b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      exact ⟨by simp [KodairaSymbol.additiveC₄Level], by simp [KodairaSymbol.additiveC₆Level]⟩

omit [IsNoetherianRing R] [IsDomain R] in
/-- Step 3 answers `II`, whose levels are `(1, 1)`. -/
lemma Step3.pow_dvd_c₄_c₆ (h : Step3.run ϖ W = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step2.pow_dvd_c₄_c₆ h
  · have h4 : ϖ ^ 1 ∣ W.c₄ := Step2.run_c₄ h' ▸ (Step2.run_hasValuation h').c₄
    have h6 : ϖ ^ 1 ∣ W.c₆ := Step2.run_c₆ h' ▸ (Step2.run_hasValuation h').c₆
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact ⟨h4, h6⟩

omit [IsNoetherianRing R] [IsDomain R] in
/-- Step 4 answers `III`, whose levels are `(1, 2)`. -/
lemma Step4.pow_dvd_c₄_c₆ (h : Step4.run ϖ W = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step3.pow_dvd_c₄_c₆ h
  · have h4 : ϖ ^ 1 ∣ W.c₄ := Step3.run_c₄ h' ▸ (Step3.run_hasValuation h').c₄
    have h6 : ϖ ^ 2 ∣ W.c₆ := Step3.run_c₆ h' ▸ (Step3.run_hasValuation h').c₆
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact ⟨h4, h6⟩

omit [IsNoetherianRing R] in
/-- Step 5 answers `IV`, whose levels are `(2, 2)`. -/
lemma Step5.pow_dvd_c₄_c₆ (hϖ : ϖ ≠ 0) (h : Step5.run ϖ W = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step4.pow_dvd_c₄_c₆ h
  · have h4 : ϖ ^ 2 ∣ W.c₄ := Step4.run_c₄ h' ▸ (Step4.run_hasValuation hϖ h').c₄
    have h6 : ϖ ^ 2 ∣ W.c₆ := Step4.run_c₆ h' ▸ (Step4.run_hasValuation hϖ h').c₆
    split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact ⟨h4, h6⟩

omit [IsNoetherianRing R] in
/-- Step 6 answers `I₀*`, whose levels are `(2, 3)`. -/
lemma Step6.pow_dvd_c₄_c₆ (hϖ : ϖ ≠ 0) (h : Step6.run ϖ W = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step5.pow_dvd_c₄_c₆ hϖ h
  · have h4 : ϖ ^ 2 ∣ W.c₄ := Step5.run_c₄ h' ▸ (Step5.run_hasValuation hϖ h').c₄
    have h6 : ϖ ^ 3 ∣ W.c₆ := Step5.run_c₆ h' ▸ (Step5.run_hasValuation hϖ h').c₆
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact ⟨h4, h6⟩

/-- Every answer of the `Iₙ*` subprocedure of Step 7 has levels `(2, 3)`: if `ϖ² ∣ V.c₄` and
`ϖ³ ∣ V.c₆`, then `ϖ^i ∣ V.c₄` and `ϖ^j ∣ V.c₆` for the levels `(i, j)` of its Kodaira symbol. -/
lemma Step7.subprocedure_pow_dvd_c₄_c₆ {V : WeierstrassCurve R} (hV₄ : ϖ ^ 2 ∣ V.c₄)
    (hV₆ : ϖ ^ 3 ∣ V.c₆) (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) :
    ϖ ^ (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol.additiveC₄Level ∣ V.c₄ ∧
      ϖ ^ (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol.additiveC₆Level ∣ V.c₆ := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => exact ⟨hV₄, hV₆⟩
  | case3 => exact ⟨hV₄, hV₆⟩

/-- Every answer of the `Iₙ*` subprocedure of Step 7 has a starred Kodaira symbol, so none is
`II`. -/
lemma Step7.subprocedure_kodairaSymbol_ne_II (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.II := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 either inherits an earlier answer or answers inside its `Iₙ*` subprocedure, with levels
at most `(2, 3)`. -/
lemma Step7.pow_dvd_c₄_c₆ (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)
    (h : Step7.run hϖ hΔ = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.pow_dvd_c₄_c₆ hϖ (heq.trans h)
  next W' heq =>
    have h4 : ϖ ^ 2 ∣ W.c₄ := Step6.run_c₄ heq ▸ (Step6.run_hasValuation hϖ heq).c₄
    have h6 : ϖ ^ 3 ∣ W.c₆ := Step6.run_c₆ heq ▸ (Step6.run_hasValuation hϖ heq).c₆
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact Step7.subprocedure_pow_dvd_c₄_c₆ h4 h6 ..

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- Step 8 answers `IV*`, whose levels are `(2, 3)`. -/
lemma Step8.pow_dvd_c₄_c₆ (h : Step8.run hϖ hΔ = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step7.pow_dvd_c₄_c₆ hϖ hΔ h
  · have h4 : ϖ ^ 2 ∣ W.c₄ := Step7.run_c₄ hϖ hΔ h' ▸ (Step7.run_hasValuation hϖ hΔ h').c₄
    have h6 : ϖ ^ 3 ∣ W.c₆ := Step7.run_c₆ hϖ hΔ h' ▸ (Step7.run_hasValuation hϖ hΔ h').c₆
    split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        exact ⟨h4, h6⟩

/-- Step 9 answers `III*`, whose levels are `(3, 4)`. -/
lemma Step9.pow_dvd_c₄_c₆ (h : Step9.run hϖ hΔ = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step8.pow_dvd_c₄_c₆ hϖ hΔ h
  · have h4 : ϖ ^ 3 ∣ W.c₄ := Step8.run_c₄ hϖ hΔ h' ▸ (Step8.run_hasValuation hϖ hΔ h').c₄
    have h6 : ϖ ^ 4 ∣ W.c₆ := Step8.run_c₆ hϖ hΔ h' ▸ (Step8.run_hasValuation hϖ hΔ h').c₆
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact ⟨h4, h6⟩

/-- Step 10 answers `II*`, whose levels are `(4, 5)`. -/
lemma Step10.pow_dvd_c₄_c₆ (h : Step10.run hϖ hΔ = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step9.pow_dvd_c₄_c₆ hϖ hΔ h
  · have h4 : ϖ ^ 4 ∣ W.c₄ := Step9.run_c₄ hϖ hΔ h' ▸ (Step9.run_hasValuation hϖ hΔ h').c₄
    have h6 : ϖ ^ 5 ∣ W.c₆ := Step9.run_c₆ hϖ hΔ h' ▸ (Step9.run_hasValuation hϖ hΔ h').c₆
    split_ifs at h
    obtain rfl := Except.error.inj h
    exact ⟨h4, h6⟩

/-- Step 11 never terminates with an answer of its own. -/
lemma Step11.pow_dvd_c₄_c₆ (h : Step11.run hϖ hΔ = Except.error out) :
    ϖ ^ out.kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ out.kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.pow_dvd_c₄_c₆ hϖ hΔ h
  · simp at h

/-- **The valuation of `c₄` and `c₆` forced by the Kodaira symbol.** For every Weierstrass curve
with `Δ ≠ 0`,

  `ϖ^{i(κ)} ∣ c₄`  and  `ϖ^{j(κ)} ∣ c₆`,  `κ` the Kodaira symbol returned,

with `i`, `j` the `additiveC₄Level` and `additiveC₆Level`. -/
theorem pow_dvd_c₄_c₆_run :
    ϖ ^ (run hϖ hΔ).kodairaSymbol.additiveC₄Level ∣ W.c₄ ∧
      ϖ ^ (run hϖ hΔ).kodairaSymbol.additiveC₆Level ∣ W.c₆ := by
  induction W, hΔ using run.induct hϖ with
  | case1 W hΔ out h =>
    rw [run_eq_of_step11_error hϖ hΔ h]
    exact Step11.pow_dvd_c₄_c₆ hϖ hΔ h
  | case2 W hΔ W' h ih =>
    have hΔ' : W'.Δ ≠ 0 := fun h0 => hΔ (by rw [← Step11.run_Δ hϖ hΔ h, h0, mul_zero])
    have h4 : ϖ ^ 4 ∣ W.c₄ := ⟨W'.c₄, (Step11.run_c₄ hϖ hΔ h).symm⟩
    have h6 : ϖ ^ 6 ∣ W.c₆ := ⟨W'.c₆, (Step11.run_c₆ hϖ hΔ h).symm⟩
    rw [run_eq_of_step11_ok hϖ hΔ h hΔ']
    exact ⟨(pow_dvd_pow ϖ (KodairaSymbol.additiveC₄Level_le_four _)).trans h4,
      (pow_dvd_pow ϖ (KodairaSymbol.additiveC₆Level_le_six _)).trans h6⟩

/-! ### The branch conditions of Steps 2–5 in terms of `c₄` and `c₆` -/

omit [IsNoetherianRing R] [IsDomain R] in
/-- **`ϖ ∣ c₄` forces `ϖ ∣ b₂` of the Step-2 translate**, so a model with `ϖ ∣ Δ` and `ϖ ∣ c₄`
passes Step 2 without answering. -/
theorem Step2.dvd_translate_b₂ (hprime : Prime ϖ) (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄) :
    ϖ ∣ (Step2.translate ϖ W).b₂ := by
  have hb₄ : ϖ ∣ (Step2.translate ϖ W).b₄ := by
    simpa using (Step2.hasValuation_translate hd).b₄
  refine hprime.dvd_of_dvd_pow (n := 2) ?_
  have hsq : (Step2.translate ϖ W).b₂ ^ 2
      = (Step2.translate ϖ W).c₄ + 24 * (Step2.translate ϖ W).b₄ := by
    rw [WeierstrassCurve.c₄]; ring
  rw [hsq, Step2.translate_c₄]
  exact dvd_add hc₄ (hb₄.mul_left 24)

end WeierstrassCurve.TateAlgorithm

namespace WeierstrassCurve

/-- **The identity behind Step 3.** For any Weierstrass curve with `ϖ ∣ b₂`, `ϖ ∣ b₄` and `ϖ ∣ a₃`,

  `ϖ² ∣ c₆ + 864 a₆`,

because `c₆ + 864a₆ = -b₂³ + 36b₂b₄ - 216a₃²`. -/
theorem sq_dvd_c₆_add_mul_a₆_of_dvd {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R}
    (hb₂ : ϖ ∣ V.b₂) (hb₄ : ϖ ∣ V.b₄) (ha₃ : ϖ ∣ V.a₃) : ϖ ^ 2 ∣ V.c₆ + 864 * V.a₆ := by
  obtain ⟨u, hu⟩ := hb₂
  obtain ⟨v, hv⟩ := hb₄
  obtain ⟨w, hw⟩ := ha₃
  refine ⟨-ϖ * u ^ 3 + 36 * u * v - 216 * w ^ 2, ?_⟩
  rw [WeierstrassCurve.c₆, WeierstrassCurve.b₆, hu, hv, hw]
  ring

/-- **The `b₄` half of Step 4.** If `ϖ ∣ b₂` and `24` is a unit, then `ϖ² ∣ c₄ ↔ ϖ² ∣ b₄`, since
`c₄ = b₂² - 24b₄`. -/
theorem sq_dvd_c₄_iff_sq_dvd_b₄ {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R}
    (h24 : IsUnit (24 : R)) (hb₂ : ϖ ∣ V.b₂) : ϖ ^ 2 ∣ V.c₄ ↔ ϖ ^ 2 ∣ V.b₄ := by
  obtain ⟨u, hu⟩ := hb₂
  have hsq : ϖ ^ 2 ∣ V.b₂ ^ 2 := ⟨u ^ 2, by rw [hu]; ring⟩
  have hc : V.c₄ = V.b₂ ^ 2 - 24 * V.b₄ := by rw [WeierstrassCurve.c₄]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := dvd_sub hsq h
    rw [hc, show V.b₂ ^ 2 - (V.b₂ ^ 2 - 24 * V.b₄) = 24 * V.b₄ from by ring] at hs
    rwa [h24.dvd_mul_left] at hs
  · rw [hc]
    exact dvd_sub hsq (h.mul_left 24)

/-- **Step 4's branch condition is a condition on `b₄`.** With `ϖ` prime, `4` a unit, `ϖ ∣ b₂` and
`ϖ² ∣ b₆`, the relation `4b₈ = b₂b₆ - b₄²` makes `ϖ³ ∣ b₈` and `ϖ² ∣ b₄` equivalent. -/
theorem cb_dvd_b₈_iff_sq_dvd_b₄ {R : Type u} [CommRing R] [IsDomain R] {ϖ : R}
    {V : WeierstrassCurve R} (hϖ : Prime ϖ) (h4 : IsUnit (4 : R)) (hb₂ : ϖ ∣ V.b₂)
    (hb₆ : ϖ ^ 2 ∣ V.b₆) : ϖ ^ 3 ∣ V.b₈ ↔ ϖ ^ 2 ∣ V.b₄ := by
  obtain ⟨u, hu⟩ := hb₂
  obtain ⟨v, hv⟩ := hb₆
  have hbb : ϖ ^ 3 ∣ V.b₂ * V.b₆ := ⟨u * v, by rw [hu, hv]; ring⟩
  have hrel : 4 * V.b₈ = V.b₂ * V.b₆ - V.b₄ ^ 2 := V.b_relation
  refine ⟨fun h => (sq_dvd_iff_cb_dvd_sq hϖ).2 ?_, fun h => ?_⟩
  · have hs := dvd_sub hbb (h.mul_left 4)
    rwa [hrel, show V.b₂ * V.b₆ - (V.b₂ * V.b₆ - V.b₄ ^ 2) = V.b₄ ^ 2 from by ring] at hs
  · have hs : ϖ ^ 3 ∣ 4 * V.b₈ := by
      rw [hrel]
      exact dvd_sub hbb ((sq_dvd_iff_cb_dvd_sq hϖ).1 h)
    rwa [h4.dvd_mul_left] at hs

/-- **The identity behind Step 5.** With `ϖ ∣ b₂` and `ϖ² ∣ b₄`,

  `ϖ³ ∣ c₆ + 216 b₆`,

since `c₆ + 216b₆ = -b₂³ + 36b₂b₄`. -/
theorem cb_dvd_c₆_add_mul_b₆_of_dvd {R : Type u} [CommRing R] {ϖ : R} {V : WeierstrassCurve R}
    (hb₂ : ϖ ∣ V.b₂) (hb₄ : ϖ ^ 2 ∣ V.b₄) : ϖ ^ 3 ∣ V.c₆ + 216 * V.b₆ := by
  obtain ⟨u, hu⟩ := hb₂
  obtain ⟨v, hv⟩ := hb₄
  refine ⟨-u ^ 3 + 36 * u * v, ?_⟩
  rw [WeierstrassCurve.c₆, hu, hv]
  ring

variable {p : ℕ} [Fact p.Prime]

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-- `864 = 2⁵ · 27` is a unit of `ℤ_[p]` for `p ≥ 5`. -/
theorem isUnit_eightSixFour (hp : 5 ≤ p) : IsUnit (864 : ℤ_[p]) := by
  simpa using (isUnit_neg_eightSixFour hp).neg

/-- `24 = 2³ · 3` is a unit of `ℤ_[p]` for `p ≥ 5`. -/
theorem isUnit_twentyFour (hp : 5 ≤ p) : IsUnit (24 : ℤ_[p]) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h : IsUnit ((2 : ℤ_[p]) ^ 3 * 3) :=
    ((PadicInt.isUnit_two hodd).pow 3).mul (PadicInt.isUnit_three hp)
  simpa [show (2 : ℤ_[p]) ^ 3 * 3 = 24 by norm_num] using h

/-- `216 = 2³ · 27` is a unit of `ℤ_[p]` for `p ≥ 5`. -/
theorem isUnit_twoHundredSixteen (hp : 5 ≤ p) : IsUnit (216 : ℤ_[p]) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h : IsUnit ((2 : ℤ_[p]) ^ 3 * 27) :=
    ((PadicInt.isUnit_two hodd).pow 3).mul (isUnit_twentySeven hp)
  simpa [show (2 : ℤ_[p]) ^ 3 * 27 = 216 by norm_num] using h

/-- **Step 4's branch condition in terms of `c₄`.** For `p ≥ 5`, a curve over `ℤ_p` with `p ∣ b₂`
and `p² ∣ b₆` satisfies

  `p³ ∣ b₈  ↔  p² ∣ c₄`. -/
theorem cb_dvd_b₈_iff_sq_dvd_c₄ (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (hb₂ : (p : ℤ_[p]) ∣ V.b₂) (hb₆ : (p : ℤ_[p]) ^ 2 ∣ V.b₆) :
    (p : ℤ_[p]) ^ 3 ∣ V.b₈ ↔ (p : ℤ_[p]) ^ 2 ∣ V.c₄ :=
  (cb_dvd_b₈_iff_sq_dvd_b₄ PadicInt.prime_p (isUnit_four hp) hb₂ hb₆).trans
    (sq_dvd_c₄_iff_sq_dvd_b₄ (isUnit_twentyFour hp) hb₂).symm

/-- **Step 5's branch condition in terms of `c₆`.** For `p ≥ 5`, a curve over `ℤ_p` with `p ∣ b₂`
and `p² ∣ b₄` satisfies

  `p³ ∣ b₆  ↔  p³ ∣ c₆`. -/
theorem cb_dvd_b₆_iff_cb_dvd_c₆ (hp : 5 ≤ p) {V : WeierstrassCurve ℤ_[p]}
    (hb₂ : (p : ℤ_[p]) ∣ V.b₂) (hb₄ : (p : ℤ_[p]) ^ 2 ∣ V.b₄) :
    (p : ℤ_[p]) ^ 3 ∣ V.b₆ ↔ (p : ℤ_[p]) ^ 3 ∣ V.c₆ := by
  have key := cb_dvd_c₆_add_mul_b₆_of_dvd hb₂ hb₄
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := dvd_sub key (h.mul_left 216)
    rwa [add_sub_cancel_right] at hs
  · have hs := dvd_sub key h
    rw [add_sub_cancel_left] at hs
    rwa [(isUnit_twoHundredSixteen hp).dvd_mul_left] at hs

/-- **Step 3's branch condition in terms of `c₆`.** For `p ≥ 5`, a model over `ℤ_p` with `p ∣ Δ`
and `p ∣ c₄` satisfies

  `p² ∣ a₆(Step-2 translate)  ↔  p² ∣ c₆`. -/
theorem sq_dvd_translate_a₆_iff_sq_dvd_c₆ (hp : 5 ≤ p) {W : WeierstrassCurve ℤ_[p]}
    (hd : (p : ℤ_[p]) ∣ W.Δ) (hc₄ : (p : ℤ_[p]) ∣ W.c₄) :
    (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) W).a₆ ↔ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  have hb₂ := Step2.dvd_translate_b₂ PadicInt.prime_p hd hc₄
  have hb₄ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).b₄ := by
    simpa using (Step2.hasValuation_translate hd).b₄
  have ha₃ : (p : ℤ_[p]) ∣ (Step2.translate (p : ℤ_[p]) W).a₃ := by
    simpa using (Step2.hasValuation_translate hd).a₃
  have key := sq_dvd_c₆_add_mul_a₆_of_dvd hb₂ hb₄ ha₃
  rw [Step2.translate_c₆] at key
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := dvd_sub key (h.mul_left 864)
    rwa [add_sub_cancel_right] at hs
  · have hs := dvd_sub key h
    rw [add_sub_cancel_left] at hs
    rwa [(isUnit_eightSixFour hp).dvd_mul_left] at hs

/-! ### Only Step 3 answers `II`

At each step the answer is either inherited from the previous step or that step's own symbol, and
only Step 3 has the symbol `II`; when it answers, `p² ∤ c₆`. -/

namespace TateAlgorithm

variable {W : WeierstrassCurve ℤ_[p]} {out : Output ℤ_[p]}

/-- **Step 3's answer `II` forces `p² ∤ c₆`**, for `p ≥ 5`. -/
theorem Step3.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p)
    (h : Step3.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · obtain ⟨n, hn⟩ := Step2.exists_kodairaSymbol_eq_I h
    rw [hn] at hκ
    simp at hκ
  · have hv := Step2.run_hasValuation h'
    have key := sq_dvd_c₆_add_mul_a₆_of_dvd (V := W') (by simpa using hv.b₂)
      (by simpa using hv.b₄) (by simpa using hv.a₃)
    rw [Step2.run_c₆ h'] at key
    split_ifs at h with ha₆
    intro hc
    have hs := dvd_sub key hc
    rw [add_sub_cancel_left, (isUnit_eightSixFour hp).dvd_mul_left] at hs
    exact ha₆ hs

/-- Step 4 answers `III`, not `II`. -/
theorem Step4.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p)
    (h : Step4.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.not_sq_dvd_c₆_of_eq_II hp h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 5 answers `IV`, not `II`. -/
theorem Step5.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p)
    (h : Step5.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.not_sq_dvd_c₆_of_eq_II hp h hκ
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- Step 6 answers `I₀*`, not `II`. -/
theorem Step6.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p)
    (h : Step6.run (p : ℤ_[p]) W = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.not_sq_dvd_c₆_of_eq_II hp h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 7 answers `Iₙ*`, not `II`. -/
theorem Step7.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.not_sq_dvd_c₆_of_eq_II hp (heq.trans h) hκ
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hκ ?_
    apply Step7.subprocedure_kodairaSymbol_ne_II

/-- Step 8 answers `IV*`, not `II`. -/
theorem Step8.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.not_sq_dvd_c₆_of_eq_II hp hΔ h hκ
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hκ

/-- Step 9 answers `III*`, not `II`. -/
theorem Step9.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.not_sq_dvd_c₆_of_eq_II hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- Step 10 answers `II*`, not `II`. -/
theorem Step10.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.not_sq_dvd_c₆_of_eq_II hp hΔ h hκ
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hκ

/-- **An answer of `II` at Steps 1–11 forces `p² ∤ c₆`**, for `p ≥ 5`. -/
theorem Step11.not_sq_dvd_c₆_of_eq_II (hp : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (h : Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out)
    (hκ : out.kodairaSymbol = KodairaSymbol.II) : ¬ (p : ℤ_[p]) ^ 2 ∣ W.c₆ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.not_sq_dvd_c₆_of_eq_II hp hΔ h hκ
  · simp at h

end TateAlgorithm

/-! ### The Step-3 answer reaches the top level -/

/-- A Step-6 answer propagates through Steps 7–11. -/
theorem step11_error_of_step6 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    {out : Output ℤ_[p]} (h6 : Step6.run (p : ℤ_[p]) W = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
  have h7 : Step7.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step7.run.eq_def]
    split
    next out' heq => exact (h6.symm.trans heq).symm
    next W' heq => exact absurd (h6.symm.trans heq) (by simp)
  have h8 : Step8.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step8.run.eq_def, h7]; rfl
  have h9 : Step9.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step9.run.eq_def, h8]; rfl
  have h10 : Step10.run PadicInt.uniformizer_ne_zero hΔ = Except.error out := by
    rw [Step10.run.eq_def, h9]; rfl
  rw [Step11.run.eq_def, h10]; rfl

/-- A Step-5 answer reaches Step 11: Step 6 is a monadic bind. -/
theorem step11_error_of_step5 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    {out : Output ℤ_[p]} (h5 : Step5.run (p : ℤ_[p]) W = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out :=
  step11_error_of_step6 hΔ (by rw [Step6.run.eq_def, h5]; rfl)

/-- A Step-4 answer reaches Step 11. -/
theorem step11_error_of_step4 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    {out : Output ℤ_[p]} (h4 : Step4.run (p : ℤ_[p]) W = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out :=
  step11_error_of_step5 hΔ (by rw [Step5.run.eq_def, h4]; rfl)

/-- A Step-3 answer reaches Step 11. -/
theorem step11_error_of_step3 {W : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    {out : Output ℤ_[p]} (s3 : Step3.run (p : ℤ_[p]) W = Except.error out) :
    Step11.run PadicInt.uniformizer_ne_zero hΔ = Except.error out :=
  step11_error_of_step4 hΔ (by rw [Step4.run.eq_def, s3]; rfl)

/-! ### The plane version: the divisibilities on every additive stratum -/

/-- **The congruence description of every stratum, from above.** For `p ≥ 5`, a coefficient pair in
the stratum `τ_p⁻¹(K)` satisfies `p^{i} ∣ a₄` and `p^{j} ∣ a₆`, with `(i, j)` the levels of `K`'s
Kodaira symbol. -/
theorem pow_dvd_of_mem_stratFibre_additive (hp : 5 ≤ p) {K : ReductionData}
    {x : ℤ_[p] × ℤ_[p]} (hxF : x ∈ stratFibre p K) :
    (p : ℤ_[p]) ^ K.1.additiveC₄Level ∣ x.1 ∧ (p : ℤ_[p]) ^ K.1.additiveC₆Level ∣ x.2 := by
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  have hs := (mem_stratFibre_iff hxUp).1 hxF
  rw [strat] at hs
  have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = K.1 := congrArg Prod.fst hs
  obtain ⟨h4, h6⟩ := TateAlgorithm.pow_dvd_c₄_c₆_run (W := ofShortNF x.1 x.2)
    PadicInt.uniformizer_ne_zero hxUp
  rw [hκ] at h4 h6
  rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4
  rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6
  exact ⟨h4, h6⟩

/-! ### The forward run at `v_p(a₆) = 1`: the `(II, 1)` stratum from below -/

/-- `v_p(y) = 1` is `p ∣ y` and `p² ∤ y`. -/
theorem emultiplicity_eq_one_iff_dvd_and_not_sq_dvd {y : ℤ_[p]} :
    emultiplicity (p : ℤ_[p]) y = ((1 : ℕ) : ℕ∞) ↔
      (p : ℤ_[p]) ∣ y ∧ ¬ (p : ℤ_[p]) ^ 2 ∣ y := by
  rw [emultiplicity_eq_coe, pow_one]

/-- **A short model with `p ∣ a₄` and `v_p(a₆) = 1` has `v_p(Δ) = 2`**, in the form `p³ ∤ Δ`; in
particular `Δ ≠ 0`. Indeed `Δ = -16(4a₄³ + 27a₆²)` with `p³ ∣ 4a₄³` and `p³ ∤ 27a₆²`. -/
theorem not_cb_dvd_ofShortNF_Δ_of_emultiplicity_eq_one (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (h4 : (p : ℤ_[p]) ∣ a₄) (h6 : (p : ℤ_[p]) ∣ a₆) (h6' : ¬ (p : ℤ_[p]) ^ 2 ∣ a₆) :
    ¬ (p : ℤ_[p]) ^ 3 ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨b, rfl⟩ := h6
  intro hd
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left] at hd
  have h1 : (p : ℤ_[p]) ^ 3 ∣ 4 * ((p : ℤ_[p]) * c) ^ 3 := ⟨4 * c ^ 3, by ring⟩
  have h2 : (p : ℤ_[p]) ^ 3 ∣ (p : ℤ_[p]) ^ 2 * (27 * b ^ 2) := by
    have hs := dvd_sub hd h1
    rwa [show 4 * ((p : ℤ_[p]) * c) ^ 3 + 27 * ((p : ℤ_[p]) * b) ^ 2
      - 4 * ((p : ℤ_[p]) * c) ^ 3 = (p : ℤ_[p]) ^ 2 * (27 * b ^ 2) by ring] at hs
  obtain ⟨z, hz⟩ := h2
  have h3 : (p : ℤ_[p]) ∣ 27 * b ^ 2 :=
    ⟨z, mul_left_cancel₀ (pow_ne_zero 2 PadicInt.uniformizer_ne_zero) (by rw [hz]; ring)⟩
  rw [(isUnit_twentySeven hp).dvd_mul_left] at h3
  exact h6' (by
    rw [pow_two]
    exact mul_dvd_mul_left _ (PadicInt.prime_p.dvd_of_dvd_pow h3))

/-- **The forward run at `(II, 1)`.** For every prime `p ≥ 5`, a short model over `ℤ_p` with
`p ∣ a₄` and `v_p(a₆) = 1` has reduction datum exactly `(II, 1)`. -/
theorem run_eq_II_of_dvd_of_not_sq_dvd (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ∣ a₄) (h6 : (p : ℤ_[p]) ∣ a₆)
    (h6' : ¬ (p : ℤ_[p]) ^ 2 ∣ a₆) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.II ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    dvd_Δ_of_dvd_of_dvd (x := (a₄, a₆)) h4 h6
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ := by
    rw [ofShortNF_c₄]; exact h4.mul_left _
  have hc₆ : ¬ (p : ℤ_[p]) ^ 2 ∣ (ofShortNF a₄ a₆).c₆ := by
    rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left]; exact h6'
  have hs1 : Step1.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok (ofShortNF a₄ a₆) := by
    rw [Step1.run.eq_def]; exact ite_eq_left hpΔ
  have hs2 : Step2.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step2.run.eq_def, hs1]
    simp only [except_ok_bind]
    exact ite_eq_left (Step2.dvd_translate_b₂ PadicInt.prime_p hpΔ hc₄)
  have hs3 : Step3.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆), KodairaSymbol.II, 1⟩ := by
    rw [Step3.run.eq_def, hs2]
    simp only [except_ok_bind]
    exact ite_eq_right fun hcon => hc₆ ((sq_dvd_translate_a₆_iff_sq_dvd_c₆ hp hpΔ hc₄).1 hcon)
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step3 hΔ hs3)]
  exact ⟨rfl, rfl⟩

/-! ### The minimal `(II, 1)` locus and its mass -/

variable (p) in
/-- **The minimal `II` locus of the coefficient plane:** the pairs with `p ∣ a₄` and
`v_p(a₆) = 1`. -/
def stratMinimalII : Set (ℤ_[p] × ℤ_[p]) :=
  ((Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ
    {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = ((1 : ℕ) : ℕ∞)}

/-- A pair `(a₄, a₆)` lies in the minimal `II` locus iff `p ∣ a₄`, `p ∣ a₆` and `p² ∤ a₆`. -/
theorem mem_stratMinimalII_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ stratMinimalII p ↔
      (p : ℤ_[p]) ∣ x.1 ∧ (p : ℤ_[p]) ∣ x.2 ∧ ¬ (p : ℤ_[p]) ^ 2 ∣ x.2 := by
  rw [stratMinimalII, Set.mem_prod]
  simp only [SetLike.mem_coe, PadicInt.mem_span_pPow_iff_le_emultiplicity, Set.mem_ofPred_eq,
    emultiplicity_eq_one_iff_dvd_and_not_sq_dvd]
  rw [show ((1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ_[p]) x.1 ↔ (p : ℤ_[p]) ∣ x.1 by
    rw [← pow_dvd_iff_le_emultiplicity, pow_one]]

/-- **The mass of the minimal `II` locus:** `(1 - p^{-1}) p^{-2}`. -/
theorem volume_stratMinimalII :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratMinimalII p)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
  rw [stratMinimalII, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.measure_span_pPow', PadicInt.volume_setOf_emultiplicity_eq]
  ring

/-- **The minimal `II` locus lies in the `(II, 1)` stratum**, for every prime `p ≥ 5`. -/
theorem stratMinimalII_subset_stratFibre (hp : 5 ≤ p) :
    stratMinimalII p ⊆ stratFibre p (KodairaSymbol.II, 1) := by
  intro x hx
  obtain ⟨h4, h6, h6'⟩ := mem_stratMinimalII_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_cb_dvd_ofShortNF_Δ_of_emultiplicity_eq_one hp h4 h6 h6' (h0 ▸ dvd_zero _)
  have hxUp : x ∈ nonsingularLocus p := hΔ
  refine (mem_stratFibre_iff hxUp).2 ?_
  obtain ⟨hκ, hc⟩ := run_eq_II_of_dvd_of_not_sq_dvd hp hΔ h4 h6 h6'
  rw [strat]
  exact Prod.ext hκ hc

/-! ### The `(II, 1)` stratum from above -/

/-- **The `(II, 1)` stratum splits into its minimal locus and the non-minimal locus.** For every
prime `p ≥ 5`,

  `τ_p⁻¹((II, 1)) ⊆ ({p ∣ a₄} × {v_p(a₆) = 1}) ∪ σ_p(ℤ_p²)`,

where `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)`. -/
theorem stratFibre_II_subset_union (hp : 5 ≤ p) :
    stratFibre p (KodairaSymbol.II, 1)
      ⊆ stratMinimalII p ∪ Set.range
          (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  intro x hxF
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  obtain ⟨h4, h6⟩ := pow_dvd_of_mem_stratFibre_additive hp hxF
  by_cases hsq : (p : ℤ_[p]) ^ 2 ∣ x.2
  · refine Or.inr ?_
    have hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp).kodairaSymbol = KodairaSymbol.II := by
      have hs := (mem_stratFibre_iff hxUp).1 hxF
      rw [strat] at hs
      exact congrArg Prod.fst hs
    have hc₆ : (p : ℤ_[p]) ^ 2 ∣ (ofShortNF x.1 x.2).c₆ := by
      rw [ofShortNF_c₆]
      exact hsq.mul_left _
    rcases e : TateAlgorithm.Step11.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hxUp with out' | W'
    · exact absurd hc₆ (TateAlgorithm.Step11.not_sq_dvd_c₆_of_eq_II hp hxUp e
        (by rw [← TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hxUp e]
            exact hκ))
    · have e4 : (p : ℤ_[p]) ^ 4 ∣ x.1 := by
        have hd : (p : ℤ_[p]) ^ 4 ∣ (ofShortNF x.1 x.2).c₄ :=
          ⟨W'.c₄, (TateAlgorithm.Step11.run_c₄ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at hd
      have e6 : (p : ℤ_[p]) ^ 6 ∣ x.2 := by
        have hd : (p : ℤ_[p]) ^ 6 ∣ (ofShortNF x.1 x.2).c₆ :=
          ⟨W'.c₆, (TateAlgorithm.Step11.run_c₆ PadicInt.uniformizer_ne_zero hxUp e).symm⟩
        rwa [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at hd
      exact PadicInt.mem_range_scaleProdByPPow_iff.2 ⟨e4, e6⟩
  · exact Or.inl (mem_stratMinimalII_iff.2
      ⟨by simpa [KodairaSymbol.additiveC₄Level] using h4,
        by simpa [KodairaSymbol.additiveC₆Level] using h6, hsq⟩)

/-! ### The forward run at Steps 4 and 5: the `III` and `IV` strata from below -/

/-- For `p ≥ 5`, Steps 1–3 continue on a short model with `p ∣ a₄` and `p² ∣ a₆`, with the Step-2
translate. -/
theorem step3_run_eq_ok_of_dvd (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]} (h4 : (p : ℤ_[p]) ∣ a₄)
    (h6 : (p : ℤ_[p]) ^ 2 ∣ a₆) :
    Step3.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
  have hpΔ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    dvd_Δ_of_dvd_of_dvd (x := (a₄, a₆)) h4 (dvd_trans (dvd_pow_self _ two_ne_zero) h6)
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ := by
    rw [ofShortNF_c₄]; exact h4.mul_left _
  have hc₆ : (p : ℤ_[p]) ^ 2 ∣ (ofShortNF a₄ a₆).c₆ := by
    rw [ofShortNF_c₆]; exact h6.mul_left _
  have hs1 : Step1.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok (ofShortNF a₄ a₆) := by
    rw [Step1.run.eq_def]; exact ite_eq_left hpΔ
  have hs2 : Step2.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step2.run.eq_def, hs1]
    simp only [except_ok_bind]
    exact ite_eq_left (Step2.dvd_translate_b₂ PadicInt.prime_p hpΔ hc₄)
  rw [Step3.run.eq_def, hs2]
  simp only [except_ok_bind]
  exact ite_eq_left ((sq_dvd_translate_a₆_iff_sq_dvd_c₆ hp hpΔ hc₄).2 hc₆)

/-- **The forward run at `III`.** For every prime `p ≥ 5`, a short model over `ℤ_p` with
`v_p(a₄) = 1` and `p² ∣ a₆` has reduction datum exactly `(III, 2)`. -/
theorem run_eq_III_of_emultiplicity_eq_one (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ∣ a₄) (h4' : ¬ (p : ℤ_[p]) ^ 2 ∣ a₄)
    (h6 : (p : ℤ_[p]) ^ 2 ∣ a₆) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.III ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 := by
  have hs3 := step3_run_eq_ok_of_dvd hp h4 h6
  have hv := Step3.run_hasValuation hs3
  have hc₄ : ¬ (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₄ := by
    rw [Step2.translate_c₄, ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
    exact h4'
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.error ⟨Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆), KodairaSymbol.III, 2⟩ := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_right fun hcon =>
      hc₄ ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv.b₂) hv.b₆).1 hcon)
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ (step11_error_of_step4 hΔ hs4)]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- **Step 5 at `IV`.** For every prime `p ≥ 5`, a short model over `ℤ_p` with `p² ∣ a₄` and
`v_p(a₆) = 2` passes Steps 1–4 and stops at Step 5 with Kodaira symbol `IV`. -/
theorem step5_run_eq_error_IV (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]} (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄)
    (h6 : (p : ℤ_[p]) ^ 2 ∣ a₆) (h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ a₆) :
    Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.error
      ⟨Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆), KodairaSymbol.IV,
        if (quadratic (p : ℤ_[p]) (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆))
          1).toPoly.Splits then 3 else 1⟩ := by
  have hs3 := step3_run_eq_ok_of_dvd hp (dvd_trans (dvd_pow_self _ two_ne_zero) h4) h6
  have hv3 := Step3.run_hasValuation hs3
  have hc₄ : (p : ℤ_[p]) ^ 2 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₄ := by
    rw [Step2.translate_c₄, ofShortNF_c₄]
    exact h4.mul_left _
  have hc₆ : ¬ (p : ℤ_[p]) ^ 3 ∣ (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)).c₆ := by
    rwa [Step2.translate_c₆, ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left]
  have hs4 : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) := by
    rw [Step4.run.eq_def, hs3]
    simp only [except_ok_bind]
    exact ite_eq_left ((cb_dvd_b₈_iff_sq_dvd_c₄ hp (by simpa using hv3.b₂) hv3.b₆).2 hc₄)
  have hv4 := Step4.run_hasValuation PadicInt.uniformizer_ne_zero hs4
  rw [Step5.run.eq_def, hs4]
  simp only [except_ok_bind]
  exact ite_eq_right fun hcon =>
    hc₆ ((cb_dvd_b₆_iff_cb_dvd_c₆ hp (by simpa using hv4.b₂) hv4.b₄).1 hcon)

open scoped Classical in
/-- **The forward run at `IV`.** For every prime `p ≥ 5`, a short model over `ℤ_p` with `p² ∣ a₄`
and `v_p(a₆) = 2` has Kodaira symbol `IV`. -/
theorem run_kodairaSymbol_eq_IV_of_emultiplicity_eq_two (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (hΔ : (ofShortNF a₄ a₆).Δ ≠ 0) (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 2 ∣ a₆)
    (h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ a₆) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.IV := by
  rw [run_eq_of_step11_error PadicInt.uniformizer_ne_zero hΔ
    (step11_error_of_step5 hΔ (step5_run_eq_error_IV hp h4 h6 h6'))]

/-! ### The minimal `III` locus, its mass, and the discriminants on the `III` and `IV` loci -/

variable (p) in
/-- **The minimal `III` locus:** the pairs with `v_p(a₄) = 1` and `p² ∣ a₆`. -/
def stratMinimalIII : Set (ℤ_[p] × ℤ_[p]) :=
  {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = ((1 : ℕ) : ℕ∞)} ×ˢ
    ((Ideal.span {(p : ℤ_[p]) ^ 2} : Ideal ℤ_[p]) : Set ℤ_[p])

/-- A pair `(a₄, a₆)` lies in the minimal `III` locus iff `p ∣ a₄`, `p² ∤ a₄` and `p² ∣ a₆`. -/
theorem mem_stratMinimalIII_iff {x : ℤ_[p] × ℤ_[p]} :
    x ∈ stratMinimalIII p ↔
      ((p : ℤ_[p]) ∣ x.1 ∧ ¬ (p : ℤ_[p]) ^ 2 ∣ x.1) ∧ (p : ℤ_[p]) ^ 2 ∣ x.2 := by
  rw [stratMinimalIII, Set.mem_prod]
  simp only [Set.mem_ofPred_eq, emultiplicity_eq_one_iff_dvd_and_not_sq_dvd, SetLike.mem_coe,
    PadicInt.mem_span_pPow_iff_le_emultiplicity, ← pow_dvd_iff_le_emultiplicity]

/-- The mass of the minimal `III` locus is `(1 - p^{-1}) p^{-3}`. -/
theorem volume_stratMinimalIII :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (stratMinimalIII p)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ 3 := by
  rw [stratMinimalIII, Measure.volume_eq_prod, Measure.prod_prod,
    PadicInt.volume_setOf_emultiplicity_eq, PadicInt.measure_span_pPow']
  ring

/-- A short model with `v_p(a₄) = 1` and `p² ∣ a₆` has `v_p(Δ) = 3`, in the form needed: `p⁴ ∤ Δ`,
hence `Δ ≠ 0`. Indeed `Δ = -16(4a₄³ + 27a₆²)` with `p³ ∥ 4a₄³` and `p⁴ ∣ 27a₆²`. -/
theorem not_pow_four_dvd_ofShortNF_Δ_of_III (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (h4 : (p : ℤ_[p]) ∣ a₄) (h4' : ¬ (p : ℤ_[p]) ^ 2 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 2 ∣ a₆) :
    ¬ (p : ℤ_[p]) ^ 4 ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨b, rfl⟩ := h6
  intro hd
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left] at hd
  have h1 : (p : ℤ_[p]) ^ 4 ∣ 27 * ((p : ℤ_[p]) ^ 2 * b) ^ 2 := ⟨27 * b ^ 2, by ring⟩
  have h2 : (p : ℤ_[p]) ^ 4 ∣ (p : ℤ_[p]) ^ 3 * (4 * c ^ 3) := by
    have hs := dvd_sub hd h1
    rwa [show 4 * ((p : ℤ_[p]) * c) ^ 3 + 27 * ((p : ℤ_[p]) ^ 2 * b) ^ 2
      - 27 * ((p : ℤ_[p]) ^ 2 * b) ^ 2 = (p : ℤ_[p]) ^ 3 * (4 * c ^ 3) from by ring] at hs
  obtain ⟨z, hz⟩ := h2
  have h3 : (p : ℤ_[p]) ∣ 4 * c ^ 3 :=
    ⟨z, mul_left_cancel₀ (pow_ne_zero 3 PadicInt.uniformizer_ne_zero) (by rw [hz]; ring)⟩
  rw [(isUnit_four hp).dvd_mul_left] at h3
  exact h4' (by
    rw [pow_two]
    exact mul_dvd_mul_left _ (PadicInt.prime_p.dvd_of_dvd_pow h3))

/-- A short model with `p² ∣ a₄` and `v_p(a₆) = 2` has `v_p(Δ) = 4`, in the form needed: `p⁵ ∤ Δ`,
hence `Δ ≠ 0`. Indeed `p⁶ ∣ 4a₄³` while `p⁴ ∥ 27a₆²`. -/
theorem not_pow_five_dvd_ofShortNF_Δ_of_IV (hp : 5 ≤ p) {a₄ a₆ : ℤ_[p]}
    (h4 : (p : ℤ_[p]) ^ 2 ∣ a₄) (h6 : (p : ℤ_[p]) ^ 2 ∣ a₆) (h6' : ¬ (p : ℤ_[p]) ^ 3 ∣ a₆) :
    ¬ (p : ℤ_[p]) ^ 5 ∣ (ofShortNF a₄ a₆).Δ := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨b, rfl⟩ := h6
  intro hd
  rw [ofShortNF_Δ, ((isUnit_sixteen hp).neg).dvd_mul_left] at hd
  have h1 : (p : ℤ_[p]) ^ 5 ∣ 4 * ((p : ℤ_[p]) ^ 2 * c) ^ 3 := ⟨(p : ℤ_[p]) * (4 * c ^ 3), by ring⟩
  have h2 : (p : ℤ_[p]) ^ 5 ∣ (p : ℤ_[p]) ^ 4 * (27 * b ^ 2) := by
    have hs := dvd_sub hd h1
    rwa [show 4 * ((p : ℤ_[p]) ^ 2 * c) ^ 3 + 27 * ((p : ℤ_[p]) ^ 2 * b) ^ 2
      - 4 * ((p : ℤ_[p]) ^ 2 * c) ^ 3 = (p : ℤ_[p]) ^ 4 * (27 * b ^ 2) from by ring] at hs
  obtain ⟨z, hz⟩ := h2
  have h3 : (p : ℤ_[p]) ∣ 27 * b ^ 2 :=
    ⟨z, mul_left_cancel₀ (pow_ne_zero 4 PadicInt.uniformizer_ne_zero) (by rw [hz]; ring)⟩
  rw [(isUnit_twentySeven hp).dvd_mul_left] at h3
  exact h6' (by
    rw [pow_succ]
    exact mul_dvd_mul_left _ (PadicInt.prime_p.dvd_of_dvd_pow h3))

/-- **The minimal `III` locus lies in the `(III, 2)` stratum**, for every prime `p ≥ 5`. -/
theorem stratMinimalIII_subset_stratFibre (hp : 5 ≤ p) :
    stratMinimalIII p ⊆ stratFibre p (KodairaSymbol.III, 2) := by
  intro x hx
  obtain ⟨⟨h4, h4'⟩, h6⟩ := mem_stratMinimalIII_iff.1 hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := fun h0 =>
    not_pow_four_dvd_ofShortNF_Δ_of_III hp h4 h4' h6 (h0 ▸ dvd_zero _)
  have hxUp : x ∈ nonsingularLocus p := hΔ
  refine (mem_stratFibre_iff hxUp).2 ?_
  obtain ⟨hκ, hc⟩ := run_eq_III_of_emultiplicity_eq_one hp hΔ h4 h4' h6
  rw [strat]
  exact Prod.ext hκ hc

end WeierstrassCurve
