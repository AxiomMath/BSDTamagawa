/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.SplitMultiplicativeTail
public import BSDTamagawa.LocalDensity.PolynomialGeometricTail

/-!
# Geometric decay of `δ_p(t)` in `t`, at every prime

For every prime `p`, including `p = 2` and `p = 3`, and every `t ≥ 5`,

  `δ_p(t) ≤ 2 p^{-⌊(t-3)/2⌋}`,

hence every polynomially weighted moment of the tail converges:

  `Summable (fun t => δ_p(t).toReal (t+1)^k)`.

An `I_n` answer of Tate's algorithm on any model forces `n ≤ v_ϖ(Δ)` for that model, so the stratum
`τ_p⁻¹((I_t, t))` lies in the locus `{v_p(Δ) ≥ t}`. Writing `-432 = p^s u` with `u` a unit and
`s ≤ 4`, the discriminant `Δ = -64a₄³ - 432a₆²` is `c(a₄) + p^s u a₆²`, and on each `a₄`-slice the
congruence `p^{s+k} ∣ c + p^s u a₆²` confines `a₆` to two residue classes modulo `p^j` whenever
`2j ≤ k + 1`.

## Main definitions

* `WeierstrassCurve.dvdΔLocus`: the locus `{v_p(Δ) ≥ m}` of the coefficient plane.

## Main results

* `WeierstrassCurve.TateAlgorithm.le_emultiplicity_Δ_of_run_kodairaSymbol_eq_I`: if Tate's
  algorithm answers `I_n` on a model, then `n ≤ v_ϖ(Δ)` of that model.
* `PadicInt.pow_dvd_or_pow_dvd_of_pow_dvd_mul`: from `p^m ∣ xy` and `2j ≤ m + 1`, one of `x`, `y`
  is divisible by `p^j`.
* `PadicInt.volume_setOf_pow_dvd_add_sq_le`: for a unit `u` and any `c`,
  `μ_p{b | p^{s+k} ∣ c + p^s u b²} ≤ 2 p^{-j}` whenever `2j ≤ k + 1`.
* `WeierstrassCurve.volume_dvdΔLocus_le`: the same bound for the plane locus `{v_p(Δ) ≥ s + k}`.
* `WeierstrassCurve.δ_le_two_mul_inv_pow`: `δ_p(t) ≤ 2 p^{-⌊(t-3)/2⌋}` for every prime `p` and
  every `t ≥ 5`.
* `WeierstrassCurve.summable_δ_toReal_mul_add_one_pow`: the weighted moments converge, for every
  `k`.
* `WeierstrassCurve.summable_δ_toReal_mul_add_one_sq`: the case `k = 2`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

universe u

/-! ### An `I_n` answer of Tate's algorithm forces `n ≤ v_ϖ(Δ)` -/

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R} {n : ℕ}

omit [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}] in
/-- **Step 1** reports `(I₀, 1)`, so its `n` is `0`. -/
lemma Step1.le_emultiplicity_Δ (h : Step1.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step1.run.eq_def] at h
  split_ifs at h
  obtain rfl := Except.error.inj h
  obtain rfl : (0 : ℕ) = n := KodairaSymbol.I.inj hn
  simp

/-- **Step 2** reports `I_n` with `n ≤ v_ϖ(Δ)`. -/
lemma Step2.le_emultiplicity_Δ (h : Step2.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step1.le_emultiplicity_Δ h hn
  · rw [Step1.run_weierstrassCurve h'] at h
    by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W).b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      have hcast : KodairaSymbol.I ((emultiplicity ϖ (Step2.translate ϖ W).Δ).toNat)
          = KodairaSymbol.I n := hn
      have hle : (n : ℕ∞) ≤ emultiplicity ϖ (Step2.translate ϖ W).Δ := by
        rw [← KodairaSymbol.I.inj hcast]
        exact ENat.natCast_toNat_le_self _
      rwa [Step2.translate_Δ] at hle

/-- **Step 3** reports `II`, never an `I_n`. -/
lemma Step3.le_emultiplicity_Δ (h : Step3.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.le_emultiplicity_Δ h hn
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 4** reports `III`, never an `I_n`. -/
lemma Step4.le_emultiplicity_Δ (h : Step4.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.le_emultiplicity_Δ h hn
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 5** reports `IV`, never an `I_n`. -/
lemma Step5.le_emultiplicity_Δ (h : Step5.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.le_emultiplicity_Δ h hn
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hn

/-- **Step 6** reports `I₀*`, which is `KodairaSymbol.I! 0` and never an `I_n`. -/
lemma Step6.le_emultiplicity_Δ (h : Step6.run ϖ W = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.le_emultiplicity_Δ h hn
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

variable [IsNoetherianRing R] [IsDomain R]

/-- Every answer of the `I_n*` subprocedure of Step 7 carries a starred Kodaira symbol, hence never
an `I_n`. -/
lemma Step7.subprocedure_ne_I (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, m, m + 1, 2 * m, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) (n : ℕ) :
    (Step7.subprocedure hϖ hΔ hm hW ha₂).kodairaSymbol ≠ KodairaSymbol.I n := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- **Step 7** reports an `I_n` only with `n ≤ v_ϖ(Δ)`: an error there is inherited from an earlier
step or comes from its `I_n*` subprocedure. -/
lemma Step7.le_emultiplicity_Δ (h : Step7.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.le_emultiplicity_Δ (heq.trans h) hn
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    refine absurd hn ?_
    apply Step7.subprocedure_ne_I

/-- **Step 8** reports `IV*`, never an `I_n`. -/
lemma Step8.le_emultiplicity_Δ (h : Step8.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.le_emultiplicity_Δ hϖ hΔ h hn
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp at hn

/-- **Step 9** reports `III*`, never an `I_n`. -/
lemma Step9.le_emultiplicity_Δ (h : Step9.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.le_emultiplicity_Δ hϖ hΔ h hn
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 10** reports `II*`, never an `I_n`. -/
lemma Step10.le_emultiplicity_Δ (h : Step10.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.le_emultiplicity_Δ hϖ hΔ h hn
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp at hn

/-- **Step 11** constructs no output, so an error there is inherited from Step 10. -/
lemma Step11.le_emultiplicity_Δ (h : Step11.run hϖ hΔ = Except.error out)
    (hn : out.kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.le_emultiplicity_Δ hϖ hΔ h hn
  · simp at h

/-- **An `I_n` answer forces `n ≤ v_ϖ(Δ)`**, for every `n`. -/
theorem run_le_emultiplicity_Δ_forall :
    ∀ n : ℕ, (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I n → (n : ℕ∞) ≤ emultiplicity ϖ W.Δ := by
  induction W, hΔ using run.induct hϖ with
  | case1 W hΔ out h =>
    intro n hn
    rw [run_eq_of_step11_error hϖ hΔ h] at hn
    exact Step11.le_emultiplicity_Δ hϖ hΔ h hn
  | case2 W hΔ W' h ih =>
    intro n hn
    have hΔ' : W'.Δ ≠ 0 := fun h0 ↦ hΔ (by rw [← Step11.run_Δ hϖ hΔ h, h0, mul_zero])
    rw [run_eq_of_step11_ok hϖ hΔ h hΔ'] at hn
    refine (ih n hn).trans (emultiplicity_le_emultiplicity_of_dvd_right ⟨ϖ ^ 12, ?_⟩)
    rw [← Step11.run_Δ hϖ hΔ h]
    ring

/-- **The minimality-free valuation bound.** If Tate's algorithm answers `I_n` on a model `W`, then
`n ≤ v_ϖ(Δ(W))`, whether or not `W` is minimal. -/
theorem le_emultiplicity_Δ_of_run_kodairaSymbol_eq_I {n : ℕ}
    (hn : (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I n) : (n : ℕ∞) ≤ emultiplicity ϖ W.Δ :=
  run_le_emultiplicity_Δ_forall hϖ hΔ n hn

end WeierstrassCurve.TateAlgorithm

/-! ### Two square roots modulo `p^j`, at every prime -/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- A natural number prime to `p` is a unit of `ℤ_[p]`. -/
theorem isUnit_natCast_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) := by
  rw [isUnit_iff]
  rcases lt_or_eq_of_le (norm_le_one ((n : ℕ) : ℤ_[p])) with hlt | heq
  · exact absurd (norm_natCast_lt_one_iff.mp hlt) hn
  · exact heq

/-- **The ultrametric splitting of a deep product.** If `p^m ∣ xy` and `2j ≤ m + 1`, then `p^j`
divides `x` or `y`. -/
theorem pow_dvd_or_pow_dvd_of_pow_dvd_mul {j m : ℕ} (hjm : 2 * j ≤ m + 1) {x y : ℤ_[p]}
    (h : (p : ℤ_[p]) ^ m ∣ x * y) :
    (p : ℤ_[p]) ^ j ∣ x ∨ (p : ℤ_[p]) ^ j ∣ y := by
  by_contra hcon
  rw [not_or, pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, not_le, not_le] at hcon
  obtain ⟨hx, hy⟩ := hcon
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hx.ne_top
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hy.ne_top
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_mul prime_p, ← ha, ← hb] at h
  rw [← ha] at hx
  rw [← hb] at hy
  have hxn : a < j := by exact_mod_cast hx
  have hyn : b < j := by exact_mod_cast hy
  have hmn : m ≤ a + b := by exact_mod_cast h
  omega

/-- **The mass of a shifted quadratic congruence class.** For a unit `u`, any `c`, and any `j` with
`2j ≤ k + 1`,

  `μ_p {b | p^{s+k} ∣ c + p^s u b²} ≤ 2 p^{-j}`. -/
theorem volume_setOf_pow_dvd_add_sq_le {s k j : ℕ} (hjk : 2 * j ≤ k + 1) {u c : ℤ_[p]}
    (hu : IsUnit u) :
    (volume : Measure ℤ_[p])
        {b : ℤ_[p] | (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2}
      ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
  rcases eq_empty_or_nonempty
      {b : ℤ_[p] | (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2} with hE | ⟨b₀, hb₀⟩
  · simp [hE]
  have hb₀' : (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b₀ ^ 2 := hb₀
  have hps : ((p : ℤ_[p]) ^ s) ≠ 0 := pow_ne_zero s prime_p.ne_zero
  have hsub : {b : ℤ_[p] | (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2}
      ⊆ (toZModPow j ⁻¹' {toZModPow j b₀}) ∪ (toZModPow j ⁻¹' {toZModPow j (-b₀)}) := by
    intro b hb
    have hb' : (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2 := hb
    have hd : (p : ℤ_[p]) ^ s * (p : ℤ_[p]) ^ k
        ∣ (p : ℤ_[p]) ^ s * (u * ((b - b₀) * (b + b₀))) := by
      have hds := dvd_sub hb' hb₀'
      rw [show c + (p : ℤ_[p]) ^ s * u * b ^ 2 - (c + (p : ℤ_[p]) ^ s * u * b₀ ^ 2)
        = (p : ℤ_[p]) ^ s * (u * ((b - b₀) * (b + b₀))) from by ring] at hds
      rwa [← pow_add]
    have hk : (p : ℤ_[p]) ^ k ∣ (b - b₀) * (b + b₀) :=
      hu.dvd_mul_left.mp ((mul_dvd_mul_iff_left hps).mp hd)
    rcases pow_dvd_or_pow_dvd_of_pow_dvd_mul hjk hk with hle | hle
    · exact Or.inl (toZModPow_eq_iff_pow_dvd_sub.mpr hle)
    · refine Or.inr (toZModPow_eq_iff_pow_dvd_sub.mpr ?_)
      rwa [sub_neg_eq_add]
  calc (volume : Measure ℤ_[p])
        {b : ℤ_[p] | (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2}
      ≤ volume ((toZModPow j ⁻¹' {toZModPow j b₀})
          ∪ (toZModPow j ⁻¹' {toZModPow j (-b₀)})) := measure_mono hsub
    _ ≤ volume (toZModPow j ⁻¹' {toZModPow j b₀})
          + volume (toZModPow j ⁻¹' {toZModPow j (-b₀)}) := measure_union_le _ _
    _ = 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
        rw [volume_preimage_toZModPow, volume_preimage_toZModPow, ENNReal.inv_pow]
        ring

end PadicInt

/-! ### The discriminant-valuation locus of the coefficient plane -/

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The locus `{v_p(Δ) ≥ m}` of the coefficient plane. -/
def dvdΔLocus (m : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  {x | (p : ℤ_[p]) ^ m ∣ (ofShortNF x.1 x.2).Δ}

/-- A point `(a₄, a₆)` lies in `dvdΔLocus p m` if and only if `p ^ m` divides the discriminant
of the short Weierstrass curve `y² = x³ + a₄ x + a₆`. -/
@[simp] theorem mem_dvdΔLocus {m : ℕ} {x : ℤ_[p] × ℤ_[p]} :
    x ∈ dvdΔLocus p m ↔ (p : ℤ_[p]) ^ m ∣ (ofShortNF x.1 x.2).Δ := Iff.rfl

/-- The locus `{v_p(Δ) ≥ m}` is measurable. -/
theorem measurableSet_dvdΔLocus (m : ℕ) : MeasurableSet (dvdΔLocus p m) := by
  have hmeas : Measurable fun x : ℤ_[p] × ℤ_[p] => (ofShortNF x.1 x.2).Δ := by
    simp only [ofShortNF_Δ]
    fun_prop
  have he : dvdΔLocus p m
      = (fun x : ℤ_[p] × ℤ_[p] => (ofShortNF x.1 x.2).Δ) ⁻¹'
          ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    ext x
    simp [Ideal.mem_span_singleton]
  rw [he]
  exact hmeas (PadicInt.measurableSet_span_pPow m)

/-- **The mass of the discriminant-valuation locus.** If `-432 = p^s u` with `u` a unit, then for
every `j` with `2j ≤ k + 1`

  `μ_p {v_p(Δ) ≥ s + k} ≤ 2 p^{-j}`. -/
theorem volume_dvdΔLocus_le {s k j : ℕ} (hjk : 2 * j ≤ k + 1) {u : ℤ_[p]} (hu : IsUnit u)
    (hpu : (p : ℤ_[p]) ^ s * u = -432) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (dvdΔLocus p (s + k)) ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
  have hslice : ∀ a : ℤ_[p], (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' dvdΔLocus p (s + k))
      ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
    intro a
    refine le_trans (measure_mono ?_)
      (PadicInt.volume_setOf_pow_dvd_add_sq_le (s := s) (k := k) (c := -64 * a ^ 3) hjk hu)
    intro b hb
    have hb' : (p : ℤ_[p]) ^ (s + k) ∣ (ofShortNF a b).Δ := hb
    rw [ofShortNF_Δ] at hb'
    change (p : ℤ_[p]) ^ (s + k) ∣ -64 * a ^ 3 + (p : ℤ_[p]) ^ s * u * b ^ 2
    rwa [show -64 * a ^ 3 + (p : ℤ_[p]) ^ s * u * b ^ 2 = -16 * (4 * a ^ 3 + 27 * b ^ 2) from by
      rw [hpu]; ring]
  calc (volume : Measure (ℤ_[p] × ℤ_[p])) (dvdΔLocus p (s + k))
      = ((volume : Measure ℤ_[p]).prod (volume : Measure ℤ_[p])) (dvdΔLocus p (s + k)) := by
        rw [← Measure.volume_eq_prod]
    _ ≤ ∫⁻ a, (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' dvdΔLocus p (s + k))
          ∂(volume : Measure ℤ_[p]) :=
        Measure.prod_apply_le (measurableSet_dvdΔLocus (s + k))
    _ ≤ ∫⁻ _ : ℤ_[p], 2 * ((p : ℝ≥0∞)⁻¹) ^ j ∂(volume : Measure ℤ_[p]) := lintegral_mono hslice
    _ = 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by rw [lintegral_const, measure_univ, mul_one]

/-! ### From the stratum to the valuation locus -/

/-- **The split-multiplicative stratum lies in `{v_p(Δ) ≥ t}`.** -/
theorem stratFibre_subset_dvdΔLocus (t : ℕ) :
    stratFibre p (KodairaSymbol.I t, t) ⊆ dvdΔLocus p t := by
  intro x hx
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
  have hstrat : strat p ⟨x, hUp⟩ = (KodairaSymbol.I t, t) := (mem_stratFibre_iff hUp).1 hx
  have hkod : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I t := by
    rw [strat] at hstrat
    exact congrArg Prod.fst hstrat
  change (p : ℤ_[p]) ^ t ∣ (ofShortNF x.1 x.2).Δ
  exact pow_dvd_of_le_emultiplicity
    (TateAlgorithm.le_emultiplicity_Δ_of_run_kodairaSymbol_eq_I PadicInt.uniformizer_ne_zero
      hUp hkod)

/-- **`δ_p(t)` is dominated by the mass of `{v_p(Δ) ≥ t}`, for `t ≥ 5`, at every prime.** -/
theorem δ_le_volume_dvdΔLocus {t : ℕ} (ht : 5 ≤ t) :
    δ p t ≤ (volume : Measure (ℤ_[p] × ℤ_[p])) (dvdΔLocus p t) := by
  rw [δ_eq_deltaP_I ht, ← volume_stratFibre]
  exact measure_mono (stratFibre_subset_dvdΔLocus t)

/-! ### `-432` as `p^s ·` unit, at every prime -/

/-- **The coefficient `-432` of `a₆²` in `Δ = -64a₄³ - 432a₆²`, factored at every prime.** There
are `s ≤ 4` and a unit `u` of `ℤ_[p]` with `p^s u = -432`:

* `p = 2`: `s = 4`, `u = -27`;
* `p = 3`: `s = 3`, `u = -16`;
* `p ≥ 5`: `s = 0`, `u = -432`. -/
theorem exists_pow_mul_isUnit_eq_neg_fourHundredThirtyTwo (p : ℕ) [Fact p.Prime] :
    ∃ s : ℕ, s ≤ 4 ∧ ∃ u : ℤ_[p], IsUnit u ∧ (p : ℤ_[p]) ^ s * u = -432 := by
  have hp : p.Prime := Fact.out
  by_cases h2 : p = 2
  · subst h2
    refine ⟨4, by norm_num, -27, ?_, by push_cast; norm_num⟩
    simpa using (PadicInt.isUnit_natCast_of_not_dvd (p := 2) (n := 27) (by norm_num)).neg
  by_cases h3 : p = 3
  · subst h3
    refine ⟨3, by norm_num, -16, ?_, by push_cast; norm_num⟩
    simpa using (PadicInt.isUnit_natCast_of_not_dvd (p := 3) (n := 16) (by norm_num)).neg
  have h5 : 5 ≤ p := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact absurd rfl h2
    · obtain ⟨m, hm⟩ := hodd
      have := hp.two_le
      omega
  have hnd : ¬ p ∣ 432 := by
    intro hd
    rw [show (432 : ℕ) = 2 ^ 4 * 3 ^ 3 from by norm_num, hp.dvd_mul] at hd
    rcases hd with hd | hd
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hd)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hd)
      omega
  refine ⟨0, by norm_num, -432, ?_, by norm_num⟩
  simpa using (PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 432) hnd).neg

/-! ### The decay law -/

/-- **Geometric decay of the tail density, at every prime.** For every prime `p` and every `t ≥ 5`

  `δ_p(t) ≤ 2 p^{-⌊(t-3)/2⌋}`. -/
theorem δ_le_two_mul_inv_pow {t : ℕ} (ht : 5 ≤ t) :
    δ p t ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ ((t - 3) / 2) := by
  obtain ⟨s, hs4, u, hu, hpu⟩ := exists_pow_mul_isUnit_eq_neg_fourHundredThirtyTwo p
  have hst : s + (t - s) = t := by omega
  have hb := volume_dvdΔLocus_le (p := p) (s := s) (k := t - s) (j := (t - 3) / 2)
    (by omega) hu hpu
  rw [hst] at hb
  exact (δ_le_volume_dvdΔLocus ht).trans hb

/-- `δ_p(t).toReal ≤ 2 p^{-⌊(t-3)/2⌋}` for every prime `p` and every `t ≥ 5`. -/
theorem δ_toReal_le_two_mul_inv_pow {t : ℕ} (ht : 5 ≤ t) :
    (δ p t).toReal ≤ 2 * ((p : ℝ)⁻¹) ^ ((t - 3) / 2) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hinv : (p : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [hp0]
  have hne : (2 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ ((t - 3) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hinv)
  have h := ENNReal.toReal_mono hne (δ_le_two_mul_inv_pow (p := p) ht)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv] using h

/-! ### Summability of the weighted moments -/

/-- `p^{-⌊s/2⌋} ≤ (4/3)(3/4)^s` for every prime `p` and every `s`. -/
theorem inv_pow_div_two_le (s : ℕ) :
    ((p : ℝ)⁻¹) ^ (s / 2) ≤ (4 / 3 : ℝ) * (3 / 4 : ℝ) ^ s := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hnn : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hle : (p : ℝ)⁻¹ ≤ (3 / 4 : ℝ) ^ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hexp : (3 / 4 : ℝ) ^ (2 * (s / 2) + 1) ≤ (3 / 4 : ℝ) ^ s :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).2 (by omega)
  calc ((p : ℝ)⁻¹) ^ (s / 2) ≤ ((3 / 4 : ℝ) ^ 2) ^ (s / 2) := by gcongr
    _ = (4 / 3 : ℝ) * (3 / 4 : ℝ) ^ (2 * (s / 2) + 1) := by
        rw [← pow_mul, pow_succ]
        ring
    _ ≤ (4 / 3 : ℝ) * (3 / 4 : ℝ) ^ s := mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- **The weighted moments of the tail density are summable, at every prime.** For every `k`,
`∑_t δ_p(t) (t+1)^k` converges in `ℝ`. -/
theorem summable_δ_toReal_mul_add_one_pow (k : ℕ) :
    Summable fun t : ℕ => (δ p t).toReal * ((t : ℝ) + 1) ^ k := by
  rw [← summable_nat_add_iff 5]
  have hmaj : Summable fun s : ℕ => (8 / 3 : ℝ) * (((s + 6 : ℕ) : ℝ) ^ k * (3 / 4 : ℝ) ^ s) :=
    (BSDTamagawa.PolyGeomTail.summable_add_pow_mul_geometric_of_norm_lt_one 6 k
      (by rw [Real.norm_eq_abs]; norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_) hmaj
  have hcast : ((s + 5 : ℕ) : ℝ) + 1 = ((s + 6 : ℕ) : ℝ) := by push_cast; ring
  have hexp : (s + 5 - 3) / 2 = (s + 2) / 2 := by omega
  have hdecay : (δ p (s + 5)).toReal ≤ 2 * ((p : ℝ)⁻¹) ^ ((s + 2) / 2) := by
    have h := δ_toReal_le_two_mul_inv_pow (p := p) (t := s + 5) (by omega)
    rwa [hexp] at h
  have hgeo : ((p : ℝ)⁻¹) ^ ((s + 2) / 2) ≤ (4 / 3 : ℝ) * (3 / 4 : ℝ) ^ s := by
    refine (inv_pow_div_two_le (p := p) (s + 2)).trans ?_
    rw [pow_add]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) s]
  have hpow : (0 : ℝ) ≤ ((s + 6 : ℕ) : ℝ) ^ k := by positivity
  calc (δ p (s + 5)).toReal * (((s + 5 : ℕ) : ℝ) + 1) ^ k
      = (δ p (s + 5)).toReal * ((s + 6 : ℕ) : ℝ) ^ k := by rw [hcast]
    _ ≤ (2 * ((p : ℝ)⁻¹) ^ ((s + 2) / 2)) * ((s + 6 : ℕ) : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hdecay hpow
    _ ≤ (2 * ((4 / 3 : ℝ) * (3 / 4 : ℝ) ^ s)) * ((s + 6 : ℕ) : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (by linarith) hpow
    _ = (8 / 3 : ℝ) * (((s + 6 : ℕ) : ℝ) ^ k * (3 / 4 : ℝ) ^ s) := by ring

/-! ### The weighted second moment at every prime -/

/-- **The weighted second moment, in `ℝ`.** `Summable (fun t => δ_p(t).toReal (t+1)²)` at every
prime. -/
theorem summable_δ_toReal_mul_add_one_sq :
    Summable fun t : ℕ => (δ p t).toReal * ((t : ℝ) + 1) ^ 2 :=
  summable_δ_toReal_mul_add_one_pow 2

/-! ### The moments `∑ δ_p(t) t^k` -/

/-- **The `k`-th moment of `δ_p` is summable in `ℝ`, at every prime**, with the bare weight
`t^k`. -/
theorem summable_δ_toReal_mul_pow (k : ℕ) :
    Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ k :=
  Summable.of_nonneg_of_le (fun t => by positivity)
    (fun t => by
      have h0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
      have h : (t : ℝ) ^ k ≤ ((t : ℝ) + 1) ^ k := by
        gcongr
        all_goals linarith
      exact mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg)
    (summable_δ_toReal_mul_add_one_pow k)

end WeierstrassCurve
