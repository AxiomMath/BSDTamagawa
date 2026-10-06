/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.HeadSumThree
public import BSDTamagawa.LocalDensity.AdditiveDecomposition

/-!
# The geometric tail law at primes `p ≥ 5`

For a prime `p ≥ 5`, granted `WeierstrassCurve.StratScaleInvariant p` (the reduction datum of a
short model is unchanged by the dilation `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)`), the local density satisfies

  `δ_p(t) = a_p p^{-t}` for every `t ≥ 5`, with `a_p = 2N² p^{-2} (1 - p^{-10})^{-1} ≤ 1`,
  `N = |goodRes p| = (p-1)/2`.

For `t ≥ 3` the part of the stratum `τ_p⁻¹((I_t, t))` outside the image of `σ_p` is the congruence
locus `{p ∤ a₄, v_p(4a₄³ + 27a₆²) = t, 864a₆ a square mod p}`, of mass exactly `2N² p^{-(t+2)}`;
the part inside the image of `σ_p` has mass `p^{-10} δ_p((I_t, t))`. Solving the resulting
fixed-point equation `δ_p((I_t, t)) = p^{-10} δ_p((I_t, t)) + 2N² p^{-(t+2)}` gives the closed
form. The factor `(1 - p^{-10})^{-1}` is the geometric series over the non-minimal models above
each minimal one.

## Main definitions

* `WeierstrassCurve.iLocus`, `WeierstrassCurve.iSplitLocus`, `WeierstrassCurve.iNonSplitLocus`: the
  level-`t` multiplicative locus `{p ∤ a₄, v_p(4a₄³ + 27a₆²) = t}` and its split and non-split
  parts.
* `WeierstrassCurve.tailConstant`: `a_p = 2N² p⁻² (1 - p⁻¹⁰)⁻¹`.

## Main results

* `WeierstrassCurve.TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I`: if Tate's algorithm answers
  `I_n` on a model with `ϖ ∣ Δ` and `ϖ ∣ c₄`, then `ϖ⁴ ∣ c₄` and `ϖ⁶ ∣ c₆`.
* `WeierstrassCurve.volume_iSplitLocus`: the split level-`t` locus has mass `2N² p^{-(t+2)}`.
* `WeierstrassCurve.stratFibre_diff_range_eq_iSplitLocus`: for `t ≥ 3`,
  `τ_p⁻¹((I_t, t)) ∖ σ_p(ℤ_p²)` is the split level-`t` locus.
* `WeierstrassCurve.deltaP_I_eq_tailConstant_mul`: `δ_p((I_t, t)) = a_p p^{-t}` for `t ≥ 3`.
* `WeierstrassCurve.δ_eq_tailConstant_mul`: `δ_p(t) = a_p p^{-t}` for `t ≥ 5`.
* `WeierstrassCurve.hasTailGeometricLaw_of_stratScaleInvariant`: `HasTailGeometricLaw p` for
  `p ≥ 5`, granted `StratScaleInvariant p`.

## Implementation notes

The tower of non-minimal models is summed implicitly, by solving a fixed-point equation for a
finite quantity rather than by a series. The only `ℝ≥0∞` difference in the final constant is
`1 - p^{-10}`, used after `p^{-10} < 1` has been established.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

universe u

/-! ### Only Steps 1 and 2 can answer `I_n`, and Step 2 cannot when `ϖ ∣ c₄` -/

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R}

/-- **A cuspidal model has `ϖ ∣ b₂` after the Step-2 translation.** If `ϖ ∣ Δ` and `ϖ ∣ c₄`, then
`ϖ` divides `b₂` of the Step-2 translate. -/
theorem Step2.dvd_translate_b₂_of_dvd_c₄ (hΔ : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄) :
    ϖ ∣ (Step2.translate ϖ W).b₂ := by
  have hb₄ : ϖ ∣ (Step2.translate ϖ W).b₄ := by simpa using (Step2.hasValuation_translate hΔ).b₄
  have hsq : ϖ ∣ (Step2.translate ϖ W).b₂ * (Step2.translate ϖ W).b₂ := by
    have h : (Step2.translate ϖ W).b₂ * (Step2.translate ϖ W).b₂
        = (Step2.translate ϖ W).c₄ + 24 * (Step2.translate ϖ W).b₄ := by
      rw [WeierstrassCurve.c₄]; ring
    rw [h, Step2.translate_c₄]
    exact dvd_add hc₄ (hb₄.mul_left 24)
  have hprime : (span {ϖ} : Ideal R).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  rcases hprime.mem_or_mem (Ideal.mem_span_singleton.2 hsq) with h | h <;>
    exact Ideal.mem_span_singleton.1 h

/-- **Step 2 does not answer on a cuspidal model.** If `ϖ ∣ Δ` and `ϖ ∣ c₄`, Step 2 hands on the
Step-2 translate. -/
theorem Step2.run_eq_ok_of_dvd_c₄ (hΔ : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄) :
    Step2.run ϖ W = Except.ok (Step2.translate ϖ W) := by
  rw [Step2.run.eq_def, Step1.run.eq_def, ite_eq_left hΔ]
  simp only [except_ok_bind]
  exact ite_eq_left (Step2.dvd_translate_b₂_of_dvd_c₄ hΔ hc₄)

/-- Step 3 answers `II`, never an `I_n`. -/
private theorem Step3.kodairaSymbol_ne_I (hΔ : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step3.run ϖ W = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · rw [Step2.run_eq_ok_of_dvd_c₄ hΔ hc₄] at h; exact absurd h (by simp)
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 4 answers `III`, never an `I_n`. -/
private theorem Step4.kodairaSymbol_ne_I (hΔ : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step4.run ϖ W = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_ne_I hΔ hc₄ h n
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 5 answers `IV`, never an `I_n`. -/
private theorem Step5.kodairaSymbol_ne_I (hΔ : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step5.run ϖ W = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_ne_I hΔ hc₄ h n
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 6 answers `I₀*`, which is `KodairaSymbol.I! 0` and not an `I_n`. -/
private theorem Step6.kodairaSymbol_ne_I (hΔ : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step6.run ϖ W = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_ne_I hΔ hc₄ h n
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

variable [IsNoetherianRing R] [IsDomain R]

/-- Every answer of the `I_n*` subprocedure of Step 7 has a starred Kodaira symbol. -/
private theorem Step7.subprocedure_kodairaSymbol_ne_I (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, m, m + 1, 2 * m, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) (n : ℕ) :
    (Step7.subprocedure hϖ hΔ hm hW ha₂).kodairaSymbol ≠ KodairaSymbol.I n := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- Step 7 either inherits an earlier answer or answers inside its `I_n*` subprocedure. -/
private theorem Step7.kodairaSymbol_ne_I (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step7.run hϖ hΔ = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_ne_I hd hc₄ (heq.trans h) n
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    apply Step7.subprocedure_kodairaSymbol_ne_I

/-- Step 8 answers `IV*`, never an `I_n`. -/
private theorem Step8.kodairaSymbol_ne_I (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step8.run hϖ hΔ = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_ne_I hϖ hΔ hd hc₄ h n
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 9 answers `III*`, never an `I_n`. -/
private theorem Step9.kodairaSymbol_ne_I (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step9.run hϖ hΔ = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.kodairaSymbol_ne_I hϖ hΔ hd hc₄ h n
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 10 answers `II*`, never an `I_n`. -/
private theorem Step10.kodairaSymbol_ne_I (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step10.run hϖ hΔ = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.kodairaSymbol_ne_I hϖ hΔ hd hc₄ h n
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 11 never answers on its own — it only minimalizes the curve. -/
private theorem Step11.kodairaSymbol_ne_I (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄)
    (h : Step11.run hϖ hΔ = Except.error out) (n : ℕ) : out.kodairaSymbol ≠ KodairaSymbol.I n := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.kodairaSymbol_ne_I hϖ hΔ hd hc₄ h n
  · simp at h

/-- **The minimality criterion at a cusp.** If Tate's algorithm answers `I_n` on a curve with
`ϖ ∣ Δ` and `ϖ ∣ c₄`, then `ϖ⁴ ∣ c₄` and `ϖ⁶ ∣ c₆`: a model whose reduction is a cusp can only be
reported multiplicative by being non-minimal. -/
theorem pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I (hd : ϖ ∣ W.Δ) (hc₄ : ϖ ∣ W.c₄) {n : ℕ}
    (h : (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I n) : ϖ ^ 4 ∣ W.c₄ ∧ ϖ ^ 6 ∣ W.c₆ := by
  cases e : Step11.run hϖ hΔ with
  | error out' =>
    exact absurd ((run_eq_of_step11_error hϖ hΔ e) ▸ h)
      (Step11.kodairaSymbol_ne_I hϖ hΔ hd hc₄ e n)
  | ok W' =>
    exact ⟨⟨W'.c₄, (Step11.run_c₄ hϖ hΔ e).symm⟩, ⟨W'.c₆, (Step11.run_c₆ hϖ hΔ e).symm⟩⟩

end WeierstrassCurve.TateAlgorithm

/-! ### The level-`t` multiplicative locus of the coefficient plane -/

namespace WeierstrassCurve

open BSDTamagawa.HeadDensityTwoBound BSDTamagawa.HeadSumThree BSDTamagawa.LocalConstancy
  BSDTamagawa.LocalReduction TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The **level-`t` multiplicative locus**: the pairs `(a₄, a₆)` with `p ∤ a₄` and
`v_p(4a₄³ + 27a₆²) = t`. -/
def iLocus (t : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  {x | ¬ (p : ℤ_[p]) ∣ x.1 ∧
    emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) = (t : ℕ∞)}

variable (p) in
/-- The **split** part of the level-`t` multiplicative locus: `-c₆ = 864 a₆` is a square modulo
`p`. -/
def iSplitLocus (t : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  iLocus p t ∩ {x | IsSquare (PadicInt.toZMod (864 * x.2))}

variable (p) in
/-- The **non-split** part of the level-`t` multiplicative locus. -/
def iNonSplitLocus (t : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  iLocus p t ∩ {x | ¬ IsSquare (PadicInt.toZMod (864 * x.2))}

/-- On the level-`t` locus with `t ≥ 1` the defining form is divisible by `p`. -/
theorem dvd_form_of_mem_iLocus {t : ℕ} (ht : 1 ≤ t) {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ iLocus p t) :
    (p : ℤ_[p]) ∣ 4 * x.1 ^ 3 + 27 * x.2 ^ 2 := by
  have h := pow_dvd_of_le_emultiplicity (a := (p : ℤ_[p])) (b := 4 * x.1 ^ 3 + 27 * x.2 ^ 2)
    (k := 1) (by rw [hx.2]; exact_mod_cast ht)
  rwa [pow_one] at h

/-- On the level-`t` locus with `t ≥ 1` also `p ∤ a₆`: `p ∣ 4a₄³ + 27a₆²` and `p ∤ a₄` force it,
`4` being a unit. -/
theorem not_dvd_snd_of_mem_iLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ iLocus p t) : ¬ (p : ℤ_[p]) ∣ x.2 := by
  intro h6
  have h1 : (p : ℤ_[p]) ∣ 27 * x.2 ^ 2 := (h6.pow two_ne_zero).mul_left 27
  have h2 : (p : ℤ_[p]) ∣ 4 * x.1 ^ 3 := by
    have hs := dvd_sub (dvd_form_of_mem_iLocus ht hx) h1
    rwa [show 4 * x.1 ^ 3 + 27 * x.2 ^ 2 - 27 * x.2 ^ 2 = 4 * x.1 ^ 3 by ring] at hs
  rw [(isUnit_four hp).dvd_mul_left] at h2
  exact hx.1 (PadicInt.prime_p.dvd_of_dvd_pow h2)

/-- On the level-`t` locus with `t ≥ 1` the residue of `864 a₆` is nonzero. -/
theorem toZMod_mul_snd_ne_zero_of_mem_iLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ iLocus p t) : PadicInt.toZMod (864 * x.2) ≠ 0 := by
  rw [Ne, ← PadicInt.dvd_iff_toZMod_eq_zero, (isUnit_eightSixFour hp).dvd_mul_left]
  exact not_dvd_snd_of_mem_iLocus hp ht hx

/-- On the level-`t` locus the discriminant has valuation `t`, since `Δ = -16(4a₄³ + 27a₆²)` and
`-16` is a unit at `p ≥ 5`. -/
theorem emultiplicity_Δ_of_mem_iLocus (hp : 5 ≤ p) {t : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ iLocus p t) :
    emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = (t : ℕ∞) := by
  rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
    PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add]
  exact hx.2

/-- On the level-`t` locus `p ∤ c₄ = -48a₄`. -/
theorem not_dvd_c₄_of_mem_iLocus (hp : 5 ≤ p) {t : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ iLocus p t) : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
  rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
  exact hx.1

/-- On the level-`t` locus with `t ≥ 1` the model is nonsingular. -/
theorem mem_nonsingularLocus_of_mem_iLocus (hp : 5 ≤ p) {t : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ iLocus p t) :
    x ∈ nonsingularLocus p := by
  intro h0
  have hΔv := emultiplicity_Δ_of_mem_iLocus hp hx
  rw [h0, emultiplicity_zero_right] at hΔv
  exact absurd hΔv (by simp)

/-! ### Measurability -/

/-- The level-`t` locus is measurable. -/
theorem measurableSet_iLocus (t : ℕ) : MeasurableSet (iLocus p t) := by
  have h1 : MeasurableSet {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1} := by
    have he : {x : ℤ_[p] × ℤ_[p] | ¬ (p : ℤ_[p]) ∣ x.1}
        = (Prod.fst ⁻¹' ((Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) : Set ℤ_[p]))ᶜ := by
      ext x; simp [Ideal.mem_span_singleton]
    rw [he]
    exact (measurable_fst (PadicInt.measurableSet_span_pPow 1)).compl
  have hmeas : Measurable fun x : ℤ_[p] × ℤ_[p] => 4 * x.1 ^ 3 + 27 * x.2 ^ 2 := by fun_prop
  have h2 : MeasurableSet {x : ℤ_[p] × ℤ_[p] |
      emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) = (t : ℕ∞)} :=
    hmeas (PadicInt.measurableSet_setOf_emultiplicity_eq (p := p) t)
  exact h1.inter h2

/-- The split part of the level-`t` locus is measurable. -/
theorem measurableSet_iSplitLocus (t : ℕ) : MeasurableSet (iSplitLocus p t) :=
  (measurableSet_iLocus t).inter measurableSet_setOf_isSquare_toZMod_snd

/-! ### The mass of the level-`t` locus -/

/-- **The slice of the level-`t` locus over `a₄` is a square level set.** -/
theorem slice_iLocus_eq (hp : 5 ≤ p) {t : ℕ} {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) :
    Prod.mk a ⁻¹' iLocus p t = PadicInt.sqLevelSet (sqTarget a) t := by
  ext b
  simp only [mem_preimage, iLocus, mem_ofPred_eq, PadicInt.mem_sqLevelSet,
    emultiplicity_add_eq hp a b]
  exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩

/-- **The mass of every slice of the level-`t` locus**, for `t ≥ 1`: it is `2(1 - p⁻¹)p⁻ᵗ` on the
good first coordinates and `0` elsewhere. -/
theorem volume_slice_iLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (a : ℤ_[p]) :
    (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' iLocus p t)
      = (goodFst p).indicator (fun _ => 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ t) a := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  by_cases ha : (p : ℤ_[p]) ∣ a
  · have hempty : Prod.mk a ⁻¹' iLocus p t = (∅ : Set ℤ_[p]) :=
      Set.eq_empty_iff_forall_notMem.2 fun b hb => hb.1 ha
    rw [hempty, measure_empty, Set.indicator_of_notMem (fun hg => hg.1 ha)]
  · rw [slice_iLocus_eq hp ha]
    by_cases hs : IsSquare (sqTarget a)
    · rw [Set.indicator_of_mem (show a ∈ goodFst p from ⟨ha, hs⟩)]
      exact PadicInt.measure_sqLevelSet_of_isSquare hodd (isUnit_sqTarget hp ha) hs ht
    · rw [Set.indicator_of_notMem (fun hg => hs hg.2),
        PadicInt.measure_sqLevelSet_of_not_isSquare hodd (isUnit_sqTarget hp ha) hs ht]

/-- **The exact mass of the level-`t` locus**, for `t ≥ 1`:

  `μ_p(iLocus t) = N p⁻¹ · 2(1 - p⁻¹)p⁻ᵗ`,  `N = |goodRes p|`. -/
theorem volume_iLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (iLocus p t)
      = (goodRes p).card * (p : ℝ≥0∞)⁻¹ * (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ t) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_iLocus t)]
  calc ∫⁻ a, (volume : Measure ℤ_[p]) (Prod.mk a ⁻¹' iLocus p t) ∂(volume : Measure ℤ_[p])
      = ∫⁻ a, (goodFst p).indicator
          (fun _ => 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ t) a ∂(volume : Measure ℤ_[p]) :=
        lintegral_congr (volume_slice_iLocus hp ht)
    _ = 2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ t * volume (goodFst p) := by
        rw [lintegral_indicator (measurableSet_goodFst hp), setLIntegral_const]
    _ = (goodRes p).card * (p : ℝ≥0∞)⁻¹ * (2 * (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ t) := by
        rw [volume_goodFst hp]; ring

/-! ### The quadratic twist halves the level-`t` locus -/

/-- **The twist fixes the level-`t` locus**: `p ∤ ν²a₄` is `p ∤ a₄`, and the form is multiplied by
the unit `ν⁶`. -/
theorem mem_iLocus_twistPlane_iff {ν : ℤ_[p]} (hν : IsUnit ν) (t : ℕ) (x : ℤ_[p] × ℤ_[p]) :
    twistPlane ν x ∈ iLocus p t ↔ x ∈ iLocus p t := by
  have hform : 4 * (ν ^ 2 * x.1) ^ 3 + 27 * (ν ^ 3 * x.2) ^ 2
      = ν ^ 6 * (4 * x.1 ^ 3 + 27 * x.2 ^ 2) := by ring
  have hval : emultiplicity (p : ℤ_[p]) (4 * (ν ^ 2 * x.1) ^ 3 + 27 * (ν ^ 3 * x.2) ^ 2)
      = emultiplicity (p : ℤ_[p]) (4 * x.1 ^ 3 + 27 * x.2 ^ 2) := by
    rw [hform, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit (hν.pow 6), zero_add]
  simp only [iLocus, mem_ofPred_eq, twistPlane_fst, twistPlane_snd]
  rw [hval, (hν.pow 2).dvd_mul_left]

/-- **The twist by a non-residue flips the split test** on the level-`t` locus. -/
theorem isSquare_toZMod_twistPlane_iff_of_mem_iLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {ν : ℤ_[p]}
    (hχ : quadraticChar (ZMod p) (PadicInt.toZMod ν) = -1) {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ iLocus p t) :
    IsSquare (PadicInt.toZMod (864 * (twistPlane ν x).2))
      ↔ ¬ IsSquare (PadicInt.toZMod (864 * x.2)) := by
  have hcast : PadicInt.toZMod (864 * (twistPlane ν x).2)
      = PadicInt.toZMod ν ^ 3 * PadicInt.toZMod (864 * x.2) := by
    rw [twistPlane_snd,
      show (864 : ℤ_[p]) * (ν ^ 3 * x.2) = ν ^ 3 * (864 * x.2) by ring, map_mul, map_pow]
  rw [hcast]
  exact isSquare_cube_mul_iff hχ (toZMod_mul_snd_ne_zero_of_mem_iLocus hp ht hx)

/-- **The twist carries the non-split part onto the split part.** -/
theorem iNonSplitLocus_eq_preimage (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {ν : ℤ_[p]} (hν : IsUnit ν)
    (hχ : quadraticChar (ZMod p) (PadicInt.toZMod ν) = -1) :
    iNonSplitLocus p t = twistPlane ν ⁻¹' iSplitLocus p t := by
  ext x
  simp only [iNonSplitLocus, iSplitLocus, Set.mem_inter_iff, Set.mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨hxL, hns⟩
    exact ⟨(mem_iLocus_twistPlane_iff hν t x).2 hxL,
      (isSquare_toZMod_twistPlane_iff_of_mem_iLocus hp ht hχ hxL).2 hns⟩
  · rintro ⟨hxL, hs⟩
    have hxL' : x ∈ iLocus p t := (mem_iLocus_twistPlane_iff hν t x).1 hxL
    exact ⟨hxL', (isSquare_toZMod_twistPlane_iff_of_mem_iLocus hp ht hχ hxL').1 hs⟩

/-- The split and non-split parts partition the level-`t` locus. -/
theorem iLocus_eq_union (t : ℕ) : iLocus p t = iSplitLocus p t ∪ iNonSplitLocus p t := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · by_cases h : IsSquare (PadicInt.toZMod (864 * x.2))
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · exact hx.elim (·.1) (·.1)

/-- The split and non-split parts are disjoint. -/
theorem disjoint_iSplitLocus_iNonSplitLocus (t : ℕ) :
    Disjoint (iSplitLocus p t) (iNonSplitLocus p t) :=
  Set.disjoint_left.2 fun _ hx hx' => hx'.2 hx.2

/-- **The split part carries exactly half the mass of the level-`t` locus.** -/
theorem volume_iLocus_eq_two_mul (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (iLocus p t) = 2 * volume (iSplitLocus p t) := by
  obtain ⟨ν, hν, hχ⟩ := exists_isUnit_quadraticChar_eq_neg_one hp
  have hns : (volume : Measure (ℤ_[p] × ℤ_[p])) (iNonSplitLocus p t)
      = volume (iSplitLocus p t) := by
    rw [iNonSplitLocus_eq_preimage hp ht hν hχ]
    exact (measurePreserving_twistPlane hν).measure_preimage
      (measurableSet_iSplitLocus t).nullMeasurableSet
  rw [iLocus_eq_union t, measure_union (disjoint_iSplitLocus_iNonSplitLocus t)
    ((measurableSet_iLocus t).inter measurableSet_setOf_isSquare_toZMod_snd.compl), hns]
  ring

/-- **The exact mass of the split level-`t` locus**: `2N² p^{-(t+2)}`, i.e. `(p-1)²/(2p^{t+2})`. -/
theorem volume_iSplitLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (iSplitLocus p t)
      = 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 2) := by
  have h : 2 * (volume : Measure (ℤ_[p] × ℤ_[p])) (iSplitLocus p t)
      = 2 * (2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 2)) := by
    rw [← volume_iLocus_eq_two_mul hp ht, volume_iLocus hp ht, one_sub_inv_eq hp, pow_add]
    ring
  exact (ENNReal.mul_right_inj two_ne_zero (by norm_num)).1 h

/-! ### The split level-`t` locus **is** the minimal part of the stratum `τ_p⁻¹(I_t, t)` -/

/-- **The split level-`t` locus lies in the stratum `τ_p⁻¹((I_t, t))`.** On it `v_p(Δ) = t`,
`p ∤ c₄ = -48a₄` and `-c₆ = 864a₆` is a square modulo `p`, so the reduction datum is `(I_t, t)`. -/
theorem mem_stratFibre_of_mem_iSplitLocus (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ iSplitLocus p t) :
    x ∈ stratFibre p (KodairaSymbol.I t, t) := by
  obtain ⟨hxL, hsq⟩ := hx
  have hΔv := emultiplicity_Δ_of_mem_iLocus hp hxL
  have hUp : x ∈ nonsingularLocus p := mem_nonsingularLocus_of_mem_iLocus hp hxL
  have hc₄ := not_dvd_c₄_of_mem_iLocus hp hxL
  have hsplit : Step2.TangentSplits (p : ℤ_[p]) (ofShortNF x.1 x.2) := by
    rwa [Step2.tangentSplits_iff_isSquare_neg_c₆ (dvd_Δ_of_emultiplicity_eq ht hΔv) hc₄
      (not_dvd_two_of_odd ((Fact.out : p.Prime).odd_of_ne_two (by omega))),
      isSquare_mod_iff_isSquare_toZMod, ofShortNF_c₆,
      show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 by ring]
  obtain ⟨hk, hc⟩ := run_kodaira_tamagawa_of_tangentSplits hUp hc₄ ht hΔv hsplit
  exact (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk hc)

/-- **A point of the stratum `τ_p⁻¹((I_t, t))` with `p ∣ a₄` is a dilate.** For `t ≥ 1` the Kodaira
symbol `I_t` forces `p ∣ Δ`, and `p ∣ a₄` gives `p ∣ c₄ = -48a₄`; so
`pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I` applies and yields `p⁴ ∣ c₄`, `p⁶ ∣ c₆`, i.e. `p⁴ ∣ a₄` and
`p⁶ ∣ a₆` at `p ≥ 5`. -/
theorem mem_range_of_mem_stratFibre_of_dvd_fst (hp : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ stratFibre p (KodairaSymbol.I t, t))
    (h4 : (p : ℤ_[p]) ∣ x.1) :
    x ∈ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hx
  have hstrat : strat p ⟨x, hUp⟩ = (KodairaSymbol.I t, t) := (mem_stratFibre_iff hUp).1 hx
  have hkod : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I t := by
    rw [strat] at hstrat
    exact congrArg Prod.fst hstrat
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
    rw [ofShortNF_c₄]
    exact h4.mul_left _
  have hd : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
    by_contra hnd
    rw [run_eq_of_not_dvd_Δ hUp hnd] at hkod
    exact absurd (KodairaSymbol.I.inj hkod) (by omega)
  obtain ⟨h4', h6'⟩ := TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I
    PadicInt.uniformizer_ne_zero hUp hd hc₄ hkod
  rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4'
  rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6'
  rw [PadicInt.mem_range_scaleProdByPPow_iff]
  exact ⟨h4', h6'⟩

/-- **The minimal part of the stratum over `(I_t, t)` is the split level-`t` locus**, for every
prime `p ≥ 5` and every `t ≥ 3`:

  `τ_p⁻¹((I_t, t)) ∖ σ_p(ℤ_p²) = {p ∤ a₄, v_p(4a₄³ + 27a₆²) = t, 864a₆ a square mod p}`.

This identity uses no hypothesis about the behaviour of `τ_p` under `σ_p`. -/
theorem stratFibre_diff_range_eq_iSplitLocus (hp : 5 ≤ p) {t : ℕ} (ht : 3 ≤ t) :
    stratFibre p (KodairaSymbol.I t, t) \
        Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])
      = iSplitLocus p t := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxF, hxR⟩
    have hUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
    have h4 : ¬ (p : ℤ_[p]) ∣ x.1 := fun hd =>
      hxR (mem_range_of_mem_stratFibre_of_dvd_fst hp (by omega) hxF hd)
    have hc₄ : ¬ (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).c₄ := by
      rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left]
      exact h4
    have hstrat : strat p ⟨x, hUp⟩ = (KodairaSymbol.I t, t) := (mem_stratFibre_iff hUp).1 hxF
    have hpair : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I t ∧
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = t := by
      rw [strat] at hstrat
      exact ⟨congrArg Prod.fst hstrat, congrArg Prod.snd hstrat⟩
    obtain ⟨hΔv, hsq⟩ := (run_kodaira_tamagawa_eq_iff_isSquare hodd hUp hc₄ ht).1 hpair
    rw [ofShortNF_Δ, emultiplicity_mul PadicInt.prime_p,
      PadicInt.emultiplicity_eq_zero_of_isUnit ((isUnit_sixteen hp).neg), zero_add] at hΔv
    rw [ofShortNF_c₆, show -(-864 * x.2) = (864 : ℤ_[p]) * x.2 by ring,
      isSquare_mod_iff_isSquare_toZMod] at hsq
    exact ⟨⟨h4, hΔv⟩, hsq⟩
  · intro x hx
    refine ⟨mem_stratFibre_of_mem_iSplitLocus hp (by omega) hx, fun hr => ?_⟩
    exact hx.1.1 (dvd_trans (dvd_pow_self _ (by norm_num : 4 ≠ 0))
      (PadicInt.mem_range_scaleProdByPPow_iff.1 hr).1)

/-! ### The fixed-point equation for `δ_p((I_t, t))` -/

/-- **The tail density satisfies a `t`-uniform fixed-point equation**, for every prime `p ≥ 5` and
`t ≥ 3`, granted `StratScaleInvariant p`:

  `δ_p((I_t, t)) = p⁻¹⁰ δ_p((I_t, t)) + 2N² p^{-(t+2)}`,  `N = |goodRes p|`. -/
theorem deltaP_I_eq_add (hp : 5 ≤ p) (h : StratScaleInvariant p) {t : ℕ} (ht : 3 ≤ t) :
    deltaP p (KodairaSymbol.I t, t)
      = ((p : ℝ≥0∞)⁻¹) ^ 10 * deltaP p (KodairaSymbol.I t, t)
        + 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 2) := by
  have hz : (p : ℝ≥0∞) ^ (-(10 : ℤ)) = ((p : ℝ≥0∞)⁻¹) ^ 10 := by
    rw [show (-(10 : ℤ)) = -((10 : ℕ) : ℤ) by norm_num]
    exact (PadicInt.measure_span_pPow (p := p) 10).symm.trans (PadicInt.measure_span_pPow' 10)
  refine (deltaP_eq_inv_pow_mul_add h (KodairaSymbol.I t, t)).trans ?_
  rw [stratFibre_diff_range_eq_iSplitLocus hp ht, volume_iSplitLocus hp (by omega), hz]

/-! ### Solving the fixed-point equation -/

/-- **The unique finite solution of `x = rx + c` at `r < 1`** is `x = c(1 - r)⁻¹`. -/
private theorem eq_mul_inv_one_sub {r c x : ℝ≥0∞} (hr : r < 1) (hx : x ≠ ⊤)
    (hxe : x = r * x + c) : x = c * (1 - r)⁻¹ := by
  have hrx : r * x ≠ ⊤ := ENNReal.mul_ne_top (ne_top_of_lt hr) hx
  have hsub : x - r * x = c :=
    ENNReal.sub_eq_of_eq_add hrx (by rw [add_comm]; exact hxe)
  have hmul : (1 - r) * x = c := by
    rw [ENNReal.sub_mul (fun _ _ => hx), one_mul, hsub]
  have h1 : (1 : ℝ≥0∞) - r ≠ 0 := (tsub_pos_of_lt hr).ne'
  have h2 : (1 : ℝ≥0∞) - r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  calc x = (1 - r)⁻¹ * ((1 - r) * x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h1 h2, one_mul]
    _ = c * (1 - r)⁻¹ := by rw [hmul, mul_comm]

variable (p) in
/-- **The tail constant** `a_p = 2N² p⁻² (1 - p⁻¹⁰)⁻¹`, `N = |goodRes p|`; in closed form
`a_p = (p-1)² p⁸ / (2(p¹⁰ - 1))`. -/
noncomputable def tailConstant : ℝ≥0∞ :=
  2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 2 * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹

/-- `N p⁻¹ ≤ 1`, since `N ≤ 2N + 1 = p`. -/
private theorem card_goodRes_mul_inv_le_one (hp : 5 ≤ p) :
    ((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ≤ 1 := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hnat : (goodRes p).card ≤ p := by
    have := eq_two_mul_card_goodRes_add_one hp
    omega
  calc ((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ≤ (p : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ := by gcongr
    _ = 1 := ENNReal.mul_inv_cancel hp0 hpt

omit [Fact p.Prime] in
/-- `p⁻¹⁰ ≤ p⁻¹`. -/
private theorem inv_pow_ten_le_inv (hp : 5 ≤ p) : ((p : ℝ≥0∞)⁻¹) ^ 10 ≤ (p : ℝ≥0∞)⁻¹ :=
  pow_le_of_le_one zero_le (ENNReal.inv_le_one.2 (by exact_mod_cast (by omega : 1 ≤ p)))
    (by norm_num)

omit [Fact p.Prime] in
/-- `p⁻¹⁰ < 1`. -/
private theorem inv_pow_ten_lt_one (hp : 5 ≤ p) : ((p : ℝ≥0∞)⁻¹) ^ 10 < 1 :=
  lt_of_le_of_lt (inv_pow_ten_le_inv hp)
    (ENNReal.inv_lt_one.2 (by exact_mod_cast (by omega : 1 < p)))

/-- **The tail constant is `≤ 1`**, for `p ≥ 5`. -/
theorem tailConstant_le_one (hp : 5 ≤ p) : tailConstant p ≤ 1 := by
  have hA : 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 2
      ≤ 1 - ((p : ℝ≥0∞)⁻¹) ^ 10 := by
    calc 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 2
        = 2 * ((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹
            * (((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) := by ring
      _ ≤ 2 * ((goodRes p).card : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ * 1 := by
          gcongr; exact card_goodRes_mul_inv_le_one hp
      _ = 1 - (p : ℝ≥0∞)⁻¹ := by rw [mul_one, one_sub_inv_eq hp]
      _ ≤ 1 - ((p : ℝ≥0∞)⁻¹) ^ 10 := tsub_le_tsub_left (inv_pow_ten_le_inv hp) 1
  have h1 : (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10 ≠ 0 := (tsub_pos_of_lt (inv_pow_ten_lt_one hp)).ne'
  have h2 : (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [tailConstant]
  calc 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 2
        * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹
      ≤ (1 - ((p : ℝ≥0∞)⁻¹) ^ 10) * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by gcongr
    _ = 1 := ENNReal.mul_inv_cancel h1 h2

/-- **The split-multiplicative row of Table 5, granted `τ_p ∘ σ_p = τ_p`:** for every prime `p ≥ 5`
and every `t ≥ 3`,

  `δ_p((I_t, t)) = a_p p^{-t}`,  `a_p = 2N² p⁻² (1 - p⁻¹⁰)⁻¹`. -/
theorem deltaP_I_eq_tailConstant_mul (hp : 5 ≤ p) (h : StratScaleInvariant p) {t : ℕ}
    (ht : 3 ≤ t) :
    deltaP p (KodairaSymbol.I t, t) = tailConstant p * ((p : ℝ≥0∞)⁻¹) ^ t := by
  have hfix : deltaP p (KodairaSymbol.I t, t)
      = ((p : ℝ≥0∞)⁻¹) ^ 10 * deltaP p (KodairaSymbol.I t, t)
        + 2 * ((goodRes p).card : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ t := by
    refine (deltaP_I_eq_add hp h ht).trans ?_
    rw [pow_add]
    ring
  rw [eq_mul_inv_one_sub (inv_pow_ten_lt_one hp) (deltaP_ne_top p _) hfix, tailConstant]
  exact mul_right_comm _ _ _

/-! ### The geometric tail law -/

/-- **The geometric tail law for `δ_p`, at every prime `p ≥ 5`, granted `τ_p ∘ σ_p = τ_p`.**

  `δ_p(t) = a_p p^{-t}` for every `t ≥ 5`, with `a_p = 2N² p⁻² (1 - p⁻¹⁰)⁻¹ ≤ 1`. -/
theorem δ_eq_tailConstant_mul (hp : 5 ≤ p) (h : StratScaleInvariant p) {t : ℕ} (ht : 5 ≤ t) :
    δ p t = tailConstant p * ((p : ℝ≥0∞)⁻¹) ^ t := by
  rw [δ_eq_deltaP_I ht, deltaP_I_eq_tailConstant_mul hp h (by omega)]

/-- **`HasTailGeometricLaw p` for every prime `p ≥ 5`, granted `StratScaleInvariant p`**, with
witness `tailConstant p`. -/
theorem hasTailGeometricLaw_of_stratScaleInvariant (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    HasTailGeometricLaw p :=
  ⟨tailConstant p, tailConstant_le_one hp, fun _ ht => δ_eq_tailConstant_mul hp h ht⟩

end WeierstrassCurve
