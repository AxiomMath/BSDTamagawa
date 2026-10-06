/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.GeometricTailSmallPrimes
public import BSDTamagawa.NumberTheory.MultiplicativeStratum

/-!
# The good-reduction stratum of the short Weierstrass plane

Let `p` be a prime, write `σ_p(a₄, a₆) = (p⁴a₄, p⁶a₆)` for the dilation of the plane `ℤ_p²` of
short Weierstrass models, and `G_p = {p ∤ Δ}` for the good-reduction locus. We study the Haar mass
`δ_p(I₀, 1)` of the stratum of models whose reduction datum is `(I₀, 1)`, the `I₀` entry of Table 5
of Griffin–Ono–Tsai.

The good-reduction tower `⋃_{k ≥ 0} σ_p^k(G_p)` is a disjoint union whose `k`-th storey has mass
`p^{-10k}(1 - p^{-1})`, so for `p ≥ 5` its mass is `(1 - p^{-1})(1 - p^{-10})^{-1}`, which equals
`(p - 1)p⁹/(p¹⁰ - 1)`.

Only Step 1 of Tate's algorithm can return the Kodaira symbol `I₀`, so over a discrete valuation
ring a curve with Kodaira symbol `I₀` and `ϖ ∣ Δ` has `ϖ⁴ ∣ c₄` and `ϖ⁶ ∣ c₆`. On the short plane
at `p ≥ 5` this says that such a model is a dilate. Assuming that the reduction datum is invariant
under `σ_p` (`StratScaleInvariant p`), the `I₀` stratum is exactly the tower, and hence
`δ_p(I₀, 1) = (p - 1)p⁹/(p¹⁰ - 1)`.

## Main definitions

* `WeierstrassCurve.goodTower`: the good-reduction tower `⋃_{k ≥ 0} σ_p^k(G_p)`.
* `WeierstrassCurve.gotI0Volume`: the real number `(p - 1)p⁹/(p¹⁰ - 1)`.
* `WeierstrassCurve.MinimalOfDvdΔ`: every short model with reduction datum `(I₀, 1)` and `p ∣ Δ` is
  of the form `(p⁴a₄, p⁶a₆)`.

## Main results

* `WeierstrassCurve.TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I_zero`: if Tate's algorithm
  returns `I₀` on a curve with `ϖ ∣ Δ`, then `ϖ⁴ ∣ c₄` and `ϖ⁶ ∣ c₆`.
* `WeierstrassCurve.volume_goodTower_eq_ofReal`: for `p ≥ 5` the tower has mass
  `(p - 1)p⁹/(p¹⁰ - 1)`.
* `WeierstrassCurve.minimalOfDvdΔ`: `MinimalOfDvdΔ p` holds for `p ≥ 5`.
* `WeierstrassCurve.stratFibre_I0_eq_goodTower`: for `p ≥ 5`, under `StratScaleInvariant p`, the
  `I₀` stratum is the good-reduction tower.
* `WeierstrassCurve.deltaP_I0_eq_ofReal`: for `p ≥ 5`, under `StratScaleInvariant p`,
  `δ_p(I₀, 1) = (p - 1)p⁹/(p¹⁰ - 1)`.

## Implementation notes

The mass of the tower is a geometric series in `ℝ≥0∞`, evaluated with `measure_iUnion` and
`ENNReal.tsum_geometric`. Closed forms are stated as `ENNReal.ofReal` of the real number
`gotI0Volume p`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

universe u

/-! ### Only Step 1 of Tate's algorithm can answer `I₀`

An `Except.error` of a step is its answer, and each step's answer is either inherited from its
predecessor or one of finitely many explicit `Output`s. Of these, only Step 1's carries the Kodaira
symbol `I₀`, and Step 1 returns it only when `ϖ ∤ Δ`; Step 2's `I_n` has `n = v_ϖ(Δ) ≥ 1`. -/

namespace WeierstrassCurve.TateAlgorithm

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal]
  [PerfectField <| R ⧸ span {ϖ}] {W : WeierstrassCurve R} {out : Output R}

omit [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}] in
/-- Step 1 answers `I₀`, but only when `ϖ ∤ Δ`; under `ϖ ∣ Δ` it does not answer at all. -/
lemma Step1.kodairaSymbol_ne_I_zero (hd : ϖ ∣ W.Δ) (h : Step1.run ϖ W = Except.error out) :
    out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step1.run.eq_def] at h
  split_ifs at h

variable [IsNoetherianRing R] [IsDomain R]

/-- Step 2 answers `I_n` with `n = v_ϖ(Δ)`, and `n ≥ 1` when `ϖ ∣ Δ`. -/
lemma Step2.kodairaSymbol_ne_I_zero (hΔ : W.Δ ≠ 0) (hd : ϖ ∣ W.Δ)
    (h : Step2.run ϖ W = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step2.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', h', h⟩
  · exact Step1.kodairaSymbol_ne_I_zero hd h
  · have hn : 0 < (emultiplicity ϖ W.Δ).toNat :=
      toNat_emultiplicity_pos (IsMaximal.ne_top inferInstance) hΔ hd
    rw [Step1.run_weierstrassCurve h'] at h
    by_cases hb₂ : ϖ ∣ (Step2.translate ϖ W).b₂
    · rw [ite_eq_left hb₂] at h
      simp at h
    · rw [ite_eq_right hb₂] at h
      obtain rfl := Except.error.inj h
      simp only [Step2.translate_Δ, ne_eq, KodairaSymbol.I.injEq]
      omega

/-- Step 3 answers `II`. -/
lemma Step3.kodairaSymbol_ne_I_zero (hΔ : W.Δ ≠ 0) (hd : ϖ ∣ W.Δ)
    (h : Step3.run ϖ W = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step3.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step2.kodairaSymbol_ne_I_zero hΔ hd h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 4 answers `III`. -/
lemma Step4.kodairaSymbol_ne_I_zero (hΔ : W.Δ ≠ 0) (hd : ϖ ∣ W.Δ)
    (h : Step4.run ϖ W = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step4.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step3.kodairaSymbol_ne_I_zero hΔ hd h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 5 answers `IV`. -/
lemma Step5.kodairaSymbol_ne_I_zero (hΔ : W.Δ ≠ 0) (hd : ϖ ∣ W.Δ)
    (h : Step5.run ϖ W = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step5.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step4.kodairaSymbol_ne_I_zero hΔ hd h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 6 answers `I₀*`, which is `KodairaSymbol.I! 0` and not `KodairaSymbol.I 0`. -/
lemma Step6.kodairaSymbol_ne_I_zero (hΔ : W.Δ ≠ 0) (hd : ϖ ∣ W.Δ)
    (h : Step6.run ϖ W = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step6.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step5.kodairaSymbol_ne_I_zero hΔ hd h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Every answer of the `I_n*` subprocedure of Step 7 has a starred Kodaira symbol. -/
lemma Step7.subprocedure_kodairaSymbol_ne_I_zero (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {b₂ b₄ b₆ b₈ c₄ c₆ Δ : ℕ}
    (hW : HasValuation ϖ W ⟨1, 1, n, n + 1, 2 * n, b₂, b₄, b₆, b₈, c₄, c₆, Δ⟩)
    (ha₂ : ¬ϖ ^ 2 ∣ W.a₂) :
    (Step7.subprocedure hϖ hΔ hn hW ha₂).kodairaSymbol ≠ KodairaSymbol.I 0 := by
  fun_induction Step7.subprocedure with
  | case1 => assumption
  | case2 => simp
  | case3 => simp

/-- Step 7 either inherits an earlier answer or answers inside its `I_n*` subprocedure. -/
lemma Step7.kodairaSymbol_ne_I_zero (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0) (hd : ϖ ∣ W.Δ)
    (h : Step7.run hϖ hΔ = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step7.run.eq_def] at h
  split at h
  next out' heq => exact Step6.kodairaSymbol_ne_I_zero hΔ hd (heq.trans h)
  next W' heq =>
    split_ifs at h
    obtain rfl := Except.error.inj h
    apply Step7.subprocedure_kodairaSymbol_ne_I_zero

variable (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

/-- Step 8 answers `IV*`. -/
lemma Step8.kodairaSymbol_ne_I_zero (hd : ϖ ∣ W.Δ)
    (h : Step8.run hϖ hΔ = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step8.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step7.kodairaSymbol_ne_I_zero hϖ hΔ hd h
  · split_ifs at h <;>
      · obtain rfl := Except.error.inj h
        simp

/-- Step 9 answers `III*`. -/
lemma Step9.kodairaSymbol_ne_I_zero (hd : ϖ ∣ W.Δ)
    (h : Step9.run hϖ hΔ = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step9.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step8.kodairaSymbol_ne_I_zero hϖ hΔ hd h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 10 answers `II*`. -/
lemma Step10.kodairaSymbol_ne_I_zero (hd : ϖ ∣ W.Δ)
    (h : Step10.run hϖ hΔ = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step10.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step9.kodairaSymbol_ne_I_zero hϖ hΔ hd h
  · split_ifs at h
    obtain rfl := Except.error.inj h
    simp

/-- Step 11 never terminates with an answer of its own. -/
lemma Step11.kodairaSymbol_ne_I_zero (hd : ϖ ∣ W.Δ)
    (h : Step11.run hϖ hΔ = Except.error out) : out.kodairaSymbol ≠ KodairaSymbol.I 0 := by
  rw [Step11.run.eq_def, Except.bind_eq_error_iff] at h
  rcases h with h | ⟨W', -, h⟩
  · exact Step10.kodairaSymbol_ne_I_zero hϖ hΔ hd h
  · simp at h

/-- **The minimality criterion at `I₀`.** If Tate's algorithm answers `I₀` on a curve with `ϖ ∣ Δ`,
then `ϖ⁴ ∣ c₄` and `ϖ⁶ ∣ c₆`, so the model is not minimal. -/
lemma pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I_zero (hd : ϖ ∣ W.Δ)
    (h : (run hϖ hΔ).kodairaSymbol = KodairaSymbol.I 0) : ϖ ^ 4 ∣ W.c₄ ∧ ϖ ^ 6 ∣ W.c₆ := by
  cases e : Step11.run hϖ hΔ with
  | error out' =>
    exact absurd ((run_eq_of_step11_error hϖ hΔ e) ▸ h)
      (Step11.kodairaSymbol_ne_I_zero hϖ hΔ hd e)
  | ok W' =>
    exact ⟨⟨W'.c₄, (Step11.run_c₄ hϖ hΔ e).symm⟩, ⟨W'.c₆, (Step11.run_c₆ hϖ hΔ e).symm⟩⟩

end WeierstrassCurve.TateAlgorithm

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

variable {p : ℕ} [Fact p.Prime]

/-! ### The iterated dilation -/

/-- Composing two dilations of the coefficient plane adds the exponents. -/
theorem _root_.PadicInt.scaleProdByPPow_comp (m n m' n' : ℕ) :
    (PadicInt.scaleProdByPPow m n : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) ∘
        PadicInt.scaleProdByPPow m' n'
      = PadicInt.scaleProdByPPow (m + m') (n + n') := by
  funext x
  simp only [Function.comp_apply, PadicInt.scaleProdByPPow_apply, pow_add, mul_assoc]

/-! ### The good-reduction tower -/

variable (p) in
/-- **The good-reduction tower.** The union over `k ≥ 0` of the dilates
`σ_p^k(goodLocus p) = {(p^{4k} a₄, p^{6k} a₆) : p ∤ Δ(a₄, a₆)}` of the good-reduction locus. -/
def goodTower : Set (ℤ_[p] × ℤ_[p]) :=
  ⋃ k : ℕ, PadicInt.scaleProdByPPow (4 * k) (6 * k) '' goodLocus p

/-- The good-reduction locus is contained in the good-reduction tower. -/
theorem goodLocus_subset_goodTower : goodLocus p ⊆ goodTower p := by
  intro x hx
  refine Set.mem_iUnion.2 ⟨0, x, hx, ?_⟩
  simp [PadicInt.scaleProdByPPow_apply]

/-- A pair with both coefficients divisible by `p` has `p ∣ Δ`, so it is off the good locus. -/
theorem dvd_Δ_of_dvd_of_dvd {x : ℤ_[p] × ℤ_[p]} (h1 : (p : ℤ_[p]) ∣ x.1)
    (h2 : (p : ℤ_[p]) ∣ x.2) : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ := by
  rw [ofShortNF_Δ]
  exact Dvd.dvd.mul_left
    (dvd_add ((dvd_pow h1 three_ne_zero).mul_left 4)
      ((dvd_pow h2 two_ne_zero).mul_left 27)) _

/-- For `p ≥ 5`, the good locus is measurable: it is the level-one cylinder over the complement of
the cuspidal cubic (`goodLocus_eq_preimage`). -/
theorem measurableSet_goodLocus (hp : 5 ≤ p) : MeasurableSet (goodLocus p) := by
  have hU : PadicInt.redPair p ⁻¹' (ellipticResidues p : Set (ZMod p × ZMod p))
      = ⋃ c ∈ ellipticResidues p, PadicInt.redPair p ⁻¹' {c} := by
    ext x; simp
  rw [goodLocus_eq_preimage hp, hU]
  exact (ellipticResidues p).measurableSet_biUnion
    fun c _ => PadicInt.measurableSet_preimage_redPair_singleton c

/-- For `p ≥ 5` and every `k`, the dilate `σ_p^k(good locus)` is measurable. -/
theorem measurableSet_scale_goodLocus (hp : 5 ≤ p) (k : ℕ) :
    MeasurableSet (PadicInt.scaleProdByPPow (4 * k) (6 * k) '' goodLocus p) :=
  (PadicInt.measurableEmbedding_scaleProdByPPow (4 * k) (6 * k)).measurableSet_image.2
    (measurableSet_goodLocus hp)

/-- **The mass of the `k`-th storey of the tower**: for `p ≥ 5`, `σ_p^k(goodLocus p)` has mass
`p^{-10k}(1 - p^{-1})`. -/
theorem volume_scale_goodLocus (hp : 5 ≤ p) (k : ℕ) :
    (volume : Measure (ℤ_[p] × ℤ_[p]))
        (PadicInt.scaleProdByPPow (4 * k) (6 * k) '' goodLocus p)
      = ((p : ℝ≥0∞)⁻¹) ^ (10 * k) * (1 - (p : ℝ≥0∞)⁻¹) := by
  rw [PadicInt.measure_image_scaleProdByPPow, volume_goodLocus hp]
  congr 1
  have h10 : -(((4 * k : ℕ) : ℤ) + ((6 * k : ℕ) : ℤ)) = -((10 * k : ℕ) : ℤ) := by
    push_cast; ring
  rw [h10, ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]

/-- The storeys of the tower are pairwise disjoint: a point of the `k`-th storey with `k < j` would
have both coefficients divisible by `p`, hence `p ∣ Δ`, contradicting good reduction. -/
theorem pairwise_disjoint_scale_goodLocus :
    Pairwise (Function.onFun Disjoint
      fun k : ℕ => PadicInt.scaleProdByPPow (4 * k) (6 * k) '' goodLocus p) := by
  have key : ∀ k j : ℕ, k < j → Disjoint
      (PadicInt.scaleProdByPPow (4 * k) (6 * k) '' goodLocus p)
      (PadicInt.scaleProdByPPow (4 * j) (6 * j) '' goodLocus p) := by
    intro k j hkj
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, -, hyz⟩
    have hpk : ((p : ℤ_[p]) ^ (4 * k)) ≠ 0 := pow_ne_zero _ PadicInt.uniformizer_ne_zero
    have hqk : ((p : ℤ_[p]) ^ (6 * k)) ≠ 0 := pow_ne_zero _ PadicInt.uniformizer_ne_zero
    have h1 : (p : ℤ_[p]) ^ (4 * k) * x.1 = (p : ℤ_[p]) ^ (4 * j) * y.1 :=
      congrArg Prod.fst hyz.symm
    have h2 : (p : ℤ_[p]) ^ (6 * k) * x.2 = (p : ℤ_[p]) ^ (6 * j) * y.2 :=
      congrArg Prod.snd hyz.symm
    have e1 : x.1 = (p : ℤ_[p]) ^ (4 * j - 4 * k) * y.1 := by
      refine mul_left_cancel₀ hpk ?_
      rw [h1, ← mul_assoc, ← pow_add]
      congr 2
      omega
    have e2 : x.2 = (p : ℤ_[p]) ^ (6 * j - 6 * k) * y.2 := by
      refine mul_left_cancel₀ hqk ?_
      rw [h2, ← mul_assoc, ← pow_add]
      congr 2
      omega
    exact hx (dvd_Δ_of_dvd_of_dvd
      (e1 ▸ (dvd_pow_self (p : ℤ_[p]) (by omega)).mul_right y.1)
      (e2 ▸ (dvd_pow_self (p : ℤ_[p]) (by omega)).mul_right y.2))
  intro k j hkj
  rcases Nat.lt_or_ge k j with h | h
  · exact key k j h
  · exact (key j k (by omega)).symm

/-- **The mass of the good-reduction tower**, for every prime `p ≥ 5`:

  `μ_p(⋃_k σ_p^k(good locus)) = (1 - p^{-1})(1 - p^{-10})^{-1}`. -/
theorem volume_goodTower (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (goodTower p)
      = (1 - (p : ℝ≥0∞)⁻¹) * (1 - ((p : ℝ≥0∞)⁻¹) ^ 10)⁻¹ := by
  rw [goodTower, measure_iUnion pairwise_disjoint_scale_goodLocus
    (measurableSet_scale_goodLocus hp)]
  have hterm : ∀ k : ℕ, (volume : Measure (ℤ_[p] × ℤ_[p]))
      (PadicInt.scaleProdByPPow (4 * k) (6 * k) '' goodLocus p)
        = (((p : ℝ≥0∞)⁻¹) ^ 10) ^ k * (1 - (p : ℝ≥0∞)⁻¹) := by
    intro k
    rw [volume_scale_goodLocus hp k, ← pow_mul]
  rw [tsum_congr hterm, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

/-! ### The Table-5 entry for `I₀`, as a rational number -/

variable (p) in
/-- **The `I₀` row of Table 5 of Griffin–Ono–Tsai:** the real number `(p - 1)p⁹/(p¹⁰ - 1)`, which
equals `(1 - p^{-1})(1 - p^{-10})^{-1}`. -/
noncomputable def gotI0Volume : ℝ := ((p : ℝ) - 1) * (p : ℝ) ^ 9 / ((p : ℝ) ^ 10 - 1)

/-- **The mass of the good-reduction tower is the `I₀` entry of Table 5**, for every prime `p ≥ 5`:

  `μ_p(⋃_k σ_p^k(good locus)) = (p - 1)p⁹/(p¹⁰ - 1)`. -/
theorem volume_goodTower_eq_ofReal (hp : 5 ≤ p) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (goodTower p) = ENNReal.ofReal (gotI0Volume p) := by
  have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hx : (0 : ℝ) < (p : ℝ) := by linarith
  have hinv : (p : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hx, ENNReal.ofReal_natCast]
  have hle : ((p : ℝ)⁻¹) ^ 10 ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [inv_le_one_iff₀]; right; linarith
  have hpos : (0 : ℝ) < 1 - ((p : ℝ)⁻¹) ^ 10 := by
    have : ((p : ℝ)⁻¹) ^ 10 < 1 := by
      refine pow_lt_one₀ (by positivity) ?_ (by norm_num)
      rw [inv_lt_one_iff₀]; right; linarith
    linarith
  have hA : (1 : ℝ≥0∞) - (p : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - (p : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hinv]
  have hB : ((p : ℝ≥0∞)⁻¹) ^ 10 = ENNReal.ofReal (((p : ℝ)⁻¹) ^ 10) := by
    rw [hinv, ← ENNReal.ofReal_pow (by positivity)]
  have hC : (1 : ℝ≥0∞) - ((p : ℝ≥0∞)⁻¹) ^ 10
      = ENNReal.ofReal (1 - ((p : ℝ)⁻¹) ^ 10) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, hB]
  rw [volume_goodTower hp, hA, hC, ← ENNReal.ofReal_inv_of_pos hpos,
    ← ENNReal.ofReal_mul (by rw [sub_nonneg, inv_le_one_iff₀]; right; linarith)]
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hx
  have h1 : (1 : ℝ) - ((p : ℝ)⁻¹) ^ 10 ≠ 0 := ne_of_gt hpos
  have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
  have h2 : (p : ℝ) ^ 10 - 1 ≠ 0 := by linarith
  rw [gotI0Volume]
  field_simp

/-! ### One storey up the tower -/

/-- One storey up: `σ_p^{k+1} = σ_p ∘ σ_p^k` on the coefficient plane. -/
theorem _root_.PadicInt.scaleProdByPPow_succ (k : ℕ) (y : ℤ_[p] × ℤ_[p]) :
    PadicInt.scaleProdByPPow (4 * (k + 1)) (6 * (k + 1)) y
      = PadicInt.scaleProdByPPow 4 6 (PadicInt.scaleProdByPPow (4 * k) (6 * k) y) := by
  rw [show 4 * (k + 1) = 4 + 4 * k by omega, show 6 * (k + 1) = 6 + 6 * k by omega,
    ← PadicInt.scaleProdByPPow_comp, Function.comp_apply]

/-! ### The exact `I₀` row, granted two named hypotheses -/

variable (p) in
/-- **The minimality hypothesis.** A nonsingular short model over `ℤ_p` whose reduction datum is
`(I₀, 1)` and whose discriminant is divisible by `p` is *non-minimal*: it is a dilate
`(p⁴a₄, p⁶a₆)`. -/
def MinimalOfDvdΔ : Prop :=
  ∀ (x : ℤ_[p] × ℤ_[p]) (hx : x ∈ nonsingularLocus p),
    strat p ⟨x, hx⟩ = (KodairaSymbol.I 0, 1) →
      (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ →
        x ∈ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p])

/-- `c₆ = -864a₆` for the short model `y² = x³ + a₄x + a₆`, since `b₂ = 0`, `b₄ = 2a₄`,
`b₆ = 4a₆`. -/
theorem ofShortNF_c₆ {R : Type*} [CommRing R] (a₄ a₆ : R) :
    (ofShortNF a₄ a₆).c₆ = -864 * a₆ := by
  simp only [c₆, b₂, b₄, b₆]; ring

/-- `-864 = -(2⁵ · 27)` is a unit of `ℤ_[p]` for `p ≥ 5`. -/
theorem isUnit_neg_eightSixFour (hp : 5 ≤ p) : IsUnit (-864 : ℤ_[p]) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h : IsUnit ((2 : ℤ_[p]) ^ 5 * 27) :=
    ((PadicInt.isUnit_two hodd).pow 5).mul (isUnit_twentySeven hp)
  simpa [show (2 : ℤ_[p]) ^ 5 * 27 = 864 by norm_num] using h.neg

/-- **The minimality hypothesis holds at every prime `p ≥ 5`.** By
`TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I_zero`, a short model with `p ∣ Δ` and Kodaira
symbol `I₀` has `p⁴ ∣ c₄ = -48a₄` and `p⁶ ∣ c₆ = -864a₆`, and `48`, `864` are units at `p ≥ 5`. -/
theorem minimalOfDvdΔ (hp : 5 ≤ p) : MinimalOfDvdΔ p := by
  intro x hx hstrat hd
  have hkod : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hx).kodairaSymbol = KodairaSymbol.I 0 := by
    rw [strat] at hstrat
    exact congrArg Prod.fst hstrat
  obtain ⟨h4, h6⟩ := TateAlgorithm.pow_dvd_c₄_c₆_of_kodairaSymbol_eq_I_zero
    PadicInt.uniformizer_ne_zero hx hd hkod
  rw [ofShortNF_c₄, (isUnit_neg_fortyEight hp).dvd_mul_left] at h4
  rw [ofShortNF_c₆, (isUnit_neg_eightSixFour hp).dvd_mul_left] at h6
  rw [PadicInt.mem_range_scaleProdByPPow_iff]
  exact ⟨h4, h6⟩

/-- **Granted `τ_p ∘ σ_p = τ_p`, the whole tower lies in the `I₀` stratum.** Here
`StratScaleInvariant p` is the invariance of the reduction datum `τ_p` under the dilation `σ_p`. -/
theorem goodTower_subset_stratFibre_I0 (h : StratScaleInvariant p) :
    goodTower p ⊆ stratFibre p (KodairaSymbol.I 0, 1) := by
  rw [goodTower, Set.iUnion_subset_iff]
  intro k
  induction k with
  | zero =>
    rintro z ⟨y, hy, rfl⟩
    simpa [PadicInt.scaleProdByPPow_apply] using goodLocus_subset_stratFibre hy
  | succ k ih =>
    rintro z ⟨y, hy, rfl⟩
    have hwF : PadicInt.scaleProdByPPow (4 * k) (6 * k) y
        ∈ stratFibre p (KodairaSymbol.I 0, 1) := ih ⟨y, hy, rfl⟩
    have hwUp : PadicInt.scaleProdByPPow (4 * k) (6 * k) y ∈ nonsingularLocus p :=
      stratFibre_subset _ hwF
    have hσUp : PadicInt.scaleProdByPPow 4 6 (PadicInt.scaleProdByPPow (4 * k) (6 * k) y)
        ∈ nonsingularLocus p := mem_nonsingularLocus_scaleProdByPPow_iff.2 hwUp
    rw [PadicInt.scaleProdByPPow_succ]
    exact (mem_stratFibre_iff hσUp).2
      ((h _ hwUp hσUp).trans ((mem_stratFibre_iff hwUp).1 hwF))

/-- The descent step, by induction on a bound for `v_p(Δ)`: a point of the `I₀` stratum is either
already on the good locus, or a dilate of a point of the `I₀` stratum with `v_p(Δ)` smaller by
`12`. -/
private theorem mem_goodTower_of_not_pow_dvd (h1 : StratScaleInvariant p)
    (h2 : MinimalOfDvdΔ p) : ∀ (n : ℕ) (x : ℤ_[p] × ℤ_[p]),
      x ∈ stratFibre p (KodairaSymbol.I 0, 1) →
      ¬ (p : ℤ_[p]) ^ n ∣ (ofShortNF x.1 x.2).Δ → x ∈ goodTower p := by
  intro n
  induction n with
  | zero =>
    intro x _ hn
    rw [pow_zero] at hn
    exact absurd (one_dvd _) hn
  | succ n ih =>
    intro x hxF hn
    by_cases hd : (p : ℤ_[p]) ∣ (ofShortNF x.1 x.2).Δ
    · have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
      obtain ⟨y, hy⟩ := h2 x hxUp ((mem_stratFibre_iff hxUp).1 hxF) hd
      subst hy
      have hyUp : y ∈ nonsingularLocus p := mem_nonsingularLocus_scaleProdByPPow_iff.1 hxUp
      have hyF : y ∈ stratFibre p (KodairaSymbol.I 0, 1) :=
        (mem_stratFibre_iff hyUp).2
          ((h1 y hyUp hxUp).symm.trans ((mem_stratFibre_iff hxUp).1 hxF))
      have hyn : ¬ (p : ℤ_[p]) ^ n ∣ (ofShortNF y.1 y.2).Δ := by
        intro hc
        refine hn ?_
        rw [Δ_scaleProdByPPow]
        exact (pow_dvd_pow (p : ℤ_[p]) (by omega : n + 1 ≤ 12 + n)).trans
          (by rw [pow_add]; exact mul_dvd_mul_left _ hc)
      obtain ⟨k, w, hw, hwy⟩ := Set.mem_iUnion.1 (ih y hyF hyn)
      exact Set.mem_iUnion.2 ⟨k + 1, w, hw, by rw [PadicInt.scaleProdByPPow_succ, hwy]⟩
    · exact goodLocus_subset_goodTower hd

/-- **Granted `StratScaleInvariant p` and `MinimalOfDvdΔ p`, the `I₀` stratum is contained in the
tower.** -/
theorem stratFibre_I0_subset_goodTower (h1 : StratScaleInvariant p) (h2 : MinimalOfDvdΔ p) :
    stratFibre p (KodairaSymbol.I 0, 1) ⊆ goodTower p := by
  intro x hxF
  have hxUp : x ∈ nonsingularLocus p := stratFibre_subset _ hxF
  refine mem_goodTower_of_not_pow_dvd h1 h2
    ((emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat + 1) x hxF ?_
  intro hdvd
  have heq : emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ
      = (((emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat : ℕ) : ℕ∞) :=
    (toNat_emultiplicity_Δ_eq_iff (W := ofShortNF x.1 x.2) hxUp _).1 rfl
  have hle := PadicInt.mem_span_pPow_iff_le_emultiplicity.1 (Ideal.mem_span_singleton.2 hdvd)
  rw [heq] at hle
  have hlt : (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat + 1
      ≤ (emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ).toNat := by exact_mod_cast hle
  omega

/-- **The `I₀` stratum is exactly the good-reduction tower**, for `p ≥ 5`, granted
`StratScaleInvariant p`. -/
theorem stratFibre_I0_eq_goodTower (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    stratFibre p (KodairaSymbol.I 0, 1) = goodTower p :=
  Set.Subset.antisymm (stratFibre_I0_subset_goodTower h (minimalOfDvdΔ hp))
    (goodTower_subset_stratFibre_I0 h)

/-- **The `I₀` row of Table 5, granted `τ_p ∘ σ_p = τ_p`:** for every prime `p ≥ 5`,

  `δ_p(I₀, 1) = (p - 1)p⁹/(p¹⁰ - 1)`.

Here `StratScaleInvariant p` is the invariance of the reduction datum under the dilation `σ_p`. -/
theorem deltaP_I0_eq_ofReal (hp : 5 ≤ p) (h : StratScaleInvariant p) :
    deltaP p (KodairaSymbol.I 0, 1) = ENNReal.ofReal (gotI0Volume p) := by
  rw [← volume_stratFibre (p := p) (KodairaSymbol.I 0, 1), stratFibre_I0_eq_goodTower hp h,
    volume_goodTower_eq_ofReal hp]

end WeierstrassCurve
