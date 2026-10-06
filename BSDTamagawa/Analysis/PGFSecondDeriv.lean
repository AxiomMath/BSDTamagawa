/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import BSDTamagawa.Analysis.PGFMean
public import BSDTamagawa.Analysis.PGFVariance

/-!
# The second-order Abel converse for probability generating functions

If the probability generating function `F(u) = ∑_k p_k u^k` of a pmf `p` is twice
left-differentiable at `u = 1`, with `F'(1) = L₁` and `F''(1) = L₂`, then `∑_k k(k-1) p_k`
converges and equals `L₂`. Consequently `Var(X) = F''(1) + F'(1) - F'(1)²`.

## Main results

* `summable_and_tsum_eq_of_hasDerivWithinAt_derivWithin`: if the pgf `F` of a pmf `p` is twice
  left-differentiable at `1`, then `∑_k k(k-1) p_k` converges and equals `F''(1)`.
* `summable_and_tsum_eq_of_hasDerivWithinAt`: Abel's mean theorem for a nonnegative summable family
  of arbitrary total mass.
* `variance_eq_of_hasDerivWithinAt_derivWithin'`: for `X` with law `p : PMF ℕ` whose pgf is twice
  left-differentiable at `1`, `Var(X) = F''(1) + F'(1) - F'(1)²`.

## Implementation notes

The second derivative is taken of `derivWithin (pgf p) (Set.Iic 1)`, whose value at `1` is
determined because `Set.Iic 1` has `UniqueDiffWithinAt` there.
-/

@[expose] public section

namespace BSDTamagawa.PGFSecondDeriv

open Filter Set Topology MeasureTheory ProbabilityTheory
open BSDTamagawa BSDTamagawa.PGFMean

/-! ## §1. The termwise-differentiated series -/

/-- **The termwise derivative of the pgf**, `F'(u) = ∑_k k p_k u^{k-1}`.

The `k = 0` term vanishes, so the `ℕ`-subtraction in the exponent is harmless. -/
noncomputable def pgfDeriv (p : ℕ → ℝ) (u : ℝ) : ℝ := ∑' k : ℕ, (k : ℝ) * p k * u ^ (k - 1)

/-- The shifted coefficient family `a_j = (j+1) p_{j+1}`, whose pgf is `pgfDeriv p`. -/
noncomputable def derivCoeff (p : ℕ → ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) * p (j + 1)

/-- The shifted coefficients are nonnegative. -/
theorem derivCoeff_nonneg {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (j : ℕ) : 0 ≤ derivCoeff p j := by
  rw [derivCoeff]
  exact mul_nonneg (by positivity) (hp (j + 1))

/-- `∑_k k r^{k-1} < ∞` for `‖r‖ < 1`: the differentiated geometric series. -/
theorem summable_natCast_mul_pow_sub_one {r : ℝ} (hr : ‖r‖ < 1) :
    Summable fun k : ℕ => (k : ℝ) * r ^ (k - 1) := by
  have hbase : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_norm_lt_one hr
  rw [← summable_nat_add_iff 1]
  refine (hbase.add hgeom).congr fun n => ?_
  push_cast [Nat.add_sub_cancel]
  ring

/-- The pgf series converges absolutely on the closed unit disc: `|p_k u^k| ≤ p_k`. -/
theorem summable_PGF_term {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) {u : ℝ}
    (hu : |u| ≤ 1) : Summable fun k : ℕ => p k * u ^ k := by
  refine Summable.of_norm_bounded hsum.summable fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hp k)]
  exact mul_le_of_le_one_right (hp k) (pow_le_one₀ (abs_nonneg u) hu)

/-- The termwise-differentiated series converges absolutely inside the open unit disc:
`|k p_k u^{k-1}| ≤ k |u|^{k-1}` because `p_k ≤ 1`. -/
theorem summable_PGFDeriv_term {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) {u : ℝ}
    (hu : |u| < 1) : Summable fun k : ℕ => (k : ℝ) * p k * u ^ (k - 1) := by
  have hu' : ‖|u|‖ < 1 := by rwa [norm_abs_eq_norm, Real.norm_eq_abs]
  refine Summable.of_norm_bounded (summable_natCast_mul_pow_sub_one hu') fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg (hp k)]
  calc (k : ℝ) * p k * |u| ^ (k - 1) ≤ (k : ℝ) * 1 * |u| ^ (k - 1) := by
        gcongr
        exact le_hasSum hsum k fun j _ => hp j
    _ = (k : ℝ) * |u| ^ (k - 1) := by rw [mul_one]

/-- **Termwise differentiation of the pgf inside the unit disc.** For `|u| < 1`,
`F'(u) = ∑_k k p_k u^{k-1}`. -/
theorem hasDerivAt_PGF {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) {u : ℝ}
    (hu : |u| < 1) : HasDerivAt (pgf p) (pgfDeriv p u) u := by
  obtain ⟨r, hur, hr1⟩ := exists_between hu
  have hr0 : (0 : ℝ) ≤ r := (abs_nonneg u).trans hur.le
  have humem : u ∈ Ioo (-r) r := abs_lt.mp hur
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => (k : ℝ) * r ^ (k - 1))
    (g := fun (k : ℕ) (z : ℝ) => p k * z ^ k)
    (g' := fun (k : ℕ) (z : ℝ) => (k : ℝ) * p k * z ^ (k - 1))
    (summable_natCast_mul_pow_sub_one (by rwa [Real.norm_of_nonneg hr0])) isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected (fun k z _ => ?_) (fun k z hz => ?_) humem
    (summable_PGF_term hp hsum (hur.trans hr1).le) humem
  · exact ((hasDerivAt_pow k z).const_mul (p k)).congr_deriv (by ring)
  · have hz' : |z| ≤ r := (abs_lt.mpr hz).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg (hp k)]
    calc (k : ℝ) * p k * |z| ^ (k - 1) ≤ (k : ℝ) * 1 * r ^ (k - 1) := by
          gcongr
          exact le_hasSum hsum k fun j _ => hp j
      _ = (k : ℝ) * r ^ (k - 1) := by rw [mul_one]

/-- Inside the disc, the derivative of the pgf *within* `Set.Iic 1` is the two-sided one: there
`Set.Iic 1` is a neighbourhood of the point. -/
theorem derivWithin_PGF_Iic_of_mem {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) : derivWithin (pgf p) (Iic 1) u = pgfDeriv p u :=
  (hasDerivAt_PGF hp hsum (abs_lt.mpr hu)).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Iic 1 u (mem_Iic.mpr hu.2.le))

/-- **The differentiated series is itself a pgf**: `∑_k k p_k u^{k-1} = ∑_j a_j u^j` with
`a_j = (j+1) p_{j+1}`, the `k = 0` term on the left vanishing. -/
theorem PGFDeriv_eq_PGF_derivCoeff {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) {u : ℝ}
    (hu : |u| < 1) : pgfDeriv p u = pgf (derivCoeff p) u := by
  rw [pgfDeriv, (summable_PGFDeriv_term hp hsum hu).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [pgf]
  refine tsum_congr fun j => ?_
  rw [derivCoeff]
  push_cast [Nat.add_sub_cancel]
  ring

/-! ## §2. Abel's mean theorem without the mass-one normalisation -/

/-- **Abel's mean theorem for a nonnegative summable family of arbitrary total mass.** For a
nonnegative family `a` with `HasSum a S`, if `F = pgf a` has left derivative `L` at `1`, then
`∑_n n a_n` converges and equals `L`. -/
theorem summable_and_tsum_eq_of_hasDerivWithinAt (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {S : ℝ}
    (hS : HasSum a S) (L : ℝ) (hL : HasDerivWithinAt (pgf a) L (Iio 1) 1) :
    Summable (fun n : ℕ => (n : ℝ) * a n) ∧ ∑' n : ℕ, (n : ℝ) * a n = L := by
  have hS0 : 0 ≤ S := HasSum.nonneg ha hS
  have hcpos : (0 : ℝ) < S + 1 := by linarith
  have hcne : S + 1 ≠ 0 := ne_of_gt hcpos
  have hite : ∀ n : ℕ, (0 : ℝ) ≤ if n = 0 then 1 else 0 := fun n => by
    by_cases h : n = 0 <;> simp [h]
  have hq0 : ∀ n : ℕ, 0 ≤ (a n + if n = 0 then (1 : ℝ) else 0) / (S + 1) := fun n =>
    div_nonneg (by linarith [ha n, hite n]) hcpos.le
  have hqsum : HasSum (fun n : ℕ => (a n + if n = 0 then (1 : ℝ) else 0) / (S + 1)) 1 := by
    have h := (hS.add (hasSum_ite_eq 0 (1 : ℝ))).div_const (S + 1)
    rwa [div_self hcne] at h
  have hPGFq : ∀ u ∈ Icc (0 : ℝ) 1,
      pgf (fun n : ℕ => (a n + if n = 0 then (1 : ℝ) else 0) / (S + 1)) u
        = (pgf a u + 1) / (S + 1) := by
    intro u hu
    have hsa : Summable fun n : ℕ => a n * u ^ n :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (ha n) (pow_nonneg hu.1 n))
        (fun n => mul_le_of_le_one_right (ha n) (pow_le_one₀ hu.1 hu.2)) hS.summable
    have hsi : HasSum (fun n : ℕ => (if n = 0 then (1 : ℝ) else 0) * u ^ n) 1 :=
      (hasSum_ite_eq 0 (1 : ℝ)).congr_fun fun n => by by_cases h : n = 0 <;> simp [h]
    rw [pgf, pgf, show (fun n : ℕ => (a n + if n = 0 then (1 : ℝ) else 0) / (S + 1) * u ^ n)
        = (fun n : ℕ => (a n * u ^ n + (if n = 0 then (1 : ℝ) else 0) * u ^ n) / (S + 1)) from
      funext fun n => by ring, tsum_div_const, hsa.tsum_add hsi.summable, hsi.tsum_eq]
  have hLq : HasDerivWithinAt (pgf fun n : ℕ => (a n + if n = 0 then (1 : ℝ) else 0) / (S + 1))
      (L / (S + 1)) (Iio 1) 1 := by
    refine ((hL.add_const 1).div_const (S + 1)).congr_of_eventuallyEq ?_
      (hPGFq 1 ⟨zero_le_one, le_rfl⟩)
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with x hx
    exact hPGFq x ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hsq, hvq⟩ := main_theorem _ hq0 hqsum (L / (S + 1)) hLq
  have hterm : ∀ n : ℕ, (n : ℝ) * ((a n + if n = 0 then (1 : ℝ) else 0) / (S + 1))
      = (n : ℝ) * a n / (S + 1) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · rw [ite_eq_right h, add_zero, mul_div_assoc]
  have hs' : Summable fun n : ℕ => (n : ℝ) * a n / (S + 1) := hsq.congr hterm
  have hv' : (∑' n : ℕ, (n : ℝ) * a n / (S + 1)) = L / (S + 1) := by
    rw [← hvq]
    exact tsum_congr fun n => (hterm n).symm
  rw [tsum_div_const] at hv'
  refine ⟨?_, (div_left_inj' hcne).mp hv'⟩
  refine (hs'.mul_right (S + 1)).congr fun n => ?_
  field_simp

/-! ## §3. The second-order Abel converse -/

/-- The shifted coefficients sum to the mean: `∑_j (j+1) p_{j+1} = ∑_k k p_k = F'(1)`. -/
theorem hasSum_derivCoeff (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1) {L₁ : ℝ}
    (h₁ : HasDerivWithinAt (pgf p) L₁ (Iio 1) 1) : HasSum (derivCoeff p) L₁ := by
  obtain ⟨hmean, hval⟩ := main_theorem p hp hsum L₁ h₁
  have hshift : Summable (derivCoeff p) := by
    refine ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) * p n) 1).mpr hmean).congr fun j => ?_
    rw [derivCoeff]
    push_cast
    ring
  have hzero := hmean.tsum_eq_zero_add
  rw [hval] at hzero
  simp only [Nat.cast_zero, zero_mul, zero_add] at hzero
  have hvalue : (∑' j : ℕ, derivCoeff p j) = L₁ := by
    rw [hzero]
    exact tsum_congr fun j => by rw [derivCoeff]; push_cast; ring
  rw [← hvalue]
  exact hshift.hasSum

/-- If `F = pgf p` has left derivative `L₁` at `1` and `derivWithin F (Set.Iic 1)` has left
derivative `L₂` at `1`, then `pgf (derivCoeff p)` has left derivative `L₂` at `1`. -/
theorem hasDerivWithinAt_PGF_derivCoeff (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    {L₁ L₂ : ℝ} (h₁ : HasDerivWithinAt (pgf p) L₁ (Iio 1) 1)
    (h₂ : HasDerivWithinAt (derivWithin (pgf p) (Iic 1)) L₂ (Iio 1) 1) :
    HasDerivWithinAt (pgf (derivCoeff p)) L₂ (Iio 1) 1 := by
  have hone : pgf (derivCoeff p) 1 = derivWithin (pgf p) (Iic 1) 1 := by
    rw [h₁.Iic_of_Iio.derivWithin (uniqueDiffOn_Iic 1 1 (mem_Iic.mpr le_rfl)), pgf]
    simpa using (hasSum_derivCoeff p hp hsum h₁).tsum_eq
  refine h₂.congr_of_eventuallyEq ?_ hone
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with x hx
  have hxmem : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  rw [derivWithin_PGF_Iic_of_mem hp hsum hxmem,
    PGFDeriv_eq_PGF_derivCoeff hp hsum (abs_lt.mpr hxmem)]

/-- **The second-order Abel converse.** Let `p` be a pmf with pgf `F = pgf p`. If `F` is
differentiable at `u = 1` from the left with `F'(1) = L₁`, and its derivative
`derivWithin F (Set.Iic 1)` is in turn differentiable at `u = 1` from the left with value `L₂`,
then the second factorial moment converges and equals `L₂`:

  `∑_k k(k-1) p_k = F''(1) < ∞.` -/
theorem summable_and_tsum_eq_of_hasDerivWithinAt_derivWithin (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hsum : HasSum p 1) {L₁ L₂ : ℝ} (h₁ : HasDerivWithinAt (pgf p) L₁ (Iio 1) 1)
    (h₂ : HasDerivWithinAt (derivWithin (pgf p) (Iic 1)) L₂ (Iio 1) 1) :
    Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * p k) ∧
      ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * p k = L₂ := by
  obtain ⟨hs, hv⟩ := summable_and_tsum_eq_of_hasDerivWithinAt (derivCoeff p)
    (derivCoeff_nonneg hp) (hasSum_derivCoeff p hp hsum h₁) L₂
    (hasDerivWithinAt_PGF_derivCoeff p hp hsum h₁ h₂)
  have hshift : ∀ j : ℕ, (j : ℝ) * derivCoeff p j
      = ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) * p (j + 1) := by
    intro j
    rw [derivCoeff]
    push_cast
    ring
  have hsg : Summable fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * p k :=
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * p k) 1).mp
      (hs.congr hshift)
  refine ⟨hsg, ?_⟩
  rw [hsg.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [← hv]
  exact tsum_congr fun j => (hshift j).symm

/-! ## §4. The variance formula -/

/-- The masses of a `PMF ℕ`, read in `ℝ`, form a pmf: they are nonnegative with sum `1`. -/
theorem hasSum_toReal_pmf (p : PMF ℕ) : HasSum (fun k : ℕ => (p k).toReal) 1 := by
  have h := ENNReal.hasSum_toReal p.tsum_coe_ne_top
  rwa [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one] at h

/-- If the pgf of `p : PMF ℕ` has a left derivative at `1`, then `n` is integrable against
`p.toMeasure`. -/
theorem integrable_of_hasDerivWithinAt (p : PMF ℕ) {L₁ : ℝ}
    (h₁ : HasDerivWithinAt (pgf fun k : ℕ => (p k).toReal) L₁ (Iio 1) 1) :
    Integrable (fun n : ℕ => (n : ℝ)) p.toMeasure := by
  obtain ⟨hsumm, -⟩ :=
    main_theorem _ (fun k => ENNReal.toReal_nonneg) (hasSum_toReal_pmf p) L₁ h₁
  rw [PGFVariance.integrable_toMeasure_iff_summable]
  refine (summable_congr fun k => ?_).mp hsumm
  rw [Real.norm_natCast]
  ring

/-- Let `X` have law `p : PMF ℕ` with pgf `F`. If `F` has left derivative `F'(1) = L₁` at `1` and
`derivWithin F (Set.Iic 1)` has left derivative `F''(1) = L₂` at `1`, then
`Var(X) = F''(1) + F'(1) - F'(1)²`. -/
@[bsd_tamagawa "T037b"]
theorem variance_eq_of_hasDerivWithinAt_derivWithin' (p : PMF ℕ) {L₁ L₂ : ℝ}
    (h₁ : HasDerivWithinAt (pgf fun k : ℕ => (p k).toReal) L₁ (Iio 1) 1)
    (h₂ : HasDerivWithinAt (derivWithin (pgf fun k : ℕ => (p k).toReal) (Iic 1)) L₂ (Iio 1) 1) :
    variance (fun n : ℕ => (n : ℝ)) p.toMeasure = L₂ + L₁ - L₁ ^ 2 := by
  have hp : ∀ k : ℕ, 0 ≤ (p k).toReal := fun k => ENNReal.toReal_nonneg
  have hsum := hasSum_toReal_pmf p
  obtain ⟨hF'', hvalue⟩ :=
    summable_and_tsum_eq_of_hasDerivWithinAt_derivWithin _ hp hsum h₁ h₂
  obtain ⟨-, hmean⟩ := main_theorem _ hp hsum L₁ h₁
  rw [PGFVariance.main_theorem p (integrable_of_hasDerivWithinAt p h₁) hF'', PGFVariance.pgfDeriv2,
    PGFVariance.pgfDeriv, hvalue, hmean]

end BSDTamagawa.PGFSecondDeriv
