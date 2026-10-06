/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import BSDTamagawa.Attr

/-!
# Variance from the derivatives of a probability generating function

Let `X` be a random variable on the nonnegative integers with probability mass function
`p_k = P(X = k)`, and let `F(s) = E[s^X] = ∑_k p_k s^k` be its probability generating function. If
`X` has a finite mean and a finite second factorial moment `F''(1) < ∞`, then
`Var(X) = F''(1) + F'(1) - F'(1)²`.

## Main definitions

* `BSDTamagawa.PGFVariance.pgfDeriv`: `F'(1) = ∑' k, k p_k`.
* `BSDTamagawa.PGFVariance.pgfDeriv2`: `F''(1) = ∑' k, k(k-1) p_k`.

## Main results

* `BSDTamagawa.PGFVariance.main_theorem_integrable`: the variance formula assuming `n²` is
  integrable.
* `BSDTamagawa.PGFVariance.pgfDeriv2_summable_iff_integrable_sq`: for `X` of finite mean,
  `F''(1) < ∞` if and only if `n²` is integrable.
* `BSDTamagawa.PGFVariance.main_theorem`: the variance formula assuming `F''(1) < ∞`.

## Implementation notes

`X` is the inclusion `fun n : ℕ => (n : ℝ)` on the probability space `p.toMeasure` of a `PMF ℕ`,
and the derivatives `F'(1)`, `F''(1)` are defined by their term-by-term series.
-/

@[expose] public section

namespace BSDTamagawa.PGFVariance

open MeasureTheory ProbabilityTheory ENNReal

/-- First derivative of the pgf at `1`, defined by term-by-term differentiation: `F'(1) = ∑ k p_k`.
This is the first factorial moment of `X`. -/
noncomputable def pgfDeriv (p : PMF ℕ) : ℝ := ∑' k : ℕ, (k : ℝ) * (p k).toReal

/-- Second derivative of the pgf at `1`, defined by term-by-term differentiation:
`F''(1) = ∑ k (k-1) p_k`. This is the second factorial moment of `X`. -/
noncomputable def pgfDeriv2 (p : PMF ℕ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal

/-- The first pgf derivative equals the mean: `F'(1) = E[X]`. -/
theorem pgfDeriv_eq_mean (p : PMF ℕ)
    (h1 : Integrable (fun n : ℕ => (n : ℝ)) p.toMeasure) :
    pgfDeriv p = ∫ n, (n : ℝ) ∂ p.toMeasure := by
  rw [PMF.integral_eq_tsum _ _ h1, pgfDeriv]
  congr 1; funext k; rw [smul_eq_mul, mul_comm]

/-- The second pgf derivative equals the second factorial moment: `F''(1) = E[X(X-1)]`. -/
theorem pgfDeriv2_eq (p : PMF ℕ)
    (h2 : Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) p.toMeasure) :
    pgfDeriv2 p = ∫ n, (n : ℝ) * ((n : ℝ) - 1) ∂ p.toMeasure := by
  rw [PMF.integral_eq_tsum _ _ h2, pgfDeriv2]
  congr 1; funext k; rw [smul_eq_mul, mul_comm]

/-- Under the standing hypothesis `Integrable n`, integrability of the second factorial moment
`n(n-1)` is equivalent to integrability of `n²`. -/
private lemma integrable_mul_sub_one_iff_sq (p : PMF ℕ)
    (h1 : Integrable (fun n : ℕ => (n : ℝ)) p.toMeasure) :
    Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) p.toMeasure ↔
      Integrable (fun n : ℕ => (n : ℝ) ^ 2) p.toMeasure :=
  ⟨fun hfac => (hfac.add h1).congr (.of_forall fun n => by simp only [Pi.add_apply]; ring),
    fun h2 => (h2.sub h1).congr (.of_forall fun n => by simp only [Pi.sub_apply]; ring)⟩

/-- For the inclusion random variable of a `PMF ℕ` with finite mean and finite second moment,
`Var(X) = F''(1) + F'(1) - F'(1)^2`. -/
theorem main_theorem_integrable (p : PMF ℕ)
    (h1 : Integrable (fun n : ℕ => (n : ℝ)) p.toMeasure)
    (h2 : Integrable (fun n : ℕ => (n : ℝ) ^ 2) p.toMeasure) :
    variance (fun n : ℕ => (n : ℝ)) p.toMeasure
      = pgfDeriv2 p + pgfDeriv p - (pgfDeriv p) ^ 2 := by
  have hmeas : AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) p.toMeasure :=
    measurable_from_top.aestronglyMeasurable
  have hmem : MemLp (fun n : ℕ => (n : ℝ)) 2 p.toMeasure :=
    (memLp_two_iff_integrable_sq hmeas).2 h2
  have hfac : Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) p.toMeasure :=
    (integrable_mul_sub_one_iff_sq p h1).mpr h2
  have hvar : variance (fun n : ℕ => (n : ℝ)) p.toMeasure
      = (∫ n, ((fun n : ℕ => (n : ℝ)) ^ 2) n ∂ p.toMeasure)
          - (∫ n, (n : ℝ) ∂ p.toMeasure) ^ 2 :=
    variance_eq_sub hmem
  have hsplit : (∫ n, ((fun n : ℕ => (n : ℝ)) ^ 2) n ∂ p.toMeasure)
      = (∫ n, (n : ℝ) * ((n : ℝ) - 1) ∂ p.toMeasure) + (∫ n, (n : ℝ) ∂ p.toMeasure) := by
    rw [← integral_add hfac h1]
    exact integral_congr_ae (.of_forall fun n => by simp only [Pi.pow_apply]; ring)
  rw [hvar, hsplit, pgfDeriv2_eq p hfac, pgfDeriv_eq_mean p h1]

/-- Integrability of a real-valued function against `p.toMeasure`, for a `PMF ℕ`, is equivalent to
summability of the absolute term series `(p k).toReal * ‖f k‖`. -/
lemma integrable_toMeasure_iff_summable (p : PMF ℕ) (f : ℕ → ℝ) :
    Integrable f p.toMeasure ↔ Summable (fun k : ℕ => (p k).toReal * ‖f k‖) := by
  have hrewrite : p.toMeasure
      = Measure.sum (fun k : ℕ => (p k) • Measure.dirac k) := by
    conv_lhs => rw [← Measure.sum_smul_dirac p.toMeasure]
    simp_rw [p.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  rw [hrewrite]
  exact integrable_sum_dirac_iff p.apply_ne_top

/-- Under the standing assumption `Integrable n`, `F''(1) < ∞` if and only if `n²` is integrable:
the series `∑' k, k(k-1)·p_k` is summable iff `n²` is integrable against the PMF measure. -/
theorem pgfDeriv2_summable_iff_integrable_sq (p : PMF ℕ)
    (h1 : Integrable (fun n : ℕ => (n : ℝ)) p.toMeasure) :
    Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) ↔
      Integrable (fun n : ℕ => (n : ℝ) ^ 2) p.toMeasure := by
  have hknn : ∀ k : ℕ, 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := fun k => by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
  have hbridge :
      Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) p.toMeasure ↔
        Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) := by
    rw [integrable_toMeasure_iff_summable]
    refine summable_congr fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hknn k)]
    ring
  exact hbridge.symm.trans (integrable_mul_sub_one_iff_sq p h1)

/-- Variance from the pgf derivatives. For the inclusion random variable of a `PMF ℕ` with finite
mean and `F''(1) < ∞` (the series `∑' k, k(k-1)·p_k` is summable),
`Var(X) = F''(1) + F'(1) - F'(1)^2`. -/
@[bsd_tamagawa "T037b"]
theorem main_theorem (p : PMF ℕ)
    (h1 : Integrable (fun n : ℕ => (n : ℝ)) p.toMeasure)
    (hF'' : Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal)) :
    variance (fun n : ℕ => (n : ℝ)) p.toMeasure
      = pgfDeriv2 p + pgfDeriv p - (pgfDeriv p) ^ 2 :=
  main_theorem_integrable p h1
    ((pgfDeriv2_summable_iff_integrable_sq p h1).mp hF'')

end BSDTamagawa.PGFVariance
