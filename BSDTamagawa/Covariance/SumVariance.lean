/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.ClosedBidisc
public import BSDTamagawa.Covariance.Summable

/-!
# The variance of `ω_Tam(E) + Ω(Tam(E))`

Under the joint limiting law `P_joint` of `ω_Tam(E)` and `Ω(Tam(E))`, the sum
`ω_Tam(E) + Ω(Tam(E))` has local exponent `e(t) = ω_{Tam,t} + Ω(t)`, its probability generating
function is the Euler product `∏_p ∑_t δ_p(t) w^{e(t)}`, and

  `Var_{P_joint}(ω_Tam(E) + Ω(Tam(E))) = ∑_p (S_p(e) - m_p(e)²)`,

where `m_p(e) = ∑_t δ_p(t) e(t)` and `S_p(e) = ∑_t δ_p(t) e(t)²`.

## Main results

* `WeierstrassCurve.factorHyp_dbl`: the reindexed pair satisfies `CovarianceFormula.FactorHyp`.
* `WeierstrassCurve.prodHyp_sumFactor`, `WeierstrassCurve.derivHyp_sumFactor`: the hypotheses of
  the first and second logarithmic derivative formulas for the Euler product
  `∏_p ∑_t δ_p(t) w^{e(t)}`.
* `WeierstrassCurve.pgf_jointSumPMF_eq_prodG`: the probability generating function of
  `ω_Tam(E) + Ω(Tam(E))` is that Euler product near `w = 1`.
* `WeierstrassCurve.variance_jointOmegaCardFactorsSum`: the variance formula.

## Implementation notes

The growth hypothesis `2^{e(t)} ≤ max 1 t` of `CovarianceFormula.FactorHyp` fails for
`e = ω_{Tam,·} + Ω` (at `t = 2` it reads `4 ≤ 2`), while `2^{e(t)} ≤ 2 max 1 t` holds. The mass
family and the exponent are therefore pushed forward along `t ↦ 2t` (`dblMass`, `dblExp`), which
leaves every sum unchanged (`tsum_dblMass_mul`) and doubles the index, so that the reindexed pair
satisfies `FactorHyp`.
-/

@[expose] public section

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open BSDTamagawa BSDTamagawa.ValuationMean BSDTamagawa.FactorCountMean
open BSDTamagawa.CovarianceFormula BSDTamagawa.PrimeFactorCovariance

/-! ### The diagonal exponent `ω_{Tam,t} + Ω(t)` -/

/-- The exponent `e(t) = ω_{Tam,t} + Ω(t)` of the statistic `ω_Tam(E) + Ω(Tam(E))`. -/
def sumExp : ℕ → ℕ := fun t => omegaIndicator t + omegaExp t

/-- `e(t) = 0` for `t ≤ 1`. -/
theorem sumExp_of_le_one {t : ℕ} (ht : t ≤ 1) : sumExp t = 0 := by
  rw [sumExp, omegaIndicator_of_le_one ht, omegaExp_eq_zero_of_le_one ht]

/-- `e(t) = 1 + Ω(t)` for `t ≥ 2`. -/
theorem sumExp_of_two_le {t : ℕ} (ht : 2 ≤ t) : sumExp t = 1 + omegaExp t := by
  rw [sumExp, omegaIndicator_of_two_le ht]

/-- `ω_{Tam,t} ≤ Ω(t)`. -/
theorem omegaIndicator_le_omegaExp (t : ℕ) : omegaIndicator t ≤ omegaExp t := by
  rcases le_or_gt t 1 with h | h
  · rw [omegaIndicator_of_le_one h]
    exact Nat.zero_le _
  · rw [omegaIndicator_of_two_le h, omegaExp_apply]
    exact ArithmeticFunction.cardFactors_pos_iff_one_lt.2 h

/-- `2^{ω_{Tam,t}} ≤ max 1 t`. -/
theorem two_pow_omegaIndicator_le (t : ℕ) : 2 ^ omegaIndicator t ≤ max 1 t := by
  rcases le_or_gt t 1 with h | h
  · rw [omegaIndicator_of_le_one h]
    simp
  · rw [omegaIndicator_of_two_le h]
    omega

/-- `e(t) ≤ 2 Ω(t)`. -/
theorem sumExp_le_two_mul_omegaExp (t : ℕ) : sumExp t ≤ 2 * omegaExp t := by
  have h := omegaIndicator_le_omegaExp t
  rw [sumExp]
  omega

/-! ### The reindexing along `t ↦ 2t` -/

/-- The mass family `δ_p` carried to the even indices, `dblMass p (2t) = δ_p(t)`, and `0` at the
odd ones. -/
noncomputable def dblMass (p : ℕ) [Fact p.Prime] (n : ℕ) : ℝ :=
  if n % 2 = 0 then scalarLocalMassReal p (n / 2) else 0

/-- The exponent `e` carried to the even indices, `dblExp (2t) = e(t)`, and `0` at the odd ones. -/
def dblExp (n : ℕ) : ℕ := if n % 2 = 0 then sumExp (n / 2) else 0

/-- `dblMass p (2t) = δ_p(t)`. -/
@[simp]
theorem dblMass_two_mul (p : ℕ) [Fact p.Prime] (t : ℕ) :
    dblMass p (2 * t) = scalarLocalMassReal p t := by
  rw [dblMass, ite_eq_left (by omega), show 2 * t / 2 = t from by omega]

/-- `dblExp (2t) = e(t)`. -/
@[simp]
theorem dblExp_two_mul (t : ℕ) : dblExp (2 * t) = sumExp t := by
  rw [dblExp, ite_eq_left (by omega), show 2 * t / 2 = t from by omega]

/-- `dblMass p n = 0` at an odd index `n`. -/
theorem dblMass_of_odd {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : n % 2 ≠ 0) : dblMass p n = 0 :=
  ite_eq_right hn

/-- `dblExp n = 0` at an odd index `n`. -/
theorem dblExp_of_odd {n : ℕ} (hn : n % 2 ≠ 0) : dblExp n = 0 := ite_eq_right hn

/-- `dblMass p n = 0` at an index `n` outside the range of `t ↦ 2t`. -/
theorem dblMass_of_notMem_range {p : ℕ} [Fact p.Prime] {n : ℕ}
    (hn : n ∉ Set.range (fun t : ℕ => 2 * t)) : dblMass p n = 0 :=
  dblMass_of_odd fun h => hn ⟨n / 2, by change 2 * (n / 2) = n; omega⟩

/-- For every `φ : ℕ → ℝ`, `∑_n dblMass_p(n) φ(dblExp(n)) = ∑_t δ_p(t) φ(e(t))`. -/
theorem tsum_dblMass_mul (p : ℕ) [Fact p.Prime] (φ : ℕ → ℝ) :
    (∑' n : ℕ, dblMass p n * φ (dblExp n))
      = ∑' t : ℕ, scalarLocalMassReal p t * φ (sumExp t) := by
  have hsupp : Function.support (fun n : ℕ => dblMass p n * φ (dblExp n))
      ⊆ Set.range (fun t : ℕ => 2 * t) := by
    intro n hn
    by_contra hcon
    refine hn ?_
    change dblMass p n * φ (dblExp n) = 0
    rw [dblMass_of_notMem_range hcon, zero_mul]
  rw [← (mul_right_injective₀ (two_ne_zero' ℕ)).tsum_eq hsupp]
  exact tsum_congr fun t => by rw [dblMass_two_mul, dblExp_two_mul]

/-- The reindexed pair has the same `powFactor` as `(δ_p, e)`. -/
theorem powFactor_dbl (p : ℕ) [Fact p.Prime] :
    powFactor (dblMass p) dblExp = powFactor (scalarLocalMassReal p) sumExp :=
  funext fun w => tsum_dblMass_mul p fun k => w ^ k

/-- The reindexed pair has the same `powFactorDeriv` as `(δ_p, e)`. -/
theorem powFactorDeriv_dbl (p : ℕ) [Fact p.Prime] :
    powFactorDeriv (dblMass p) dblExp = powFactorDeriv (scalarLocalMassReal p) sumExp :=
  funext fun w => tsum_dblMass_mul p fun k => (k : ℝ) * w ^ (k - 1)

/-- The reindexed pair has the same `powFactorDeriv2` as `(δ_p, e)`. -/
theorem powFactorDeriv2_dbl (p : ℕ) [Fact p.Prime] :
    powFactorDeriv2 (dblMass p) dblExp = powFactorDeriv2 (scalarLocalMassReal p) sumExp :=
  funext fun w => tsum_dblMass_mul p fun k => (k : ℝ) * (((k - 1 : ℕ) : ℝ) * w ^ (k - 1 - 1))

/-- The reindexed pair has the same first moment as `(δ_p, e)`. -/
theorem expMoment1_dbl (p : ℕ) [Fact p.Prime] :
    expMoment1 (dblMass p) dblExp = expMoment1 (scalarLocalMassReal p) sumExp :=
  tsum_dblMass_mul p fun k => (k : ℝ)

/-- The reindexed pair has the same second moment as `(δ_p, e)`. -/
theorem expMoment2_dbl (p : ℕ) [Fact p.Prime] :
    expMoment2 (dblMass p) dblExp = expMoment2 (scalarLocalMassReal p) sumExp :=
  tsum_dblMass_mul p fun k => (k : ℝ) ^ 2

/-- The reindexed pair `(dblMass p, dblExp)` satisfies `CovarianceFormula.FactorHyp`. -/
theorem factorHyp_dbl (p : ℕ) [Fact p.Prime] : FactorHyp (dblMass p) dblExp where
  nonneg n := by
    by_cases hn : n % 2 = 0
    · rw [dblMass, ite_eq_left hn]
      exact scalarLocalMassReal_nonneg _
    · rw [dblMass_of_odd hn]
  total := by
    have hfun : (dblMass p ∘ fun t : ℕ => 2 * t) = scalarLocalMassReal p :=
      funext fun t => dblMass_two_mul p t
    refine ((mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff fun n hn =>
      dblMass_of_notMem_range hn).mp ?_
    rw [hfun]
    exact hasSum_scalarLocalMassReal
  growth n := by
    by_cases hn : n % 2 = 0
    · obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 2 * t := ⟨n / 2, by omega⟩
      rw [dblExp_two_mul]
      rcases le_or_gt t 1 with ht | ht
      · rw [sumExp_of_le_one ht]
        simp
      · rw [sumExp_of_two_le ht, pow_add, pow_one, omegaExp_apply]
        have h1 : 2 ^ ArithmeticFunction.cardFactors t ≤ t :=
          FirstMoment.two_pow_cardFactors_le (by omega)
        have h2 : max 1 (2 * t) = 2 * t := by omega
        omega
    · rw [dblExp_of_odd hn]
      simp
  moment k := by
    refine ((mul_right_injective₀ (two_ne_zero' ℕ)).summable_iff fun n hn => ?_).mp ?_
    · rw [dblMass_of_notMem_range hn, zero_mul]
    · refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
        ((summable_δ_toReal_mul_add_one_pow (p := p) k).mul_left ((2 : ℝ) ^ k))
      · simp only [Function.comp_apply, dblMass_two_mul]
        exact mul_nonneg (scalarLocalMassReal_nonneg t) (by positivity)
      · simp only [Function.comp_apply, dblMass_two_mul, scalarLocalMassReal]
        have hle : (((2 * t : ℕ) : ℝ) + 1) ^ k ≤ (2 : ℝ) ^ k * ((t : ℝ) + 1) ^ k := by
          rw [← mul_pow]
          refine pow_le_pow_left₀ (by positivity) ?_ k
          push_cast
          linarith
        exact (mul_le_mul_of_nonneg_left hle ENNReal.toReal_nonneg).trans_eq (by ring)

/-! ### The diagonal local factor at a prime, and its two bounds -/

/-- The local factor `h_q(w) = ∑_t δ_q(t) w^{ω_{Tam,t} + Ω(t)}`. -/
noncomputable def sumFactor (q : {n : ℕ // n.Prime}) : ℝ → ℝ :=
  powFactor (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) sumExp

/-- The first moment `m_q(e) = ∑_t δ_q(t) e(t)`. -/
noncomputable def sumMoment1 (q : {n : ℕ // n.Prime}) : ℝ :=
  expMoment1 (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) sumExp

/-- The second moment `S_q(e) = ∑_t δ_q(t) e(t)²`. -/
noncomputable def sumMoment2 (q : {n : ℕ // n.Prime}) : ℝ :=
  expMoment2 (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) sumExp

section Diag

variable (q : {n : ℕ // n.Prime})

/-- `h_q` is the `powFactor` of the reindexed pair. -/
theorem sumFactor_eq_powFactor_dbl : sumFactor q = powFactor (@dblMass (q : ℕ) ⟨q.2⟩) dblExp :=
  (@powFactor_dbl (q : ℕ) ⟨q.2⟩).symm

/-- `h_q(1) = 1`. -/
theorem sumFactor_one : sumFactor q 1 = 1 := by
  rw [sumFactor_eq_powFactor_dbl]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).powFactor_one

/-- `h_q` is differentiable at every `|w| < 2`. -/
theorem differentiableAt_sumFactor {w : ℝ} (hw : |w| < 2) :
    DifferentiableAt ℝ (sumFactor q) w := by
  rw [sumFactor_eq_powFactor_dbl]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).differentiableAt_powFactor hw

/-- At `|w| < 2`, `h_q'(w) = ∑_t δ_q(t) e(t) w^{e(t) - 1}`. -/
theorem deriv_sumFactor {w : ℝ} (hw : |w| < 2) :
    deriv (sumFactor q) w = powFactorDeriv (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) sumExp w := by
  rw [sumFactor_eq_powFactor_dbl,(@factorHyp_dbl (q : ℕ) ⟨q.2⟩).deriv_powFactor hw,
    @powFactorDeriv_dbl (q : ℕ) ⟨q.2⟩]

/-- `|h_q'(w)| ≤ m_q(e)` for `|w| ≤ 1`. -/
theorem abs_deriv_sumFactor_le {w : ℝ} (hw2 : |w| < 2) (hw1 : |w| ≤ 1) :
    |deriv (sumFactor q) w| ≤ sumMoment1 q := by
  rw [deriv_sumFactor q hw2, ← @powFactorDeriv_dbl (q : ℕ) ⟨q.2⟩, sumMoment1,
    ← @expMoment1_dbl (q : ℕ) ⟨q.2⟩]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).abs_powFactorDeriv_le hw1

/-- `h_q'` is differentiable at every `|w| < 2`. -/
theorem differentiableAt_deriv_sumFactor {w : ℝ} (hw : |w| < 2) :
    DifferentiableAt ℝ (deriv (sumFactor q)) w := by
  rw [sumFactor_eq_powFactor_dbl]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).differentiableAt_deriv_powFactor hw

/-- At `|w| < 2`, `h_q''(w) = ∑_t δ_q(t) e(t) (e(t) - 1) w^{e(t) - 2}`. -/
theorem deriv_deriv_sumFactor {w : ℝ} (hw : |w| < 2) :
    deriv (deriv (sumFactor q)) w
      = powFactorDeriv2 (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) sumExp w := by
  rw [sumFactor_eq_powFactor_dbl,(@factorHyp_dbl (q : ℕ) ⟨q.2⟩).deriv_deriv_powFactor hw,
    @powFactorDeriv2_dbl (q : ℕ) ⟨q.2⟩]

/-- `|h_q''(w)| ≤ S_q(e)` for `|w| ≤ 1`. -/
theorem abs_deriv_deriv_sumFactor_le {w : ℝ} (hw2 : |w| < 2) (hw1 : |w| ≤ 1) :
    |deriv (deriv (sumFactor q)) w| ≤ sumMoment2 q := by
  rw [deriv_deriv_sumFactor q hw2, ← @powFactorDeriv2_dbl (q : ℕ) ⟨q.2⟩, sumMoment2,
    ← @expMoment2_dbl (q : ℕ) ⟨q.2⟩]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).abs_powFactorDeriv2_le hw1

/-- `h_q'(1) = m_q(e)`. -/
theorem deriv_sumFactor_one : deriv (sumFactor q) 1 = sumMoment1 q := by
  rw [deriv_sumFactor q (by rw [abs_one]; norm_num), sumMoment1]
  exact FactorHyp.powFactorDeriv_one

/-- `h_q''(1) = S_q(e) - m_q(e)`. -/
theorem deriv_deriv_sumFactor_one :
    deriv (deriv (sumFactor q)) 1 = sumMoment2 q - sumMoment1 q := by
  rw [deriv_deriv_sumFactor q (by rw [abs_one]; norm_num), ← @powFactorDeriv2_dbl (q : ℕ) ⟨q.2⟩,
    sumMoment2, sumMoment1, ← @expMoment2_dbl (q : ℕ) ⟨q.2⟩, ← @expMoment1_dbl (q : ℕ) ⟨q.2⟩,
    ← (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).powFactorDeriv2_one_add]
  ring

/-- `0 ≤ m_q(e)`. -/
theorem sumMoment1_nonneg : 0 ≤ sumMoment1 q := by
  rw [sumMoment1, ← @expMoment1_dbl (q : ℕ) ⟨q.2⟩]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).expMoment1_nonneg

/-- `0 ≤ S_q(e)`. -/
theorem sumMoment2_nonneg : 0 ≤ sumMoment2 q := by
  rw [sumMoment2, ← @expMoment2_dbl (q : ℕ) ⟨q.2⟩]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).expMoment2_nonneg

/-- The diagonal factor series converges at every `|w| ≤ 2`. -/
theorem summable_sumFactorTerm {w : ℝ} (hw : |w| ≤ 2) :
    Summable fun t : ℕ => @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ t * w ^ sumExp t := by
  have h := (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).summable_term hw
  refine (((mul_right_injective₀ (two_ne_zero' ℕ)).summable_iff fun n hn => ?_).mpr h).congr
    fun t => ?_
  · rw [@dblMass_of_notMem_range (q : ℕ) ⟨q.2⟩ n hn, zero_mul]
  · simp only [Function.comp_apply, dblMass_two_mul, dblExp_two_mul]

/-- The second-moment family of the diagonal exponent is summable. -/
theorem summable_sumMoment2Term :
    Summable fun t : ℕ => @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ t * (sumExp t : ℝ) ^ 2 := by
  have h := (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).summable_moment2Term
  refine (((mul_right_injective₀ (two_ne_zero' ℕ)).summable_iff fun n hn => ?_).mpr h).congr
    fun t => ?_
  · rw [@dblMass_of_notMem_range (q : ℕ) ⟨q.2⟩ n hn, zero_mul]
  · simp only [Function.comp_apply, dblMass_two_mul, dblExp_two_mul]

/-- `S_q(e) ≤ 4 S_q(Ω)`. -/
theorem sumMoment2_le_four_mul_primeMoment2 : sumMoment2 q ≤ 4 * primeMoment2 omegaExp q := by
  have hΩ := (@factorHyp_δ (q : ℕ) ⟨q.2⟩ omegaExp two_pow_omegaExp_le).summable_moment2Term
  rw [sumMoment2, expMoment2, primeMoment2, expMoment2, ← hΩ.tsum_mul_left 4]
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_sumMoment2Term q) (hΩ.mul_left 4)
  have hnn : (0 : ℝ) ≤ @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ t :=
    @scalarLocalMassReal_nonneg (q : ℕ) ⟨q.2⟩ t
  have hle : ((sumExp t : ℕ) : ℝ) ≤ 2 * ((omegaExp t : ℕ) : ℝ) := by
    exact_mod_cast sumExp_le_two_mul_omegaExp t
  have hsq : (sumExp t : ℝ) ^ 2 ≤ 4 * (omegaExp t : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (sumExp t), Nat.cast_nonneg (α := ℝ) (omegaExp t)]
  have hkey := mul_le_mul_of_nonneg_left hsq hnn
  have hring : @scalarLocalMassReal (q : ℕ) ⟨q.2⟩ t * (4 * (omegaExp t : ℝ) ^ 2)
      = 4 * (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩ t * (omegaExp t : ℝ) ^ 2) := by ring
  linarith

end Diag

/-- `∑_p S_p(e) < ∞`. -/
theorem summable_sumMoment2 : Summable sumMoment2 :=
  Summable.of_nonneg_of_le sumMoment2_nonneg sumMoment2_le_four_mul_primeMoment2
    ((summable_primeMoment2' two_pow_omegaExp_le).mul_left 4)

/-- `∑_p m_p(e) < ∞`. -/
theorem summable_sumMoment1 : Summable sumMoment1 := by
  refine Summable.of_nonneg_of_le sumMoment1_nonneg (fun q => ?_) summable_sumMoment2
  rw [sumMoment1, sumMoment2, ← @expMoment1_dbl (q : ℕ) ⟨q.2⟩, ← @expMoment2_dbl (q : ℕ) ⟨q.2⟩]
  exact (@factorHyp_dbl (q : ℕ) ⟨q.2⟩).expMoment1_le_expMoment2

/-! ### Hypotheses of the logarithmic derivative formulas -/

/-- The window radius `η = min 1 (1/(2 A + 1))` with `A = ∑_p m_p(e)`. -/
noncomputable def sumWindowRadius : ℝ :=
  min 1 (1 / (2 * (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) + 1))

/-- The family `h_p` satisfies `LogDerivProduct.ProdHyp` with bound family `m_p(e)`, constant
`∑_p m_p(e)` and window radius `sumWindowRadius`. -/
theorem prodHyp_sumFactor :
    LogDerivProduct.ProdHyp sumFactor sumMoment1 (∑' q : {n : ℕ // n.Prime}, sumMoment1 q)
      sumWindowRadius := by
  have hsum := summable_sumMoment1
  have hsup : 0 ≤ ∑' q : {n : ℕ // n.Prime}, sumMoment1 q := tsum_nonneg sumMoment1_nonneg
  have hmem : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| < 2 := fun w hw => by
    rw [abs_of_nonneg hw.1]; linarith [hw.2]
  have hmem1 : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| ≤ 1 := fun w hw => by
    rw [abs_of_nonneg hw.1]; exact hw.2
  refine
    { normalisation := sumFactor_one
      diff := fun q w hw => differentiableAt_sumFactor q (hmem w hw)
      bound_deriv := fun q w hw => abs_deriv_sumFactor_le q (hmem w hw) (hmem1 w hw)
      A_nonneg := sumMoment1_nonneg
      summable_A := hsum
      A_sup_nonneg := hsup
      A_sup_bound := fun q => hsum.le_tsum q fun j _ => sumMoment1_nonneg j
      eta_pos := lt_min zero_lt_one (by positivity)
      eta_le_one := min_le_left _ _
      domain_const := ?_ }
  have h1 : sumWindowRadius ≤ 1 / (2 * (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) + 1) :=
    min_le_right _ _
  have hden : (0 : ℝ) < 2 * (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) + 1 := by linarith
  have h2 : 2 * (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) * sumWindowRadius
      ≤ 2 * (∑' q : {n : ℕ // n.Prime}, sumMoment1 q)
        * (1 / (2 * (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) + 1)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  refine h2.trans ?_
  rw [mul_one_div, div_le_one hden]
  linarith

/-- The family `h_p` satisfies `SecondLogDerivProduct.DerivHyp` with bound family `S_p(e)`. -/
theorem derivHyp_sumFactor : SecondLogDerivProduct.DerivHyp sumFactor sumMoment2 := by
  have hmem : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| < 2 := fun w hw => by
    rw [abs_of_nonneg hw.1]; linarith [hw.2]
  have hmem1 : ∀ w ∈ Set.Icc (0 : ℝ) 1, |w| ≤ 1 := fun w hw => by
    rw [abs_of_nonneg hw.1]; exact hw.2
  exact
    { diff2 := fun q w hw => differentiableAt_deriv_sumFactor q (hmem w hw)
      bound_deriv2 := fun q w hw => abs_deriv_deriv_sumFactor_le q (hmem w hw) (hmem1 w hw)
      B_nonneg := sumMoment2_nonneg
      summable_B := summable_sumMoment2 }

/-- `∑_p m_p(e)² < ∞`. -/
theorem summable_sumMoment1_sq : Summable fun q : {n : ℕ // n.Prime} => sumMoment1 q ^ 2 :=
  (SecondLogDerivProduct.summable_deriv_one_sq prodHyp_sumFactor).congr fun q => by
    rw [deriv_sumFactor_one q]

/-! ### The two one-sided derivatives of a pgf that equals the diagonal product -/

section PGFCore

variable {μ : PMF ℕ}

/-- `∑_p h_p'(1) = ∑_p m_p(e)`. -/
theorem tsum_deriv_sumFactor_one :
    (∑' q : {n : ℕ // n.Prime}, deriv (sumFactor q) 1)
      = ∑' q : {n : ℕ // n.Prime}, sumMoment1 q :=
  tsum_congr deriv_sumFactor_one

/-- `∑_p (h_p'(1))^2 = ∑_p m_p(e)^2`. -/
theorem tsum_deriv_sumFactor_one_sq :
    (∑' q : {n : ℕ // n.Prime}, deriv (sumFactor q) 1 ^ 2)
      = ∑' q : {n : ℕ // n.Prime}, sumMoment1 q ^ 2 :=
  tsum_congr fun q => by rw [deriv_sumFactor_one q]

/-- `∑_p h_p''(1) = ∑_p (S_p(e) - m_p(e))`. -/
theorem tsum_deriv_deriv_sumFactor_one :
    (∑' q : {n : ℕ // n.Prime}, deriv (deriv (sumFactor q)) 1)
      = ∑' q : {n : ℕ // n.Prime}, (sumMoment2 q - sumMoment1 q) :=
  tsum_congr deriv_deriv_sumFactor_one

/-- If the probability generating function `F` of `μ` equals `∏_p h_p` on `[1 - η, 1]`, then
`F'(1) = ∑_p m_p(e)` from the left. -/
theorem hasDerivWithinAt_pgf_sum
    (hpgf : ∀ w ∈ Set.Icc (1 - sumWindowRadius) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG sumFactor w) :
    HasDerivWithinAt (PGFMean.pgf fun n : ℕ => (μ n).toReal)
      (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) (Set.Iio 1) 1 := by
  have hprod := LogDerivProduct.hasDerivWithinAt_prodG prodHyp_sumFactor
  rw [tsum_deriv_sumFactor_one] at hprod
  refine hprod.congr_of_eventuallyEq ?_ (hpgf 1 (LogDerivProduct.one_mem_window prodHyp_sumFactor))
  filter_upwards [Ioo_mem_nhdsLT (LogDerivProduct.window_lt_one prodHyp_sumFactor)] with x hx
  exact hpgf x ⟨hx.left.le, hx.right.le⟩

/-- If the probability generating function `F` of `μ` equals `∏_p h_p` on `[1 - η, 1]`, then the
two functions have the same derivative within `Iic 1` on `(1 - η, 1]`. -/
theorem derivWithin_pgf_sum_eq
    (hpgf : ∀ w ∈ Set.Icc (1 - sumWindowRadius) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG sumFactor w) {w : ℝ}
    (hw : w ∈ Set.Ioc (1 - sumWindowRadius) 1) :
    derivWithin (PGFMean.pgf fun n : ℕ => (μ n).toReal) (Set.Iic 1) w
      = derivWithin (LogDerivProduct.prodG sumFactor) (Set.Iic 1) w := by
  refine Filter.EventuallyEq.derivWithin_eq ?_ (hpgf w ⟨hw.left.le, hw.right⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hw.left), self_mem_nhdsWithin]
    with x hx1 hx2
  exact hpgf x ⟨hx1.le, hx2⟩

/-- If the probability generating function `F` of `μ` equals `∏_p h_p` on `[1 - η, 1]`, then
`F''(1) = ∑_p (S_p - m_p) + (∑_p m_p)² - ∑_p m_p²` from the left. -/
theorem hasDerivWithinAt_derivWithin_pgf_sum
    (hpgf : ∀ w ∈ Set.Icc (1 - sumWindowRadius) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG sumFactor w) :
    HasDerivWithinAt (derivWithin (PGFMean.pgf fun n : ℕ => (μ n).toReal) (Set.Iic 1))
      ((∑' q : {n : ℕ // n.Prime}, (sumMoment2 q - sumMoment1 q))
        + (∑' q : {n : ℕ // n.Prime}, sumMoment1 q) ^ 2
        - ∑' q : {n : ℕ // n.Prime}, sumMoment1 q ^ 2) (Set.Iio 1) 1 := by
  have h :=
    SecondLogDerivProduct.hasDerivWithinAt_derivWithin_prodG prodHyp_sumFactor derivHyp_sumFactor
  rw [tsum_deriv_deriv_sumFactor_one, tsum_deriv_sumFactor_one, tsum_deriv_sumFactor_one_sq] at h
  have hlt := LogDerivProduct.window_lt_one prodHyp_sumFactor
  refine h.congr_of_eventuallyEq ?_ (derivWithin_pgf_sum_eq hpgf ⟨hlt, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsLT hlt] with x hx
  exact derivWithin_pgf_sum_eq hpgf ⟨hx.left, hx.right.le⟩

/-- If the probability generating function of `μ` equals `∏_p h_p` on `[1 - η, 1]`, then
`Var_μ = ∑_p (S_p(e) - m_p(e)²)`. -/
theorem variance_of_pgf_sum
    (hpgf : ∀ w ∈ Set.Icc (1 - sumWindowRadius) 1,
      PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG sumFactor w) :
    variance (fun n : ℕ => (n : ℝ)) μ.toMeasure
      = ∑' q : {n : ℕ // n.Prime}, (sumMoment2 q - sumMoment1 q ^ 2) := by
  rw [BSDTamagawa.PGFSecondDeriv.variance_eq_of_hasDerivWithinAt_derivWithin' μ
    (hasDerivWithinAt_pgf_sum hpgf) (hasDerivWithinAt_derivWithin_pgf_sum hpgf)]
  have h1 := summable_sumMoment1
  have h2 := summable_sumMoment2
  have hd : Summable fun q : {n : ℕ // n.Prime} => sumMoment2 q - sumMoment1 q := h2.sub h1
  have hsplit : (∑' q : {n : ℕ // n.Prime}, (sumMoment2 q - sumMoment1 q))
      + (∑' q : {n : ℕ // n.Prime}, sumMoment1 q)
      = ∑' q : {n : ℕ // n.Prime}, sumMoment2 q := by
    rw [← hd.tsum_add h1]
    exact tsum_congr fun q => by ring
  rw [h2.tsum_sub summable_sumMoment1_sq, ← hsplit]
  ring

end PGFCore

/-! ### The law of `ω_Tam(E) + Ω(Tam(E))` and its pgf -/

/-- The mass of the joint pmf, read back in `ℝ`, is the joint density. -/
theorem toReal_jointOmegaCardFactorsPMF (rb : ℕ × ℕ) :
    (jointOmegaCardFactorsPMF rb).toReal = jointOmegaCardFactorsDensity rb.1 rb.2 :=
  ENNReal.toReal_ofReal (jointOmegaCardFactorsDensity_nonneg rb.1 rb.2)

/-- The law of `ω_Tam(E) + Ω(Tam(E))`, the pushforward of `P_joint` along the coordinate sum, as a
`PMF ℕ`. -/
noncomputable def jointSumPMF : PMF ℕ :=
  jointOmegaCardFactorsPMF.map fun rb : ℕ × ℕ => rb.1 + rb.2

/-- The law of the sum is the pushforward of `P_joint` itself. -/
theorem jointSumPMF_toMeasure :
    jointSumPMF.toMeasure
      = jointOmegaCardFactorsMeasure.map fun rb : ℕ × ℕ => rb.1 + rb.2 := by
  rw [jointSumPMF, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    jointOmegaCardFactorsPMF_toMeasure]

/-- For `w ∈ [0, 1]`, `∑_n P_W(n) w^n = ∑_{(r, b)} π(r, b) w^{r + b}`. -/
theorem pgf_jointSumPMF {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    PGFMean.pgf (fun n : ℕ => (jointSumPMF n).toReal) w
      = ∑' rb : ℕ × ℕ, jointOmegaCardFactorsDensity rb.1 rb.2 * w ^ (rb.1 + rb.2) := by
  have habs : ∀ n : ℕ, ‖w ^ n‖ ≤ 1 := fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw0 n)]
    exact pow_le_one₀ hw0 hw1
  have hqint : Integrable (fun n : ℕ => w ^ n) jointSumPMF.toMeasure :=
    (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable (.of_forall habs)
  have hpint : Integrable (fun rb : ℕ × ℕ => w ^ (rb.1 + rb.2))
      jointOmegaCardFactorsPMF.toMeasure :=
    (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (.of_forall fun rb => habs _)
  rw [PGFMean.pgf]
  calc (∑' n : ℕ, (jointSumPMF n).toReal * w ^ n)
      = ∫ n, w ^ n ∂ jointSumPMF.toMeasure := by
        rw [PMF.integral_eq_tsum _ _ hqint]
        exact tsum_congr fun n => by rw [smul_eq_mul]
    _ = ∫ rb, w ^ (rb.1 + rb.2) ∂ jointOmegaCardFactorsPMF.toMeasure := by
        rw [jointSumPMF, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
          integral_map (measurable_of_countable _).aemeasurable
            measurable_from_top.aestronglyMeasurable]
    _ = ∑' rb : ℕ × ℕ, jointOmegaCardFactorsDensity rb.1 rb.2 * w ^ (rb.1 + rb.2) := by
        rw [PMF.integral_eq_tsum _ _ hpint]
        exact tsum_congr fun rb => by
          rw [smul_eq_mul, toReal_jointOmegaCardFactorsPMF]

/-- For real `w` with `|w| ≤ 1`, `g_p(w, w) = ∑_t δ_p(t) w^{ω_{Tam,t} + Ω(t)}`. -/
theorem ofReal_sumFactor_eq (q : {n : ℕ // n.Prime}) {w : ℝ} (hw : |w| ≤ 1) :
    ((sumFactor q w : ℝ) : ℂ)
      = omegaCardFactorsEulerFactor (q : ℕ) (w : ℂ) (w : ℂ) := by
  have hn : ‖((w : ℝ) : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hC := @hasSum_δ_toReal_mul_omegaCardFactorsFaceWeight (q : ℕ) ⟨q.2⟩ (w : ℂ) (w : ℂ) hn
  have hR : HasSum (fun t : ℕ => ((@scalarLocalMassReal (q : ℕ) ⟨q.2⟩ t * w ^ sumExp t : ℝ) : ℂ))
      ((sumFactor q w : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr (summable_sumFactorTerm q (by linarith [hw])).hasSum
  rw [← @omegaCardFactorsEulerFactor_of_prime (q : ℕ) ⟨q.2⟩ (w : ℂ) (w : ℂ)] at hC
  refine hR.unique (hC.congr_fun fun t => ?_)
  simp only [scalarLocalMassReal]
  rcases le_or_gt t 1 with ht | ht
  · have hΩ : ArithmeticFunction.cardFactors t = 0 := by
      have h0 := omegaExp_eq_zero_of_le_one ht
      rwa [omegaExp_apply] at h0
    rw [ite_eq_right (by omega : ¬ 1 < t), hΩ, sumExp_of_le_one ht]
    push_cast
    ring
  · rw [ite_eq_left ht, sumExp_of_two_le (by omega), omegaExp_apply]
    push_cast
    ring

/-- On `[1 - η, 1]` the real product `LogDerivProduct.prodG sumFactor w` coerces to the bivariate
Euler product `omegaCardFactorsEulerProduct w w`. -/
theorem ofReal_prodG_sumFactor {w : ℝ} (hw : w ∈ Set.Icc (1 - sumWindowRadius) 1) :
    ((LogDerivProduct.prodG sumFactor w : ℝ) : ℂ)
      = omegaCardFactorsEulerProduct (w : ℂ) (w : ℂ) := by
  have hunit := LogDerivProduct.subset_unitInterval prodHyp_sumFactor hw
  have habs : |w| ≤ 1 := by rw [abs_of_nonneg hunit.1]; exact hunit.2
  have hmap := (LogDerivProduct.hasProd_prodG prodHyp_sumFactor hw).map Complex.ofRealHom
    Complex.continuous_ofReal
  rw [omegaCardFactorsEulerProduct]
  exact ((hmap.congr_fun fun q => by
    simpa using (ofReal_sumFactor_eq q habs).symm).tprod_eq).symm

/-- On `[1 - η, 1]` the probability generating function of `ω_Tam(E) + Ω(Tam(E))` equals `∏_p h_p`.
-/
theorem pgf_jointSumPMF_eq_prodG {w : ℝ} (hw : w ∈ Set.Icc (1 - sumWindowRadius) 1) :
    PGFMean.pgf (fun n : ℕ => (jointSumPMF n).toReal) w = LogDerivProduct.prodG sumFactor w := by
  have hunit := LogDerivProduct.subset_unitInterval prodHyp_sumFactor hw
  have hn : ‖((w : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hunit.1]
    exact hunit.2
  refine Complex.ofReal_inj.mp ?_
  rw [pgf_jointSumPMF hunit.1 hunit.2, Complex.ofReal_tsum, ofReal_prodG_sumFactor hw,
    ← tsum_jointOmegaCardFactorsDensity_mul_pow hn hn]
  refine tsum_congr fun rb => ?_
  push_cast
  rw [pow_add]
  ring

/-! ### The variance -/

/-- `Var_{P_joint}(ω_Tam(E) + Ω(Tam(E))) = ∑_{p prime} (S_p(e) - m_p(e)²)`, with
`e = ω_{Tam,·} + Ω`. -/
theorem variance_jointOmegaCardFactorsSum :
    variance (fun rb : ℕ × ℕ => (rb.1 : ℝ) + (rb.2 : ℝ)) jointOmegaCardFactorsMeasure
      = ∑' q : {n : ℕ // n.Prime}, (sumMoment2 q - sumMoment1 q ^ 2) := by
  have hfun : ((fun n : ℕ => (n : ℝ)) ∘ fun rb : ℕ × ℕ => rb.1 + rb.2)
      = fun rb : ℕ × ℕ => (rb.1 : ℝ) + (rb.2 : ℝ) := by
    funext rb
    simp
  have hvar := variance_of_pgf_sum (μ := jointSumPMF) fun w hw => pgf_jointSumPMF_eq_prodG hw
  rw [jointSumPMF_toMeasure, variance_map measurable_from_top.aemeasurable
    (measurable_of_countable _).aemeasurable, hfun] at hvar
  exact hvar

end WeierstrassCurve
