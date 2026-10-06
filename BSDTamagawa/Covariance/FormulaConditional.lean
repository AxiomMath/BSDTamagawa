/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Analysis.PGFSecondDeriv
public import BSDTamagawa.LocalDensity.AdditiveDecomposition
public import BSDTamagawa.Valuation.JointDensity
public import BSDTamagawa.Valuation.LawProbability
public import BSDTamagawa.Analysis.SecondLogDerivProduct
public import BSDTamagawa.Covariance.Local

/-!
# Ingredients for the covariance formula

For distinct primes `ℓ ≠ ℓ'`, the covariance of `v_ℓ(Tam(E))` and `v_{ℓ'}(Tam(E))` in the limiting
joint valuation law `P_{{ℓ,ℓ'}}` equals the absolutely convergent sum `∑_p C_p(ℓ, ℓ')` of the local
covariances; this is proved in `BSDTamagawa.Covariance.Formula`. This file sets up the objects
that proof works with.

The covariance is obtained by polarisation. At the one-parameter point `z_i = w^{t_i}` the joint
generating function becomes the univariate Euler product of the local factors

  `h_p^{(t)}(w) = ∑_{τ ≥ 1} δ_p(τ) w^{E_t(τ)}`,   `E_t(τ) = ∑_i t_i v_i(τ)`,

whose one-sided derivatives at `w = 1` give the variance of `∑_i t_i j_i` in terms of

  `m_p(E) = ∑_τ δ_p(τ) E(τ)`,  `S_p(E) = ∑_τ δ_p(τ) E(τ)^2`.

Here we provide the local factor `∑_τ c_τ w^{e(τ)}` of a mass family with its derivatives and
moments, the moments of `δ_p` under the geometric tail law `HasTailGeometricLaw p`, the bound
`S_p(e) ≤ 150/p²` for `p ≥ 5`, the weight vectors `e_ℓ`, `e_{ℓ'}`, `1` on `Π = {ℓ, ℓ'}`, the joint
law `P_Π` as a `PMF`, and the identification of the pgf of `∑_i t_i 𝐣_i` with the weighted power
series of the joint densities.

## Main definitions

* `BSDTamagawa.CovarianceFormula.powFactor`: the local factor `∑_τ c_τ w^{e(τ)}`.
* `BSDTamagawa.CovarianceFormula.FactorHyp`: the hypotheses on a mass family and an exponent.
* `WeierstrassCurve.primeFactor`: the local factor `h_q(w) = ∑_τ δ_q(τ) w^{e(τ)}` at a prime `q`.
* `WeierstrassCurve.tamagawaValuationPMF`: the joint valuation densities as a `PMF`.
* `WeierstrassCurve.valWeightPMF`: the law of the weighted coordinate sum `∑_i t_i 𝐣_i`.

## Main results

* `WeierstrassCurve.expMoment2_le_of_tailLaw`: `S_p(e) ≤ 150/p²` for `p ≥ 5`.
-/

@[expose] public section

namespace BSDTamagawa.CovarianceFormula

open Filter Set
open scoped Topology

/-! ## §1. The local factor `∑_τ c_τ w^{e(τ)}` of a mass family with controlled exponents

Throughout, `c` is a nonnegative mass family of total mass `1` and `e` is an exponent function with
`2^{e(τ)} ≤ max 1 τ`. -/

/-- The local factor `h(w) = ∑_τ c_τ w^{e(τ)}`. -/
noncomputable def powFactor (c : ℕ → ℝ) (e : ℕ → ℕ) (w : ℝ) : ℝ := ∑' t : ℕ, c t * w ^ e t

/-- The termwise first derivative of `powFactor`. -/
noncomputable def powFactorDeriv (c : ℕ → ℝ) (e : ℕ → ℕ) (w : ℝ) : ℝ :=
  ∑' t : ℕ, c t * ((e t : ℝ) * w ^ (e t - 1))

/-- The termwise second derivative of `powFactor`. -/
noncomputable def powFactorDeriv2 (c : ℕ → ℝ) (e : ℕ → ℕ) (w : ℝ) : ℝ :=
  ∑' t : ℕ, c t * ((e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * w ^ (e t - 1 - 1)))

/-- The first moment `m(e) = ∑_τ c_τ e(τ)`, the value of `powFactorDeriv` at `w = 1`. -/
noncomputable def expMoment1 (c : ℕ → ℝ) (e : ℕ → ℕ) : ℝ := ∑' t : ℕ, c t * (e t : ℝ)

/-- The second moment `S(e) = ∑_τ c_τ e(τ)^2`. -/
noncomputable def expMoment2 (c : ℕ → ℝ) (e : ℕ → ℕ) : ℝ := ∑' t : ℕ, c t * (e t : ℝ) ^ 2

/-- The hypothesis package on the pair `(c, e)`: `c` is a probability mass family, the exponent `e`
grows at most logarithmically (`2^{e τ} ≤ max 1 τ`, so `e(0) = e(1) = 0` and `e(τ) ≤ τ`), and `c`
has all moments against the polynomial weights `(τ + 1)^k`. -/
structure FactorHyp (c : ℕ → ℝ) (e : ℕ → ℕ) : Prop where
  /-- The masses are nonnegative. -/
  nonneg : ∀ t, 0 ≤ c t
  /-- The masses sum to `1`. -/
  total : HasSum c 1
  /-- `2^{e τ} ≤ max 1 τ`: the exponent is at most `log₂ τ`. -/
  growth : ∀ t, 2 ^ e t ≤ max 1 t
  /-- All polynomial moments converge. -/
  moment : ∀ k : ℕ, Summable fun t : ℕ => c t * ((t : ℝ) + 1) ^ k

/-- `max 1 τ ≤ τ + 1`, in `ℝ`. -/
private theorem natCast_max_le (t : ℕ) : ((max 1 t : ℕ) : ℝ) ≤ (t : ℝ) + 1 := by
  have : (max 1 t : ℕ) ≤ t + 1 := by omega
  exact_mod_cast this

/-- `a b ≤ (a + b)^2` for natural numbers, in `ℝ`. -/
theorem natCast_mul_le_natCast_add_sq (a b : ℕ) : (a : ℝ) * b ≤ ((a + b : ℕ) : ℝ) ^ 2 := by
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]

namespace FactorHyp

variable {c : ℕ → ℝ} {e : ℕ → ℕ} (H : FactorHyp c e)

include H

/-- `2^k ≤ τ + 1` for every `k ≤ e τ`: the growth hypothesis, monotone in the exponent. -/
theorem two_pow_le {t k : ℕ} (hk : k ≤ e t) : (2 : ℝ) ^ k ≤ (t : ℝ) + 1 := by
  have h1 : (2 : ℕ) ^ k ≤ 2 ^ e t := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : (2 : ℕ) ^ k ≤ max 1 t := h1.trans (H.growth t)
  calc (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((max 1 t : ℕ) : ℝ) := by exact_mod_cast h2
    _ ≤ (t : ℝ) + 1 := natCast_max_le t

/-- `|w^k| ≤ τ + 1` for `|w| ≤ 2` and `k ≤ e τ`. -/
theorem abs_pow_le {t k : ℕ} (hk : k ≤ e t) {w : ℝ} (hw : |w| ≤ 2) :
    |w ^ k| ≤ (t : ℝ) + 1 := by
  rw [abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg w) hw k).trans (two_pow_le H hk)

/-- `e τ ≤ τ + 1`, in `ℝ`. -/
theorem natCast_e_le (t : ℕ) : ((e t : ℕ) : ℝ) ≤ (t : ℝ) + 1 := by
  calc ((e t : ℕ) : ℝ) ≤ ((2 ^ e t : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self.le
    _ = (2 : ℝ) ^ e t := by push_cast; ring
    _ ≤ (t : ℝ) + 1 := two_pow_le H le_rfl

/-- `e τ - 1 ≤ τ + 1`, in `ℝ`. -/
theorem natCast_e_sub_one_le (t : ℕ) : ((e t - 1 : ℕ) : ℝ) ≤ (t : ℝ) + 1 :=
  le_trans (by exact_mod_cast Nat.sub_le (e t) 1) (natCast_e_le H t)

/-- `e 0 = 0`: the growth hypothesis at `τ = 0` reads `2^{e 0} ≤ 1`. -/
theorem e_zero : e 0 = 0 := by
  have h := H.growth 0
  simp only [Nat.max_eq_left (Nat.zero_le 1)] at h
  by_contra hne
  have : 2 ^ e 0 ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hne)
  omega

/-- `e 1 = 0`: the growth hypothesis at `τ = 1` reads `2^{e 1} ≤ 1`. -/
theorem e_one : e 1 = 0 := by
  have h := H.growth 1
  simp only [Nat.max_self] at h
  by_contra hne
  have : 2 ^ e 1 ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hne)
  omega

/-- `e τ ≤ 2` for `τ ≤ 4`: `2^{e τ} ≤ max 1 τ ≤ 4`. -/
theorem e_le_two {t : ℕ} (ht : t ≤ 4) : e t ≤ 2 := by
  have h := H.growth t
  have hm : max 1 t ≤ 4 := by omega
  by_contra hcon
  have : 2 ^ 3 ≤ 2 ^ e t := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `e τ ≤ τ`, in `ℕ`: `e τ ≤ 2^{e τ} ≤ max 1 τ`, and `e 1 = 0`. -/
theorem e_le_self (t : ℕ) : e t ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact le_of_eq (e_zero H)
  · have h1 : e t ≤ 2 ^ e t := Nat.lt_two_pow_self.le
    have h2 : 2 ^ e t ≤ max 1 t := H.growth t
    have h3 : max 1 t = t := by omega
    omega

/-! ### Termwise bounds -/

/-- `|c_τ w^{e τ}| ≤ c_τ (τ + 1)` on `|w| ≤ 2`. -/
theorem abs_term_le (t : ℕ) {w : ℝ} (hw : |w| ≤ 2) :
    |c t * w ^ e t| ≤ c t * ((t : ℝ) + 1) ^ 1 := by
  rw [abs_mul, abs_of_nonneg (H.nonneg t), pow_one]
  exact mul_le_mul_of_nonneg_left (abs_pow_le H le_rfl hw) (H.nonneg t)

/-- `|c_τ e τ w^{e τ - 1}| ≤ c_τ (τ + 1)^2` on `|w| ≤ 2`. -/
theorem abs_derivTerm_le (t : ℕ) {w : ℝ} (hw : |w| ≤ 2) :
    |c t * ((e t : ℝ) * w ^ (e t - 1))| ≤ c t * ((t : ℝ) + 1) ^ 2 := by
  have hpos : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_nonneg (H.nonneg t), abs_mul, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
  calc (e t : ℝ) * |w ^ (e t - 1)|
      ≤ ((t : ℝ) + 1) * ((t : ℝ) + 1) :=
        mul_le_mul (natCast_e_le H t) (abs_pow_le H (Nat.sub_le _ _) hw) (abs_nonneg _) hpos
    _ = ((t : ℝ) + 1) ^ 2 := by ring

/-- `|c_τ e τ (e τ - 1) w^{e τ - 2}| ≤ c_τ (τ + 1)^3` on `|w| ≤ 2`. -/
theorem abs_deriv2Term_le (t : ℕ) {w : ℝ} (hw : |w| ≤ 2) :
    |c t * ((e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * w ^ (e t - 1 - 1)))|
      ≤ c t * ((t : ℝ) + 1) ^ 3 := by
  have hpos : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_nonneg (H.nonneg t), abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
  calc (e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * |w ^ (e t - 1 - 1)|)
      ≤ ((t : ℝ) + 1) * (((t : ℝ) + 1) * ((t : ℝ) + 1)) := by
        refine mul_le_mul (natCast_e_le H t) ?_ ?_ hpos
        · exact mul_le_mul (natCast_e_sub_one_le H t)
            (abs_pow_le H ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) hw)
            (abs_nonneg _) hpos
        · positivity
    _ = ((t : ℝ) + 1) ^ 3 := by ring

/-! ### Summability -/

/-- The factor series converges at every `|w| ≤ 2`. -/
theorem summable_term {w : ℝ} (hw : |w| ≤ 2) : Summable fun t : ℕ => c t * w ^ e t :=
  Summable.of_norm_bounded (H.moment 1) fun t => abs_term_le H t hw

/-- The derivative series converges at every `|w| ≤ 2`. -/
theorem summable_derivTerm {w : ℝ} (hw : |w| ≤ 2) :
    Summable fun t : ℕ => c t * ((e t : ℝ) * w ^ (e t - 1)) :=
  Summable.of_norm_bounded (H.moment 2) fun t => abs_derivTerm_le H t hw

/-- The first-moment family is summable. -/
theorem summable_moment1Term : Summable fun t : ℕ => c t * (e t : ℝ) := by
  refine Summable.of_norm_bounded (H.moment 1) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (H.nonneg t), Nat.abs_cast, pow_one]
  exact mul_le_mul_of_nonneg_left (natCast_e_le H t) (H.nonneg t)

/-- The second-moment family is summable. -/
theorem summable_moment2Term : Summable fun t : ℕ => c t * (e t : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded (H.moment 2) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (H.nonneg t), abs_pow, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (natCast_e_le H t) 2

/-- The family whose sum is `powFactorDeriv2 c e 1` is summable. -/
theorem summable_deriv2AtOneTerm :
    Summable fun t : ℕ => c t * ((e t : ℝ) * ((e t - 1 : ℕ) : ℝ)) := by
  refine Summable.of_norm_bounded (H.moment 2) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (H.nonneg t), abs_mul, Nat.abs_cast, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
  calc (e t : ℝ) * ((e t - 1 : ℕ) : ℝ) ≤ ((t : ℝ) + 1) * ((t : ℝ) + 1) :=
        mul_le_mul (natCast_e_le H t) (natCast_e_sub_one_le H t) (Nat.cast_nonneg _)
          (by positivity)
    _ = ((t : ℝ) + 1) ^ 2 := by ring

/-! ### Nonnegativity and the corner values -/

/-- `0 ≤ m(e)`. -/
theorem expMoment1_nonneg : 0 ≤ expMoment1 c e :=
  tsum_nonneg fun t => mul_nonneg (H.nonneg t) (Nat.cast_nonneg _)

/-- `0 ≤ S(e)`. -/
theorem expMoment2_nonneg : 0 ≤ expMoment2 c e :=
  tsum_nonneg fun t => mul_nonneg (H.nonneg t) (by positivity)

/-- `m(e) ≤ S(e)`: termwise `n ≤ n^2` for a natural number `n`. -/
theorem expMoment1_le_expMoment2 : expMoment1 c e ≤ expMoment2 c e := by
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_moment1Term H) (summable_moment2Term H)
  refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
  have : e t ≤ e t ^ 2 := Nat.le_self_pow (by norm_num) _
  calc (e t : ℝ) ≤ ((e t ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
    _ = (e t : ℝ) ^ 2 := by push_cast; ring

/-- `h(1) = ∑_τ c_τ = 1`. -/
theorem powFactor_one : powFactor c e 1 = 1 := by
  rw [powFactor, tsum_congr fun t : ℕ => by rw [one_pow, mul_one]]
  exact H.total.tsum_eq

omit H in
/-- `h'(1) = m(e)`. -/
theorem powFactorDeriv_one : powFactorDeriv c e 1 = expMoment1 c e :=
  tsum_congr fun t => by rw [one_pow, mul_one]

/-- `h''(1) + m(e) = S(e)`: termwise `n(n-1) + n = n^2` in `ℕ`. -/
theorem powFactorDeriv2_one_add : powFactorDeriv2 c e 1 + expMoment1 c e = expMoment2 c e := by
  have h1 : powFactorDeriv2 c e 1 = ∑' t : ℕ, c t * ((e t : ℝ) * ((e t - 1 : ℕ) : ℝ)) :=
    tsum_congr fun t => by rw [one_pow, mul_one]
  rw [h1, expMoment1, ← (summable_deriv2AtOneTerm H).tsum_add (summable_moment1Term H), expMoment2]
  refine tsum_congr fun t => ?_
  have hsq : (e t : ℝ) * ((e t - 1 : ℕ) : ℝ) + (e t : ℝ) = (e t : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (e t) with h | h
    · rw [h]; norm_num
    · have h1 : ((e t - 1 : ℕ) : ℝ) = (e t : ℝ) - 1 := by
        have : (1 : ℕ) ≤ e t := h
        push_cast [Nat.cast_sub this]
        ring
      rw [h1]; ring
  rw [← hsq]; ring

/-! ### Differentiability, and the identification of the derivatives -/

/-- **Termwise differentiation of the factor series.** For `|w| < 2`,
`h'(w) = ∑_τ c_τ e(τ) w^{e(τ)-1}`. -/
theorem hasDerivAt_powFactor {w : ℝ} (hw : |w| < 2) :
    HasDerivAt (powFactor c e) (powFactorDeriv c e w) w := by
  have hmem : w ∈ Ioo (-2 : ℝ) 2 := abs_lt.1 hw
  refine hasDerivAt_tsum_of_isPreconnected (u := fun t : ℕ => c t * ((t : ℝ) + 1) ^ 2)
    (g := fun (t : ℕ) (x : ℝ) => c t * x ^ e t)
    (g' := fun (t : ℕ) (x : ℝ) => c t * ((e t : ℝ) * x ^ (e t - 1)))
    (H.moment 2) isOpen_Ioo isPreconnected_Ioo (fun t x _ => ?_) (fun t x hx => ?_) hmem
    (summable_term H hw.le) hmem
  · exact (hasDerivAt_pow (e t) x).const_mul (c t)
  · rw [Real.norm_eq_abs]
    exact abs_derivTerm_le H t (le_of_lt (abs_lt.2 hx))

/-- `deriv h = h'` on `|w| < 2`. -/
theorem deriv_powFactor {w : ℝ} (hw : |w| < 2) :
    deriv (powFactor c e) w = powFactorDeriv c e w :=
  (hasDerivAt_powFactor H hw).deriv

/-- `h` is differentiable on `|w| < 2`. -/
theorem differentiableAt_powFactor {w : ℝ} (hw : |w| < 2) :
    DifferentiableAt ℝ (powFactor c e) w :=
  (hasDerivAt_powFactor H hw).differentiableAt

/-- `deriv h` and the termwise derivative series agree on a neighbourhood of any `|w| < 2`. -/
theorem deriv_powFactor_eventuallyEq {w : ℝ} (hw : |w| < 2) :
    deriv (powFactor c e) =ᶠ[𝓝 w] powFactorDeriv c e := by
  filter_upwards [Ioo_mem_nhds (abs_lt.1 hw).1 (abs_lt.1 hw).2] with x hx
  exact deriv_powFactor H (abs_lt.2 hx)

/-- **Termwise second differentiation.** For `|w| < 2`, `h''(w) = ∑_τ c_τ e(τ)(e(τ)-1) w^{e(τ)-2}`.
-/
theorem hasDerivAt_powFactorDeriv {w : ℝ} (hw : |w| < 2) :
    HasDerivAt (powFactorDeriv c e) (powFactorDeriv2 c e w) w := by
  have hmem : w ∈ Ioo (-2 : ℝ) 2 := abs_lt.1 hw
  refine hasDerivAt_tsum_of_isPreconnected (u := fun t : ℕ => c t * ((t : ℝ) + 1) ^ 3)
    (g := fun (t : ℕ) (x : ℝ) => c t * ((e t : ℝ) * x ^ (e t - 1)))
    (g' := fun (t : ℕ) (x : ℝ) =>
      c t * ((e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * x ^ (e t - 1 - 1))))
    (H.moment 3) isOpen_Ioo isPreconnected_Ioo (fun t x _ => ?_) (fun t x hx => ?_) hmem
    (summable_derivTerm H hw.le) hmem
  · exact ((hasDerivAt_pow (e t - 1) x).const_mul ((e t : ℝ))).const_mul (c t)
  · rw [Real.norm_eq_abs]
    exact abs_deriv2Term_le H t (le_of_lt (abs_lt.2 hx))

/-- `deriv (deriv h) w = h''(w)` on `|w| < 2`. -/
theorem deriv_deriv_powFactor {w : ℝ} (hw : |w| < 2) :
    deriv (deriv (powFactor c e)) w = powFactorDeriv2 c e w := by
  rw [(deriv_powFactor_eventuallyEq H hw).deriv_eq]
  exact (hasDerivAt_powFactorDeriv H hw).deriv

/-- `deriv h` is differentiable on `|w| < 2`. -/
theorem differentiableAt_deriv_powFactor {w : ℝ} (hw : |w| < 2) :
    DifferentiableAt ℝ (deriv (powFactor c e)) w :=
  ((deriv_powFactor_eventuallyEq H hw).differentiableAt_iff).2
    (hasDerivAt_powFactorDeriv H hw).differentiableAt

/-! ### The uniform bounds on `[0, 1]` -/

/-- `|h'(w)| ≤ m(e)` for `|w| ≤ 1`. -/
theorem abs_powFactorDeriv_le {w : ℝ} (hw : |w| ≤ 1) :
    |powFactorDeriv c e w| ≤ expMoment1 c e := by
  have hb : ∀ t : ℕ, ‖c t * ((e t : ℝ) * w ^ (e t - 1))‖ ≤ c t * (e t : ℝ) := fun t => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (H.nonneg t), abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
    calc (e t : ℝ) * |w ^ (e t - 1)| ≤ (e t : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left
            (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg w) hw) (Nat.cast_nonneg _)
      _ = (e t : ℝ) := mul_one _
  have hsn : Summable fun t : ℕ => ‖c t * ((e t : ℝ) * w ^ (e t - 1))‖ :=
    Summable.of_nonneg_of_le (fun t => norm_nonneg _) hb (summable_moment1Term H)
  rw [powFactorDeriv, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hb (summable_moment1Term H))

/-- `|h''(w)| ≤ S(e)` for `|w| ≤ 1`. -/
theorem abs_powFactorDeriv2_le {w : ℝ} (hw : |w| ≤ 1) :
    |powFactorDeriv2 c e w| ≤ expMoment2 c e := by
  have hb : ∀ t : ℕ,
      ‖c t * ((e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * w ^ (e t - 1 - 1)))‖ ≤ c t * (e t : ℝ) ^ 2 :=
    fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (H.nonneg t), abs_mul, abs_mul, Nat.abs_cast,
        Nat.abs_cast]
      refine mul_le_mul_of_nonneg_left ?_ (H.nonneg t)
      have hpow : |w ^ (e t - 1 - 1)| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg w) hw
      have h1 : ((e t - 1 : ℕ) : ℝ) ≤ (e t : ℝ) := by exact_mod_cast Nat.sub_le (e t) 1
      calc (e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * |w ^ (e t - 1 - 1)|)
          ≤ (e t : ℝ) * ((e t : ℝ) * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact mul_le_mul h1 hpow (abs_nonneg _) (Nat.cast_nonneg _)
        _ = (e t : ℝ) ^ 2 := by ring
  have hsn : Summable fun t : ℕ =>
      ‖c t * ((e t : ℝ) * (((e t - 1 : ℕ) : ℝ) * w ^ (e t - 1 - 1)))‖ :=
    Summable.of_nonneg_of_le (fun t => norm_nonneg _) hb (summable_moment2Term H)
  rw [powFactorDeriv2, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hb (summable_moment2Term H))

end FactorHyp

end BSDTamagawa.CovarianceFormula

namespace WeierstrassCurve

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open BSDTamagawa BSDTamagawa.CovarianceFormula

/-! ## §2. The local density in `ℝ`, and its moments under the tail law -/

/-- `δ_p(τ)` read in `ℝ`. -/
noncomputable def scalarLocalMassReal (p : ℕ) [Fact p.Prime] (t : ℕ) : ℝ := (δ p t).toReal

variable {p : ℕ} [Fact p.Prime]

/-- The real local masses are nonnegative. -/
theorem scalarLocalMassReal_nonneg (t : ℕ) : 0 ≤ scalarLocalMassReal p t := ENNReal.toReal_nonneg

/-- The real local masses have total mass `1`. -/
theorem hasSum_scalarLocalMassReal : HasSum (scalarLocalMassReal p) 1 := by
  have h := ENNReal.hasSum_toReal (f := δ p) (by rw [tsum_δ]; exact ENNReal.one_ne_top)
  have hreal : ∑' t : ℕ, (δ p t).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq fun t => ne_top_of_le_ne_top ENNReal.one_ne_top (δ_le_one t),
      tsum_δ, ENNReal.toReal_one]
  rwa [hreal] at h

/-- **The tail law, in `ℝ`.** If `HasTailGeometricLaw p`, there is a real constant `a ∈ [0, 1]`
with `δ_p(τ) = a p^{-τ}` for every `τ ≥ 5`. -/
theorem exists_tailReal_of_tailLaw (h : HasTailGeometricLaw p) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      ∀ t : ℕ, 5 ≤ t → scalarLocalMassReal p t = a * ((p : ℝ)⁻¹) ^ t := by
  obtain ⟨a, ha, hgeom⟩ := h
  refine ⟨a.toReal, ENNReal.toReal_nonneg, ?_, fun t ht => ?_⟩
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha
  · rw [scalarLocalMassReal, hgeom t ht, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **All polynomial moments of `δ_p` converge under the tail law.** For every `k`,
`∑_τ δ_p(τ) (τ + 1)^k < ∞`. -/
theorem summable_scalarLocalMassReal_mul_pow_of_tailLaw (h : HasTailGeometricLaw p) (k : ℕ) :
    Summable fun t : ℕ => scalarLocalMassReal p t * ((t : ℝ) + 1) ^ k := by
  obtain ⟨a, -, -, hgeom⟩ := exists_tailReal_of_tailLaw h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hrpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hrne : ((p : ℝ))⁻¹ ≠ 0 := ne_of_gt hrpos
  have hrlt : ‖((p : ℝ))⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrpos, inv_eq_one_div, div_lt_one hp0]
    exact hp1
  have hg : Summable fun n : ℕ => (n : ℝ) ^ k * ((p : ℝ)⁻¹) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k hrlt
  have hg6 : Summable fun s : ℕ => ((s + 6 : ℕ) : ℝ) ^ k * ((p : ℝ)⁻¹) ^ (s + 6) :=
    (summable_nat_add_iff 6).mpr hg
  refine (summable_nat_add_iff 5).mp ((hg6.mul_left (a * ((p : ℝ)⁻¹)⁻¹)).congr fun s => ?_)
  have hx : ((s + 5 : ℕ) : ℝ) + 1 = ((s + 6 : ℕ) : ℝ) := by push_cast; ring
  have hr6 : ((p : ℝ)⁻¹) ^ (s + 6) = ((p : ℝ)⁻¹) ^ (s + 5) * (p : ℝ)⁻¹ := by
    rw [show s + 6 = (s + 5) + 1 from rfl, pow_succ]
  rw [hgeom (s + 5) (by omega), hx, hr6]
  field_simp

/-! ## §3. The index set `Π = {ℓ, ℓ'}`, its two indices, and the weighted exponents -/

section Pair

variable {ℓ ℓ' : ℕ}

/-- The first index carries `ℓ`. -/
@[simp] theorem coe_valPairFst : ((valPairFst ℓ ℓ' : ↥({ℓ, ℓ'} : Finset ℕ)) : ℕ) = ℓ := rfl

/-- The second index carries `ℓ'`. -/
@[simp] theorem coe_valPairSnd : ((valPairSnd ℓ ℓ' : ↥({ℓ, ℓ'} : Finset ℕ)) : ℕ) = ℓ' := rfl

/-- `↥{ℓ, ℓ'}` has exactly the two named elements. -/
theorem univ_valPairIndex (ℓ ℓ' : ℕ) :
    (Finset.univ : Finset ↥({ℓ, ℓ'} : Finset ℕ)) = {valPairFst ℓ ℓ', valPairSnd ℓ ℓ'} := by
  refine Finset.ext fun i => ?_
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h : i = valPairFst ℓ ℓ'
  · exact Or.inl h
  · exact Or.inr (eq_valPairSnd_of_ne h)

/-- A sum over `↥{ℓ, ℓ'}` is the sum of its two terms. -/
theorem sum_univ_valPairIndex {M : Type*} [AddCommMonoid M] (hne : ℓ ≠ ℓ')
    (f : ↥({ℓ, ℓ'} : Finset ℕ) → M) :
    ∑ i, f i = f (valPairFst ℓ ℓ') + f (valPairSnd ℓ ℓ') := by
  rw [univ_valPairIndex ℓ ℓ', Finset.sum_insert (by simpa using valPairFst_ne_valPairSnd hne),
    Finset.sum_singleton]

/-! ### The three weight vectors -/

/-- The weight vector `e_ℓ` picking out the `ℓ`-coordinate. -/
def valFstWeight (ℓ ℓ' : ℕ) (i : ↥({ℓ, ℓ'} : Finset ℕ)) : ℕ :=
  if i = valPairFst ℓ ℓ' then 1 else 0

/-- The weight vector `e_{ℓ'}` picking out the `ℓ'`-coordinate. -/
def valSndWeight (ℓ ℓ' : ℕ) (i : ↥({ℓ, ℓ'} : Finset ℕ)) : ℕ :=
  if i = valPairSnd ℓ ℓ' then 1 else 0

/-- The all-ones weight vector, whose weighted sum is `v_ℓ + v_{ℓ'}`. -/
def valTotalWeight (ℓ ℓ' : ℕ) : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ := fun _ => 1

/-! ### The weighted coordinate sum and the weighted exponent -/

/-- The weighted coordinate sum `∑_i t_i 𝐣_i`, an `ℕ`-valued random variable on the multi-index
space `ℤ_{≥0}^Π`. At `t = e_ℓ` it is the coordinate `𝐣_ℓ`; at `t = 1` it is `𝐣_ℓ + 𝐣_{ℓ'}`. -/
def valWeightSum {P : Finset ℕ} (t : ↥P → ℕ) (r : ↥P → ℕ) : ℕ := ∑ i, t i * r i

/-- The weighted exponent `E_t(τ) = ∑_i t_i v_i(τ)`. -/
def valExpWeight (P : Finset ℕ) (t : ↥P → ℕ) (τ : ℕ) : ℕ := ∑ i : ↥P, t i * padicValNat (i : ℕ) τ

/-- `E_{e_ℓ} = v_ℓ`. -/
theorem valExpWeight_fst (hne : ℓ ≠ ℓ') (τ : ℕ) :
    valExpWeight {ℓ, ℓ'} (valFstWeight ℓ ℓ') τ = padicValNat ℓ τ := by
  rw [valExpWeight, sum_univ_valPairIndex hne]
  simp [valFstWeight, (valPairFst_ne_valPairSnd hne).symm]

/-- `E_{e_{ℓ'}} = v_{ℓ'}`. -/
theorem valExpWeight_snd (hne : ℓ ≠ ℓ') (τ : ℕ) :
    valExpWeight {ℓ, ℓ'} (valSndWeight ℓ ℓ') τ = padicValNat ℓ' τ := by
  rw [valExpWeight, sum_univ_valPairIndex hne]
  simp [valSndWeight, valPairFst_ne_valPairSnd hne]

/-- `E_1 = v_ℓ + v_{ℓ'}`. -/
theorem valExpWeight_total (hne : ℓ ≠ ℓ') (τ : ℕ) :
    valExpWeight {ℓ, ℓ'} (valTotalWeight ℓ ℓ') τ = padicValNat ℓ τ + padicValNat ℓ' τ := by
  rw [valExpWeight, sum_univ_valPairIndex hne]
  simp [valTotalWeight]

/-- `∑_i (e_ℓ)_i 𝐣_i = 𝐣_ℓ`. -/
theorem valWeightSum_fst (hne : ℓ ≠ ℓ') (r : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ) :
    valWeightSum (valFstWeight ℓ ℓ') r = r (valPairFst ℓ ℓ') := by
  rw [valWeightSum, sum_univ_valPairIndex hne]
  simp [valFstWeight, (valPairFst_ne_valPairSnd hne).symm]

/-- `∑_i (e_{ℓ'})_i 𝐣_i = 𝐣_{ℓ'}`. -/
theorem valWeightSum_snd (hne : ℓ ≠ ℓ') (r : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ) :
    valWeightSum (valSndWeight ℓ ℓ') r = r (valPairSnd ℓ ℓ') := by
  rw [valWeightSum, sum_univ_valPairIndex hne]
  simp [valSndWeight, valPairFst_ne_valPairSnd hne]

/-- `∑_i 1 · 𝐣_i = 𝐣_ℓ + 𝐣_{ℓ'}`. -/
theorem valWeightSum_total (hne : ℓ ≠ ℓ') (r : ↥({ℓ, ℓ'} : Finset ℕ) → ℕ) :
    valWeightSum (valTotalWeight ℓ ℓ') r = r (valPairFst ℓ ℓ') + r (valPairSnd ℓ ℓ') := by
  rw [valWeightSum, sum_univ_valPairIndex hne]
  simp [valTotalWeight]

/-! ### The growth condition `2^{E(τ)} ≤ max 1 τ` -/

/-- `2^{v_ℓ(τ)} ≤ max 1 τ` for a prime `ℓ`. -/
theorem two_pow_padicValNat_le (hℓ : ℓ.Prime) (t : ℕ) : 2 ^ padicValNat ℓ t ≤ max 1 t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [padicValNat_zero_right]; simp
  · have h1 : 2 ^ padicValNat ℓ t ≤ ℓ ^ padicValNat ℓ t := Nat.pow_le_pow_left hℓ.two_le _
    have h2 : ℓ ^ padicValNat ℓ t ≤ t := Nat.le_of_dvd ht pow_padicValNat_dvd
    have h3 : max 1 t = t := by omega
    omega

/-- `2^{v_ℓ(τ) + v_{ℓ'}(τ)} ≤ max 1 τ` for distinct primes `ℓ ≠ ℓ'`. -/
theorem two_pow_padicValNat_add_le (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (t : ℕ) :
    2 ^ (padicValNat ℓ t + padicValNat ℓ' t) ≤ max 1 t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [padicValNat_zero_right, padicValNat_zero_right]; simp
  · have hco : Nat.Coprime (ℓ ^ padicValNat ℓ t) (ℓ' ^ padicValNat ℓ' t) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hℓ hℓ').2 hne)
    have hdvd : ℓ ^ padicValNat ℓ t * ℓ' ^ padicValNat ℓ' t ∣ t :=
      hco.mul_dvd_of_dvd_of_dvd pow_padicValNat_dvd pow_padicValNat_dvd
    have h1 : 2 ^ (padicValNat ℓ t + padicValNat ℓ' t)
        ≤ ℓ ^ padicValNat ℓ t * ℓ' ^ padicValNat ℓ' t := by
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left hℓ.two_le _)
        (Nat.pow_le_pow_left hℓ'.two_le _)
    have h2 := Nat.le_of_dvd ht hdvd
    have h3 : max 1 t = t := by omega
    omega

end Pair

/-! ## §4. Factor hypotheses at `δ_p`, summability of the marginals, and the `O(p^{-2})` bound -/

section Moments

variable {p : ℕ} [Fact p.Prime]

/-- **The tail law implies `FactorHyp`.** For any exponent function with `2^{e(τ)} ≤ max 1 τ`, the
pair `(δ_p, e)` satisfies `FactorHyp`. -/
theorem factorHyp_of_tailLaw (h : HasTailGeometricLaw p) {e : ℕ → ℕ}
    (he : ∀ t, 2 ^ e t ≤ max 1 t) : FactorHyp (scalarLocalMassReal p) e where
  nonneg := scalarLocalMassReal_nonneg
  total := hasSum_scalarLocalMassReal
  growth := he
  moment := summable_scalarLocalMassReal_mul_pow_of_tailLaw h

/-! ### Summability of the marginals -/

/-- The `ℝ≥0∞` sum `∑_τ δ_p(τ) n(τ)` is finite as soon as the corresponding real family is
summable.
-/
theorem tsum_δ_mul_natCast_ne_top_of_summable {f : ℕ → ℕ}
    (hs : Summable fun t : ℕ => (δ p t).toReal * (f t : ℝ)) :
    (∑' t : ℕ, δ p t * (f t : ℝ≥0∞)) ≠ ⊤ := by
  have hnn : ∀ t : ℕ, 0 ≤ (δ p t).toReal * (f t : ℝ) := fun t =>
    mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hterm : ∀ t : ℕ, δ p t * (f t : ℝ≥0∞)
      = ENNReal.ofReal ((δ p t).toReal * (f t : ℝ)) := fun t => by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (δ_le_one t)),
      ENNReal.ofReal_natCast]
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg hnn hs]
  exact ENNReal.ofReal_ne_top

/-- The two-weight version of `tsum_δ_mul_natCast_ne_top_of_summable`. -/
theorem tsum_δ_mul_natCast_mul_natCast_ne_top_of_summable {f g : ℕ → ℕ}
    (hs : Summable fun t : ℕ => (δ p t).toReal * (f t : ℝ) * (g t : ℝ)) :
    (∑' t : ℕ, δ p t * (f t : ℝ≥0∞) * (g t : ℝ≥0∞)) ≠ ⊤ := by
  have hnn : ∀ t : ℕ, 0 ≤ (δ p t).toReal * (f t : ℝ) * (g t : ℝ) := fun t =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hterm : ∀ t : ℕ, δ p t * (f t : ℝ≥0∞) * (g t : ℝ≥0∞)
      = ENNReal.ofReal ((δ p t).toReal * (f t : ℝ) * (g t : ℝ)) := fun t => by
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (δ_le_one t)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg hnn hs]
  exact ENNReal.ofReal_ne_top

/-- **The marginal family `valuationTerm p r` is summable under the tail law**, for every prime
`r`. -/
theorem summable_valuationTerm_of_tailLaw (h : HasTailGeometricLaw p) {r : ℕ} (hr : r.Prime) :
    Summable (valuationTerm p r) := by
  have hfac := factorHyp_of_tailLaw h (e := fun t => padicValNat r t)
    (two_pow_padicValNat_le hr)
  exact summable_valuationTerm p r
    (tsum_δ_mul_natCast_ne_top_of_summable hfac.summable_moment1Term)

/-! ### The marginal moment in the language of §1 -/

/-- `m_p(v_r) = μ_{p,r}`. -/
theorem expMoment1_padicValNat (r : ℕ) :
    expMoment1 (scalarLocalMassReal p) (fun t => padicValNat r t) = valuationMoment p r := rfl

/-! ### The `O(p^{-2})` bound at `p ≥ 5` -/

/-- `δ_p(τ) ≤ 9/p^2` for `τ ≠ 1`, in `ℝ`. -/
theorem scalarLocalMassReal_le_nine_div_sq {t : ℕ} (ht : t ≠ 1) :
    scalarLocalMassReal p t ≤ 9 / (p : ℝ) ^ 2 := by
  rw [scalarLocalMassReal]
  have hp0 : ((p : ℝ≥0∞)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hne : (9 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.div_ne_top (by norm_num) hp0
  have h := ENNReal.toReal_mono hne (δ_le_nine_div_sq (p := p) ht)
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h
  simpa using h

/-- **`S_p(e) ≪ p^{-2}`.** For every prime `p ≥ 5` with the tail law and every exponent function
with `2^{e(τ)} ≤ max 1 τ`,

  `S_p(e) = ∑_τ δ_p(τ) e(τ)^2 ≤ 150/p^2`. -/
theorem expMoment2_le_of_tailLaw (hp : 5 ≤ p) (h : HasTailGeometricLaw p) {e : ℕ → ℕ}
    (he : ∀ t, 2 ^ e t ≤ max 1 t) :
    expMoment2 (scalarLocalMassReal p) e ≤ 150 / (p : ℝ) ^ 2 := by
  have H := factorHyp_of_tailLaw h he
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsm := H.summable_moment2Term
  have hterm : ∀ i : ℕ, 2 ≤ i → i ≤ 4 →
      scalarLocalMassReal p i * (e i : ℝ) ^ 2 ≤ 36 / (p : ℝ) ^ 2 := by
    intro i h2 h4
    have hc := scalarLocalMassReal_le_nine_div_sq (p := p) (t := i) (by omega)
    have he2 : (e i : ℝ) ^ 2 ≤ 4 := by
      have hle : (e i : ℝ) ≤ 2 := by exact_mod_cast H.e_le_two h4
      nlinarith [Nat.cast_nonneg (α := ℝ) (e i)]
    calc scalarLocalMassReal p i * (e i : ℝ) ^ 2 ≤ (9 / (p : ℝ) ^ 2) * 4 :=
          mul_le_mul hc he2 (by positivity) (by positivity)
      _ = 36 / (p : ℝ) ^ 2 := by ring
  have hhead : (∑ i ∈ Finset.range 5, scalarLocalMassReal p i * (e i : ℝ) ^ 2)
      ≤ 108 / (p : ℝ) ^ 2 := by
    have h0 : scalarLocalMassReal p 0 * (e 0 : ℝ) ^ 2 = 0 := by rw [H.e_zero]; norm_num
    have h1 : scalarLocalMassReal p 1 * (e 1 : ℝ) ^ 2 = 0 := by rw [H.e_one]; norm_num
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    have h2 := hterm 2 (by norm_num) (by norm_num)
    have h3 := hterm 3 (by norm_num) (by norm_num)
    have h4 := hterm 4 (by norm_num) (by norm_num)
    have hcalc : (36 : ℝ) / (p : ℝ) ^ 2 + 36 / (p : ℝ) ^ 2 + 36 / (p : ℝ) ^ 2
        = 108 / (p : ℝ) ^ 2 := by ring
    linarith
  obtain ⟨a, ha0, ha1, hgeom⟩ := exists_tailReal_of_tailLaw h
  have hx0 : (0 : ℝ) ≤ 4 / (p : ℝ) := by positivity
  have hx45 : (4 : ℝ) / (p : ℝ) ≤ 4 / 5 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    linarith
  have hx1 : (4 : ℝ) / (p : ℝ) < 1 := by linarith
  have hb : ∀ s : ℕ, scalarLocalMassReal p (s + 5) * (e (s + 5) : ℝ) ^ 2
      ≤ (4 / (p : ℝ)) ^ (s + 5) := by
    intro s
    have hee : (e (s + 5) : ℝ) ^ 2 ≤ (4 : ℝ) ^ (s + 5) := by
      have hn1 : e (s + 5) ≤ 2 ^ (s + 5) := (H.e_le_self _).trans Nat.lt_two_pow_self.le
      have hn2 : (e (s + 5)) ^ 2 ≤ (2 ^ (s + 5)) ^ 2 := Nat.pow_le_pow_left hn1 2
      have hn3 : (2 ^ (s + 5)) ^ 2 = 4 ^ (s + 5) := by
        rw [← pow_mul, mul_comm (s + 5) 2, pow_mul]
        norm_num
      rw [hn3] at hn2
      exact_mod_cast hn2
    have hsplit : (4 / (p : ℝ)) ^ (s + 5) = (4 : ℝ) ^ (s + 5) * ((p : ℝ)⁻¹) ^ (s + 5) := by
      rw [← mul_pow, div_eq_mul_inv]
    rw [hgeom (s + 5) (by omega), hsplit]
    have hr : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ (s + 5) := by positivity
    calc a * ((p : ℝ)⁻¹) ^ (s + 5) * (e (s + 5) : ℝ) ^ 2
        ≤ 1 * ((p : ℝ)⁻¹) ^ (s + 5) * (4 : ℝ) ^ (s + 5) :=
          mul_le_mul (mul_le_mul_of_nonneg_right ha1 hr) hee (by positivity) (by positivity)
      _ = (4 : ℝ) ^ (s + 5) * ((p : ℝ)⁻¹) ^ (s + 5) := by ring
  have hsummx : Summable fun s : ℕ => (4 / (p : ℝ)) ^ (s + 5) := by
    refine ((summable_geometric_of_lt_one hx0 hx1).mul_right ((4 / (p : ℝ)) ^ 5)).congr fun s => ?_
    rw [← pow_add]
  have htailsum : Summable fun s : ℕ => scalarLocalMassReal p (s + 5) * (e (s + 5) : ℝ) ^ 2 :=
    (summable_nat_add_iff 5).mpr hsm
  have hgeomval : (∑' s : ℕ, (4 / (p : ℝ)) ^ (s + 5))
      = (1 - 4 / (p : ℝ))⁻¹ * (4 / (p : ℝ)) ^ 5 := by
    rw [tsum_congr fun s : ℕ => (pow_add (4 / (p : ℝ)) s 5), tsum_mul_right,
      tsum_geometric_of_lt_one hx0 hx1]
  have hpos : (0 : ℝ) < 1 - 4 / (p : ℝ) := by linarith
  have hinv : (1 - 4 / (p : ℝ))⁻¹ ≤ 5 := by
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 5)]
    have h5 : (5 : ℝ)⁻¹ = 1 / 5 := by norm_num
    rw [h5]
    linarith
  have hquint : (5 : ℝ) * (4 / (p : ℝ)) ^ 5 ≤ 42 / (p : ℝ) ^ 2 := by
    have hfive : (5 : ℝ) * (4 / (p : ℝ)) ^ 5 = 5120 / (p : ℝ) ^ 5 := by
      rw [div_pow]; ring
    rw [hfive, div_le_div_iff₀ (by positivity) (by positivity)]
    have h125 : (125 : ℝ) ≤ (p : ℝ) ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h125 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)]
  have htail : (∑' s : ℕ, scalarLocalMassReal p (s + 5) * (e (s + 5) : ℝ) ^ 2)
      ≤ 42 / (p : ℝ) ^ 2 := by
    refine le_trans (htailsum.tsum_le_tsum hb hsummx) ?_
    rw [hgeomval]
    refine le_trans (mul_le_mul_of_nonneg_right hinv (by positivity)) hquint
  have hsplit := Summable.sum_add_tsum_nat_add 5 hsm
  rw [expMoment2, ← hsplit]
  have : (108 : ℝ) / (p : ℝ) ^ 2 + 42 / (p : ℝ) ^ 2 = 150 / (p : ℝ) ^ 2 := by ring
  linarith

end Moments

/-! ## §5. The local factors of the Euler product over the primes -/

section PrimeProduct

/-- The local factor `h_q(w) = ∑_τ δ_q(τ) w^{e(τ)}` at the prime `q`. -/
noncomputable def primeFactor (e : ℕ → ℕ) (q : {n : ℕ // n.Prime}) : ℝ → ℝ :=
  powFactor (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) e

/-- `m_q(e) = ∑_τ δ_q(τ) e(τ)`, the uniform bound on `|h_q'|` over `[0,1]`. -/
noncomputable def primeMoment1 (e : ℕ → ℕ) (q : {n : ℕ // n.Prime}) : ℝ :=
  expMoment1 (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) e

/-- `S_q(e) = ∑_τ δ_q(τ) e(τ)^2`, the uniform bound on `|h_q''|` over `[0,1]`. -/
noncomputable def primeMoment2 (e : ℕ → ℕ) (q : {n : ℕ // n.Prime}) : ℝ :=
  expMoment2 (@scalarLocalMassReal (q : ℕ) ⟨q.2⟩) e

variable {e : ℕ → ℕ}

/-- The window radius `η = min 1 (1/(2 A_sup + 1))`, so that `2 A_sup η ≤ 1`. -/
noncomputable def windowRadius (e : ℕ → ℕ) : ℝ :=
  min 1 (1 / (2 * (∑' q : {n : ℕ // n.Prime}, primeMoment1 e q) + 1))

/-! ### The first one-sided derivative of a pgf that equals the Euler product -/

section PGFCore

variable {μ : PMF ℕ}

/-- On the window, the first derivative of the pgf within `Set.Iic 1` is that of the real product
`LogDerivProduct.prodG`. -/
theorem derivWithin_pgf_eq (hpgf : ∀ w ∈ Set.Icc (1 - windowRadius e) 1,
    PGFMean.pgf (fun n : ℕ => (μ n).toReal) w = LogDerivProduct.prodG (primeFactor e) w) {w : ℝ}
    (hw : w ∈ Set.Ioc (1 - windowRadius e) 1) :
    derivWithin (PGFMean.pgf fun n : ℕ => (μ n).toReal) (Set.Iic 1) w
      = derivWithin (LogDerivProduct.prodG (primeFactor e)) (Set.Iic 1) w := by
  refine Filter.EventuallyEq.derivWithin_eq ?_ (hpgf w ⟨hw.left.le, hw.right⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hw.left), self_mem_nhdsWithin]
    with x hx1 hx2
  exact hpgf x ⟨hx1.le, hx2⟩

end PGFCore

end PrimeProduct

/-! ## §6. The joint law `P_Π` as a `PMF`, and the pgf of a weighted coordinate sum -/

section Joint

open BSDTamagawa.MultiIndex

variable {P : Finset ℕ}

/-- **The joint valuation densities, as a `PMF`.** The mass at the multi-index `𝐣` is
`ENNReal.ofReal (Q_Π(𝐣))`. -/
noncomputable def tamagawaValuationPMF (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) : PMF (↥P → ℕ) :=
  ⟨fun j => ENNReal.ofReal (tamagawaValuationDensity P j),
    ENNReal.summable.hasSum_iff.mpr <| by
      rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun j => ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 j).1)
          (hasPolydiscExpansion_tamagawaValuationDensity P hP).2.1,
        tsum_tamagawaValuationDensity_eq_one P hP, ENNReal.ofReal_one]⟩

/-- The mass of the joint pmf at `𝐣` is `ENNReal.ofReal (Q_Π(𝐣))`, by definition. -/
theorem tamagawaValuationPMF_apply (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (j : ↥P → ℕ) :
    (tamagawaValuationPMF hP) j = ENNReal.ofReal (tamagawaValuationDensity P j) := rfl

/-- The masses of the joint pmf, read back in `ℝ`, are the densities `Q_Π(𝐣)`. -/
theorem tamagawaValuationPMF_apply_toReal (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (j : ↥P → ℕ) :
    ((tamagawaValuationPMF hP) j).toReal = tamagawaValuationDensity P j :=
  ENNReal.toReal_ofReal ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 j).1

/-- **The measure of the joint pmf is the joint valuation law `P_Π`.** -/
theorem tamagawaValuationPMF_toMeasure (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) :
    (tamagawaValuationPMF hP).toMeasure = tamagawaValuationMeasure P := by
  refine Measure.ext fun s hs => ?_
  rw [PMF.toMeasure_apply_eq_tsum, tamagawaValuationMeasure, Measure.sum_apply _ hs]
  refine tsum_congr fun j => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases h : j ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, mul_one,
      tamagawaValuationPMF_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- **The law of `∑_i t_i 𝐣_i`**, the pushforward of the joint law along the weighted coordinate
sum, as a `PMF ℕ`. -/
noncomputable def valWeightPMF (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (t : ↥P → ℕ) : PMF ℕ :=
  (tamagawaValuationPMF hP).map (valWeightSum t)

/-- The law of the weighted sum is the pushforward of the joint pmf's measure. -/
theorem valWeightPMF_toMeasure_map (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (t : ↥P → ℕ) :
    (valWeightPMF hP t).toMeasure
      = (tamagawaValuationPMF hP).toMeasure.map (valWeightSum t) := by
  rw [valWeightPMF]
  exact (PMF.toMeasure_map _ _ (measurable_of_countable _)).symm

/-- The law of the weighted sum is the pushforward of the joint valuation law `P_Π`. -/
theorem valWeightPMF_toMeasure (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (t : ↥P → ℕ) :
    (valWeightPMF hP t).toMeasure = (tamagawaValuationMeasure P).map (valWeightSum t) := by
  rw [valWeightPMF_toMeasure_map, tamagawaValuationPMF_toMeasure]

/-! ### The one-parameter point `z_i = w^{t_i}` -/

/-- The multi-monomial at `z_i = w^{t_i}` is the ordinary power `w^{∑_i t_i 𝐣_i}`. -/
theorem multiMonomial_valWeightSum (t r : ↥P → ℕ) (w : ℝ) :
    multiMonomial r (fun i => ((w ^ t i : ℝ) : ℂ)) = ((w ^ valWeightSum t r : ℝ) : ℂ) := by
  have hterm : ∀ i : ↥P, (((w ^ t i : ℝ) : ℂ)) ^ r i = (((w ^ t i) ^ r i : ℝ) : ℂ) := fun i => by
    push_cast
    ring
  rw [multiMonomial, Finset.prod_congr rfl fun i _ => hterm i, ← Complex.ofReal_prod]
  congr 1
  rw [valWeightSum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => (pow_mul w (t i) (r i)).symm

/-- The local monomial at `z_i = w^{t_i}` is `w^{E_t(τ)}`. -/
theorem prod_pow_valExpWeight (t : ↥P → ℕ) (w : ℝ) (τ : ℕ) :
    ∏ i : ↥P, ((w ^ t i : ℝ) : ℂ) ^ padicValNat (i : ℕ) τ
      = ((w ^ valExpWeight P t τ : ℝ) : ℂ) := by
  have hterm : ∀ i : ↥P, ((w ^ t i : ℝ) : ℂ) ^ padicValNat (i : ℕ) τ
      = (((w ^ t i) ^ padicValNat (i : ℕ) τ : ℝ) : ℂ) := fun i => by
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => hterm i, ← Complex.ofReal_prod]
  congr 1
  rw [valExpWeight, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => (pow_mul w (t i) (padicValNat (i : ℕ) τ)).symm

/-- **The local factor of the joint valuation Euler product at `z_i = w^{t_i}` is the real power
factor `primeFactor`.** -/
theorem ofReal_primeFactor_eq (t : ↥P → ℕ) (q : {n : ℕ // n.Prime}) (w : ℝ) :
    ((primeFactor (valExpWeight P t) q w : ℝ) : ℂ)
      = ∑' τ : ℕ, ((@δ (q : ℕ) ⟨q.2⟩ τ).toReal : ℂ)
          * ∏ i : ↥P, ((w ^ t i : ℝ) : ℂ) ^ padicValNat (i : ℕ) τ := by
  rw [primeFactor, powFactor, Complex.ofReal_tsum]
  refine tsum_congr fun τ => ?_
  rw [prod_pow_valExpWeight, Complex.ofReal_mul, scalarLocalMassReal]

/-- The weighted power series converges absolutely on `[0, 1]`. -/
theorem summable_density_mul_pow_valWeightSum (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (t : ↥P → ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Summable fun j : ↥P → ℕ => tamagawaValuationDensity P j * w ^ valWeightSum t j :=
  Summable.of_nonneg_of_le
    (fun j => mul_nonneg ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 j).1
      (pow_nonneg hw0 _))
    (fun j => mul_le_of_le_one_right ((hasPolydiscExpansion_tamagawaValuationDensity P hP).1 j).1
      (pow_le_one₀ hw0 hw1))
    (hasPolydiscExpansion_tamagawaValuationDensity P hP).2.1

/-- **The joint valuation generating identity along the one-parameter family `z_i = w^{t_i}`:**
`∑_𝐣 Q_Π(𝐣) w^{∑_i t_i 𝐣_i} = ∏_p h_p(w^t)`. -/
theorem ofReal_tsum_density_mul_pow_valWeightSum (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (t : ↥P → ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ((∑' j : ↥P → ℕ, tamagawaValuationDensity P j * w ^ valWeightSum t j : ℝ) : ℂ)
      = ∏' q : {n : ℕ // n.Prime}, ∑' τ : ℕ, ((@δ (q : ℕ) ⟨q.2⟩ τ).toReal : ℂ)
          * ∏ i : ↥P, ((w ^ t i : ℝ) : ℂ) ^ padicValNat (i : ℕ) τ := by
  have hz : ∀ i : ↥P, ‖((w ^ t i : ℝ) : ℂ)‖ ≤ 1 := fun i => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw0 _)]
    exact pow_le_one₀ hw0 hw1
  refine (Complex.hasSum_ofReal.mpr
    (summable_density_mul_pow_valWeightSum hP t hw0 hw1).hasSum).unique ?_
  refine (hasSum_tamagawaValuationDensity_mul_multiMonomial_tprod_primes P hP hz).congr_fun
    fun j => ?_
  rw [multiMonomial_valWeightSum]
  push_cast
  ring

/-- **The pgf of the weighted coordinate sum is the weighted power series.** -/
theorem pgf_valWeightPMF (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (t : ↥P → ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    PGFMean.pgf (fun n : ℕ => ((valWeightPMF hP t) n).toReal) w
      = ∑' j : ↥P → ℕ, tamagawaValuationDensity P j * w ^ valWeightSum t j := by
  have habs : ∀ n : ℕ, ‖w ^ n‖ ≤ 1 := fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw0 n)]
    exact pow_le_one₀ hw0 hw1
  have hqint : Integrable (fun n : ℕ => w ^ n) (valWeightPMF hP t).toMeasure :=
    (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable (.of_forall habs)
  have hpint : Integrable (fun j : ↥P → ℕ => w ^ valWeightSum t j)
      (tamagawaValuationPMF hP).toMeasure :=
    (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (.of_forall fun j => habs _)
  rw [PGFMean.pgf]
  calc (∑' n : ℕ, ((valWeightPMF hP t) n).toReal * w ^ n)
      = ∫ n, w ^ n ∂ (valWeightPMF hP t).toMeasure := by
        rw [PMF.integral_eq_tsum _ _ hqint]
        exact tsum_congr fun n => by rw [smul_eq_mul]
    _ = ∫ j, w ^ valWeightSum t j ∂ (tamagawaValuationPMF hP).toMeasure := by
        rw [valWeightPMF_toMeasure_map,
          integral_map (measurable_of_countable _).aemeasurable
            measurable_from_top.aestronglyMeasurable]
    _ = ∑' j : ↥P → ℕ, tamagawaValuationDensity P j * w ^ valWeightSum t j := by
        rw [PMF.integral_eq_tsum _ _ hpint]
        exact tsum_congr fun j => by
          rw [smul_eq_mul, tamagawaValuationPMF_apply_toReal]

end Joint

/-! ## §7. The weighted exponents at the three weight vectors, and the cross moment -/

section Main

variable {ℓ ℓ' : ℕ}

/-- `E_{e_ℓ} = v_ℓ`, as functions. -/
theorem valExpWeight_fst_eq (hne : ℓ ≠ ℓ') :
    valExpWeight {ℓ, ℓ'} (valFstWeight ℓ ℓ') = fun τ => padicValNat ℓ τ :=
  funext (valExpWeight_fst hne)

/-- `E_{e_{ℓ'}} = v_{ℓ'}`, as functions. -/
theorem valExpWeight_snd_eq (hne : ℓ ≠ ℓ') :
    valExpWeight {ℓ, ℓ'} (valSndWeight ℓ ℓ') = fun τ => padicValNat ℓ' τ :=
  funext (valExpWeight_snd hne)

/-- `E_1 = v_ℓ + v_{ℓ'}`, as functions. -/
theorem valExpWeight_total_eq (hne : ℓ ≠ ℓ') :
    valExpWeight {ℓ, ℓ'} (valTotalWeight ℓ ℓ') = fun τ => padicValNat ℓ τ + padicValNat ℓ' τ :=
  funext (valExpWeight_total hne)

/-- Every element of `Π = {ℓ, ℓ'}` is prime. -/
theorem prime_mem_pair (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) :
    ∀ x ∈ ({ℓ, ℓ'} : Finset ℕ), Nat.Prime x := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hℓ
  · exact hℓ'

section LocalBounds

variable {p : ℕ} [Fact p.Prime]

/-- The cross moment is nonnegative: every term is. -/
theorem crossValuationMoment_nonneg (ℓ ℓ' : ℕ) : 0 ≤ crossValuationMoment p ℓ ℓ' :=
  tsum_nonneg fun t => crossValuationTerm_nonneg p ℓ ℓ' t

end LocalBounds

end Main

end WeierstrassCurve
