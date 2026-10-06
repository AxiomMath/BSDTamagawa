/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.AdditiveDecomposition
public import BSDTamagawa.Analysis.PGFMean
public import BSDTamagawa.Valuation.LawProbability

/-!
# Ingredients for the mean of `v_ℓ(Tam(E))`, granted the geometric tail law

For a fixed prime `ℓ`, let `P = P_{{ℓ}}` be the limiting joint valuation law at `Π = {ℓ}`, the
limiting law of the `ℓ`-adic valuation `v_ℓ(Tam(E))` of the Tamagawa product of short Weierstrass
curves ordered by height. Granted the geometric tail law `HasTailGeometricLaw q` at every prime
`q` (`δ_q(t) = a q^{-t}` for `t ≥ 5`, with `a ≤ 1`), one expects

`𝔼_P[v_ℓ(Tam(E))] = ∑_{p ∈ 𝒫} ∑_{t ≥ 1} δ_p(t) v_ℓ(t) < ∞`.

That identity is not proved here; this file sets up ingredients for it. The route goes through
the generating function of `P`: for `|w| ≤ 1` it is the scalar Euler product at `Π = {ℓ}`, whose
real local factors are `h_p(w) = ∑_t δ_p(t) w^{v_ℓ(t)}`, and the mean is then read off from the
moments `A_p = ∑_t δ_p(t) v_ℓ(t) = h_p'(1)`. The analytic input is set up for a general exponent
function `k` with `k(t) ≤ t + 1` and `2^{k(t)} ≤ t + 1`, which covers both `v_ℓ` and `Ω`.

## Main definitions

* `BSDTamagawa.ValuationMean.MassFamily`: conditions on masses `c` and an exponent `k` under which
  `w ↦ ∑_t c_t w^{k(t)}` may be differentiated termwise on `(-3/2, 3/2)`.
* `BSDTamagawa.ValuationMean.eulerFactor`: the real local Euler factor
  `h_p(w) = ∑_t δ_p(t) w^{k(t)}`.
* `BSDTamagawa.ValuationMean.eulerMoment`: the moment `A_p = ∑_t δ_p(t) k(t)`.
* `BSDTamagawa.ValuationMean.valuationDensity`: the limiting density `Q_{{ℓ}}(j)` of
  `v_ℓ(Tam(E))` on `ℤ_{≥0}`.
* `BSDTamagawa.ValuationMean.valuationPMF`: the same law as a `PMF ℕ`.

## Main results

* `BSDTamagawa.ValuationMean.map_tamagawaValuationMeasure`: `valuationPMF` is the pushforward of
  `P_{{ℓ}}` along `ℤ_{≥0}^{{ℓ}} ≃ ℤ_{≥0}`.
-/

@[expose] public section

namespace BSDTamagawa.ValuationMean

open Set

/-! ### A real mass family with bounded exponents -/

/-- The hypotheses under which `w ↦ ∑' t, c t · w ^ k t` may be differentiated termwise on
`(-3/2, 3/2)`. -/
structure MassFamily (c : ℕ → ℝ) (k : ℕ → ℕ) : Prop where
  /-- The masses are nonnegative. -/
  nonneg : ∀ t, 0 ≤ c t
  /-- The masses sum to `1`. -/
  hasSum_one : HasSum c 1
  /-- The exponent grows at most linearly. -/
  exp_le : ∀ t, (k t : ℝ) ≤ (t : ℝ) + 1
  /-- `2 ^ k t ≤ t + 1`: the exponent grows at most logarithmically. -/
  two_pow_exp_le : ∀ t, (2 : ℝ) ^ k t ≤ (t : ℝ) + 1
  /-- The second moment converges. -/
  summable_sq : Summable fun t => c t * ((t : ℝ) + 1) ^ 2

/-- `w ↦ ∑' t, c t · w ^ k t`, the local factor attached to a mass family. -/
noncomputable def localFactor (c : ℕ → ℝ) (k : ℕ → ℕ) (w : ℝ) : ℝ := ∑' t : ℕ, c t * w ^ k t

/-- The termwise derivative of `localFactor`. -/
noncomputable def localDeriv (c : ℕ → ℝ) (k : ℕ → ℕ) (w : ℝ) : ℝ :=
  ∑' t : ℕ, c t * (k t : ℝ) * w ^ (k t - 1)

/-- At `w = 1` the termwise derivative is the first moment `∑' t, c t · k t`. -/
theorem localDeriv_one (c : ℕ → ℝ) (k : ℕ → ℕ) :
    localDeriv c k 1 = ∑' t : ℕ, c t * (k t : ℝ) := by
  simp [localDeriv]

section

variable {c : ℕ → ℝ} {k : ℕ → ℕ} (H : MassFamily c k)

include H

/-- The first moment converges: `c t · k t ≤ c t (t+1)^2`. -/
theorem summable_moment : Summable fun t : ℕ => c t * (k t : ℝ) := by
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (H.nonneg t) (by positivity))
    (fun t => ?_) H.summable_sq
  have h1 : (k t : ℝ) ≤ ((t : ℝ) + 1) ^ 2 := by
    nlinarith [H.exp_le t, t.cast_nonneg (α := ℝ)]
  exact mul_le_mul_of_nonneg_left h1 (H.nonneg t)

/-- For `w ∈ (-3/2, 3/2)`, the termwise derivative `c_t k(t) w^{k(t)-1}` has norm at most
`c_t (t + 1)^2`. -/
theorem termwise_bound {w : ℝ} (hw : w ∈ Ioo (-(3 / 2) : ℝ) (3 / 2)) (t : ℕ) :
    ‖c t * (k t : ℝ) * w ^ (k t - 1)‖ ≤ c t * ((t : ℝ) + 1) ^ 2 := by
  have hct := H.nonneg t
  have hw₂ : |w| ≤ 2 := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hkey : |w| ^ (k t - 1) ≤ (t : ℝ) + 1 :=
    calc |w| ^ (k t - 1) ≤ (2 : ℝ) ^ (k t - 1) := pow_le_pow_left₀ (abs_nonneg w) hw₂ _
      _ ≤ (2 : ℝ) ^ k t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ ≤ (t : ℝ) + 1 := H.two_pow_exp_le t
  calc ‖c t * (k t : ℝ) * w ^ (k t - 1)‖ = c t * (k t : ℝ) * |w| ^ (k t - 1) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hct,
          abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
    _ ≤ c t * ((t : ℝ) + 1) * ((t : ℝ) + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (H.exp_le t) hct) hkey
          (pow_nonneg (abs_nonneg w) _) (by positivity)
    _ = c t * ((t : ℝ) + 1) ^ 2 := by ring

/-- **Termwise differentiation of the local factor.** On `(-3/2, 3/2)` the series
`∑' t, c t · w ^ k t` is differentiable with derivative `localDeriv c k w`. -/
theorem hasDerivAt_localFactor {w : ℝ} (hw : w ∈ Ioo (-(3 / 2) : ℝ) (3 / 2)) :
    HasDerivAt (localFactor c k) (localDeriv c k w) w := by
  have hone : (1 : ℝ) ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  have hsum1 : Summable fun t : ℕ => c t * (1 : ℝ) ^ k t := by
    simpa using H.hasSum_one.summable
  exact hasDerivAt_tsum_of_isPreconnected H.summable_sq isOpen_Ioo isPreconnected_Ioo
    (fun t x _ => by
      simpa [mul_assoc] using (hasDerivAt_pow (k t) x).const_mul (c t))
    (fun t x hx => termwise_bound H hx t) hone hsum1 hw

/-- The local factor is normalised: `f (1) = ∑' t, c t = 1`. -/
theorem localFactor_one : localFactor c k 1 = 1 := by
  simpa [localFactor] using H.hasSum_one.tsum_eq

/-- On `[0, 1]` the derivative of the local factor is bounded by the first moment. -/
theorem abs_localDeriv_le {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    |localDeriv c k w| ≤ ∑' t : ℕ, c t * (k t : ℝ) := by
  have hterm : ∀ t : ℕ, c t * (k t : ℝ) * w ^ (k t - 1) ≤ c t * (k t : ℝ) := by
    intro t
    have hck : (0 : ℝ) ≤ c t * (k t : ℝ) := mul_nonneg (H.nonneg t) (k t).cast_nonneg
    calc c t * (k t : ℝ) * w ^ (k t - 1) ≤ c t * (k t : ℝ) * 1 := by
          gcongr
          exact pow_le_one₀ hw.1 hw.2
      _ = c t * (k t : ℝ) := mul_one _
  have hnn : ∀ t : ℕ, 0 ≤ c t * (k t : ℝ) * w ^ (k t - 1) := fun t =>
    mul_nonneg (mul_nonneg (H.nonneg t) (k t).cast_nonneg) (pow_nonneg hw.1 _)
  have hsummable : Summable fun t : ℕ => c t * (k t : ℝ) * w ^ (k t - 1) :=
    Summable.of_nonneg_of_le hnn hterm (summable_moment H)
  rw [localDeriv, abs_of_nonneg (tsum_nonneg hnn)]
  exact hsummable.tsum_le_tsum hterm (summable_moment H)

end

/-! ### The scalar local densities as a mass family -/

open WeierstrassCurve

open scoped ENNReal

/-- Every `δ_p(t)` is finite. -/
theorem δ_ne_top' (p : ℕ) [Fact p.Prime] (t : ℕ) : δ p t ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [tsum_δ]; exact ENNReal.one_ne_top) (ENNReal.le_tsum t)

/-- The real masses `(δ_p(t)).toReal` sum to `1`. -/
theorem hasSum_toReal_δ (p : ℕ) [Fact p.Prime] : HasSum (fun t : ℕ => (δ p t).toReal) 1 := by
  have hsummable : Summable fun t : ℕ => (δ p t).toReal :=
    ENNReal.summable_toReal (by rw [tsum_δ]; exact ENNReal.one_ne_top)
  have hval : ∑' t : ℕ, (δ p t).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (δ_ne_top' p), tsum_δ, ENNReal.toReal_one]
  exact hval ▸ hsummable.hasSum

/-! ### The two exponent functions -/

/-- `Ω(t) ≤ t + 1`. -/
theorem cardFactors_cast_le (t : ℕ) :
    ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) ≤ (t : ℝ) + 1 := by
  have := FirstMoment.cardFactors_le_self t
  have : ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast this
  linarith

/-- `2^{Ω(t)} ≤ t + 1`. -/
theorem two_pow_cardFactors_cast_le (t : ℕ) :
    (2 : ℝ) ^ (ArithmeticFunction.cardFactors t : ℕ) ≤ (t : ℝ) + 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  · have h := FirstMoment.two_pow_cardFactors_le ht
    have h' : ((2 ^ (ArithmeticFunction.cardFactors t : ℕ) : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

/-- `v_ℓ(t) ≤ t + 1`, through `v_ℓ(t) ≤ Ω(t)`. -/
theorem factorization_cast_le (ℓ t : ℕ) : (((t.factorization) ℓ : ℕ) : ℝ) ≤ (t : ℝ) + 1 := by
  have h : (((t.factorization) ℓ : ℕ) : ℝ) ≤ ((ArithmeticFunction.cardFactors t : ℕ) : ℝ) := by
    exact_mod_cast FirstMoment.factorization_le_cardFactors t ℓ
  exact h.trans (cardFactors_cast_le t)

/-- `2^{v_ℓ(t)} ≤ t + 1`, through `v_ℓ(t) ≤ Ω(t)`. -/
theorem two_pow_factorization_cast_le (ℓ t : ℕ) :
    (2 : ℝ) ^ ((t.factorization) ℓ : ℕ) ≤ (t : ℝ) + 1 :=
  (pow_le_pow_right₀ (by norm_num) (FirstMoment.factorization_le_cardFactors t ℓ)).trans
    (two_pow_cardFactors_cast_le t)

/-- The exponent function `t ↦ v_ℓ(t)`. -/
def valExp (ℓ : ℕ) : ℕ → ℕ := fun t => (t.factorization) ℓ

/-- `valExp` unfolded. -/
theorem valExp_apply (ℓ t : ℕ) : valExp ℓ t = (t.factorization) ℓ := rfl

/-- `v_ℓ(t) ≤ t + 1`, in the `valExp` spelling. -/
theorem valExp_cast_le (ℓ : ℕ) : ∀ t, ((valExp ℓ t : ℕ) : ℝ) ≤ (t : ℝ) + 1 :=
  factorization_cast_le ℓ

/-- `2^{v_ℓ(t)} ≤ t + 1`, in the `valExp` spelling. -/
theorem two_pow_valExp_cast_le (ℓ : ℕ) : ∀ t, (2 : ℝ) ^ (valExp ℓ t) ≤ (t : ℝ) + 1 :=
  two_pow_factorization_cast_le ℓ

/-! ### The prime-indexed Euler family -/

/-- The real local Euler factor `h_p(w) = ∑_t δ_p(t) w^{k(t)}` at a prime `p`, and `1` at a
non-prime `p`. -/
noncomputable def eulerFactor (k : ℕ → ℕ) (p : ℕ) (w : ℝ) : ℝ :=
  if h : p.Prime then localFactor (fun t : ℕ => (@δ p ⟨h⟩ t).toReal) k w else 1

/-- The first `k`-moment `A_p = ∑_t δ_p(t) k(t)`, `0` off the primes. -/
noncomputable def eulerMoment (k : ℕ → ℕ) (p : ℕ) : ℝ :=
  if h : p.Prime then ∑' t : ℕ, (@δ p ⟨h⟩ t).toReal * (k t : ℝ) else 0

/-- At a prime the Euler factor is the local factor of the mass family `(δ_p(t))_t`. -/
theorem eulerFactor_of_prime (k : ℕ → ℕ) (p : ℕ) [Fact p.Prime] :
    eulerFactor k p = localFactor (fun t : ℕ => (δ p t).toReal) k :=
  funext fun _ => dite_eq_left Fact.out

/-- Off the primes the Euler factor is the constant `1`. -/
theorem eulerFactor_of_not_prime {k : ℕ → ℕ} {p : ℕ} (hp : ¬ p.Prime) :
    eulerFactor k p = fun _ : ℝ => 1 :=
  funext fun _ => dite_eq_right hp

/-- At a prime the moment is the first `k`-moment of `δ_p`. -/
theorem eulerMoment_of_prime (k : ℕ → ℕ) (p : ℕ) [Fact p.Prime] :
    eulerMoment k p = ∑' t : ℕ, (δ p t).toReal * (k t : ℝ) :=
  dite_eq_left Fact.out

/-- Off the primes the moment is `0`. -/
theorem eulerMoment_of_not_prime {k : ℕ → ℕ} {p : ℕ} (hp : ¬ p.Prime) : eulerMoment k p = 0 :=
  dite_eq_right hp

/-- The moments are nonnegative. -/
theorem eulerMoment_nonneg (k : ℕ → ℕ) (p : ℕ) : 0 ≤ eulerMoment k p := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [eulerMoment_of_prime]
    exact tsum_nonneg fun t => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  · rw [eulerMoment_of_not_prime hp]

/-- If `∑_t δ_q(t) k(t) ≤ 37/q²` in `ℝ≥0∞`, then `A_q ≤ 37/q²` in `ℝ`. -/
theorem eulerMoment_le_of_tsum_le {k : ℕ → ℕ} {q : ℕ} [Fact q.Prime]
    (hmom : (∑' t : ℕ, δ q t * (k t : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2) :
    eulerMoment k q ≤ 37 / (q : ℝ) ^ 2 := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).pos.ne'
  have hne : ∀ t : ℕ, δ q t * (k t : ℝ≥0∞) ≠ ⊤ := fun t =>
    ENNReal.mul_ne_top (δ_ne_top' q t) (ENNReal.natCast_ne_top _)
  have htop : (37 : ℝ≥0∞) / (q : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (pow_ne_zero 2 hq0)
  calc eulerMoment k q = ∑' t : ℕ, (δ q t * (k t : ℝ≥0∞)).toReal := by
        rw [eulerMoment_of_prime]
        exact tsum_congr fun t => by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ = (∑' t : ℕ, δ q t * (k t : ℝ≥0∞)).toReal := (ENNReal.tsum_toReal_eq hne).symm
    _ ≤ ((37 : ℝ≥0∞) / (q : ℝ≥0∞) ^ 2).toReal := ENNReal.toReal_mono htop hmom
    _ = 37 / (q : ℝ) ^ 2 := by
        rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
        norm_num

/-- Above `q = 5` the moment bound `37/q²` is at most `2`. -/
theorem eulerMoment_le_two {k : ℕ → ℕ} {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q)
    (hmom : (∑' t : ℕ, δ q t * (k t : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2) :
    eulerMoment k q ≤ 2 := by
  have hq5 : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  refine (eulerMoment_le_of_tsum_le hmom).trans ?_
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

/-- If `∑_t δ_q(t) k(t) ≤ 37/q²` at every prime `q ≥ 5`, then the moments `A_p` are summable. -/
theorem summable_eulerMoment {k : ℕ → ℕ}
    (hmom : ∀ (q : ℕ) [Fact q.Prime], 5 ≤ q →
      (∑' t : ℕ, δ q t * (k t : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2) :
    Summable (eulerMoment k) := by
  have hsum : Summable fun s : ℕ => 37 * (1 / ((↑(s + 5) : ℝ)) ^ 2) :=
    ((summable_nat_add_iff 5).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left 37
  refine (summable_nat_add_iff 5).mp
    (Summable.of_nonneg_of_le (fun s => eulerMoment_nonneg k _) (fun s => ?_) hsum)
  by_cases hp : (s + 5).Prime
  · have : Fact (s + 5).Prime := ⟨hp⟩
    refine (eulerMoment_le_of_tsum_le (hmom (s + 5) (by omega))).trans ?_
    rw [mul_one_div]
  · rw [eulerMoment_of_not_prime hp]
    positivity

/-! ### The window constants `A_sup` and `η` -/

/-- The bound `A_sup = A_2 + A_3 + 2` on the moments `A_p`. -/
noncomputable def eulerSup (k : ℕ → ℕ) : ℝ := eulerMoment k 2 + eulerMoment k 3 + 2

/-- The window radius `η = (2 A_sup)⁻¹`. -/
noncomputable def eulerEta (k : ℕ → ℕ) : ℝ := (2 * eulerSup k)⁻¹

/-- `A_sup ≥ 2`. -/
theorem two_le_eulerSup (k : ℕ → ℕ) : 2 ≤ eulerSup k := by
  have := eulerMoment_nonneg k 2
  have := eulerMoment_nonneg k 3
  rw [eulerSup]; linarith

/-- `A_sup` dominates every moment. -/
theorem eulerMoment_le_eulerSup {k : ℕ → ℕ}
    (hmom : ∀ (q : ℕ) [Fact q.Prime], 5 ≤ q →
      (∑' t : ℕ, δ q t * (k t : ℝ≥0∞)) ≤ 37 / (q : ℝ≥0∞) ^ 2) (p : ℕ) :
    eulerMoment k p ≤ eulerSup k := by
  have h2 := eulerMoment_nonneg k 2
  have h3 := eulerMoment_nonneg k 3
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst hp2; rw [eulerSup]; linarith
    · by_cases hp3 : p = 3
      · subst hp3; rw [eulerSup]; linarith
      · have : Fact p.Prime := ⟨hp⟩
        have h5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
        have hle := eulerMoment_le_two h5 (hmom p h5)
        rw [eulerSup]; linarith
  · rw [eulerMoment_of_not_prime hp, eulerSup]; linarith

/-- `0 < η`. -/
theorem eulerEta_pos (k : ℕ → ℕ) : 0 < eulerEta k := by
  have := two_le_eulerSup k
  rw [eulerEta]
  positivity

/-- `η ≤ 1/4`, so the window `[1 - η, 1]` sits inside `[3/4, 1]`. -/
theorem eulerEta_le_quarter (k : ℕ → ℕ) : eulerEta k ≤ 1 / 4 := by
  have h := two_le_eulerSup k
  rw [eulerEta, inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- A point of `[0, 1]` lies in the differentiation interval `(-3/2, 3/2)`. -/
theorem mem_Ioo_of_mem_unitInterval {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    w ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) :=
  ⟨by linarith [hw.1], by linarith [hw.2]⟩

/-- A point of the window has `|w| ≤ 1`. -/
theorem abs_le_one_of_mem_window {k : ℕ → ℕ} {w : ℝ} (hw : w ∈ Icc (1 - eulerEta k) 1) :
    |w| ≤ 1 := by
  have h := eulerEta_le_quarter k
  have hpos := eulerEta_pos k
  rw [abs_le]
  exact ⟨by linarith [hw.1], hw.2⟩

/-! ### The Euler factors in `ℂ` -/

/-- For `|w| ≤ 1` the local series converges absolutely: `|δ_p(t) w^{k(t)}| ≤ δ_p(t)`. -/
theorem summable_toReal_δ_mul_pow (p : ℕ) [Fact p.Prime] (k : ℕ → ℕ) {w : ℝ} (hw : |w| ≤ 1) :
    Summable fun t : ℕ => (δ p t).toReal * w ^ k t := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => (δ p t).toReal)
    (hasSum_toReal_δ p).summable fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_pow]
  calc (δ p t).toReal * |w| ^ k t ≤ (δ p t).toReal * 1 := by
        gcongr
        exact pow_le_one₀ (abs_nonneg w) hw
    _ = (δ p t).toReal := mul_one _

/-- The coerced Euler factor at a prime, `|w| ≤ 1`: the coercion passes through the sum. -/
theorem ofReal_eulerFactor_of_prime (p : ℕ) [Fact p.Prime] (k : ℕ → ℕ) {w : ℝ} (hw : |w| ≤ 1) :
    ((eulerFactor k p w : ℝ) : ℂ) = ∑' t : ℕ, ((δ p t).toReal : ℂ) * (w : ℂ) ^ k t := by
  have hreal : HasSum (fun t : ℕ => (δ p t).toReal * w ^ k t) (eulerFactor k p w) := by
    rw [eulerFactor_of_prime, localFactor]
    exact (summable_toReal_δ_mul_pow p k hw).hasSum
  refine ((Complex.hasSum_ofReal.mpr hreal).tsum_eq).symm.trans ?_
  exact tsum_congr fun t => by push_cast; ring

/-! ### The singleton parameter set `Π = {ℓ}` -/

/-- Every index of `{ℓ}` is `singletonIdx ℓ`. -/
theorem eq_singletonIdx {ℓ : ℕ} (i : ↥({ℓ} : Finset ℕ)) : i = singletonIdx ℓ :=
  Subtype.ext (Finset.mem_singleton.mp i.2)

/-- The equivalence `ℤ_{≥0}^{{ℓ}} ≃ ℤ_{≥0}` sending a multi-index over `{ℓ}` to its value at
`ℓ`. -/
def singletonEquiv (ℓ : ℕ) : (↥({ℓ} : Finset ℕ) → ℕ) ≃ ℕ where
  toFun g := g (singletonIdx ℓ)
  invFun n := fun _ => n
  left_inv g := funext fun i => by rw [eq_singletonIdx i]
  right_inv _ := rfl

/-- The multi-monomial over `{ℓ}` at a constant vector is the single power `z^{j_ℓ}`. -/
theorem multiMonomial_singletonPrime (ℓ : ℕ) (g : ↥({ℓ} : Finset ℕ) → ℕ) (z : ℂ) :
    MultiIndex.multiMonomial g (fun _ => z) = z ^ g (singletonIdx ℓ) := by
  rw [MultiIndex.multiMonomial]
  exact Finset.prod_eq_single (singletonIdx ℓ)
    (fun b _ hb => absurd (eq_singletonIdx b) hb) fun h => absurd (Finset.mem_univ _) h

/-- For a prime `ℓ`, the scalar weight at `Π = {ℓ}`, `s = 0`, `w = 1` and constant `𝐳 = z` is
`z^{v_ℓ(t)}`. -/
theorem scalarWeight_singleton {ℓ : ℕ} (hℓ : ℓ.Prime) (z : ℂ) (t : ℕ) :
    scalarWeight {ℓ} 0 1 (fun _ => z) t = z ^ ((t.factorization) ℓ : ℕ) := by
  rw [scalarWeight, multiMonomial_singletonPrime, Nat.factorization_def t hℓ]
  simp [singletonIdx]

/-- For a prime `ℓ` and `|w| ≤ 1`, the coerced real Euler factor `h_p(w)` is the scalar local
factor at `Π = {ℓ}`, `s = 0`, `w = 1` with the constant vector `𝐳 = w`. -/
theorem ofReal_eulerFactor_eq_scalarLocalFactor {ℓ : ℕ} (hℓ : ℓ.Prime) (p : ℕ) {w : ℝ}
    (hw : |w| ≤ 1) :
    ((eulerFactor (valExp ℓ) p w : ℝ) : ℂ)
      = scalarLocalFactor {ℓ} p 0 1 (fun _ => (w : ℂ)) := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [ofReal_eulerFactor_of_prime p _ hw, scalarLocalFactor_eq_tsum_of_prime]
    exact tsum_congr fun t => by rw [scalarWeight_singleton hℓ, valExp_apply]
  · rw [eulerFactor_of_not_prime hp, scalarLocalFactor_of_not_prime hp]
    norm_num

/-! ### The univariate density and its generating function -/

/-- The limiting density `Q_{{ℓ}}(j)` of `v_ℓ(Tam(E))` on `ℤ_{≥0}`: the joint valuation density at
`Π = {ℓ}` of the multi-index with value `j`. -/
noncomputable def valuationDensity (ℓ j : ℕ) : ℝ :=
  tamagawaValuationDensity {ℓ} (fun _ => j)

/-- If `ℓ` is prime, then every element of `{ℓ}` is prime. -/
theorem forall_prime_singleton {ℓ : ℕ} (hℓ : ℓ.Prime) : ∀ q ∈ ({ℓ} : Finset ℕ), Nat.Prime q :=
  fun q hq => by rw [Finset.mem_singleton.mp hq]; exact hℓ

/-- Each `Q_{{ℓ}}(j)` is nonnegative. -/
theorem valuationDensity_nonneg {ℓ : ℕ} (hℓ : ℓ.Prime) (j : ℕ) : 0 ≤ valuationDensity ℓ j :=
  ((hasPolydiscExpansion_tamagawaValuationDensity {ℓ} (forall_prime_singleton hℓ)).1 _).1

/-- The densities `Q_{{ℓ}}(j)` sum to `1`. -/
theorem hasSum_valuationDensity {ℓ : ℕ} (hℓ : ℓ.Prime) : HasSum (valuationDensity ℓ) 1 := by
  have hsummable : Summable (valuationDensity ℓ) :=
    ((singletonEquiv ℓ).symm.summable_iff (f := tamagawaValuationDensity {ℓ})).mpr
      (hasPolydiscExpansion_tamagawaValuationDensity {ℓ} (forall_prime_singleton hℓ)).2.1
  have hval : ∑' j : ℕ, valuationDensity ℓ j = 1 := by
    rw [show (fun j : ℕ => valuationDensity ℓ j)
        = fun j : ℕ => tamagawaValuationDensity {ℓ} ((singletonEquiv ℓ).symm j) from rfl,
      (singletonEquiv ℓ).symm.tsum_eq]
    exact tsum_tamagawaValuationDensity_eq_one {ℓ} (forall_prime_singleton hℓ)
  exact hval ▸ hsummable.hasSum

/-- For `‖w‖ ≤ 1`, `∑_j Q_{{ℓ}}(j) w^j` is the scalar Euler product at `Π = {ℓ}`, `s = 0`,
`w = 1` with the constant vector `𝐳 = w`. -/
theorem tsum_valuationDensity_mul_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    (∑' j : ℕ, ((valuationDensity ℓ j : ℝ) : ℂ) * w ^ j)
      = ∏' p : ℕ, scalarLocalFactor {ℓ} p 0 1 (fun _ => w) := by
  rw [← tsum_tamagawaValuationDensity_mul_multiMonomial {ℓ} (forall_prime_singleton hℓ)
    (z := fun _ => w) fun _ => hw]
  rw [← (singletonEquiv ℓ).symm.tsum_eq fun g : ↥({ℓ} : Finset ℕ) → ℕ =>
    ((tamagawaValuationDensity {ℓ} g : ℝ) : ℂ) * MultiIndex.multiMonomial g (fun _ => w)]
  exact tsum_congr fun j => by rw [multiMonomial_singletonPrime]; rfl

/-- The real generating series converges absolutely for `|w| ≤ 1`. -/
theorem summable_valuationDensity_mul_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {w : ℝ} (hw : |w| ≤ 1) :
    Summable fun j : ℕ => valuationDensity ℓ j * w ^ j := by
  refine Summable.of_norm_bounded (g := valuationDensity ℓ) (hasSum_valuationDensity hℓ).summable
    fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (valuationDensity_nonneg hℓ j), abs_pow]
  calc valuationDensity ℓ j * |w| ^ j ≤ valuationDensity ℓ j * 1 := by
        gcongr
        · exact valuationDensity_nonneg hℓ j
        · exact pow_le_one₀ (abs_nonneg w) hw
    _ = valuationDensity ℓ j := mul_one _

/-- For `|w| ≤ 1`, the coerced generating function `PGFMean.pgf Q_{{ℓ}}` at `w` is the scalar Euler
product at `Π = {ℓ}`, `s = 0`, `w = 1` with the constant vector `𝐳 = w`. -/
theorem ofReal_pgf_valuationDensity {ℓ : ℕ} (hℓ : ℓ.Prime) {w : ℝ} (hw : |w| ≤ 1) :
    ((PGFMean.pgf (valuationDensity ℓ) w : ℝ) : ℂ)
      = ∏' p : ℕ, scalarLocalFactor {ℓ} p 0 1 (fun _ => (w : ℂ)) := by
  rw [← tsum_valuationDensity_mul_pow hℓ (w := (w : ℂ)) (by simpa using hw)]
  have hreal : HasSum (fun j : ℕ => valuationDensity ℓ j * w ^ j)
      (PGFMean.pgf (valuationDensity ℓ) w) := by
    rw [PGFMean.pgf]
    exact (summable_valuationDensity_mul_pow hℓ hw).hasSum
  refine ((Complex.hasSum_ofReal.mpr hreal).tsum_eq).symm.trans ?_
  exact tsum_congr fun j => by push_cast; ring

/-! ### The law on `ℤ_{≥0}` -/

open MeasureTheory

/-- The limiting law of `v_ℓ(Tam(E))` on `ℤ_{≥0}`, as a `PMF ℕ` with mass `Q_{{ℓ}}(j)` at `j`. -/
noncomputable def valuationPMF (ℓ : ℕ) (hℓ : ℓ.Prime) : PMF ℕ :=
  ⟨fun j : ℕ => ENNReal.ofReal (valuationDensity ℓ j), by
    have h : ∑' j : ℕ, ENNReal.ofReal (valuationDensity ℓ j) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (valuationDensity_nonneg hℓ)
        (hasSum_valuationDensity hℓ).summable, (hasSum_valuationDensity hℓ).tsum_eq,
        ENNReal.ofReal_one]
    exact h ▸ ENNReal.summable.hasSum⟩

/-- The mass at `j`, read back in `ℝ`, is the density itself. -/
theorem toReal_valuationPMF_apply {ℓ : ℕ} (hℓ : ℓ.Prime) (j : ℕ) :
    ((valuationPMF ℓ hℓ) j).toReal = valuationDensity ℓ j :=
  ENNReal.toReal_ofReal (valuationDensity_nonneg hℓ j)

/-- `toReal_valuationPMF_apply` as an equality of functions. -/
theorem toReal_valuationPMF {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (fun j : ℕ => ((valuationPMF ℓ hℓ) j).toReal) = valuationDensity ℓ :=
  funext (toReal_valuationPMF_apply hℓ)

/-- `singletonEquiv` as a measurable equivalence. -/
def singletonMeasurableEquiv (ℓ : ℕ) : (↥({ℓ} : Finset ℕ) → ℕ) ≃ᵐ ℕ where
  toEquiv := singletonEquiv ℓ
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun _ => measurable_id

/-- The pushforward of `P_{{ℓ}}` along `singletonEquiv` is `valuationPMF`. -/
theorem map_tamagawaValuationMeasure {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Measure.map (singletonMeasurableEquiv ℓ) (tamagawaValuationMeasure {ℓ})
      = (valuationPMF ℓ hℓ).toMeasure := by
  refine Measure.ext_of_singleton fun n => ?_
  have hpre : (singletonMeasurableEquiv ℓ) ⁻¹' {n} = {(fun _ => n : ↥({ℓ} : Finset ℕ) → ℕ)} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun h => funext fun i => by rw [eq_singletonIdx i]; exact h, fun h => by rw [h]; rfl⟩
  rw [(singletonMeasurableEquiv ℓ).map_apply,
    (valuationPMF ℓ hℓ).toMeasure_apply_singleton _ (measurableSet_singleton n), hpre,
    tamagawaValuationMeasure_singleton]
  rfl

end BSDTamagawa.ValuationMean
